'use strict';

/**
 * Saltwater render service
 *
 * n8n is the brain: it schedules, holds state in Data Tables, decides what to
 * make and what to call it, and alerts on failure. This service is the hands:
 * it owns the disk, the ffmpeg binary and the YouTube upload.
 *
 * Every job is asynchronous. POST returns a job id immediately; n8n polls
 * GET /jobs/:id until status is "done" or "error". Job records are written to
 * disk so a restart mid-render does not lose the trail.
 */

const express = require('express');
const fs = require('fs');
const fsp = require('fs/promises');
const path = require('path');
const os = require('os');
const crypto = require('crypto');
const { spawn } = require('child_process');
const { google } = require('googleapis');

const DATA_DIR = process.env.DATA_DIR || '/data';
const PORT = Number(process.env.PORT || 8080);
const RENDER_KEY = process.env.RENDER_KEY || '';
const FAL_KEY = process.env.FAL_KEY || '';
const ELEVENLABS_API_KEY = process.env.ELEVENLABS_API_KEY || '';
const YT_CLIENT_ID = process.env.YT_CLIENT_ID || '';
const YT_CLIENT_SECRET = process.env.YT_CLIENT_SECRET || '';
const YT_REFRESH_TOKEN = process.env.YT_REFRESH_TOKEN || '';
// Sessions are filed here on upload. Shorts are not — dropping a 15-second
// clip into a sleep playlist means someone drifting off gets a hard cut.
// A per-job `playlist_id` overrides this; empty means no filing at all.
const YT_PLAYLIST_ID = process.env.YT_PLAYLIST_ID || '';
const PEXELS_API_KEY = process.env.PEXELS_API_KEY || '';

const DIRS = {
  visuals: path.join(DATA_DIR, 'assets', 'visuals'),
  loops: path.join(DATA_DIR, 'assets', 'loops'),
  tracks: path.join(DATA_DIR, 'assets', 'tracks'),
  renders: path.join(DATA_DIR, 'renders'),
  jobs: path.join(DATA_DIR, 'jobs'),
  tmp: path.join(DATA_DIR, 'tmp'),
};

const FAL_MODEL = 'fal-ai/bytedance/seedance/v1/pro/fast/text-to-video';

/**
 * How far to darken a loop, 0 (untouched) to 1 (nearly black).
 *
 * The library is split into two pools. Day clips — focus and study content,
 * watched in a lit room — stay untouched, so the default here is 0. Night
 * clips are graded down at generation time by passing "dim" on /jobs/visual,
 * because sleep content is watched in a dark room and a clip that reads well
 * at midday is glaring at 1am. 0.6 is the sleep setting: it takes a bright
 * scene down to dusk without crushing it to mud.
 *
 * LOOP_DIM changes the default for the whole service; "dim" on /jobs/visual
 * and /jobs/reloop overrides it per call.
 */
const DEFAULT_DIM = clamp01(Number(process.env.LOOP_DIM ?? 0));

/*
 * Loop picture quality. Defaults reproduce the previous hard-coded values
 * exactly, so nothing already in the library changes shape until it is
 * deliberately rebuilt.
 *
 * These belong together: CRF sets how much detail the encoder keeps and
 * maxrate caps the peaks. Moving one without the other is the classic way to
 * change nothing and believe you tested something.
 */
/*
 * The sea that runs under every session. Set AMBIENCE_SLUG to a track on the
 * volume and every render mixes it in beneath the music; leave it empty and
 * renders behave exactly as before. AMBIENCE_DB is how far under the music it
 * sits — both are overridable per job.
 */
/*
 * What language the audio is in. "zxx" is the ISO code for no linguistic
 * content, which is the honest answer for instrumental music and stops YouTube
 * guessing — guessing is how a Japanese caption track appeared on a video with
 * no words in it. Applied after upload, never during, and skipped silently if
 * YouTube refuses it. Set AUDIO_LANGUAGE='' to stop trying entirely.
 */
const AUDIO_LANGUAGE = process.env.AUDIO_LANGUAGE === undefined
  ? 'zxx' : String(process.env.AUDIO_LANGUAGE);

const AMBIENCE_SLUG = String(process.env.AMBIENCE_SLUG || '');
const AMBIENCE_DB = clampNum(Number(process.env.AMBIENCE_DB), -40, 0, -12);

const LOOP_CRF = clampNum(Number(process.env.LOOP_CRF), 14, 34, 26);
const LOOP_MAXRATE = clampNum(Number(process.env.LOOP_MAXRATE), 600, 6000, 2500);

/*
 * What is asked of fal. 720p and ten seconds were hard-coded, which meant
 * trying anything else was a redeploy. They are per-request now, with the old
 * values as defaults.
 */
const VISUAL_RESOLUTION = String(process.env.VISUAL_RESOLUTION || '720p');
const VISUAL_SECONDS = clampNum(Number(process.env.VISUAL_SECONDS), 3, 12, 10);

// ---------------------------------------------------------------- utilities

function clampNum(n, lo, hi, fallback) {
  const v = Number(n);
  if (!Number.isFinite(v)) return fallback;
  return Math.min(hi, Math.max(lo, v));
}

function clamp01(n) {
  if (!Number.isFinite(n)) return 0;
  if (n < 0) return 0;
  if (n > 1) return 1;
  return n;
}

/**
 * Night grade, expressed as a single 0..1 dial.
 *
 * Brightness and gamma do the darkening (gamma pulls the midtones down harder
 * than the blacks, so the water keeps some shape instead of going flat).
 * Saturation comes off because a bright orange sunset stays attention-grabbing
 * even when it is dim. The colorbalance pass leans blue and away from red,
 * which is what makes it read as moonlight rather than as an underexposed
 * daytime shot.
 */
function nightGrade(dim) {
  const d = clamp01(dim);
  if (d === 0) return '';
  const brightness = (-0.22 * d).toFixed(3);
  const contrast = (1 - 0.10 * d).toFixed(3);
  const saturation = (1 - 0.35 * d).toFixed(3);
  const gamma = (1 - 0.22 * d).toFixed(3);
  const red = (-0.06 * d).toFixed(3);
  const blue = (0.10 * d).toFixed(3);
  return `,eq=brightness=${brightness}:contrast=${contrast}:saturation=${saturation}:gamma=${gamma}`
    + `,colorbalance=rs=${red}:bs=${blue}`;
}

/**
 * Vivid grade — the opposite direction, for daytime relaxation and focus
 * content, which is watched awake in a lit room.
 *
 * This is the hyper-real landscape look: saturation and contrast up, midtones
 * lifted so shadows open rather than block up, a little unsharp for the
 * micro-contrast that reads as "HDR", and a teal-orange split — cool shadows,
 * warm highlights. Viewers now read this look as AI-generated even on real
 * photographs, which is worth knowing but is not a reason to avoid it: it is
 * simply what the top channels in that lane look like.
 *
 * The unsharp amount is kept low on purpose. Push it and you get halos on
 * every horizon, and the extra high-frequency detail wrecks the bitrate cap
 * the session render depends on.
 */
function vividGrade(vivid) {
  const v = clamp01(vivid);
  if (v === 0) return '';
  const brightness = (0.02 * v).toFixed(3);
  const contrast = (1 + 0.16 * v).toFixed(3);
  const saturation = (1 + 0.45 * v).toFixed(3);
  const gamma = (1 + 0.10 * v).toFixed(3);
  const redHi = (0.06 * v).toFixed(3);
  const blueHi = (-0.04 * v).toFixed(3);
  const blueSh = (0.05 * v).toFixed(3);
  const sharpen = (0.6 * v).toFixed(2);
  return `,eq=brightness=${brightness}:contrast=${contrast}:saturation=${saturation}:gamma=${gamma}`
    + `,colorbalance=rh=${redHi}:bh=${blueHi}:bs=${blueSh}`
    + `,unsharp=luma_msize_x=7:luma_msize_y=7:luma_amount=${sharpen}`;
}

/**
 * Pick the grade for a clip. The two directions are mutually exclusive — a
 * clip is either being taken down for night or pushed up for day — so if a
 * caller passes both, dim wins and vivid is ignored rather than the two
 * fighting each other through the filter chain.
 */
function gradeChain(opts) {
  const o = opts || {};
  const dim = clamp01(Number(o.dim));
  if (dim > 0) return nightGrade(dim);
  return vividGrade(Number(o.vivid));
}

/**
 * Resolve what a request asked for into a settled look. Asking for vivid and
 * saying nothing about dim means vivid — otherwise LOOP_DIM would quietly
 * override every day-pool request on a service configured for night.
 */
function lookFrom(opts) {
  const o = opts || {};
  const vivid = clamp01(Number(o.vivid));
  const dimGiven = o.dim !== undefined && o.dim !== null;
  const dim = dimGiven ? clamp01(Number(o.dim)) : undefined;
  if (vivid > 0 && !dim) return { dim: 0, vivid };
  return { dim: dim === undefined ? DEFAULT_DIM : dim, vivid: 0 };
}

function describeLook(look) {
  if (look.dim > 0) return `dim ${look.dim}`;
  if (look.vivid > 0) return `vivid ${look.vivid}`;
  return 'ungraded';
}

async function ensureDirs() {
  for (const dir of Object.values(DIRS)) {
    await fsp.mkdir(dir, { recursive: true });
  }
}

function slugSafe(value) {
  return String(value || '').replace(/[^a-zA-Z0-9._-]/g, '');
}

function run(cmd, args, { timeoutMs = 45 * 60 * 1000 } = {}) {
  return new Promise((resolve, reject) => {
    const child = spawn(cmd, args, { stdio: ['ignore', 'pipe', 'pipe'] });
    let stdout = '';
    let stderr = '';
    const timer = setTimeout(() => {
      child.kill('SIGKILL');
      reject(new Error(`${cmd} timed out after ${Math.round(timeoutMs / 1000)}s`));
    }, timeoutMs);

    child.stdout.on('data', (d) => { stdout += d.toString(); });
    child.stderr.on('data', (d) => { stderr += d.toString().slice(0, 4000); });
    child.on('error', (err) => { clearTimeout(timer); reject(err); });
    child.on('close', (code) => {
      clearTimeout(timer);
      if (code === 0) return resolve({ stdout: stdout.trim(), stderr: stderr.trim() });
      reject(new Error(`${cmd} exited ${code}: ${stderr.trim().slice(0, 1500)}`));
    });
  });
}

const ffmpeg = (args, opts) => run('ffmpeg', ['-y', '-v', 'error', ...args], opts);

async function probeDuration(file) {
  const { stdout } = await run('ffprobe', [
    '-v', 'error', '-show_entries', 'format=duration', '-of', 'csv=p=0', file,
  ], { timeoutMs: 60000 });
  const seconds = Number(stdout);
  if (!Number.isFinite(seconds)) throw new Error(`ffprobe returned no duration for ${file}`);
  return seconds;
}

/**
 * Mean level of a slice of audio, in dBFS.
 *
 * volumedetect reports on stderr, so this calls ffmpeg directly rather than
 * through the `ffmpeg` helper, which forces `-v error` and would suppress the
 * very line being parsed.
 */
/**
 * Dynamic range control for the session audio.
 *
 * A generated bed can contain a transient — a wave breaking, a swell — that
 * sits 15 dB above everything around it. On a normal track that is musical.
 * On a sleep track at 2am it wakes the listener, which is the one failure this
 * channel cannot afford. One did exactly that, and it was found by ear rather
 * than by anything in this file.
 *
 * The compressor is deliberately gentle and slow: a 3:1 ratio with a soft knee
 * and a 1.2s release rides the loud passages down without the pumping that
 * heavy compression puts on ambient material. The limiter behind it is the
 * hard stop — nothing gets past -3 dBFS whatever the bed does.
 *
 * Set SLEEP_DRC=0 to render flat, e.g. to compare against an earlier session.
 */
function sleepDrc() {
  if (String(process.env.SLEEP_DRC ?? '1') === '0') return '';
  // level=disabled matters. Without it alimiter normalises the output back up
  // to full scale, which silently undoes the ceiling — measured: the "limited"
  // peak came out at 0.0 dBFS instead of the -3.1 the limit implies.
  return 'acompressor=threshold=-18dB:ratio=3:attack=50:release=1200:knee=6:makeup=1.5,'
    + 'alimiter=limit=0.7:attack=5:release=200:level=disabled,';
}

/**
 * Find the loudest moment in a bed, and how far it sticks out.
 *
 * Walks the file in windows and records the peak of each. A bed that swells
 * and recedes has windows within a few dB of one another; a bed with a wave
 * crash in it has one window sitting well above the rest, and this reports
 * where. That is the difference between "atmospheric" and "wakes the listener
 * at 2am", and nothing in this service could see it until a listener did.
 */
async function transientScan(file, duration) {
  const win = 6;
  const peaks = [];
  for (let t = 0; t + 1 < duration; t += win) {
    const r = await run('ffmpeg', [
      '-hide_banner', '-nostats', '-ss', String(t), '-t', String(Math.min(win, duration - t)),
      '-i', file, '-af', 'volumedetect', '-f', 'null', '-',
    ], { timeoutMs: 60000 }).catch(() => null);
    // RMS, not peak. Peak barely moves across a piece of music — it is set by
    // whatever transient happens to be loudest — so a swell that doubles the
    // perceived volume can leave the peak almost unchanged. The first version
    // of this scan measured peak, reported every bed as "even", and missed a
    // passage a listener had already told me was too loud. RMS is what the ear
    // is actually responding to.
    const rms = r && r.stderr.match(/mean_volume:\s*(-?[\d.]+) dB/);
    const pk = r && r.stderr.match(/max_volume:\s*(-?[\d.]+) dB/);
    if (rms) peaks.push({ at: t, level: Number(rms[1]), peak: pk ? Number(pk[1]) : null });
  }
  if (!peaks.length) return null;

  const sorted = peaks.map((p) => p.level).slice().sort((a, b) => a - b);
  const median = sorted[Math.floor(sorted.length / 2)];
  const worst = peaks.reduce((a, b) => (b.level > a.level ? b : a));
  const quiet = peaks.reduce((a, b) => (b.level < a.level ? b : a));
  const above = Number((worst.level - median).toFixed(1));
  return {
    loudest_at_sec: worst.at,
    loudest_rms_dbfs: worst.level,
    quietest_rms_dbfs: quiet.level,
    typical_rms_dbfs: Number(median.toFixed(1)),
    swing_db: Number((worst.level - quiet.level).toFixed(1)),
    sticks_out_db: above,
    // 6 dB is roughly a doubling of perceived level against the bed's own norm.
    flag: above >= 9 ? 'loud passage - could wake a sleeper'
      : (above >= 6 ? 'noticeable swell' : 'even'),
  };
}

async function meanVolume(file, startSec, lenSec) {
  const r = await run('ffmpeg', [
    '-hide_banner', '-nostats',
    '-ss', String(Math.max(0, startSec)), '-t', String(lenSec),
    '-i', file, '-af', 'volumedetect', '-f', 'null', '-',
  ], { timeoutMs: 3 * 60 * 1000 });
  const m = r.stderr.match(/mean_volume:\s*(-?[\d.]+) dB/);
  return m ? Number(m[1]) : null;
}

/**
 * Measure one music bed.
 *
 * Integrated loudness (LUFS) is how loud the bed feels overall; the head and
 * tail levels are what actually matter at a join, because the session render
 * concatenates beds with a hard cut. A four-second window rather than an
 * instant, so a single quiet moment does not masquerade as a level change.
 */
/**
 * Spectral flatness — the one measurement that separates music from noise.
 *
 * Every other number in this service is a level: how loud, how much range,
 * how big a step at a join. None of them can tell a pad from a hiss, which is
 * exactly why two beds that were noise textures rather than music sat in
 * rotation for weeks passing every check while ruining every video they
 * appeared in.
 *
 * Flatness is the ratio of the geometric to the arithmetic mean of the power
 * spectrum. A tone concentrates its energy in a few bins and scores near zero;
 * noise spreads energy evenly and scores near one. Measured on this pipeline:
 * a sine 0.004, brown noise 0.44, white noise 0.85, a real music bed about
 * 0.04, and the two beds that had to be retired about 0.65.
 *
 * Returns the mean across the file, or null if the filter is unavailable —
 * a missing measurement must never fail a render.
 */
async function spectralFlatness(file) {
  try {
    const r = await run('ffmpeg', [
      '-hide_banner', '-nostats', '-i', file,
      '-af', 'aspectralstats=measure=flatness,'
        + 'ametadata=print:key=lavfi.aspectralstats.1.flatness:file=-',
      '-f', 'null', '-',
    ], { timeoutMs: 5 * 60 * 1000 });
    const hits = String(r.stdout || '').match(/flatness=([0-9.eE+-]+)/g) || [];
    if (!hits.length) return null;
    let sum = 0;
    let n = 0;
    for (const h of hits) {
      const v = Number(h.split('=')[1]);
      if (Number.isFinite(v)) { sum += v; n += 1; }
    }
    return n ? Number((sum / n).toFixed(4)) : null;
  } catch (err) {
    return null;
  }
}

// Above this, a bed is a texture rather than a piece of music. Set from the
// measured gap: real beds clustered around 0.04, the retired ones around 0.65.
// 0.25 sits in empty space between the two populations.
const NOISE_FLATNESS = Number(process.env.NOISE_FLATNESS ?? 0.25);

/**
 * How loud a finished bed sits, in LUFS.
 *
 * This was -16 for the whole life of the pipeline, which was simply the wrong
 * target. -16 LUFS is the podcast and broadcast convention: it exists so
 * speech stays intelligible over road noise. Sleep music is the opposite
 * problem — it plays in a silent room, to someone who is trying to stop
 * noticing it, often through a speaker a metre from their head. Everything the
 * channel has published has been mastered about six decibels too loud for the
 * only situation it is ever used in.
 *
 * -22 is the new default. YouTube only ever turns loud uploads down toward its
 * own -14 reference and never turns quiet ones up, so a quieter master stays
 * quiet on playback — which is the whole point.
 *
 * Overridable per job with target_lufs, because some material wants to sit
 * further back still.
 */
const TRACK_LUFS = clampNum(Number(process.env.TRACK_LUFS), -32, -12, -22);

function loudnormFilter(targetLufs) {
  const t = clampNum(Number(targetLufs), -32, -12, TRACK_LUFS);
  // The true-peak ceiling has to come down with the integrated level, or a
  // quieter master keeps its old peaks and simply gains crest factor — the
  // opposite of "smoother to listen to".
  //
  // The clamp is not cosmetic: loudnorm only accepts TP in [-9, 0] and errors
  // out otherwise. A first cut at this used t + 6 with no lower bound, which
  // asked for TP = -16 at a -22 target and failed every single job with
  // "Value -16.000000 for parameter 'TP' out of range". +13 gives a natural
  // 13 dB crest for ambient and lands inside the range everywhere it matters.
  const tp = Math.max(-9, Math.min(-1.5, t + 13));
  return { filter: `loudnorm=I=${t}:TP=${tp.toFixed(1)}:LRA=11`, target: t };
}

async function measureTrack(file) {
  const duration = await probeDuration(file);
  let integrated = null;
  let truePeak = null;
  let range = null;
  try {
    const r = await run('ffmpeg', [
      '-hide_banner', '-nostats', '-i', file,
      '-af', 'loudnorm=print_format=json', '-f', 'null', '-',
    ], { timeoutMs: 5 * 60 * 1000 });
    const m = r.stderr.match(/\{[\s\S]*?"input_i"[\s\S]*?\}/);
    if (m) {
      const j = JSON.parse(m[0]);
      integrated = Number(j.input_i);
      truePeak = Number(j.input_tp);
      range = Number(j.input_lra);
    }
  } catch (err) {
    // A bed that cannot be analysed should not fail the whole report.
    integrated = null;
  }
  const win = Math.min(4, Math.max(1, duration / 10));
  const flatness = await spectralFlatness(file);
  return {
    duration_sec: Math.round(duration),
    integrated_lufs: integrated,
    true_peak_dbtp: truePeak,
    loudness_range_lu: range,
    spectral_flatness: flatness,
    reads_as_noise: flatness === null ? null : flatness > NOISE_FLATNESS,
    head_dbfs: await meanVolume(file, 0, win),
    tail_dbfs: await meanVolume(file, duration - win, win),
    transient: await transientScan(file, duration),
  };
}

async function probeStreams(file) {
  const { stdout } = await run('ffprobe', [
    '-v', 'error', '-show_entries', 'stream=codec_type', '-of', 'csv=p=0', file,
  ], { timeoutMs: 60000 });
  return stdout.split('\n').map((s) => s.trim()).filter(Boolean);
}

/**
 * What kind of file is this? Stills and clips need different treatment, and a
 * file extension is not evidence, so ask ffprobe. A still reports no usable
 * duration; anything with real running time is treated as video.
 */
async function probeMedia(file) {
  const { stdout } = await run('ffprobe', [
    '-v', 'error',
    '-show_entries', 'format=format_name,duration',
    '-of', 'default=noprint_wrappers=1',
    file,
  ], { timeoutMs: 60000 });
  const format = ((stdout.match(/format_name=(.*)/) || [])[1] || '').trim();
  const duration = Number(((stdout.match(/duration=(.*)/) || [])[1] || '').trim());
  const seconds = Number.isFinite(duration) ? duration : 0;
  return { format, duration: seconds, isImage: seconds < 0.5 };
}

async function download(url, dest) {
  const res = await fetch(url);
  if (!res.ok) throw new Error(`download failed ${res.status} for ${url}`);
  const buf = Buffer.from(await res.arrayBuffer());
  await fsp.writeFile(dest, buf);
  return buf.length;
}

// -------------------------------------------------------------- job storage

const jobs = new Map();

async function persistJob(job) {
  try {
    await fsp.writeFile(path.join(DIRS.jobs, `${job.id}.json`), JSON.stringify(job, null, 2));
  } catch (err) {
    console.error('job persist failed', job.id, err.message);
  }
}

function createJob(kind, input) {
  const job = {
    id: crypto.randomUUID(),
    kind,
    input,
    status: 'running',
    created_at: new Date().toISOString(),
    updated_at: new Date().toISOString(),
    result: null,
    error: null,
    log: [],
  };
  jobs.set(job.id, job);
  persistJob(job);
  return job;
}

function step(job, message) {
  job.log.push(`${new Date().toISOString()} ${message}`);
  job.updated_at = new Date().toISOString();
  console.log(`[${job.kind}:${job.id}] ${message}`);
}

async function finishJob(job, result) {
  job.status = 'done';
  job.result = result;
  job.updated_at = new Date().toISOString();
  await persistJob(job);
}

async function failJob(job, err) {
  job.status = 'error';
  // describeApiError, not err.message. A googleapis rejection stringifies to
  // the bare word "Error" with the reason buried in response.data, and a job
  // whose recorded failure is "Error" tells whoever reads it nothing at all.
  job.error = describeApiError(err);
  job.updated_at = new Date().toISOString();
  console.error(`[${job.kind}:${job.id}] FAILED ${job.error}`);
  await persistJob(job);
}

function startJob(kind, input, worker) {
  const job = createJob(kind, input);
  Promise.resolve()
    .then(() => worker(job))
    .then((result) => finishJob(job, result))
    .catch((err) => failJob(job, err));
  return job;
}

// -------------------------------------------------------------------- brand

/**
 * The SALTWATER lockup, burned into every loop as a corner mark.
 *
 * It lives here as base64 rather than as a file in the repo for one reason:
 * server.js is the only thing that gets pasted into GitHub, so a mark that
 * travels inside it can never go missing, and the Dockerfile never has to
 * learn about a second file. Thirteen kilobytes is a fair price for that.
 *
 * The mark goes on at loop-build time, not at session time. The session render
 * stream-copies its loops for two hours; overlaying there would force a full
 * re-encode and cost hours of CPU per night. Overlaying here costs nothing —
 * the loop is being encoded anyway — and every session and Short inherits it.
 *
 * Consequence worth knowing: changing or removing the mark means re-looping
 * the library (/jobs/reloop), not re-rendering anything.
 */
const LOCKUP_B64 =
    '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'
  + '8d8Y2Xi1SNCtKQ61mdastZwbeEVk9jDrWC2ucndglb1yEmbteVLHW8pT57bO0RUWS8Cf7sE5t9XrdMQRZuuYc3/6R2ppkgSS'
  + 'dRrbLvZFgW3c4kW9C2RDrIsF1M0JOdc+/7HxBUvrK0OQvT5i3nqOOBQs4d35yVqzs3V57tcNZbim8udqt5abUsp7FUhrtnp5'
  + '+rouzLEVd1TAoKblb1lVvV7Tmq1Wzg8L+DY20RqStWZP8U35aI9ezfwmcu7+Qi9aYCCNziD7tNUcf8835eFKljzPq8OezG9e'
  + 'ThZm9/ZNudvwBgW906do9/um/Kjtv0/75r9AzewB/mc432NhLcdGzJuYOXX/K/zeX8rLlfZvwvzPyvK8OvJ1TqKwlqjTuD6d'
  + 'kGa3ulpPHtZzH9QjV/7uqe0p+l/0vkkje7Rcq12z6TSuWs79Nzx+XRfZas3CyrUOamP3jMtHtcp+4puya8a1nVqjkudtz7Dn'
  + 'Kd+U45MsTphNfqV0pW/Kn/imPErB9YCVvikPGl6D3e8cv+2bclwJSnXAN+Va35QLfVP+muoIa/x3Fo9LsnjWTuOR2tRzYdZJ'
  + '/aly5r0+e6H6+XIjU7vdF0wezzSaeJVrbZXrNmeLquV8Z/02yzqytmZvqXmQjXsS87+fsE9AMv/eZf51vinvqV0ZnJV6SW6D'
  + 'gi2vZls8WWs26M2w9b4Jyg24rvldZa4Fac3mn68sYyh1pvZXutNiOTzku4ljcY6DbsQv0SP0XwGfGxXwUB2tL1qztnKeaR3J'
  + 'wuw0fannw6xToUpKmLVtns7tmLJNw4xtpX8bt/reVrqXXurRk73/k0MqMh4UYbZqOX+L1mVZR7JO43sCpu1W4yDrf/fHr0M/'
  + '+1iMnY+6Oc83Jf1Luy+P8ZkdfFOer1V5+u8XXhP62cW+KW9QIWHFn2dbPPurA+rcnk12lVSFt8jQmi1vzlxfGDkh1/VVr/+l'
  + 'qvWb1mzVcv7PvsFo1miSrdZssD/hYicEgy7Wn//VEaaeRj05cOoWQ6n7R1p6bw32xlQqJCzwj/j20ySLJw2zJwVM+381LdoV'
  + 'vinR4736n6dl0MX6O9835duGUt4WOHWab8r/SZW6/x7lbxVelmt9U+ZEfv4035QvUyGRi1uTfNhJ/AVi8AJ17DhO3hVRtm4X'
  + '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'
  + 'XmvU5eS+xPiWuK7rft96CcwIaQvlHWaTHP1TQvNMnTTbK5KmN+v66DRNFOCMGNfpz7iu67rzu66tL8Xp7XbXdV13WeT6n7QY'
  + 'aNOmHHe5WbHLd26Xtc3qmDYQcciPcl3XdQ/LtUwat7A9FvmZx7tegZs47WywEGbPin1yN1Gmt4Vcd7f+zOt65KTvX5KFVM2f'
  + '1PMOsxe7ruu6I5od+qMS5GGVhTp5hKV+iagbGx+M/MzDruu67j2h81e4ruu698XI1VtzDLNdfhw3+oteJ/ZXwk6mT22fG/y5'
  + 'qKXj59TmV+KOteVMlG/wfFfSvZqmqfqyb16/xmUo1XRlYm9L86iHWXNmtkxtl2WWbUmbatJ1Zj8zmD63tKaX/PinTprZI+nX'
  + 'kHLtpoaneCzG3YqSYty/2diEjQnX/0iBdwBe2HH3nA0Pxyzft4TO3xIyfZqkr0iSbmubPi5Tfj+bokxGx9zSRl17s+W92qiH'
  + 'zxpNs5HzP82hTjaei5wT87ip60hkD+RwZOapsZ9WGU3zCUlqPgdg03BJ0uMx62TUs923Vq5GZe4OWJDoO4ZVMda2IiDF8Nzc'
  + 'n9uTsVm+DUhfwksSlW94l+QZvnRmtUzx58V1Xff+XMtkINGWrrDaabz9XsyRxp+4W5ZDB92GRGX5ZOJ1Tg25xS3blkzv0mGY'
  + '9oYbtySdxo2vroa23YR2e6I8zE10boxfJ/tyKJ9kZ7L+iBK0+zVftifrLXUam+lcbp/n/6Sdzivzz1JJl+m+XLv1knUPLdWR'
  + 'bf9v8p4EfFLHty07XXca6pqRpBv0eaMdUGa6hc3Ww3hbYKerNf+ytNPVGK+D8xHN1ViNlLRRw7RVX4pZCz+tWwruNO5MLc0Z'
  + 'oLfrpJn9YaKbXZKu9PoBu3dDlDLMJqmQUd9XhHe8mLdRu7b897SOLWWY7SzTIc2pb0iapDVGq/Mq77HzhvVdhh4pX5ht/L9a'
  + 'k0t0Suu0o17PuSx31y8lSStTD9kXlOoOek2StEinJCyB0XolQblFpZ9HmF3TMpxIujNAsmBdRJ3cQ7+qcZiVftE2iO8G7d6t'
  + 'G7msrw5YV7nvTUbK0Xht8/47pnEfd6m0f38+qu0wcb0TZ6vVmdc4WY72aqY6Tq7cyBF7yunAUufu9Vz6alp/fulNPdRoqq95'
  + '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'
  + 'IVgG9u28EgAAAABJRU5ErkJggg==';

const BRAND_MODE = String(process.env.BRAND_MODE || 'corner').toLowerCase();
// Kept low on purpose. This sits in a dark bedroom for two hours; a bright
// rectangle in the corner is the fastest way to lose a sleep viewer.
const BRAND_OPACITY = clamp01(Number(process.env.BRAND_OPACITY ?? 0.32));
const BRAND_MARGIN_PCT = clamp01(Number(process.env.BRAND_MARGIN_PCT ?? 0.04));
// Bottom-LEFT by default. YouTube draws its own click-to-subscribe watermark in
// the bottom-right of the player, and two marks stacked in one corner reads as
// a mistake rather than a brand. Left corner for us, right corner for YouTube.
const BRAND_CORNER = String(process.env.BRAND_CORNER || 'bl').toLowerCase();
const LOCKUP_PATH = path.join(os.tmpdir(), 'saltwater-lockup.png');

let lockupReady = false;
function ensureLockup() {
  if (lockupReady) return true;
  try {
    fs.writeFileSync(LOCKUP_PATH, Buffer.from(LOCKUP_B64, 'base64'));
    lockupReady = true;
  } catch (err) {
    // A missing mark is not worth failing a night's render over.
    console.error('lockup write failed:', err.message);
    lockupReady = false;
  }
  return lockupReady;
}

/**
 * Extra ffmpeg inputs and the filter tail that puts the mark bottom-right.
 *
 * Returns the plain `format=yuv420p[v]` tail when branding is off, so callers
 * can always append `brand.chain` and never branch.
 */
function brandOverlay(scale) {
  const plain = { inputs: [], chain: ',format=yuv420p[v]' };
  if (BRAND_MODE === 'off' || BRAND_OPACITY <= 0) return plain;
  if (!ensureLockup()) return plain;

  const parts = String(scale).split(':');
  const w = Number(parts[0]);
  const h = Number(parts[1]);
  if (!Number.isFinite(w) || !Number.isFinite(h) || w < 2 || h < 2) return plain;

  // A vertical frame is half as wide, so the same percentage would render the
  // mark unreadably small on a phone. Shorts get a proportionally larger one.
  const isWide = w >= h;
  const pct = Number(process.env.BRAND_WIDTH_PCT ?? (isWide ? 0.18 : 0.30));
  const markW = Math.max(80, Math.round(w * clamp01(pct)));
  const margin = Math.round(w * BRAND_MARGIN_PCT);
  const op = BRAND_OPACITY.toFixed(3);

  const x = BRAND_CORNER.indexOf('l') !== -1 ? `${margin}` : `W-w-${margin}`;
  const y = BRAND_CORNER.indexOf('t') !== -1 ? `${margin}` : `H-h-${margin}`;

  return {
    inputs: ['-i', LOCKUP_PATH],
    chain: '[base];'
      + `[1:v]scale=${markW}:-1:flags=lanczos,format=rgba,colorchannelmixer=aa=${op}[lg];`
      + `[base][lg]overlay=${x}:${y}:eof_action=repeat,format=yuv420p[v]`,
  };
}

function brandStatus() {
  return {
    mode: BRAND_MODE,
    corner: BRAND_CORNER,
    opacity: BRAND_OPACITY,
    lockup: ensureLockup(),
  };
}

// ------------------------------------------------------------- media makers

/**
 * Turn a raw ~10s clip into a 9s seamless loop whose last second crossfades
 * back onto its first.
 *
 * The bitrate cap is the important part. The session render stream-copies this
 * file for hours, so its bitrate becomes the bitrate of a multi-gigabyte output.
 * Capped at 2.5 Mbps a one-hour session lands near 1.1 GB; uncapped it was
 * closer to 5 GB and filled the volume mid-render. Slow ambient footage carries
 * this bitrate with no visible loss.
 */
async function buildLoop(rawPath, loopPath, scale, look, motion) {
  const grade = gradeChain(look === undefined ? { dim: DEFAULT_DIM } : look);
  const brand = brandOverlay(scale);

  // `slow` stretches the source in time: 2 means half speed, so a 10s clip
  // becomes a 20s one and everything in it drifts instead of moving. Some
  // generated clips arrive far too energetic for a bedroom at 1am, and no
  // amount of grading fixes motion.
  //
  // `xfade` is how long the loop takes to dissolve back onto its own first
  // frame. One second is enough on slow water and visibly steps on anything
  // faster, because the eye catches the jump before the blend finishes.
  const slow = clampNum(motion && motion.slow, 1, 4, 1);

  /*
   * Picture quality, and why it is two dials rather than one.
   *
   * `crf` is what actually decides how much detail survives. `maxrate` only
   * trims peaks. On slow water CRF 26 settles well below 2500 kbps on its own,
   * so raising the cap by itself changes nothing at all — the encoder was
   * never touching it. Anyone tuning only maxrate measures no difference and
   * concludes bitrate does not matter here, which is the wrong conclusion
   * drawn from a test that never changed the bitrate.
   *
   * Both are capped, because this file's bitrate is the finished session's
   * bitrate: the two-hour render stream-copies it. 2500 kbps x 7200 s is a
   * 2.25 GB upload; 6000 kbps is 5.4 GB, and the volume is 4.5 GB. So 6000 is
   * the ceiling and even that only fits if little else is on disk.
   */
  const crf = Math.round(clampNum(motion && motion.crf, 14, 34, LOOP_CRF));
  const maxrate = Math.round(clampNum(motion && motion.maxrate, 600, 6000, LOOP_MAXRATE));

  const raw = await probeDuration(rawPath).catch(() => 10);
  const total = raw * slow;
  // The fade has to fit twice inside the clip with material left in between.
  const fade = clampNum(motion && motion.xfade, 0.5, Math.max(0.5, total / 3), 1);

  /*
   * Closing the loop.
   *
   * The previous version cut the source into 0-8 and 8-10 and crossfaded one
   * into the other. Those two pieces are already adjacent in time, so the
   * blend did nothing, the output ran from second 0 to second 10, and playing
   * it on repeat jumped from the last frame straight back to the first. A
   * viewer sees that as a step every nine seconds. One did.
   *
   * The fix is the standard construction. Hold back the first `fade` seconds,
   * play the middle, then dissolve the clip's own tail onto that held-back
   * head. The dissolve ends exactly on the frame the middle began with, so
   * the last frame of the output equals its first and the join disappears.
   *
   *   out = [ mid: fade .. total-fade ] + [ tail .. head crossfade ]
   *   length = total - fade
   *
   * Measured on a test clip: mean frame difference across the loop point fell
   * from 7.22 to 0.91.
   */
  const speed = slow === 1 ? '' : `setpts=${slow.toFixed(3)}*PTS,`;
  const f = fade.toFixed(3);
  const midEnd = (total - fade).toFixed(3);
  const tot = total.toFixed(3);

  // Applied after the grade: a straight multiplier on luma, used by the
  // auto-dim pass below to land a clip on a target brightness rather than on
  // a guessed dim value.
  const g = clampNum(motion && motion.lumaGain, 0.1, 1, 1);
  const gainChain = g === 1 ? '' : `,lutyuv=y='clip(val*${g.toFixed(4)},16,235)'`;

  const filter = [
    `[0:v]${speed}split=3[h][m][t];`,
    `[h]trim=0:${f},setpts=PTS-STARTPTS[head];`,
    `[m]trim=${f}:${midEnd},setpts=PTS-STARTPTS[mid];`,
    `[t]trim=${midEnd}:${tot},setpts=PTS-STARTPTS[tailseg];`,
    `[tailseg][head]xfade=transition=fade:duration=${f}:offset=0[blend];`,
    `[mid][blend]concat=n=2:v=1:a=0,`
      + `scale=${scale}:flags=lanczos${grade}${gainChain}${brand.chain}`,
  ].join('');
  await ffmpeg([
    '-i', rawPath,
    ...brand.inputs,
    '-filter_complex', filter,
    '-map', '[v]', '-an',
    '-c:v', 'libx264', '-preset', 'slow', '-crf', String(crf),
    '-maxrate', `${maxrate}k`, '-bufsize', `${maxrate * 2}k`,
    '-r', '30', '-g', '60', '-keyint_min', '60', '-sc_threshold', '0',
    '-movflags', '+faststart',
    loopPath,
  ], { timeoutMs: 20 * 60 * 1000 });
}

/**
 * Generate a ~10s clip on fal, then cut it down to a 9s seamless loop whose
 * last second crossfades back onto its first, so the repeat point is invisible.
 * Nothing longer is pre-encoded: the session render loops this file with
 * -stream_loop and -c:v copy, which costs almost nothing.
 */
async function makeVisual(job, {
  slug, aspect, prompt, dim, vivid,
  resolution, duration, slow, xfade, crf, maxrate, camera_fixed: cameraFixed,
}) {
  const safe = slugSafe(slug);
  const isWide = aspect === '16x9';
  const scale = isWide ? '1920:1080' : '1080:1920';
  const rawPath = path.join(DIRS.visuals, `${safe}.mp4`);
  const loopPath = path.join(DIRS.loops, `${safe}_loop.mp4`);

  // fal prices on pixels x frames, so resolution is the cost dial: a 10s
  // 1080p clip is roughly 2.2x a 720p one, because that is the pixel ratio.
  const wantRes = ['480p', '720p', '1080p'].indexOf(String(resolution)) === -1
    ? VISUAL_RESOLUTION : String(resolution);
  const wantSecs = clampNum(Number(duration), 3, 12, VISUAL_SECONDS);

  step(job, `requesting generation from fal (${wantRes}, ${wantSecs}s)`);
  const res = await fetch(`https://fal.run/${FAL_MODEL}`, {
    method: 'POST',
    headers: { Authorization: `Key ${FAL_KEY}`, 'Content-Type': 'application/json' },
    body: JSON.stringify({
      prompt,
      aspect_ratio: isWide ? '16:9' : '9:16',
      resolution: wantRes,
      duration: wantSecs,
      // A locked camera is what a two-hour sleep scene wants. The old default
      // let the model drift the frame, which reads as a slow pan that resets
      // every loop.
      camera_fixed: cameraFixed === undefined ? true : Boolean(cameraFixed),
    }),
  });
  if (!res.ok) throw new Error(`fal ${res.status}: ${(await res.text()).slice(0, 600)}`);
  const body = await res.json();
  const url = body && body.video && body.video.url;
  if (!url) throw new Error(`fal returned no video url: ${JSON.stringify(body).slice(0, 600)}`);

  step(job, 'downloading clip (fal deletes results after ~1h)');
  const bytes = await download(url, rawPath);

  const look = lookFrom({ dim, vivid });
  const motion = { slow, xfade, crf, maxrate };
  step(job, `building seamless loop (${describeLook(look)})`);
  await buildLoop(rawPath, loopPath, scale, look, motion);

  const loopSeconds = await probeDuration(loopPath);
  const loopBytes = await fsp.stat(loopPath).then((s) => s.size).catch(() => 0);
  // The number that decides whether a two-hour session fits on the volume,
  // reported here so it never has to be guessed: the session stream-copies
  // this file, so its size scales straight from these seconds to 7200.
  const projected7200 = loopSeconds > 0
    ? Math.round((loopBytes / loopSeconds) * 7200) : 0;
  return {
    slug: safe,
    aspect,
    file_path: rawPath,
    loop_path: loopPath,
    source_bytes: bytes,
    loop_seconds: Number(loopSeconds.toFixed(2)),
    loop_bytes: loopBytes,
    projected_2h_bytes: projected7200,
    projected_2h_gb: Number((projected7200 / 1e9).toFixed(2)),
    resolution: wantRes,
    requested_seconds: wantSecs,
    crf: Math.round(clampNum(crf, 14, 34, LOOP_CRF)),
    maxrate_kbps: Math.round(clampNum(maxrate, 600, 6000, LOOP_MAXRATE)),
    slow: clampNum(slow, 1, 4, 1),
    dim: look.dim,
    vivid: look.vivid,
  };
}

/**
 * Of the files Pexels offers for one video, pick the smallest that still fills
 * the frame. Their top rendition is often 4K, which is a slow download and a
 * pointless one — buildLoop scales to 1080 either way.
 */
function pickStockFile(video, targetWidth, isWide) {
  const files = (video.video_files || []).filter(
    (f) => f.link && f.width && f.height && String(f.file_type || '').indexOf('mp4') !== -1,
  );
  if (!files.length) return null;
  const oriented = files.filter((f) => (isWide ? f.width >= f.height : f.height > f.width));
  const pool = oriented.length ? oriented : files;
  const bigEnough = pool.filter((f) => f.width >= targetWidth);
  const sorted = (bigEnough.length ? bigEnough : pool).slice().sort((a, b) => a.width - b.width);
  return bigEnough.length ? sorted[0] : sorted[sorted.length - 1];
}

/**
 * Take a clip from Pexels rather than generating one.
 *
 * Same output contract as makeVisual — a ~10s raw on the volume plus a 9s
 * graded loop — so everything downstream (reloop, sessions, Shorts) treats a
 * stock clip and a generated clip identically. The difference is the price:
 * the Pexels API is free and unmetered at this volume, so growing the library
 * stops costing anything.
 *
 * Stock clips run long and vary in codec and frame rate, so the download is
 * cut to a 10-second window from the middle and re-encoded before it is
 * stored. That keeps the raw on disk to the same shape a fal clip has, which
 * is what lets /jobs/reloop retune a stock clip later without re-downloading.
 */
async function makeStockVisual(job, { slug, aspect, query, dim, vivid, exclude, page, min_duration }) {
  if (!PEXELS_API_KEY) throw new Error('PEXELS_API_KEY is not set on the render service');
  const safe = slugSafe(slug);
  const isWide = aspect === '16x9';
  const scale = isWide ? '1920:1080' : '1080:1920';
  const targetWidth = isWide ? 1920 : 1080;
  const orientation = isWide ? 'landscape' : 'portrait';
  const minDuration = Math.max(11, Number(min_duration) || 12);
  const skip = (Array.isArray(exclude) ? exclude : []).map(Number).filter(Number.isFinite);
  const pageNum = Math.max(1, Number(page) || (1 + Math.floor(Math.random() * 3)));

  const rawPath = path.join(DIRS.visuals, `${safe}.mp4`);
  const loopPath = path.join(DIRS.loops, `${safe}_loop.mp4`);
  const tmpPath = path.join(DIRS.tmp, `${safe}_stock.mp4`);

  step(job, `searching Pexels for "${query}" (${orientation}, page ${pageNum})`);
  const url = `https://api.pexels.com/videos/search?query=${encodeURIComponent(query)}`
    + `&orientation=${orientation}&size=medium&per_page=40&page=${pageNum}`;
  const res = await fetch(url, { headers: { Authorization: PEXELS_API_KEY } });
  if (!res.ok) throw new Error(`pexels ${res.status}: ${(await res.text()).slice(0, 400)}`);
  const body = await res.json();

  // Long enough to cut a 10s window out of the middle, and not one we already have.
  const candidates = ((body && body.videos) || []).filter(
    (v) => Number(v.duration) >= minDuration && skip.indexOf(Number(v.id)) === -1,
  );
  if (!candidates.length) {
    throw new Error(`pexels returned no usable clip for "${query}" `
      + `(${orientation}, page ${pageNum}, min ${minDuration}s) — try another query or page`);
  }

  const video = candidates[Math.floor(Math.random() * candidates.length)];
  const file = pickStockFile(video, targetWidth, isWide);
  if (!file) throw new Error(`pexels clip ${video.id} has no usable mp4 rendition`);

  step(job, `downloading pexels ${video.id} (${file.width}x${file.height}, ${video.duration}s)`);
  const bytes = await download(file.link, tmpPath);

  // Openings and endings are where stock clips have camera moves and fades.
  const start = Math.max(0, Math.floor((Number(video.duration) - 10) / 2));
  step(job, `cutting 10s from ${start}s and normalising`);
  try {
    await ffmpeg([
      '-ss', String(start), '-i', tmpPath, '-t', '10', '-an',
      '-c:v', 'libx264', '-preset', 'veryfast', '-crf', '20',
      '-r', '30', '-pix_fmt', 'yuv420p',
      rawPath,
    ], { timeoutMs: 15 * 60 * 1000 });
  } finally {
    await fsp.rm(tmpPath, { force: true });
  }

  const look = lookFrom({ dim, vivid });
  step(job, `building seamless loop (${describeLook(look)})`);
  await buildLoop(rawPath, loopPath, scale, look);

  const duration = await probeDuration(loopPath);
  const author = (video.user && video.user.name) || 'Pexels';
  return {
    slug: safe,
    aspect,
    file_path: rawPath,
    loop_path: loopPath,
    source_bytes: bytes,
    loop_seconds: Number(duration.toFixed(2)),
    dim: look.dim,
    vivid: look.vivid,
    source: 'pexels',
    pexels_id: Number(video.id),
    credit: `${author} on Pexels`,
    credit_url: video.url || '',
  };
}

/**
 * Turn a still into a slow, drifting move that returns exactly to where it
 * started.
 *
 * A session can now hold a single picture for two hours, so the number that
 * matters is not how far the frame moves but how often the movement comes
 * back around. At the old ten-second cycle a two-hour session breathed in and
 * out 720 times, which is often enough to notice. Thirty seconds is 240, and
 * at this speed that reads as drift rather than as a loop.
 *
 * Three things move, all on cosines of the same period so all three land back
 * at their starting value on the last frame:
 *
 *   zoom   1.10 -> 1.18, one full cycle
 *   x      one cycle left and right
 *   y      two cycles up and down
 *
 * One horizontal cycle against two vertical ones traces a figure of eight, so
 * the frame never retraces its own path and the movement does not read as
 * mechanical. The last frame still equals the first, which is what lets
 * buildLoop close the loop invisibly.
 *
 * The base zoom sits at 1.14 rather than 1.045 because panning needs somewhere
 * to pan to: at 1.14 there is about 6% of the frame in reserve on each side and
 * the drift uses 4.2% of it. Measured at the extremes of the move, no black
 * edge ever enters frame. It costs roughly a tenth of the picture, which a
 * 2848-wide source can afford without going soft at 1080p.
 *
 * The source is scaled to double the target first: zoompan samples from the
 * upscaled frame, which is what keeps a slow push from stepping between pixels.
 */
async function stillToClip(srcPath, outPath, scale) {
  const parts = scale.split(':');
  const w = Number(parts[0]);
  const h = Number(parts[1]);
  const seconds = clampNum(Number(process.env.STILL_MOTION_SECONDS), 5, 120, 30);
  const frames = Math.round(seconds * 30);
  // Amplitude as a fraction of the frame, so 9x16 drifts like 16x9 does.
  // 0.038 leaves about 26px of unused reserve at the tightest moment of the
  // move — the point where the vertical drift peaks while the zoom happens to
  // be near its widest. Raising this to 0.042 still works but cuts that to 17px,
  // which is too little to absorb a rounding difference in another ffmpeg build.
  const driftX = clamp01(Number(process.env.STILL_DRIFT ?? 0.038));
  const driftY = driftX;
  const filter = [
    `scale=${w * 2}:${h * 2}:force_original_aspect_ratio=increase:flags=lanczos`,
    `crop=${w * 2}:${h * 2}`,
    `zoompan=z='1.14+0.04*cos(2*PI*on/${frames})':d=${frames}`
      + `:x='iw/2-(iw/zoom/2)+${driftX}*iw*sin(2*PI*on/${frames})'`
      + `:y='ih/2-(ih/zoom/2)+${driftY}*ih*sin(4*PI*on/${frames})'`
      + `:s=${w}x${h}:fps=30`,
    'format=yuv420p',
  ].join(',');
  await ffmpeg([
    '-i', srcPath,
    '-vf', filter,
    '-frames:v', String(frames),
    '-c:v', 'libx264', '-preset', 'veryfast', '-crf', '20',
    '-r', '30', '-pix_fmt', 'yuv420p',
    outPath,
  ], { timeoutMs: 15 * 60 * 1000 });
}

/**
 * Bring in a visual from any URL — a clip or a still generated somewhere this
 * service cannot call, then parked somewhere with a direct link.
 *
 * Produces exactly what makeVisual and makeStockVisual produce, so an imported
 * asset is indistinguishable downstream: sessions, Shorts and /jobs/reloop all
 * treat it the same. Short sources are looped up to ten seconds rather than
 * rejected, because generators commonly hand back four or five.
 */
async function makeImportVisual(job, { slug, aspect, url, dim, vivid, start, source, credit }) {
  const safe = slugSafe(slug);
  const isWide = aspect === '16x9';
  const scale = isWide ? '1920:1080' : '1080:1920';
  const rawPath = path.join(DIRS.visuals, `${safe}.mp4`);
  const loopPath = path.join(DIRS.loops, `${safe}_loop.mp4`);
  const tmpPath = path.join(DIRS.tmp, `${safe}_import.bin`);

  step(job, `downloading ${String(url).slice(0, 140)}`);
  const bytes = await download(url, tmpPath);

  const media = await probeMedia(tmpPath);
  try {
    if (media.isImage) {
      step(job, `still (${media.format}) — building 10s slow zoom`);
      await stillToClip(tmpPath, rawPath, scale);
    } else if (media.duration >= 10.5) {
      const startAt = Number.isFinite(Number(start))
        ? Math.max(0, Number(start))
        : Math.max(0, Math.floor((media.duration - 10) / 2));
      step(job, `video ${media.duration.toFixed(1)}s — cutting 10s from ${startAt}s`);
      await ffmpeg([
        '-ss', String(startAt), '-i', tmpPath, '-t', '10', '-an',
        '-vf', `scale=${scale}:force_original_aspect_ratio=increase:flags=lanczos,crop=${scale}`,
        '-c:v', 'libx264', '-preset', 'veryfast', '-crf', '20',
        '-r', '30', '-pix_fmt', 'yuv420p',
        rawPath,
      ], { timeoutMs: 15 * 60 * 1000 });
    } else {
      step(job, `video only ${media.duration.toFixed(1)}s — repeating to fill 10s`);
      await ffmpeg([
        '-stream_loop', '-1', '-i', tmpPath, '-t', '10', '-an',
        '-vf', `scale=${scale}:force_original_aspect_ratio=increase:flags=lanczos,crop=${scale}`,
        '-c:v', 'libx264', '-preset', 'veryfast', '-crf', '20',
        '-r', '30', '-pix_fmt', 'yuv420p',
        rawPath,
      ], { timeoutMs: 15 * 60 * 1000 });
    }
  } finally {
    await fsp.rm(tmpPath, { force: true });
  }

  const look = lookFrom({ dim, vivid });
  step(job, `building seamless loop (${describeLook(look)})`);
  await buildLoop(rawPath, loopPath, scale, look);

  const duration = await probeDuration(loopPath);
  return {
    slug: safe,
    aspect,
    file_path: rawPath,
    loop_path: loopPath,
    source_bytes: bytes,
    loop_seconds: Number(duration.toFixed(2)),
    dim: look.dim,
    vivid: look.vivid,
    kind: media.isImage ? 'still' : 'video',
    source: source || 'import',
    credit: credit || '',
  };
}

/** Generate a music bed on ElevenLabs and loudness-match it to the rest. */
async function makeTrack(job, { slug, prompt, length_ms, target_lufs }) {
  const safe = slugSafe(slug);
  const rawPath = path.join(DIRS.tmp, `${safe}_raw.mp3`);
  const outPath = path.join(DIRS.tracks, `${safe}.mp3`);
  const lengthMs = Number(length_ms) || 180000;

  step(job, 'requesting bed from ElevenLabs');
  const res = await fetch('https://api.elevenlabs.io/v1/music', {
    method: 'POST',
    headers: { 'xi-api-key': ELEVENLABS_API_KEY, 'Content-Type': 'application/json' },
    body: JSON.stringify({
      prompt,
      music_length_ms: lengthMs,
      force_instrumental: true,
      output_format: 'mp3_44100_128',
      model_id: 'music_v1',
    }),
  });
  if (!res.ok) throw new Error(`elevenlabs ${res.status}: ${(await res.text()).slice(0, 600)}`);
  await fsp.writeFile(rawPath, Buffer.from(await res.arrayBuffer()));

  const ln = loudnormFilter(target_lufs);
  step(job, `normalising loudness to ${ln.target} LUFS`);
  await ffmpeg([
    '-i', rawPath,
    '-af', ln.filter,
    '-c:a', 'libmp3lame', '-b:a', '192k',
    outPath,
  ], { timeoutMs: 10 * 60 * 1000 });
  await fsp.rm(rawPath, { force: true });

  const duration = await probeDuration(outPath);
  // Checked here rather than only in the report, because the cheapest moment
  // to find out that a generation came back as texture instead of music is
  // the moment it arrives — not after it has been through a two-hour render.
  const flatness = await spectralFlatness(outPath);
  if (flatness !== null && flatness > NOISE_FLATNESS) {
    step(job, `WARNING: spectral flatness ${flatness} — this reads as noise, `
      + `not music (music sits near 0.04, retired textures near 0.65)`);
  }
  return {
    slug: safe,
    file_path: outPath,
    duration_sec: Math.round(duration),
    spectral_flatness: flatness,
    reads_as_noise: flatness === null ? null : flatness > NOISE_FLATNESS,
  };
}

/**
 * Bring in a bed from any URL — a field recording, or a piece made somewhere
 * this service cannot call.
 *
 * The visual side has had /jobs/import since the start; the audio side never
 * did, so every bed in the library had to come from ElevenLabs. That was fine
 * while all six were generated and is not fine the moment a real recording is
 * the right answer for a video.
 *
 * Normalised to -16 LUFS like every generated bed, so it sits level with the
 * rest of the library and nothing has to be re-balanced around it. Forced to
 * stereo because a mono source would otherwise play only on one side of the
 * render's stereo pair.
 */
async function makeImportTrack(job, { slug, url, mood, target_lufs }) {
  const safe = slugSafe(slug);
  const tmpPath = path.join(DIRS.tmp, `${safe}_import.bin`);
  const outPath = path.join(DIRS.tracks, `${safe}.mp3`);

  step(job, `downloading ${String(url).slice(0, 140)}`);
  const bytes = await download(url, tmpPath);

  try {
    const before = await measureTrack(tmpPath);
    const ln = loudnormFilter(target_lufs);
    step(job, `source ${before.duration_sec}s at ${before.integrated_lufs} LUFS`
      + ` — normalising to ${ln.target}`);
    await ffmpeg([
      '-i', tmpPath,
      '-af', ln.filter,
      '-ac', '2', '-ar', '44100',
      '-c:a', 'libmp3lame', '-b:a', '192k',
      outPath,
    ], { timeoutMs: 10 * 60 * 1000 });
  } finally {
    await fsp.rm(tmpPath, { force: true });
  }

  const after = await measureTrack(outPath);
  return {
    slug: safe,
    mood: mood || 'imported',
    file_path: outPath,
    source_bytes: bytes,
    duration_sec: Math.round(after.duration_sec),
    integrated_lufs: after.integrated_lufs,
    loudness_range_lu: after.loudness_range_lu,
    head_dbfs: after.head_dbfs,
    tail_dbfs: after.tail_dbfs,
  };
}

// ------------------------------------------------------------------ renders

/**
 * Build one seamless audio reel from the unique beds, and loop that instead of
 * splicing beds end to end.
 *
 * The bug this exists to fix: every bed fades out to near-silence in its last
 * seconds and starts at full level, and the concat demuxer splices with no
 * overlap at all. Measured on the live beds:
 *
 *   drift ends at -73.3 dBFS, focus starts at -20.6  ->  a 52.7 dB step
 *   hush  ends at -77.1 dBFS, sleep starts at -16.1  ->  a 61.0 dB step
 *
 * The sound dies away to nothing and then comes straight back. A listener
 * hears that as a swell out of silence, and it lands every three minutes for
 * the whole session. Jack heard it twice, at 6:00 and again at 42:00 — the
 * same drift->focus join, two cycles apart.
 *
 * It stayed hidden for so long because integrated loudness across the beds is
 * matched to 0.7 LU. Averages agree; it is only the seams that jump. Measuring
 * the beds told us nothing — the fault was in the space between them.
 *
 * The fix is a crossfade rather than a splice: each bed is dissolved into the
 * next over XFADE seconds, so the outgoing fade-out is covered by the incoming
 * fade-in and the level never dips. Then the reel is closed into a loop the
 * same way buildLoop closes video — hold back the head, play the middle,
 * dissolve the tail onto the held-back head — so repeating the reel has no
 * seam either. Every join in a two-hour session becomes a crossfade, including
 * the ones between repeats.
 *
 * The curve is qsin, the equal-power crossfade: uncorrelated material sums by
 * power, not amplitude, so a linear fade leaves a hole in the middle of every
 * dissolve.
 *
 * The crossfade is deliberately SHORT, and that took a second listener report
 * to get right. The first version dissolved over eight seconds without
 * trimming, which cured the level step and replaced it with a different fault:
 * for eight seconds two unrelated pieces of music play at once, in different
 * keys. Jack heard that at 14:12 — the tide-into-hush join — and called it
 * annoying rather than startling, which is exactly the difference between a
 * harmonic clash and a level jump.
 *
 * Trimming the fades first is what makes a short dissolve possible, because
 * both edges are then at full level. Measured across a looped reel of test
 * beds shaped like the real ones:
 *
 *   hard splice                    31.27 dB dip, no overlap
 *   8s crossfade, untrimmed         4.47 dB dip, 8s of two beds at once
 *   3s crossfade, fades trimmed     0.46 dB dip, 3s of two beds at once
 *
 * Both faults at once, which is the point: neither a dip nor a lingering
 * overlap. BED_XFADE tunes it if three seconds still reads as too much.
 *
 * And three seconds still read as too much. Jack caught the same tide-into-hush
 * join again at 13:41 — the reel had shortened from 1032s to 992s, and 14:12
 * scaled by that ratio is 13:39, so it was the same seam moved, not a new one.
 * Two unrelated pieces of music cannot be joined invisibly; a shorter dissolve
 * only makes the clash briefer.
 *
 * So the pipeline now sends ONE bed per session. A bed crossfaded into itself
 * is in its own key by definition, so the loop close has nothing to clash with,
 * and a two-hour session has no bed-to-bed transitions at all. The six beds
 * become six different-sounding videos rather than six textures fighting inside
 * every video — the same reasoning that put one picture in each session.
 *
 * The trim and the loop close still matter for a single bed: spliced against
 * itself, its own fade-out would run straight into its own fade-in. *
 * The reel is written as WAV, not AAC, and that is not a detail. A compressed
 * stream carries encoder priming samples, and -stream_loop re-inserts them on
 * every pass: measured on a test reel looped four times, the output ran 62 ms
 * long and every loop point held a 5 ms window at -240 dBFS -- true digital
 * silence. A gap that short is not heard as a gap, it is heard as a click, and
 * it would land at every repeat for the length of the session. PCM has no
 * priming, so a loop is sample-exact. The reel is a transient file deleted
 * after the render, so the size costs nothing.
 */
const BED_XFADE = clampNum(Number(process.env.BED_XFADE), 1, 30, 3);

// 'dip' — fade out to nothing, fade the next up from nothing, no overlap.
// 'xfade' — the old equal-power dissolve. See buildBedReel for why dip won.
const BED_JOIN = String(process.env.BED_JOIN || 'dip').toLowerCase();

// Long enough that the level change is a drift rather than a duck, short
// enough that the quiet patch never feels like the music stopped.
const BED_FADE = clampNum(Number(process.env.BED_FADE), 1, 30, 6);

/**
 * Find where a bed's sustained material actually starts and stops.
 *
 * Every bed is written with its own fade-in and fade-out, and those fades are
 * the whole reason the joins were a problem. Crossfading over them does not
 * help: the outgoing fade and the incoming fade are both already dropping, so
 * the dissolve happens across two ramps and still dips. Cutting them off first
 * means the crossfade joins two passages that are each at full level, and the
 * dissolve can then be short.
 *
 * Reads the RMS envelope in one pass, buckets it per second, and walks in from
 * each end until the level is within 3 dB of the bed's own typical level. The
 * trim is capped so a bed with a genuinely quiet opening is not gutted.
 */
async function sustainedEdges(file) {
  const DROP_DB = 3;
  const MAX_TRIM = 20;
  const r = await run('ffmpeg', [
    '-hide_banner', '-nostats', '-i', file,
    '-af', 'astats=metadata=1:reset=1,'
      + 'ametadata=print:key=lavfi.astats.Overall.RMS_level:file=-',
    '-f', 'null', '-',
  ], { timeoutMs: 5 * 60 * 1000 }).catch(() => null);
  if (!r) return null;

  const buckets = new Map();
  let sec = null;
  for (const line of r.stdout.split('\n')) {
    const p = line.match(/pts_time:([\d.]+)/);
    if (p) { sec = Math.floor(Number(p[1])); continue; }
    const v = line.match(/RMS_level=(-?[\d.]+|-inf)/);
    if (v && sec !== null) {
      const db = v[1] === '-inf' ? -120 : Number(v[1]);
      if (!buckets.has(sec) || db > buckets.get(sec)) buckets.set(sec, db);
    }
  }
  const secs = [...buckets.keys()].sort((a, b) => a - b);
  if (secs.length < 20) return null;
  const levels = secs.map((s) => buckets.get(s));
  const sorted = levels.slice().sort((a, b) => a - b);
  const typical = sorted[Math.floor(sorted.length / 2)];
  const floorDb = typical - DROP_DB;

  let head = 0;
  while (head < levels.length && levels[head] < floorDb) head += 1;
  let tail = levels.length - 1;
  while (tail > head && levels[tail] < floorDb) tail -= 1;
  if (tail - head < levels.length / 2) return null; // implausible; leave it alone

  return {
    start: Math.min(head, MAX_TRIM),
    end: levels.length - Math.min(levels.length - 1 - tail, MAX_TRIM),
  };
}

/**
 * Rewrite an audio file so its end runs into its beginning without a splice.
 *
 * Needed because the ambience layer is looped with -stream_loop for the whole
 * session. A wave recording that simply stops and restarts steps in amplitude
 * at the wrap, and that step is a click — heard most clearly during a bed dip,
 * when the sea is the only thing playing. Which is precisely the moment the
 * ambience exists to cover.
 *
 * Same construction as the picture loop: hold back the first `fade` seconds,
 * play the middle, then dissolve the file's own tail onto that held-back head.
 * The dissolve ends on the frame the middle began with, so last equals first.
 * Output is `fade` seconds shorter than the input.
 *
 * The dissolve is two explicit qsin fades summed with amix, NOT acrossfade.
 * acrossfade looks like the obvious tool and is wrong here: given two pieces
 * exactly as long as the fade, it emits an empty stream. Measured — the blend
 * came out at 0.000s and the "closed" loop was simply the middle section, so
 * the wrap it was supposed to remove was still there, 9.7 dB of step. The
 * manual version measures -0.2 dB across the same wrap with no power notch
 * through the blend.
 */
async function closeAudioLoop(src, dst, fadeSec) {
  const total = await probeDuration(src);
  const f = clampNum(fadeSec, 0.5, 20, 4);
  if (!Number.isFinite(total) || total <= f * 3) {
    throw new Error(`audio too short to close into a loop (${total}s, fade ${f}s)`);
  }
  const ff = f.toFixed(3);
  const midEnd = (total - f).toFixed(3);
  await ffmpeg([
    '-i', src,
    '-filter_complex',
    `[0:a]asplit=3[h][m][t];`
      + `[h]atrim=0:${ff},asetpts=PTS-STARTPTS,`
      + `afade=t=in:st=0:d=${ff}:curve=qsin[head];`
      + `[m]atrim=${ff}:${midEnd},asetpts=PTS-STARTPTS[mid];`
      + `[t]atrim=${midEnd}:${total.toFixed(3)},asetpts=PTS-STARTPTS,`
      + `afade=t=out:st=0:d=${ff}:curve=qsin[tailseg];`
      + `[tailseg][head]amix=inputs=2:duration=shortest:normalize=0[blend];`
      + `[mid][blend]concat=n=2:v=0:a=1[out]`,
    '-map', '[out]',
    '-c:a', 'pcm_s16le', '-ar', '44100', '-ac', '2',
    dst,
  ], { timeoutMs: 15 * 60 * 1000 });
  return probeDuration(dst);
}

async function buildBedReel(job, bedPaths, reelPath) {
  const n = bedPaths.length;
  const inputs = [];
  for (const p of bedPaths) inputs.push('-i', p);

  // Trim each bed back to its sustained region before anything else.
  const parts = [];
  const labels = [];
  const durations = [];
  let trimmed = 0;
  for (let i = 0; i < n; i += 1) {
    const e = await sustainedEdges(bedPaths[i]);
    const full = await probeDuration(bedPaths[i]).catch(() => 0);
    const label = `[t${i}]`;
    labels.push(label);
    if (e && (e.start > 0 || e.end > 0)) {
      parts.push(`[${i}:a]atrim=${e.start}:${e.end},asetpts=PTS-STARTPTS${label}`);
      durations.push(Math.max(1, e.end - e.start));
      trimmed += 1;
    } else {
      parts.push(`[${i}:a]anull${label}`);
      durations.push(Math.max(1, full));
    }
  }
  if (trimmed) step(job, `trimmed the built-in fades off ${trimmed} of ${n} beds`);

  // How one bed becomes the next.
  //
  // "dip" is the default and exists because the crossfade was wrong. An
  // equal-power dissolve holds both beds at -3 dB through the middle of the
  // transition, which is exactly loud enough for two unrelated pieces of music
  // in two unrelated keys to be heard fighting. Jack caught that three times
  // running, through two different fixes, and the reason no crossfade length
  // helped is that overlap itself was the problem.
  //
  // So: don't overlap. Fade one out to nothing, fade the next up from nothing,
  // butt them together. Nothing is ever sounding at the same time as anything
  // else, so there is nothing to clash. The cost is a soft dip in level every
  // few minutes, which on sleep music is close to unnoticeable and is in any
  // case far less noticeable than a key clash.
  //
  // In dip mode the reel also needs no loop close: the last bed already fades
  // out and the first already fades in, so the wrap is the same dip as every
  // other join.
  const dip = BED_JOIN === 'dip';
  if (dip) {
    const f = BED_FADE;
    const fades = [];
    for (let i = 0; i < n; i += 1) {
      const d = durations[i];
      const outAt = Math.max(0, d - f).toFixed(3);
      parts.push(`${labels[i]}afade=t=in:st=0:d=${f},`
        + `afade=t=out:st=${outAt}:d=${f}[f${i}]`);
      fades.push(`[f${i}]`);
    }
    if (n === 1) {
      parts.push(`[f0]anull[chained]`);
    } else {
      parts.push(`${fades.join('')}concat=n=${n}:v=0:a=1[chained]`);
    }
  } else {
    // The old equal-power dissolve, kept behind BED_JOIN=xfade so the previous
    // behaviour can be restored in one variable if the dip turns out worse.
    if (n === 1) {
      parts.push(`${labels[0]}anull[chained]`);
    }
    let cur = labels[0];
    for (let i = 1; i < n; i += 1) {
      const out = i === n - 1 ? '[chained]' : `[x${i}]`;
      parts.push(`${cur}${labels[i]}acrossfade=d=${BED_XFADE}:c1=qsin:c2=qsin${out}`);
      cur = `[x${i}]`;
    }
  }

  const chainPath = path.join(DIRS.tmp, `${path.basename(reelPath, '.wav')}_chain.wav`);
  step(job, dip
    ? `joining ${n} beds with a ${BED_FADE}s dip between each`
    : `crossfading ${n} beds at ${BED_XFADE}s`);
  await ffmpeg([
    ...inputs,
    '-filter_complex', parts.join(';'),
    '-map', '[chained]',
    '-c:a', 'pcm_s16le', '-ar', '44100', '-ac', '2',
    chainPath,
  ], { timeoutMs: 20 * 60 * 1000 });

  // In dip mode the wrap is already a dip, so there is nothing to close.
  if (dip) {
    const reelSeconds = await probeDuration(chainPath).catch(() => 0);
    step(job, `reel is ${Math.round(reelSeconds)}s and already loops cleanly`);
    await fsp.rename(chainPath, reelPath);
    return reelPath;
  }

  // Close the reel into a loop, so the join between one repeat and the next is
  // a crossfade too rather than the one hard splice we would have left behind.
  const total = await probeDuration(chainPath);
  const f = BED_XFADE;
  if (!Number.isFinite(total) || total <= f * 3) {
    step(job, 'reel too short to close; using the chain as-is');
    await fsp.rename(chainPath, reelPath);
    return reelPath;
  }
  // Was an inline copy of the same construction, using acrossfade, which
  // emits an empty blend when the pieces are exactly the fade length — so
  // this path silently produced an unclosed reel. It never showed up because
  // BED_JOIN defaults to dip and returns above. Fixed by sharing the helper,
  // which is tested.
  step(job, `closing the reel loop (${Math.round(total)}s)`);
  const closed = await closeAudioLoop(chainPath, reelPath, f);
  step(job, `  reel closed at ${closed.toFixed(1)}s`);
  await fsp.rm(chainPath, { force: true });
  return reelPath;
}

async function writeConcatList(listPath, files) {
  const body = files.map((f) => `file '${f.replace(/'/g, "'\\''")}'`).join('\n');
  await fsp.writeFile(listPath, `${body}\n`);
}

/**
 * Build the video side of a session as a concat list rather than one clip on
 * endless repeat, so a two-hour session moves through several scenes instead
 * of showing the same nine seconds eight hundred times.
 *
 * Every loop comes out of buildLoop with identical encoder settings, which is
 * what lets the render still stream-copy: no re-encode, no extra disk, no
 * extra hour of CPU. The price is a hard cut where one scene hands over to
 * the next. At a segment of several minutes that reads as a scene change
 * rather than a glitch — crossfading between scenes instead would force a
 * full re-encode of the entire session and cost hours per render.
 */
async function buildVideoList(listPath, loops, totalSeconds, segmentSeconds) {
  const lengths = [];
  for (const loop of loops) {
    const len = await probeDuration(loop);
    lengths.push(len > 0.5 ? len : 9);
  }

  const files = [];
  let elapsed = 0;
  let scene = 0;
  // Overshoot by a minute; -t trims the tail back to the exact duration.
  while (elapsed < totalSeconds + 60 && files.length < 40000) {
    const idx = scene % loops.length;
    const repeats = Math.max(1, Math.ceil(segmentSeconds / lengths[idx]));
    for (let n = 0; n < repeats; n += 1) files.push(loops[idx]);
    elapsed += repeats * lengths[idx];
    scene += 1;
  }
  await writeConcatList(listPath, files);
  return { entries: files.length, segments: scene };
}

async function renderSession(job, input) {
  const runId = slugSafe(input.run_id);
  const duration = Number(input.duration_sec);
  if (!Number.isFinite(duration) || duration < 60) throw new Error(`bad duration_sec: ${input.duration_sec}`);

  // visual_slugs is the current shape; visual_slug is still accepted so an
  // older caller keeps working.
  const slugs = (Array.isArray(input.visual_slugs) && input.visual_slugs.length
    ? input.visual_slugs
    : [input.visual_slug])
    .map(slugSafe)
    .filter(Boolean);
  if (!slugs.length) throw new Error('no visual_slug or visual_slugs supplied');

  const loops = slugs.map((s) => path.join(DIRS.loops, `${s}_loop.mp4`));
  for (const l of loops) {
    if (!fs.existsSync(l)) throw new Error(`visual loop missing: ${l}`);
  }

  /*
   * Make room before writing three gigabytes onto a four-and-a-half gigabyte
   * volume.
   *
   * This is here because the nightly run failed with "no space left on device"
   * an hour after thirty fal source clips landed on the same volume — each of
   * them 25 MB that no render will ever read, because sessions play the loop.
   * A render that discovers the disk is full does so two minutes in, with a
   * half-written file that then sits there taking up the space the next
   * attempt needs. The failure compounds.
   *
   * So: check first, and if the headroom is not there, drop the two things
   * that are safe to drop — orphaned renders of any age, and fal sources.
   * Loops and tracks are the library and are never touched. Only runs when
   * the disk is actually short, so a healthy volume keeps its sources and
   * /jobs/reloop keeps working.
   */
  const projectedGb = (duration / 7200) * 3.3;
  const diskBefore = await diskUsage();
  if (Number.isFinite(diskBefore.avail_gb) && diskBefore.avail_gb < projectedGb + 0.4) {
    step(job, `only ${diskBefore.avail_gb} GB free and this render needs about `
      + `${projectedGb.toFixed(1)} GB - sweeping`);
    const swept = await sweepVolume({ sources: true, renders: true, tmp: true, older_than_days: 0 });
    step(job, `freed ${swept.freed_mb} MB from ${swept.candidates} files, `
      + `${swept.disk_after.avail_gb} GB free now`);
    if (Number.isFinite(swept.disk_after.avail_gb)
      && swept.disk_after.avail_gb < projectedGb + 0.2) {
      throw new Error(`not enough disk for a ${Math.round(duration / 60)} min render: `
        + `${swept.disk_after.avail_gb} GB free, needs about ${projectedGb.toFixed(1)} GB. `
        + `Loops ${swept.assets.loops.mb} MB, tracks ${swept.assets.tracks.mb} MB, `
        + `renders ${swept.assets.renders.mb} MB. Grow the volume or shorten the session.`);
    }
  }

  const tracks = (input.tracks || []).map((t) => path.join(DIRS.tracks, `${slugSafe(t)}.mp3`));
  if (!tracks.length) throw new Error('no tracks supplied');
  for (const t of tracks) {
    if (!fs.existsSync(t)) throw new Error(`track missing: ${t}`);
  }

  // How long each scene holds before cutting to the next one.
  const segment = Math.max(30, Number(input.segment_sec) || 300);

  const reelPath = path.join(DIRS.tmp, `${runId}_reel.wav`);
  const videoListPath = path.join(DIRS.tmp, `${runId}_video.txt`);
  const outPath = path.join(DIRS.renders, `${runId}.mp4`);

  // The caller sends the bed sequence already repeated out to session length.
  // The reel repeats itself, so only the distinct beds are needed, in the order
  // they first appear.
  const uniqueBeds = [];
  for (const t of tracks) { if (uniqueBeds.indexOf(t) === -1) uniqueBeds.push(t); }
  await buildBedReel(job, uniqueBeds, reelPath);
  const reelSeconds = await probeDuration(reelPath).catch(() => 0);

  const plan = await buildVideoList(videoListPath, loops, duration, segment);

  const fadeOutStart = Math.max(0, duration - 12);

  /*
   * The continuous layer under everything.
   *
   * Why this exists: beds are joined by a dip, meaning each one fades out to
   * actual silence before the next fades up. I called that "close to
   * unnoticeable" in buildBedReel. It is not. Twelve seconds of nothing every
   * few minutes is startling in a dark room — a listener reported it at the
   * first join he sat through.
   *
   * A dip is still the right way to join two unrelated pieces of music, so the
   * fix is not to remove the hole but to put something in it. One sea running
   * unbroken for the whole session means the music recedes into water rather
   * than into silence, and the join stops being an event.
   *
   * It also replaces the old arrangement, where waves were baked into
   * individual beds on a coin flip. That made the ocean appear and disappear
   * every few minutes, and at a join you could lose the music and the sea in
   * the same second.
   *
   * Level is a plain dB offset rather than a loudness target: the ambience
   * asset is already mastered to the same -22 LUFS as the beds, so this just
   * says how far under the music it sits. -12 dB is present but never in the
   * way. amix carries normalize=0 because the default divides every input by
   * the input count, which would halve the music the moment a sea was added.
   */
  const ambSlug = slugSafe(String(input.ambience_slug || AMBIENCE_SLUG || ''));
  const ambSrc = ambSlug ? path.join(DIRS.tracks, `${ambSlug}.mp3`) : '';
  let ambPath = '';
  if (ambSrc && fs.existsSync(ambSrc)) {
    // Built once and kept beside the source, because closing the loop costs a
    // full decode and re-encode and the answer never changes.
    const closed = path.join(DIRS.tracks, `${ambSlug}.closed.wav`);
    if (!fs.existsSync(closed)) {
      step(job, `closing ${ambSlug} into a seamless loop (first use)`);
      try {
        const secs = await closeAudioLoop(ambSrc, closed, 4);
        step(job, `  ambience loop is ${secs.toFixed(1)}s and wraps cleanly`);
      } catch (err) {
        // Better a faint wrap in the sea than no sea at all.
        await fsp.rm(closed, { force: true });
        step(job, `  could not close the ambience loop (${err.message}); using it raw`);
      }
    }
    ambPath = fs.existsSync(closed) ? closed : ambSrc;
  }
  const useAmb = Boolean(ambPath);
  if (ambSlug && !useAmb) {
    // Loud, because a missing sea is the difference between the video we
    // intended and the one with holes in it — and it must not fail the render.
    step(job, `ambience "${ambSlug}" not found on the volume — rendering without it`);
  }
  const ambDb = clampNum(
    input.ambience_db === undefined ? AMBIENCE_DB : Number(input.ambience_db),
    -40, 0, AMBIENCE_DB,
  );

  /*
   * Holding the music back so the video opens on water alone.
   *
   * Only meaningful when there is an ambience layer — without one this would
   * open on silence, so it is ignored in that case rather than producing a
   * video that appears to be broken for its first few minutes.
   *
   * The delay is applied to the reel before it is mixed, and the reel is an
   * infinite looped input, so this prepends the gap once and everything after
   * it runs as normal.
   */
  const musicStart = clampNum(input.music_start_sec, 0, Math.max(0, duration - 60), 0);
  const musicFade = clampNum(input.music_fade_sec, 1, 120, 20);

  const tail = `${sleepDrc()}afade=t=in:st=0:d=8,afade=t=out:st=${fadeOutStart}:d=12`;

  // Built as two whole command lines rather than one line with pieces spliced
  // into it at computed offsets. The spliced version was shorter and I could
  // not read it, which is how an argument ends up in the wrong position and
  // ffmpeg reports something that has nothing to do with the mistake.
  const args = ['-f', 'concat', '-safe', '0', '-i', videoListPath,
    '-stream_loop', '-1', '-i', reelPath];
  if (useAmb) args.push('-stream_loop', '-1', '-i', ambPath);
  args.push('-t', String(duration));
  if (useAmb) {
    const delayMs = Math.round(musicStart * 1000);
    // adelay wants one value per channel, and the reel is stereo.
    const music = musicStart > 0
      ? `[1:a]adelay=${delayMs}|${delayMs},`
        + `afade=t=in:st=${musicStart.toFixed(3)}:d=${musicFade.toFixed(3)}[music];`
      : '';
    const musicLabel = musicStart > 0 ? '[music]' : '[1:a]';
    args.push(
      '-filter_complex',
      music
        + `[2:a]volume=${ambDb}dB[sea];`
        + `${musicLabel}[sea]amix=inputs=2:duration=first:dropout_transition=0:normalize=0[mixed];`
        + `[mixed]${tail}[a]`,
      '-map', '0:v:0', '-map', '[a]',
    );
  } else {
    args.push('-map', '0:v:0', '-map', '1:a:0', '-af', tail);
  }
  args.push(
    '-c:v', 'copy',
    '-c:a', 'aac', '-b:a', '192k', '-ar', '44100', '-ac', '2',
    '-movflags', '+faststart',
    outPath,
  );

  step(job, `rendering ${Math.round(duration / 60)} min session from ${loops.length} `
    + `visual(s) in ${plan.segments} segments of ${segment}s, `
    + `${uniqueBeds.length} beds on a ${Math.round(reelSeconds)}s seamless reel`
    + (useAmb ? `, ${ambSlug} underneath at ${ambDb} dB` : ', no ambience layer')
    + (useAmb && musicStart > 0
      ? `, water alone until ${Math.floor(musicStart / 60)}:${String(Math.round(musicStart % 60)).padStart(2, '0')} then music in over ${musicFade}s`
      : ''));
  try {
    await ffmpeg(args, { timeoutMs: 60 * 60 * 1000 });
  } catch (err) {
    // A failed render leaves a partial file that can be gigabytes. Without this
    // the volume fills up and every subsequent night fails too.
    await fsp.rm(outPath, { force: true });
    await fsp.rm(reelPath, { force: true });
    await fsp.rm(videoListPath, { force: true });
    throw err;
  }
  await fsp.rm(reelPath, { force: true });
  await fsp.rm(videoListPath, { force: true });

  await verify(job, outPath, duration);
  return outPath;
}

/**
 * Find a font ffmpeg can draw with.
 *
 * The image is node:20-alpine plus ffmpeg and nothing else, so until the
 * Dockerfile installs one there is no font on the box at all and drawtext
 * fails with "Cannot find a valid font". Rather than hard-code a path and
 * discover that at 2am, scan the places a font could be and report the answer
 * on /health, so a missing font is visible before a Short needs one.
 *
 * Cached: the filesystem does not change under a running container.
 */
// Type sizes on the 1080x1920 canvas. Both settable, because the right size is
// a judgement made by looking rather than a number to derive.
const TIP_SIZE = clampNum(Number(process.env.SHORT_TIP_SIZE), 28, 120, 54);
// Same size as the tip, on purpose. Shrinking the second line made it read as
// a footnote to the first, and it is not a footnote — the two beats are equal
// halves of the same message, one after the other, in the same voice.
const CTA_SIZE = clampNum(Number(process.env.SHORT_CTA_SIZE), 24, 120, TIP_SIZE);

/**
 * The two gradient scrims, built once and kept in tmp.
 *
 * Cached deliberately: they never change, and the alternative — generating the
 * ramp live for every frame of every Short — is what made the first attempt
 * hang. Rebuilt automatically if the container's tmp is cleared.
 */
const SCRIM_TOP_PATH = path.join(os.tmpdir(), 'saltwater-scrim-top.png');
const SCRIM_BOT_PATH = path.join(os.tmpdir(), 'saltwater-scrim-bottom.png');
async function ensureScrims(w, topH, botH) {
  if (!fs.existsSync(SCRIM_TOP_PATH)) {
    await ffmpeg(['-f', 'lavfi', '-i',
      `gradients=s=${w}x${topH}:c0=black@0.70:c1=black@0.0:x0=0:y0=0:x1=0:y1=${topH}`,
      '-frames:v', '1', SCRIM_TOP_PATH], { timeoutMs: 60000 });
  }
  if (!fs.existsSync(SCRIM_BOT_PATH)) {
    await ffmpeg(['-f', 'lavfi', '-i',
      `gradients=s=${w}x${botH}:c0=black@0.0:c1=black@0.80:x0=0:y0=0:x1=0:y1=${botH}`,
      '-frames:v', '1', SCRIM_BOT_PATH], { timeoutMs: 60000 });
  }
  return { top: SCRIM_TOP_PATH, bottom: SCRIM_BOT_PATH };
}

let fontPathCache;
function findFont() {
  if (fontPathCache !== undefined) return fontPathCache;
  // Serif italic, regular weight — Jack's pick off a side-by-side render on a
  // real frame.
  //
  // Bold was ruled out first: in either face it reads as shouting, which is
  // the wrong register for a sleep video and for the moment someone sees it.
  // Between the two regular italics, the sans is cleaner and the serif is
  // quieter and more written — and the serif is the one that looks like it
  // belongs beside a hand-painted picture rather than beside every other
  // channel in the feed.
  //
  // FONT_PATH overrides everything, so changing face is a variable rather than
  // a deploy.
  const candidates = [
    process.env.FONT_PATH,
    // Alpine's font-dejavu
    '/usr/share/fonts/dejavu/DejaVuSerif-Italic.ttf',
    '/usr/share/fonts/dejavu/DejaVuSans-Oblique.ttf',
    '/usr/share/fonts/dejavu/DejaVuSans.ttf',
    // Debian/Ubuntu layout, in case the base image ever changes
    '/usr/share/fonts/truetype/dejavu/DejaVuSerif-Italic.ttf',
    '/usr/share/fonts/truetype/dejavu/DejaVuSans-Oblique.ttf',
    '/usr/share/fonts/truetype/dejavu/DejaVuSans.ttf',
    '/usr/share/fonts/TTF/DejaVuSerif-Italic.ttf',
  ].filter(Boolean);
  fontPathCache = null;
  for (const c of candidates) {
    if (fs.existsSync(c)) { fontPathCache = c; break; }
  }
  return fontPathCache;
}

/**
 * One drawtext clause.
 *
 * The caption goes through a file rather than inline. drawtext's own escaping
 * treats ':' as an argument separator and "'" as a quote, so any caption with
 * a colon or an apostrophe — "Can't sleep?" being the obvious one — either
 * breaks the filter or silently loses characters. textfile sidesteps the whole
 * problem.
 *
 * The shadow is not decoration. These frames are graded to a mean luma in the
 * forties but carry bright areas — moonlight on water, bioluminescence — and
 * white text over the bright part of a dark picture is the one place it
 * disappears.
 */
/**
 * A fade-in, hold, fade-out envelope for drawtext's alpha.
 *
 * Quoted, because the expression is full of commas and a bare comma in a
 * filtergraph ends the filter. Nothing goes through a shell here, so the
 * quotes reach ffmpeg's own parser, which is what has to see them.
 *
 * Ramps rather than hard cuts. Text that snaps on is the visual equivalent of
 * a level step, and this is a sleep channel.
 */
function textAlpha(inAt, outAt, fade, peak) {
  const a = inAt.toFixed(2);
  const b = (inAt + fade).toFixed(2);
  const c = (outAt - fade).toFixed(2);
  const d = outAt.toFixed(2);
  const p = peak.toFixed(2);
  return `'if(lt(t,${a}),0,`
    + `if(lt(t,${b}),${p}*(t-${a})/${fade},`
    + `if(lt(t,${c}),${p},`
    + `if(lt(t,${d}),${p}*(${d}-t)/${fade},0))))'`;
}

/**
 * House style for on-screen copy: no full stop at the end of a line.
 *
 * A caption is not a sentence in a paragraph — the line break already does the
 * separating, and the trailing dot makes it read as closed and formal where
 * the whole register is meant to be unhurried. Question marks and commas stay,
 * because those carry meaning; a period only carries finality.
 *
 * Enforced here rather than trusted to the copy, because a style rule that
 * lives only in a document quietly stops being true.
 */
function captionLines(raw) {
  return String(raw)
    .replace(/\\n/g, '\n')
    // U+2028/2029 are line breaks too; normalise them rather than deleting
    // them, or two lines silently run together into one word.
    .replace(/[\u2028\u2029]/g, '\n')
    .split(/\r?\n/)
    // Strip every control character, not just the line breaks. Whatever
    // arrives here has been through a Code node, JSON, HTTP and a file, and
    // any one of those can leave something invisible behind.
    .map((line) => line.replace(/[\u0000-\u001f\u007f-\u009f\u2028\u2029]/g, '').trim())
    .map((line) => line.replace(/\.+$/, ''))
    .filter((line) => line.length)
    .slice(0, 4);
}

function drawTextClause(file, size, yExpr, alphaExpr) {
  return [
    `drawtext=fontfile=${findFont()}`,
    `textfile=${file}`,
    'fontcolor=white',
    `alpha=${alphaExpr}`,
    `fontsize=${size}`,
    'line_spacing=16',
    'x=(w-text_w)/2',
    `y=${yExpr}`,
    'shadowcolor=black@0.65',
    'shadowx=0',
    'shadowy=4',
  ].join(':');
}

/**
 * A vertical Short cut from the same picture and the same music as the session
 * it advertises.
 *
 * Two things the first version did not do.
 *
 * **It needed its own 9:16 artwork,** and there was exactly one vertical
 * visual in the library, itself retired for moving too much. So the Short pool
 * was empty in practice. This builds 1080x1920 out of the 16:9 loop instead:
 * a heavily blurred, slightly darkened copy of the frame fills the screen, and
 * the sharp frame sits across the middle at full width. That is the standard
 * vertical treatment for landscape source, and here it earns its place twice
 * over — the painting's composition survives intact instead of being cropped
 * to a ninth of its width, and the blurred bands above and below are exactly
 * where the text wants to go.
 *
 * **It said nothing.** A silent dark loop in a vertical feed is a swipe. The
 * hook and the call to action are burned in, because Shorts are watched with
 * the sound off far more often than a sleep channel would like to admit.
 */
async function renderShort(job, input) {
  const runId = slugSafe(input.run_id);
  const loopPath = path.join(DIRS.loops, `${slugSafe(input.visual_slug)}_loop.mp4`);
  if (!fs.existsSync(loopPath)) throw new Error(`visual loop missing: ${loopPath}`);

  const trackPath = path.join(DIRS.tracks, `${slugSafe(input.track_slug)}.mp3`);
  if (!fs.existsSync(trackPath)) throw new Error(`track missing: ${trackPath}`);

  const outPath = path.join(DIRS.renders, `${runId}.mp4`);
  const startAt = Number(input.audio_start_sec);
  const seek = Number.isFinite(startAt) ? startAt : 40;
  let seconds = clampNum(Number(input.seconds), 10, 180, 40);

  // Snap the length to a whole number of visual loop cycles.
  //
  // The picture loop is palindromic — its last frame is its first frame — so a
  // Short that runs for an exact multiple of it starts and ends on the same
  // image and repeats invisibly. Anything else does not: a 30-second Short cut
  // from a 29-second loop ends one second into the second pass, so when the
  // Shorts feed loops it, the picture jumps. That is a real visible fault at
  // the seam and the sort of thing that reads as "something happened at the
  // end" without being nameable.
  const loopSeconds = await probeDuration(loopPath).catch(() => 0);
  if (loopSeconds > 1) {
    const cycles = Math.max(1, Math.round(seconds / loopSeconds));
    const snapped = Math.round(cycles * loopSeconds * 1000) / 1000;
    if (Math.abs(snapped - seconds) > 0.05) {
      step(job, `snapping ${seconds}s to ${snapped}s — `
        + `${cycles} x the ${loopSeconds.toFixed(2)}s picture loop, so it repeats seamlessly`);
      seconds = snapped;
    }
  }
  const W = 1080;
  const H = 1920;

  // Full bleed: the picture is cropped to 9:16 and fills the screen, with the
  // text over it.
  //
  // An earlier version inset the whole 16:9 frame across the middle with a
  // blurred copy filling the bands above and below. It preserved the entire
  // composition, which sounded like the right trade and was not — on a phone
  // it reads as a photo in a frame rather than a place you are looking at, and
  // more than half the screen is spent on blur. Cropped, this painting keeps
  // the surf, the glow, the moon path and the edge of the rock, and it fills
  // the whole display.
  //
  // Two gradient scrims do the work the blurred bands used to do for
  // legibility: a light one at the top and a stronger one at the bottom, both
  // fading to nothing so there is no visible edge. They are not optional. The
  // frame drifts for the whole Short, so whatever sits behind a caption at the
  // first frame is not what sits behind it at the last, and the bottom of this
  // picture is the brightest part of it.
  const TOP_SCRIM = 480;
  const BOT_SCRIM = 740;
  const BOT_AT = H - BOT_SCRIM;
  const scrims = await ensureScrims(W, TOP_SCRIM, BOT_SCRIM);
  const parts = [
    `[0:v]scale=${W}:${H}:force_original_aspect_ratio=increase,crop=${W}:${H}[b]`,
    '[b][2:v]overlay=0:0[s1]',
    `[s1][3:v]overlay=0:${BOT_AT}[s2]`,
  ];
  let last = '[s2]';

  // Two beats, not one.
  //
  //   beat 1  a small thing the viewer can actually do, right now, for free
  //   beat 2  the session that is waiting for them
  //
  // The order is the whole point. A call to action that arrives before the
  // viewer has got anything is an advert; the same words after they have
  // actually breathed out once are an offer.
  //
  // Ten seconds is the default handover, and it is a real number rather than a
  // fraction of the Short so it does not drift when the length changes.
  // Reading the line takes about three seconds and a slow exhale takes six to
  // eight, so ten covers reading it and doing it once — which is the whole
  // job. Anything under about five would put the instruction on screen for
  // less time than the thing it asks for, which is worse than not asking.
  const font = findFont();
  const written = [];
  if (!font) {
    step(job, 'no font on this image — rendering the short without captions');
  } else {
    const tip = String(input.tip || input.hook || '').trim();
    const cta = String(input.cta || '').trim();
    const handover = clampNum(Number(input.handover_sec), 3,
      Math.max(4, seconds - 4), 10);

    // One drawtext per line, never a newline inside the text.
    //
    // A multi-line caption used to be a single drawtext with "\n" in it, which
    // is the obvious way to do it and rendered perfectly on ffmpeg 6. On the
    // ffmpeg 8 in this image the text shaper maps that newline to a .notdef
    // glyph — so the line still breaks AND a small empty box appears at the
    // end of it. It shipped in the first real Short.
    //
    // Positioning each line explicitly costs nothing, removes the control
    // character entirely rather than hoping the next ffmpeg handles it, and
    // makes the line spacing an actual number instead of a font metric.
    let n = 0;
    const drawLines = async (raw, size, topExpr, alphaExpr, tag) => {
      const lines = captionLines(raw);
      const lead = Math.round(size * 1.34);
      for (let i = 0; i < lines.length; i += 1) {
        const f = path.join(DIRS.tmp, `${runId}_${tag}${i}.txt`);
        await fsp.writeFile(f, lines[i], 'utf8');
        written.push(f);
        n += 1;
        const y = i === 0 ? topExpr : `${topExpr}+${i * lead}`;
        parts.push(`${last}${drawTextClause(f, size, y, alphaExpr)}[x${n}]`);
        last = `[x${n}]`;
      }
      return lines;
    };

    if (tip) {
      // The instruction sits in the dark band above the picture, at reading
      // height. 54px is about 5% of the frame width — plainly readable on a
      // phone and deliberately not more than that. Large type on a sleep video
      // is the visual equivalent of raising your voice, and the picture is
      // supposed to be the thing being looked at.
      const lines = await drawLines(tip, TIP_SIZE, 'h*0.10',
        textAlpha(0.6, handover + 0.8, 1.2, 0.94), 'tip');
      step(job, `tip: ${JSON.stringify(lines)}`);
    }
    if (cta) {
      // The offer sits low, near where the link to the full video appears —
      // but the last line has to finish above y=1540, because YouTube's own
      // caption, channel name and button rail cover everything below that.
      // Two lines of 54px stand about 145px, so 0.72 lands the bottom around
      // 1530. It starts fading in while the instruction is still leaving, so
      // the frame is never empty and never carries both messages at once.
      const lines = await drawLines(cta, CTA_SIZE, 'h*0.72',
        textAlpha(handover, seconds - 0.4, 1.2, 0.90), 'cta');
      step(job, `cta: ${JSON.stringify(lines)}`);
    }
    step(job, `tip holds to ${Math.round(handover)}s, then the session line`);
  }
  /*
   * The mark is OFF on Shorts from 2026-09-06, by decision.
   *
   * On a 9:16 phone screen it competes with the captions and with YouTube's
   * own action rail, and a Short's job is to stop a thumb, not to sign itself.
   * Long-form keeps the mark: nobody scrolls past a two-hour video.
   *
   * One thing this cannot undo. The mark is burned into a loop at loop-build
   * time, not here. A Short cropped from a 16:9 loop loses it automatically,
   * because the crop takes the middle 56% of the width and the mark lives in
   * the bottom-left corner — so turning the redraw off leaves it genuinely
   * unmarked. But a Short cut from a native 9:16 loop built after branding
   * landed carries the mark inside the loop itself, and no setting here can
   * remove it; that loop has to be rebuilt with BRAND_MODE=off.
   *
   * Everything below is the reasoning for the old always-draw behaviour, kept
   * because it explains why the redraw exists at all and what breaks if
   * someone switches it back on carelessly.
   *
   * Two failed attempts at being clever about this, so here it is in full.
   */
  // On a cropped 16:9 loop the mark is definitely missing: it is burned in at
  // the bottom-left, and taking the middle 56% of the width throws that corner
  // away. So it has to be redrawn there.
  //
  // On an already-vertical loop I skipped the redraw, on the grounds that such
  // a loop carries its own mark. That is only true of loops built after the
  // branding went in. tide-9x16-mtmf656w was built at 03:56 on 4 September and
  // branding landed that afternoon, so it has no mark and the Short went out
  // without one.
  //
  // Inferring from the file is guesswork either way, and the two errors are
  // not equal. A missing mark is a plain defect. A doubled one is not, because
  // the redraw lands in the same corner at the same relative size and the same
  // opacity as the burned-in one, so the two coincide almost exactly and read
  // as a single, slightly firmer mark. Given a choice between sometimes absent
  // and sometimes marginally denser, always-draw is the right side to be
  // wrong on.
  //
  // Bottom-left, 30% of the width, standard margin — left because YouTube's
  // own action rail owns the right edge.
  //
  // Whether the mark is drawn also decides whether its file is an ffmpeg input
  // at all. An earlier version always passed the input "so the indices stay
  // fixed" but only wrote the file when drawing, so the first vertical Short
  // died opening a file for a mark it was never going to use.
  // Default off for Shorts. `brand: true` on a single job puts it back, and
  // SHORT_BRAND=on flips the default, so the decision is reversible without
  // another deploy.
  const brandWanted = input.brand === undefined
    ? String(process.env.SHORT_BRAND || 'off').toLowerCase() !== 'off'
    : Boolean(input.brand);
  const drawMark = brandWanted && BRAND_MODE !== 'off' && BRAND_OPACITY > 0 && ensureLockup();
  step(job, drawMark ? 'drawing the mark bottom-left' : 'no mark on this Short');
  if (drawMark) {
    const markW = Math.round(W * clamp01(Number(process.env.BRAND_SHORT_WIDTH_PCT ?? 0.30)));
    const margin = Math.round(W * BRAND_MARGIN_PCT);
    parts.push(`[4:v]scale=${markW}:-1,format=rgba,`
      + `colorchannelmixer=aa=${BRAND_OPACITY.toFixed(3)}[mark]`);
    parts.push(`${last}[mark]overlay=${margin}:H-h-${margin}[br]`);
    last = '[br]';
  }

  parts.push(`${last}format=yuv420p[v]`);

  const fadeOut = Math.max(0, seconds - 2);
  step(job, `cutting a ${seconds}s vertical short${font ? ' with captions' : ''}`);
  try {
    await ffmpeg([
      '-stream_loop', '-1', '-i', loopPath,
      '-ss', String(seek), '-t', String(seconds), '-i', trackPath,
      // The scrims as still images, inputs 2 and 3.
      //
      // They were the `gradients` lavfi source first, which is correct and
      // unusably slow: as a live source it recomputes the ramp for every frame
      // of the Short, and a three-second test had not finished after five
      // minutes. As a single PNG each takes 0.08s to make once and costs an
      // ordinary overlay thereafter.
      '-loop', '1', '-i', scrims.top,
      '-loop', '1', '-i', scrims.bottom,
    ].concat(drawMark ? ['-loop', '1', '-i', LOCKUP_PATH] : []).concat([
      '-t', String(seconds),
      '-filter_complex', parts.join(';'),
      '-map', '[v]', '-map', '1:a:0',
      '-c:v', 'libx264', '-preset', 'medium', '-crf', '20', '-r', '30',
      '-c:a', 'aac', '-b:a', '192k', '-ar', '44100',
      '-af', `${sleepDrc()}afade=t=in:st=0:d=1.5,afade=t=out:st=${fadeOut}:d=2`,
      '-movflags', '+faststart',
      outPath,
    ]), { timeoutMs: 20 * 60 * 1000 });
  } finally {
    for (const f of written) await fsp.rm(f, { force: true });
  }

  await verify(job, outPath, seconds);
  return outPath;
}

/** Never upload a file that has not been probed. */
async function verify(job, file, targetSeconds) {
  const stat = await fsp.stat(file);
  const duration = await probeDuration(file);
  const streams = await probeStreams(file);
  const drift = Math.abs(duration - targetSeconds) / targetSeconds;

  if (stat.size < 500 * 1024) throw new Error(`render too small: ${stat.size} bytes`);
  if (!streams.includes('video')) throw new Error('render has no video stream');
  if (!streams.includes('audio')) throw new Error('render has no audio stream');
  if (drift > 0.05) throw new Error(`duration drift ${(drift * 100).toFixed(1)}% (${duration.toFixed(1)}s vs ${targetSeconds}s)`);

  step(job, `verified ${(stat.size / 1048576).toFixed(0)} MB, ${duration.toFixed(0)}s`);
  return { bytes: stat.size, duration_sec: Math.round(duration) };
}

// ------------------------------------------------------------------ youtube

function youtubeClient() {
  if (!YT_CLIENT_ID || !YT_CLIENT_SECRET || !YT_REFRESH_TOKEN) {
    throw new Error('YouTube credentials are not configured on the render service');
  }
  const auth = new google.auth.OAuth2(YT_CLIENT_ID, YT_CLIENT_SECRET);
  auth.setCredentials({ refresh_token: YT_REFRESH_TOKEN });
  return google.youtube({ version: 'v3', auth });
}

async function uploadToYouTube(job, file, meta) {
  const youtube = youtubeClient();
  const tags = String(meta.tags || '').split(',').map((t) => t.trim()).filter(Boolean);

  step(job, 'uploading to YouTube');
  const res = await youtube.videos.insert({
    part: ['snippet', 'status'],
    requestBody: {
      snippet: {
        title: String(meta.title || '').slice(0, 100),
        description: String(meta.description || '').slice(0, 5000),
        tags,
        categoryId: '10',
        // The language of the title and description, not of the audio.
        //
        // Nothing else optional goes in here. This call carries the rendered
        // file, costs 1,600 quota units and an hour of CPU to reach, and a
        // rejected field throws all of it away — which is exactly what
        // happened when defaultAudioLanguage was set here and YouTube refused
        // the value. Everything that is nice to have is applied afterwards by
        // finishVideo, where a failure costs nothing.
        defaultLanguage: 'en',
      },
      status: {
        privacyStatus: meta.privacy_status || 'private',
        selfDeclaredMadeForKids: false,
        embeddable: true,
        license: 'youtube',
      },
    },
    media: { body: fs.createReadStream(file) },
  });

  const videoId = res && res.data && res.data.id;
  if (!videoId) throw new Error('YouTube returned no video id');
  step(job, `uploaded as ${videoId}`);

  await finishVideo(job, youtube, videoId, meta, res.data.snippet);
  await setThumbnail(job, youtube, videoId, meta);
  await addToPlaylist(job, youtube, videoId, meta.playlist_id);
  return videoId;
}

/**
 * Everything applied to a video AFTER it exists: the audio language, and the
 * per-language titles and descriptions.
 *
 * Split out from the upload deliberately. Setting defaultAudioLanguage inside
 * videos.insert killed the whole job when YouTube refused the value, throwing
 * away a completed render. Anything optional belongs in a follow-up call that
 * is allowed to fail, and this one is: a published video without translations
 * is still a published video.
 *
 * Two things about videos.update that are easy to get wrong:
 *
 *   It REPLACES the parts it is given. Sending localizations wipes whatever
 *   was there rather than merging, which is why this only ever runs on a video
 *   it just created — a video someone has hand-edited in Studio must never be
 *   sent through here.
 *
 *   The snippet has to go along for the ride. Updating localizations without
 *   resending snippet.defaultLanguage fails with defaultLanguageNotSet, and a
 *   partial snippet blanks whatever is left out. So the snippet the insert
 *   returned is echoed back with only the fields we mean to change.
 *
 * Costs 50 quota units regardless of how many languages, against a 10,000/day
 * budget of which the upload already spent 1,600.
 *
 * The two changes are attempted together and then, if that is refused, one at
 * a time — so an unsupported audio language cannot cost us the translations,
 * and vice versa.
 */
async function finishVideo(job, youtube, videoId, meta, snippet) {
  const audioLang = String(meta.audio_language || AUDIO_LANGUAGE || '').trim();

  // Drop anything malformed rather than letting one bad row fail all of them,
  // and hold to YouTube's own limits so the API does not reject the batch.
  const clean = {};
  const loc = meta && meta.localizations;
  if (loc && typeof loc === 'object') {
    for (const [lang, v] of Object.entries(loc)) {
      if (!v || typeof v !== 'object') continue;
      const title = String(v.title || '').trim().slice(0, 100);
      if (!title) continue;
      clean[lang] = { title, description: String(v.description || '').slice(0, 5000) };
    }
  }
  const langs = Object.keys(clean);
  if (!audioLang && !langs.length) return null;

  const base = Object.assign({}, snippet, {
    defaultLanguage: snippet.defaultLanguage || 'en',
  });

  async function attempt(withAudio, withLocs) {
    const body = { id: videoId, snippet: Object.assign({}, base) };
    const parts = ['snippet'];
    if (withAudio) body.snippet.defaultAudioLanguage = audioLang;
    if (withLocs) { body.localizations = clean; parts.push('localizations'); }
    await youtube.videos.update({ part: parts, requestBody: body });
  }

  const wantAudio = Boolean(audioLang);
  const wantLocs = langs.length > 0;
  try {
    await attempt(wantAudio, wantLocs);
    const bits = [];
    if (wantAudio) bits.push(`audio language ${audioLang}`);
    if (wantLocs) bits.push(`${langs.length} localisations (${langs.join(', ')})`);
    step(job, `set ${bits.join(' and ')}`);
    return { audio: wantAudio ? audioLang : null, langs };
  } catch (err) {
    step(job, `combined metadata update refused (${describeApiError(err)}) — retrying separately`);
  }

  const out = { audio: null, langs: [] };
  if (wantLocs) {
    try {
      await attempt(false, true);
      step(job, `set ${langs.length} localisations (${langs.join(', ')})`);
      out.langs = langs;
    } catch (err) {
      step(job, `localisations failed (video is still published): ${describeApiError(err)}`);
    }
  }
  if (wantAudio) {
    try {
      await attempt(true, false);
      step(job, `set audio language ${audioLang}`);
      out.audio = audioLang;
    } catch (err) {
      step(job, `audio language "${audioLang}" rejected: ${describeApiError(err)}`);
    }
  }
  return out;
}

/**
 * Turn a googleapis error into something a log line can use.
 *
 * Their errors stringify to the bare word "Error" surprisingly often, with
 * everything useful hidden in response.data. A job that failed with a message
 * of "Error" is a job nobody can debug — that happened once already.
 */
function describeApiError(err) {
  const d = err && err.response && err.response.data;
  const inner = d && d.error;
  const parts = [];
  if (inner && inner.message) parts.push(inner.message);
  if (inner && Array.isArray(inner.errors)) {
    for (const e of inner.errors) {
      const bit = [e.reason, e.location].filter(Boolean).join(' @ ');
      if (bit) parts.push(bit);
    }
  }
  if (!parts.length && err && err.message) parts.push(err.message);
  // Not everything thrown is an Error. A bare string carries its own meaning
  // and must not be flattened to "unknown".
  if (!parts.length && typeof err === 'string' && err.trim()) parts.push(err.trim());
  if (!parts.length && err !== null && err !== undefined) {
    const s = String(err);
    if (s && s !== '[object Object]') parts.push(s);
  }
  if (!parts.length) parts.push('unknown error');
  return parts.join('; ').slice(0, 400);
}

/**
 * Give the video its own thumbnail instead of letting YouTube pick one.
 *
 * Left alone, YouTube chooses from three frames it samples itself. On a video
 * that is deliberately graded to a mean luma in the forties, all three are
 * dark, and the one it picks is usually the muddiest — which is how a
 * two-hour render of a hand-painted moonlit shore ends up represented by a
 * grey rectangle in search results.
 *
 * The first frame of the loop is the honest choice: it is the picture as the
 * viewer will actually see it, after the zoom crop, the grade and the corner
 * mark, so the thumbnail cannot promise something the video does not show.
 * Scaled to 1280x720 and encoded generously — the 2 MB ceiling is far away at
 * this resolution and thumbnail compression is what makes a dark image band.
 *
 * Non-fatal for the same reason as the playlist: the upload already cost an
 * hour of CPU, and a thumbnail that would not set must not turn a published
 * video into a failed run. Custom thumbnails also need a verified channel, so
 * on an unverified account this fails every time and must stay harmless.
 */
async function setThumbnail(job, youtube, videoId, meta) {
  const slug = slugSafe(meta.thumbnail_slug
    || meta.visual_slug
    || (Array.isArray(meta.visual_slugs) ? meta.visual_slugs[0] : ''));
  if (!slug) return null;
  const loop = path.join(DIRS.loops, `${slug}_loop.mp4`);
  if (!fs.existsSync(loop)) {
    step(job, `no loop for ${slug}; leaving YouTube to pick a thumbnail`);
    return null;
  }
  const thumb = path.join(DIRS.tmp, `${slug}_thumb.jpg`);
  try {
    await ffmpeg([
      '-i', loop, '-frames:v', '1',
      '-vf', 'scale=1280:720:flags=lanczos',
      '-q:v', '2', thumb,
    ], { timeoutMs: 60000 });
    await youtube.thumbnails.set({
      videoId,
      media: { mimeType: 'image/jpeg', body: fs.createReadStream(thumb) },
    });
    step(job, `set custom thumbnail from ${slug}`);
    return slug;
  } catch (err) {
    step(job, `thumbnail not set (video is still published): ${err.message}`);
    return null;
  } finally {
    await fsp.rm(thumb, { force: true });
  }
}

/**
 * File the video in a playlist, if one is configured.
 *
 * Deliberately non-fatal. The upload is the thing that cost an hour of CPU and
 * a night's work; a playlist that has been renamed, deleted, or had its id
 * mistyped must not turn a published video into a failed run. A failure here
 * is logged as a step and the job carries on.
 */
async function addToPlaylist(job, youtube, videoId, override) {
  const playlistId = String(override || YT_PLAYLIST_ID || '').trim();
  // 'none' is how a caller says "not this one" without unsetting the default.
  if (!playlistId || playlistId === 'none') return null;
  try {
    await youtube.playlistItems.insert({
      part: ['snippet'],
      requestBody: {
        snippet: {
          playlistId,
          resourceId: { kind: 'youtube#video', videoId },
        },
      },
    });
    step(job, `added to playlist ${playlistId}`);
    return playlistId;
  } catch (err) {
    step(job, `playlist add failed (video is still published): ${err.message}`);
    return null;
  }
}

/**
 * Build one video that plays several beds back to back so they can be judged
 * before anything is committed to a two-hour render.
 *
 * The gap this fills: audio could be put onto the volume and measured, but the
 * only way to actually hear a bed was to render two hours of video and upload
 * it. That is why beds that were plainly noise rather than music survived in
 * rotation for weeks — every check the pipeline ran was a level check, and no
 * level check can tell a pad from a hiss. A ten-minute audition costs one
 * upload and settles it by ear in ten minutes.
 *
 * Deliberately different from renderSession in one respect: the beds are cut
 * hard, not crossfaded. A crossfade here would blend two candidates into each
 * other at exactly the moment the listener is deciding between them, and it
 * would make the timings inexact. Each bed gets exactly `seconds_each`, so
 * candidate k begins at (k-1) * seconds_each and can be named by the clock.
 *
 * `skip_sec` steps over the fade-in that generated beds start with, so the
 * first thing heard is the bed proper rather than three seconds of nothing.
 * Everything else — the sleep compressor, the visual, the encoder — is what a
 * real session uses, so what is auditioned is what gets shipped.
 */
async function renderAudition(job, input) {
  const runId = slugSafe(input.run_id);
  const slug = slugSafe(input.visual_slug);
  const loop = path.join(DIRS.loops, `${slug}_loop.mp4`);
  if (!fs.existsSync(loop)) throw new Error(`visual loop missing: ${loop}`);

  const slugs = (input.tracks || []).map(slugSafe).filter(Boolean);
  if (slugs.length < 2) throw new Error('an audition needs at least two tracks');
  if (slugs.length > 20) throw new Error('an audition takes at most twenty tracks');
  const files = slugs.map((s) => path.join(DIRS.tracks, `${s}.mp3`));
  for (const f of files) {
    if (!fs.existsSync(f)) throw new Error(`track missing: ${f}`);
  }

  const each = clampNum(Number(input.seconds_each), 20, 300, 60);
  const skip = clampNum(Number(input.skip_sec), 0, 60, 5);
  const total = each * files.length;
  const fade = 0.75;

  const stripPath = path.join(DIRS.tmp, `${runId}_audition.wav`);
  const videoListPath = path.join(DIRS.tmp, `${runId}_audition_video.txt`);
  const outPath = path.join(DIRS.renders, `${runId}.mp4`);

  // apad between the two atrims is what makes the timings exact. Without it a
  // bed shorter than skip + each yields a short segment, every candidate after
  // it slides earlier, and the timing map handed to the listener is wrong from
  // that point on — the one thing an audition cannot get away with.
  // The skip has to give way to the bed's actual length. A bed of exactly
  // `each` seconds asked to skip five would be padded with five seconds of
  // digital silence at the end of its slot — which, in an audition whose whole
  // purpose is to judge whether the audio is right, reads as the audio being
  // broken. Take as much of the head off as the bed can spare and no more.
  const lengths = [];
  for (const f of files) lengths.push(await probeDuration(f).catch(() => 0));
  const short = [];
  files.forEach((_f, i) => {
    if (lengths[i] > 0 && lengths[i] < each) short.push(`${slugs[i]} (${Math.round(lengths[i])}s)`);
  });
  if (short.length) {
    step(job, `shorter than the ${each}s slot, will be padded: ${short.join(', ')}`);
  }

  const args = [];
  for (const f of files) args.push('-i', f);
  const parts = [];
  const labels = [];
  files.forEach((_f, i) => {
    const head = lengths[i] > 0 ? Math.max(0, Math.min(skip, lengths[i] - each)) : skip;
    parts.push(`[${i}:a]atrim=start=${head.toFixed(3)}:duration=${each},asetpts=N/SR/TB,`
      + `apad,atrim=duration=${each},asetpts=N/SR/TB,`
      + `afade=t=in:st=0:d=${fade},afade=t=out:st=${(each - fade).toFixed(2)}:d=${fade},`
      + `aresample=44100,aformat=sample_fmts=s16:channel_layouts=stereo[c${i}]`);
    labels.push(`[c${i}]`);
  });
  parts.push(`${labels.join('')}concat=n=${files.length}:v=0:a=1[out]`);

  step(job, `cutting ${files.length} beds to ${each}s each (${Math.round(total / 60)} min)`);
  await ffmpeg(args.concat([
    '-filter_complex', parts.join(';'),
    '-map', '[out]',
    '-c:a', 'pcm_s16le', '-ar', '44100', '-ac', '2',
    stripPath,
  ]), { timeoutMs: 15 * 60 * 1000 });

  await buildVideoList(videoListPath, [loop], total, Math.min(300, total));

  // sleepDrc() is empty when SLEEP_DRC=0, and `-af ''` is an ffmpeg error
  // rather than a no-op, so the flag has to disappear with the filter.
  const drc = sleepDrc().replace(/,$/, '');
  step(job, `rendering the audition over ${slug}`);
  try {
    await ffmpeg([
      '-f', 'concat', '-safe', '0', '-i', videoListPath,
      '-i', stripPath,
      '-t', String(total),
      '-map', '0:v:0', '-map', '1:a:0',
      '-c:v', 'copy',
      '-c:a', 'aac', '-b:a', '192k', '-ar', '44100', '-ac', '2',
    ].concat(drc ? ['-af', drc] : []).concat([
      '-movflags', '+faststart',
      outPath,
    ]), { timeoutMs: 30 * 60 * 1000 });
  } catch (err) {
    await fsp.rm(outPath, { force: true });
    throw err;
  } finally {
    await fsp.rm(stripPath, { force: true });
    await fsp.rm(videoListPath, { force: true });
  }

  // Measured after the render rather than before, so a slow measurement never
  // sits between the listener and the thing they asked for. The flag is the
  // point: a candidate that reads as noise can be discounted before it is
  // played, and if the ear disagrees with the number that is worth knowing too.
  const map = [];
  for (let i = 0; i < slugs.length; i += 1) {
    const flatness = await spectralFlatness(files[i]);
    map.push({
      n: i + 1,
      slug: slugs[i],
      at: `${String(Math.floor(i * each / 60)).padStart(2, '0')}:`
        + `${String(Math.round(i * each % 60)).padStart(2, '0')}`,
      spectral_flatness: flatness,
      reads_as_noise: flatness === null ? null : flatness > NOISE_FLATNESS,
    });
  }
  return { file: outPath, seconds_each: each, total_sec: total, map };
}

// ------------------------------------------------------------ housekeeping

async function pruneRenders(days) {
  const cutoff = Date.now() - days * 86400000;
  const entries = await fsp.readdir(DIRS.renders).catch(() => []);
  let removed = 0;
  for (const name of entries) {
    if (!name.endsWith('.mp4')) continue;
    const full = path.join(DIRS.renders, name);
    const stat = await fsp.stat(full).catch(() => null);
    if (stat && stat.mtimeMs < cutoff) {
      await fsp.rm(full, { force: true });
      removed += 1;
    }
  }
  return removed;
}

/**
 * What is on the volume, by directory, in bytes.
 *
 * Cheap enough to run before a render. The point is to be able to say WHICH
 * directory filled the disk rather than only that it is full — "no space left
 * on device" out of ffmpeg names the symptom and nothing else.
 */
async function dirSize(dir) {
  const entries = await fsp.readdir(dir).catch(() => []);
  let bytes = 0;
  let count = 0;
  for (const name of entries) {
    const stat = await fsp.stat(path.join(dir, name)).catch(() => null);
    if (stat && stat.isFile()) { bytes += stat.size; count += 1; }
  }
  return { bytes, count };
}

async function assetBreakdown() {
  const out = {};
  for (const [name, dir] of Object.entries(DIRS)) {
    const { bytes, count } = await dirSize(dir);
    out[name] = { files: count, mb: +(bytes / 1048576).toFixed(1) };
  }
  return out;
}

/**
 * Delete what a render does not need.
 *
 * Three things accumulate on a 4.5 GB volume that a two-hour render needs
 * 3.2 GB of:
 *
 *   renders   A finished session is deleted after it uploads. One that FAILS
 *             is not, and it is the largest single file the service makes.
 *             The old prune only removed renders older than two days, which
 *             is no help at all when the render that just failed is the thing
 *             filling the disk.
 *   visuals   The fal source clips. 25 MB each against an 8 MB loop, and the
 *             loop is what every session actually plays. Thirty beaches put
 *             three quarters of a gigabyte here that no render reads.
 *   tmp       Whatever ffmpeg left behind.
 *
 * Loops and tracks are never touched: those are the library.
 *
 * Dropping a source costs exactly one thing — /jobs/reloop can no longer
 * rebuild that clip, because it re-encodes from the source. That matters if
 * the burned-in mark changes. keep_sources holds them; older_than_days keeps
 * anything recent.
 */
async function sweepVolume(opts) {
  const o = opts || {};
  const dry = Boolean(o.dry_run);
  const days = Number.isFinite(Number(o.older_than_days)) ? Number(o.older_than_days) : 0;
  const cutoff = Date.now() - days * 86400000;

  const before = await diskUsage();
  const plan = [];

  const sweepDir = async (dir, label, exts) => {
    const entries = await fsp.readdir(dir).catch(() => []);
    for (const name of entries) {
      if (exts && !exts.some((e) => name.endsWith(e))) continue;
      const full = path.join(dir, name);
      const stat = await fsp.stat(full).catch(() => null);
      if (!stat || !stat.isFile()) continue;
      if (stat.mtimeMs >= cutoff) continue;
      plan.push({ what: label, name, mb: +(stat.size / 1048576).toFixed(1), full });
    }
  };

  if (o.renders !== false) await sweepDir(DIRS.renders, 'render', ['.mp4']);
  if (o.sources !== false) await sweepDir(DIRS.visuals, 'source', ['.mp4']);
  if (o.tmp !== false) await sweepDir(DIRS.tmp, 'tmp', null);

  let freed = 0;
  const removed = [];
  if (!dry) {
    for (const item of plan) {
      await fsp.rm(item.full, { force: true });
      freed += item.mb;
      removed.push(`${item.what}:${item.name}`);
    }
  }

  return {
    dry_run: dry,
    older_than_days: days,
    candidates: plan.length,
    would_free_mb: +plan.reduce((a, b) => a + b.mb, 0).toFixed(1),
    freed_mb: +freed.toFixed(1),
    removed: dry ? plan.map((p) => `${p.what}:${p.name}`) : removed,
    disk_before: before,
    disk_after: dry ? before : await diskUsage(),
    assets: await assetBreakdown(),
  };
}

async function diskUsage() {
  try {
    const { stdout } = await run('df', ['-Pk', DATA_DIR], { timeoutMs: 10000 });
    const line = stdout.split('\n').pop().split(/\s+/);
    return { size_gb: +(Number(line[1]) / 1048576).toFixed(1), used_gb: +(Number(line[2]) / 1048576).toFixed(1), avail_gb: +(Number(line[3]) / 1048576).toFixed(1) };
  } catch (err) {
    return { error: err.message };
  }
}

// ---------------------------------------------------------------------- app

const app = express();
app.use(express.json({ limit: '1mb' }));

app.use((req, res, next) => {
  if (req.path === '/health') return next();
  if (!RENDER_KEY) return res.status(500).json({ error: 'RENDER_KEY is not set on the service' });
  if (req.get('x-render-key') !== RENDER_KEY) return res.status(401).json({ error: 'unauthorized' });
  return next();
});

app.get('/health', async (_req, res) => {
  let ffmpegVersion = null;
  try {
    const { stdout } = await run('ffmpeg', ['-version'], { timeoutMs: 10000 });
    ffmpegVersion = stdout.split('\n')[0];
  } catch (err) {
    ffmpegVersion = `unavailable: ${err.message}`;
  }
  res.json({
    ok: true,
    ffmpeg: ffmpegVersion,
    data_dir: DATA_DIR,
    // Null here means Shorts will render without their captions. Better seen
    // on a health check than discovered in a finished video.
    font: findFont(),
    disk: await diskUsage(),
    // Whether a sea is configured, and whether the file is actually there.
    // A missing ambience file does not fail a render, so without this the only
    // symptom would be a silent join nobody notices until they listen.
    // Shorts carry no mark by default from 2026-09-06; long-form still does.
    short_brand: String(process.env.SHORT_BRAND || 'off').toLowerCase() !== 'off',
    ambience: {
      slug: AMBIENCE_SLUG || null,
      db: AMBIENCE_DB,
      present: AMBIENCE_SLUG
        ? fs.existsSync(path.join(DIRS.tracks, `${slugSafe(AMBIENCE_SLUG)}.mp3`))
        : null,
    },
    // The picture dials, so a deploy can be confirmed from the health check
    // instead of by rendering something and looking at it.
    loop: {
      crf: LOOP_CRF,
      maxrate_kbps: LOOP_MAXRATE,
      projected_2h_gb_at_maxrate: Number((LOOP_MAXRATE * 1000 / 8 * 7200 / 1e9).toFixed(2)),
      visual_resolution: VISUAL_RESOLUTION,
      visual_seconds: VISUAL_SECONDS,
    },
    configured: {
      render_key: Boolean(RENDER_KEY),
      fal: Boolean(FAL_KEY),
      elevenlabs: Boolean(ELEVENLABS_API_KEY),
      pexels: Boolean(PEXELS_API_KEY),
      youtube: Boolean(YT_CLIENT_ID && YT_CLIENT_SECRET && YT_REFRESH_TOKEN),
    },
    default_dim: DEFAULT_DIM,
    brand: brandStatus(),
    playlist: YT_PLAYLIST_ID || null,
    host: os.hostname(),
  });
});

/**
 * Proves the YouTube credentials actually work: refreshes an access token and
 * asks the API which channel it is authorised for. Read-only, no quota cost
 * worth counting, and the fastest way to catch an expired refresh token.
 */
app.get('/youtube/whoami', async (_req, res) => {
  try {
    const youtube = youtubeClient();
    const result = await youtube.channels.list({ part: ['snippet', 'statistics'], mine: true });
    const channel = result && result.data && result.data.items && result.data.items[0];
    if (!channel) {
      return res.status(404).json({ ok: false, error: 'Token is valid but no channel is attached to this account' });
    }
    res.json({
      ok: true,
      channel_id: channel.id,
      title: channel.snippet.title,
      subscribers: channel.statistics.subscriberCount,
      videos: channel.statistics.videoCount,
    });
  } catch (err) {
    const msg = err && err.message ? err.message : String(err);
    res.status(502).json({
      ok: false,
      error: msg,
      hint: /invalid_grant/i.test(msg)
        ? 'Refresh token is expired or revoked — re-run the OAuth Playground and update YT_REFRESH_TOKEN'
        : 'Check YT_CLIENT_ID, YT_CLIENT_SECRET and YT_REFRESH_TOKEN',
    });
  }
});

app.get('/jobs/:id', (req, res) => {
  const job = jobs.get(req.params.id);
  if (!job) return res.status(404).json({ error: 'job not found' });
  res.json({
    id: job.id, kind: job.kind, status: job.status,
    result: job.result, error: job.error,
    created_at: job.created_at, updated_at: job.updated_at,
    log: job.log.slice(-12),
  });
});

app.post('/jobs/visual', (req, res) => {
  const b = req.body || {};
  const { slug, aspect, prompt, dim, vivid } = b;
  if (!slug || !prompt) return res.status(400).json({ error: 'slug and prompt are required' });
  if (aspect !== '16x9' && aspect !== '9x16') return res.status(400).json({ error: 'aspect must be 16x9 or 9x16' });
  // resolution / duration reach fal; slow, xfade, crf and maxrate reach the
  // loop build. All optional, all defaulting to the values that were
  // hard-coded before, so existing callers are unaffected.
  const job = startJob('visual', { slug, aspect }, (j) => makeVisual(j, {
    slug, aspect, prompt, dim, vivid,
    resolution: b.resolution,
    duration: b.duration,
    slow: b.slow,
    xfade: b.xfade,
    crf: b.crf,
    maxrate: b.maxrate,
    camera_fixed: b.camera_fixed,
  }));
  res.status(202).json({ job_id: job.id, status: job.status });
});

/**
 * Add a visual from Pexels instead of generating one. Free, so this is the
 * endpoint that grows the library without spending anything.
 *
 * Body: { slug, aspect, query, dim?, page?, exclude?, min_duration? }
 * "exclude" takes pexels ids already in sw_visuals so repeat runs on the same
 * query do not keep landing on the same clip.
 */
app.post('/jobs/stock', (req, res) => {
  const { slug, aspect, query, dim, vivid, page, exclude, min_duration } = req.body || {};
  if (!slug || !query) return res.status(400).json({ error: 'slug and query are required' });
  if (aspect !== '16x9' && aspect !== '9x16') return res.status(400).json({ error: 'aspect must be 16x9 or 9x16' });
  const job = startJob('stock', { slug, aspect, query }, (j) => makeStockVisual(j, {
    slug, aspect, query, dim, vivid, page, exclude, min_duration,
  }));
  res.status(202).json({ job_id: job.id, status: job.status });
});

/**
 * Import a visual from any direct URL — a clip or a still made somewhere this
 * service cannot call. Drop the file anywhere with a direct link (a raw
 * GitHub URL works) and pass it here.
 *
 * Body: { slug, aspect, url, dim?, start?, source?, credit? }
 * "start" overrides where the 10s window is cut from; omit it and the middle
 * of the clip is used, which is where stock and generated footage is calmest.
 */
app.post('/jobs/import', (req, res) => {
  const { slug, aspect, url, dim, vivid, start, source, credit } = req.body || {};
  if (!slug || !url) return res.status(400).json({ error: 'slug and url are required' });
  if (aspect !== '16x9' && aspect !== '9x16') return res.status(400).json({ error: 'aspect must be 16x9 or 9x16' });
  const job = startJob('import', { slug, aspect }, (j) => makeImportVisual(j, {
    slug, aspect, url, dim, vivid, start, source, credit,
  }));
  res.status(202).json({ job_id: job.id, status: job.status });
});

/**
 * Rebuild loops from raw clips already on disk, at the capped bitrate and the
 * current grade. Costs nothing — no fal or Pexels call — so it is also how
 * you retune the library.
 *
 * Pick the targets one of three ways: {"slug": "..."} for one clip,
 * {"slugs": ["...", "..."]} for a named set, or {"all": true} for everything.
 * Prefer "slugs" once the library has both pools in it — "all" applies one
 * grade to every clip, which is how you would accidentally strip the night
 * grade off the whole night pool while brightening the day pool.
 *
 * Grade with {"dim": 0.35} or {"vivid": 0.7}; omit both to use LOOP_DIM.
 */
app.post('/jobs/reloop', (req, res) => {
  const body = req.body || {};

  // Three shapes, in order of specificity:
  //   { groups: [{ slugs, dim|vivid }, ...] }  each group keeps its own look
  //   { slugs: [...], dim }                    one look for the listed slugs
  //   { slug } / { all: true }                 one clip, or the whole library
  //
  // `groups` exists because the library is not uniform: every clip was looped
  // at the dim that suited it, and that value lives in n8n, not here. A single
  // reloop-all would flatten fifteen carefully tuned night clips to one dial
  // setting. Groups let the caller rebuild everything in one sequential job
  // while each clip keeps the look it was given.
  const groups = Array.isArray(body.groups) && body.groups.length
    ? body.groups
    : [{ slugs: body.slugs, dim: body.dim, vivid: body.vivid, all: body.all, slug: body.slug }];

  const job = startJob('reloop', { groups: groups.length }, async (j) => {
    const files = await fsp.readdir(DIRS.visuals).catch(() => []);
    const available = files.filter((f) => f.endsWith('.mp4')).map((f) => f.slice(0, -4));

    const rebuilt = [];
    const skipped = [];
    for (const group of groups) {
      const look = lookFrom({ dim: group.dim, vivid: group.vivid });
      const motion = {
        slow: group.slow, xfade: group.xfade,
        crf: group.crf, maxrate: group.maxrate,
      };
      const wanted = Array.isArray(group.slugs) && group.slugs.length
        ? group.slugs.map(slugSafe).filter(Boolean)
        : null;
      const targets = available.filter((s) => {
        if (group.all) return true;
        if (wanted) return wanted.indexOf(s) !== -1;
        return s === slugSafe(group.slug);
      });
      if (wanted) {
        for (const w of wanted) if (targets.indexOf(w) === -1) skipped.push(w);
      }

      for (const slug of targets) {
        const isWide = slug.indexOf('-16x9-') !== -1;
        const scale = isWide ? '1920:1080' : '1080:1920';
        const slowLabel = motion.slow && Number(motion.slow) !== 1
          ? `, ${Number(motion.slow).toFixed(2)}x slower` : '';
        step(j, `re-encoding ${slug} at capped bitrate, ${describeLook(look)}${slowLabel}`);
        const bright = await buildLoopToTarget(
          path.join(DIRS.visuals, `${slug}.mp4`),
          path.join(DIRS.loops, `${slug}_loop.mp4`),
          scale,
          look,
          motion,
          group.target_brightness,
        );
        if (bright.corrected) {
          step(j, `  dimmed ${slug} from ${bright.before} to ${bright.after}`);
        }
        const loopFile = path.join(DIRS.loops, `${slug}_loop.mp4`);
        const lbytes = await fsp.stat(loopFile).then((s) => s.size).catch(() => 0);
        const lsecs = await probeDuration(loopFile).catch(() => 0);
        rebuilt.push({ slug, dim: look.dim, vivid: look.vivid,
          slow: clampNum(motion.slow, 1, 4, 1), xfade: clampNum(motion.xfade, 0.5, 4, 1),
          crf: Math.round(clampNum(motion.crf, 14, 34, LOOP_CRF)),
          maxrate_kbps: Math.round(clampNum(motion.maxrate, 600, 6000, LOOP_MAXRATE)),
          loop_seconds: Number(lsecs.toFixed(2)),
          loop_bytes: lbytes,
          projected_2h_gb: lsecs > 0
            ? Number(((lbytes / lsecs) * 7200 / 1e9).toFixed(2)) : 0,
          brightness: bright });
      }
    }
    if (!rebuilt.length) throw new Error('no raw clips matched');

    return {
      rebuilt: rebuilt.length,
      slugs: rebuilt.map((r) => r.slug),
      detail: rebuilt,
      skipped,
      brand: brandStatus(),
      disk: await diskUsage(),
    };
  });
  res.status(202).json({ job_id: job.id, status: job.status });
});

app.post('/jobs/track', (req, res) => {
  const { slug, prompt, length_ms, target_lufs } = req.body || {};
  if (!slug || !prompt) return res.status(400).json({ error: 'slug and prompt are required' });
  const job = startJob('track', { slug },
    (j) => makeTrack(j, { slug, prompt, length_ms, target_lufs }));
  res.status(202).json({ job_id: job.id, status: job.status });
});

/**
 * Re-normalise a bed already on the volume to a different loudness.
 *
 * Needed because the target changed after the library was built: everything
 * generated before this was mastered at -16 LUFS, which is a speech target and
 * about six decibels too loud for music whose entire job is to be ignorable in
 * a silent room. Regenerating would produce different music; this changes only
 * the level of the music that was already approved.
 *
 * Reversible in the same way as /jobs/flatten: the first relevel of a bed
 * writes the untouched original beside it as <slug>.orig.mp3 and never
 * overwrites that, so repeated relevels always work from the original rather
 * than compounding on each other.
 *
 * Body: { slug, target_lufs }
 */
app.post('/jobs/relevel', (req, res) => {
  const { slug, target_lufs } = req.body || {};
  if (!slug) return res.status(400).json({ error: 'slug is required' });
  const job = startJob('relevel', { slug }, async (j) => {
    const safe = slugSafe(slug);
    const file = path.join(DIRS.tracks, `${safe}.mp3`);
    const orig = path.join(DIRS.tracks, `${safe}.orig.mp3`);
    if (!fs.existsSync(file)) throw new Error(`track missing: ${file}`);

    if (!fs.existsSync(orig)) {
      await fsp.copyFile(file, orig);
      step(j, `kept the original as ${safe}.orig.mp3`);
    } else {
      step(j, `working from the original kept at ${safe}.orig.mp3`);
    }

    const before = await measureTrack(orig);
    const ln = loudnormFilter(target_lufs);
    const tmp = path.join(DIRS.tmp, `${safe}_relevel.mp3`);
    step(j, `${before.integrated_lufs} LUFS -> ${ln.target}`);
    await ffmpeg([
      '-i', orig,
      '-af', ln.filter,
      '-ac', '2', '-ar', '44100',
      '-c:a', 'libmp3lame', '-b:a', '192k',
      tmp,
    ], { timeoutMs: 10 * 60 * 1000 });
    await fsp.rename(tmp, file);

    const after = await measureTrack(file);
    return {
      slug: safe,
      target_lufs: ln.target,
      before_lufs: before.integrated_lufs,
      after_lufs: after.integrated_lufs,
      true_peak_dbtp: after.true_peak_dbtp,
      loudness_range_lu: after.loudness_range_lu,
      spectral_flatness: after.spectral_flatness,
      original_kept_at: `${safe}.orig.mp3`,
    };
  });
  res.status(202).json({ job_id: job.id, status: job.status });
});

/**
 * Import a bed from any direct URL — the audio counterpart of /jobs/import.
 * Drop the file anywhere with a direct link (a raw GitHub URL works) and pass
 * it here. Normalised to -16 LUFS and forced to stereo so it sits alongside
 * the generated beds without anything else needing to change.
 *
 * Body: { slug, url, mood? }
 */
app.post('/jobs/importtrack', (req, res) => {
  const { slug, url, mood, target_lufs } = req.body || {};
  if (!slug || !url) return res.status(400).json({ error: 'slug and url are required' });
  const job = startJob('importtrack', { slug },
    (j) => makeImportTrack(j, { slug, url, mood, target_lufs }));
  res.status(202).json({ job_id: job.id, status: job.status });
});

app.post('/jobs/session', (req, res) => {
  const input = req.body || {};
  // Either shape is valid. visual_slugs is current; visual_slug is the older
  // single-scene form and renderSession still accepts it. This guard only
  // checked the singular, so a caller sending the current shape got a 400
  // telling it to send a field the renderer does not need — invisible for
  // months because WF-A happens to send both.
  const hasVisual = Boolean(input.visual_slug)
    || (Array.isArray(input.visual_slugs) && input.visual_slugs.length > 0);
  if (!input.run_id || !hasVisual || !input.duration_sec) {
    return res.status(400).json({
      error: 'run_id, duration_sec and one of visual_slug / visual_slugs are required',
    });
  }
  const label = input.visual_slug
    || (Array.isArray(input.visual_slugs) ? input.visual_slugs[0] : '');
  const job = startJob('session', { run_id: input.run_id, visual_slug: label }, async (j) => {
    const file = await renderSession(j, input);
    const videoId = await uploadToYouTube(j, file, input);
    await fsp.rm(file, { force: true });
    step(j, 'deleted local render after successful upload');
    const pruned = await pruneRenders(2);
    if (pruned) step(j, `pruned ${pruned} orphaned renders`);
    return { video_id: videoId, pruned, disk: await diskUsage() };
  });
  res.status(202).json({ job_id: job.id, status: job.status });
});

app.post('/jobs/short', (req, res) => {
  const input = req.body || {};
  if (!input.run_id || !input.visual_slug || !input.track_slug) {
    return res.status(400).json({ error: 'run_id, visual_slug and track_slug are required' });
  }
  const job = startJob('short', { run_id: input.run_id, visual_slug: input.visual_slug }, async (j) => {
    const file = await renderShort(j, input);
    // Shorts never go in the sessions playlist — see YT_PLAYLIST_ID.
    const videoId = await uploadToYouTube(j, file, Object.assign({}, input, { playlist_id: 'none' }));
    await fsp.rm(file, { force: true });
    step(j, 'deleted local render after successful upload');
    return { video_id: videoId, disk: await diskUsage() };
  });
  res.status(202).json({ job_id: job.id, status: job.status });
});

/**
 * Measure every music bed and the step at each join.
 *
 * A session strings the beds end to end with a hard cut and no crossfade, so
 * a bed that ends 4 dB below where the next one starts is an audible jump —
 * roughly every twenty minutes, to someone who is trying to fall asleep. This
 * is the one part of the pipeline nobody can check by eye, and nobody had
 * checked by ear either.
 *
 * Joins are reported in filename order and wrap from the last bed back to the
 * first, which is the order WF-A cycles them in.
 */
/**
 * Lay a true binaural beat under an existing bed and save the result as a new
 * bed. The source is left untouched.
 *
 * Body: { slug, source_slug, left_hz, right_hz, tone_db?, mood? }
 *
 * A binaural beat is two steady tones a few hertz apart, one in each ear; the
 * brain hears the difference as a pulse at that gap. 68 Hz against 70 Hz gives
 * a 2 Hz beat, which is the delta band the sleep channels label their tracks
 * with. Asking a music model for this produces something that sounds roughly
 * like it and measures wrong, so the tones are synthesised here to the hertz
 * and mixed in at a fixed level instead.
 *
 * Two things this cannot do anything about, both worth stating plainly: the
 * effect needs headphones, because on a speaker the two channels mix in the
 * air before they reach either ear; and the evidence for binaural beats doing
 * much of anything is thin. It is a format the audience searches for, not a
 * treatment.
 */
app.post('/jobs/binaural', (req, res) => {
  const { slug, source_slug, left_hz, right_hz, tone_db, mood } = req.body || {};
  if (!slug || !source_slug || !left_hz || !right_hz) {
    return res.status(400).json({
      error: 'slug, source_slug, left_hz and right_hz are required',
    });
  }
  const job = startJob('binaural', { slug }, async (j) => {
    const safe = slugSafe(slug);
    const src = path.join(DIRS.tracks, `${slugSafe(source_slug)}.mp3`);
    if (!fs.existsSync(src)) throw new Error(`source track missing: ${src}`);
    const out = path.join(DIRS.tracks, `${safe}.mp3`);

    const lf = clampNum(Number(left_hz), 20, 1000, 68);
    const rf = clampNum(Number(right_hz), 20, 1000, 70);
    const beat = Math.abs(rf - lf);
    if (beat < 0.5 || beat > 40) {
      throw new Error(`a ${beat} Hz difference is not a usable beat frequency`);
    }
    // Quiet on purpose. The tones are meant to sit under the music, not to be
    // a feature of it; louder than about -20 dB and a steady low sine stops
    // being subliminal and starts being a hum somebody cannot unhear.
    const db = clampNum(Number(tone_db), -40, -12, -24);
    const seconds = await probeDuration(src);

    step(j, `mixing a ${beat} Hz beat (${lf} Hz left, ${rf} Hz right) at ${db} dB `
      + `under ${source_slug}`);
    await ffmpeg([
      '-i', src,
      '-f', 'lavfi', '-t', String(seconds), '-i', `sine=frequency=${lf}:sample_rate=44100`,
      '-f', 'lavfi', '-t', String(seconds), '-i', `sine=frequency=${rf}:sample_rate=44100`,
      '-filter_complex',
      // join, not amerge: the two sines must stay in their own channels all
      // the way to the file, because a beat that has been summed to mono is
      // just two tones and no beat at all.
      `[1:a][2:a]join=inputs=2:channel_layout=stereo,volume=${db}dB[tones];`
        + `[0:a]aformat=sample_fmts=fltp:channel_layouts=stereo[bed];`
        // normalize=0 matters. amix scales its inputs by 1/n by default, which
        // would quietly drop the music 6 dB below every other bed on the volume.
        + `[bed][tones]amix=inputs=2:duration=first:normalize=0,`
        + `alimiter=limit=0.89:level=disabled[out]`,
      '-map', '[out]',
      '-c:a', 'libmp3lame', '-b:a', '192k', '-ar', '44100', '-ac', '2',
      out,
    ], { timeoutMs: 15 * 60 * 1000 });

    const m = await measureTrack(out);
    return {
      slug: safe,
      source_slug: slugSafe(source_slug),
      left_hz: lf,
      right_hz: rf,
      beat_hz: beat,
      tone_db: db,
      mood: mood || '',
      headphones_only: true,
      measured: m,
    };
  });
  res.status(202).json({ job_id: job.id, status: job.status });
});

/**
 * Audition several beds in one video before committing any of them to a
 * session. Uploads unlisted and files it in no playlist.
 *
 * Body: { run_id, visual_slug, tracks: [slug], seconds_each?, skip_sec?,
 *         title?, privacy_status? }
 */
app.post('/jobs/audition', (req, res) => {
  const input = req.body || {};
  if (!input.run_id || !input.visual_slug
    || !Array.isArray(input.tracks) || input.tracks.length < 2) {
    return res.status(400).json({
      error: 'run_id, visual_slug and a tracks array of at least two slugs are required',
    });
  }
  const job = startJob('audition', { run_id: input.run_id }, async (j) => {
    const built = await renderAudition(j, input);
    const lines = built.map.map((m) => `${m.at}  —  ${m.n}. ${m.slug}`
      + (m.spectral_flatness === null ? '' : `  [flatness ${m.spectral_flatness}`
        + `${m.reads_as_noise ? ' — READS AS NOISE' : ''}]`));
    const videoId = await uploadToYouTube(j, built.file, {
      title: String(input.title || 'Saltwater — bed audition (not for publication)').slice(0, 100),
      description: ['Working file. Each bed plays for '
        + `${built.seconds_each} seconds, cut hard, in this order:`, '']
        .concat(lines).join('\n'),
      tags: '',
      visual_slug: input.visual_slug,
      privacy_status: input.privacy_status || 'unlisted',
      playlist_id: 'none',
    });
    await fsp.rm(built.file, { force: true });
    step(j, 'deleted local render after successful upload');
    return {
      video_id: videoId,
      url: `https://youtu.be/${videoId}`,
      seconds_each: built.seconds_each,
      total_sec: built.total_sec,
      map: built.map,
      disk: await diskUsage(),
    };
  });
  res.status(202).json({ job_id: job.id, status: job.status });
});

app.post('/jobs/audio', (_req, res) => {
  const job = startJob('audio', {}, async (j) => {
    const files = (await fsp.readdir(DIRS.tracks).catch(() => []))
      .filter((f) => f.endsWith('.mp3')).sort();
    if (!files.length) throw new Error('no music beds on the volume');

    const tracks = [];
    for (const f of files) {
      step(j, `measuring ${f}`);
      const m = await measureTrack(path.join(DIRS.tracks, f));
      tracks.push(Object.assign({ slug: f.slice(0, -4) }, m));
    }

    const joins = [];
    for (let i = 0; i < tracks.length; i += 1) {
      const a = tracks[i];
      const b = tracks[(i + 1) % tracks.length];
      const stepDb = (a.tail_dbfs === null || b.head_dbfs === null)
        ? null : Number((b.head_dbfs - a.tail_dbfs).toFixed(1));
      const lufsStep = (a.integrated_lufs === null || b.integrated_lufs === null)
        ? null : Number((b.integrated_lufs - a.integrated_lufs).toFixed(1));
      let verdict = 'unknown';
      if (stepDb !== null) {
        const abs = Math.abs(stepDb);
        if (abs < 1.5) verdict = 'inaudible';
        else if (abs < 3) verdict = 'noticeable';
        else verdict = 'audible jump';
      }
      joins.push({ from: a.slug, to: b.slug, level_step_db: stepDb, loudness_step_lu: lufsStep, verdict });
    }

    const worst = joins.reduce((acc, x) => {
      if (x.level_step_db === null) return acc;
      if (!acc || Math.abs(x.level_step_db) > Math.abs(acc.level_step_db)) return x;
      return acc;
    }, null);

    const lufs = tracks.map((t) => t.integrated_lufs).filter((n) => Number.isFinite(n));
    const spread = lufs.length
      ? Number((Math.max(...lufs) - Math.min(...lufs)).toFixed(1)) : null;

    // Two independent signals for "this bed has loud passages": how far its
    // loudest stretch sits above its own norm, and its loudness range, which
    // is the standard measure of how much a piece varies. Either one alone can
    // miss; a bed that trips either is worth a listen.
    const spiky = tracks
      .filter((t) => (t.transient && t.transient.sticks_out_db >= 6)
        || Number(t.loudness_range_lu) >= 6)
      .map((t) => ({
        slug: t.slug,
        at_sec: t.transient ? t.transient.loudest_at_sec : null,
        sticks_out_db: t.transient ? t.transient.sticks_out_db : null,
        swing_db: t.transient ? t.transient.swing_db : null,
        loudness_range_lu: t.loudness_range_lu,
        flag: t.transient ? t.transient.flag : 'unknown',
      }));

    return { tracks, joins, worst_join: worst, loudness_spread_lu: spread, spiky_beds: spiky };
  });
  res.status(202).json({ job_id: job.id, status: job.status });
});

/**
 * How fast does each loop move, and how visible is its seam?
 *
 * Two numbers per clip, both from the same idea: the average brightness of the
 * difference between one frame and the next. A clip where almost nothing moves
 * scores near zero; a clip with waves rolling through it scores high.
 *
 *   motion       averaged across the whole loop
 *   seam         the single difference between the last frame and the first
 *
 * The seam is what a viewer sees as a "step" every nine seconds. Judged
 * against that clip's own motion rather than an absolute number, because a
 * step that would be glaring on still water is invisible in a snowstorm.
 */
async function loopMotion(file) {
  // Brightness first: the average luminance of the actual frames, 0-255.
  // A sleep clip is watched in a dark bedroom, so this matters as much as
  // motion does — a bright clip lights the room whatever else is right about
  // it. Measured on the finished loop, so it includes the night grade.
  let bright = null;
  let brightP95 = null;
  try {
    const bs = await run('ffmpeg', [
      '-hide_banner', '-nostats', '-i', file,
      '-vf', 'scale=160:-2,signalstats,metadata=print:key=lavfi.signalstats.YAVG',
      '-f', 'null', '-',
    ], { timeoutMs: 3 * 60 * 1000 });
    const vals = [];
    const rx = /lavfi\.signalstats\.YAVG=([\d.]+)/g;
    let mm = rx.exec(bs.stderr);
    while (mm) { vals.push(Number(mm[1])); mm = rx.exec(bs.stderr); }
    if (vals.length) {
      bright = Number((vals.reduce((a, b) => a + b, 0) / vals.length).toFixed(1));
      const sv = vals.slice().sort((a, b) => a - b);
      brightP95 = Number(sv[Math.floor(sv.length * 0.95)].toFixed(1));
    }
  } catch (err) {
    bright = null;
  }

  const r = await run('ffmpeg', [
    '-hide_banner', '-nostats', '-i', file,
    '-vf', 'scale=320:-2,tblend=all_mode=difference,signalstats,metadata=print:key=lavfi.signalstats.YAVG',
    '-f', 'null', '-',
  ], { timeoutMs: 5 * 60 * 1000 });
  const vals = [];
  const re = /lavfi\.signalstats\.YAVG=([\d.]+)/g;
  let m = re.exec(r.stderr);
  while (m) { vals.push(Number(m[1])); m = re.exec(r.stderr); }
  if (vals.length < 4) return null;

  // First entry is frame 1 against frame 0; drop nothing, but the seam is
  // measured separately below since tblend never wraps around.
  const mean = vals.reduce((a, b) => a + b, 0) / vals.length;
  const sorted = vals.slice().sort((a, b) => a - b);
  const p90 = sorted[Math.floor(sorted.length * 0.9)];

  // Last frame against first frame: what the eye sees when the loop restarts.
  const dur = await probeDuration(file);
  const tmpA = path.join(DIRS.tmp, `seam_a_${path.basename(file)}.png`);
  const tmpB = path.join(DIRS.tmp, `seam_b_${path.basename(file)}.png`);
  let seam = null;
  try {
    await ffmpeg(['-ss', '0', '-i', file, '-frames:v', '1', '-vf', 'scale=320:-2', tmpA]);
    await ffmpeg(['-sseof', '-0.05', '-i', file, '-frames:v', '1', '-vf', 'scale=320:-2', tmpB]);
    const s = await run('ffmpeg', ['-hide_banner', '-nostats', '-i', tmpB, '-i', tmpA,
      '-filter_complex', '[0][1]blend=all_mode=difference,signalstats,metadata=print:key=lavfi.signalstats.YAVG',
      '-f', 'null', '-'], { timeoutMs: 60000 });
    const mm = s.stderr.match(/lavfi\.signalstats\.YAVG=([\d.]+)/);
    if (mm) seam = Number(mm[1]);
  } catch (err) {
    seam = null;
  }
  await fsp.rm(tmpA, { force: true });
  await fsp.rm(tmpB, { force: true });

  const ratio = (seam !== null && mean > 0.01) ? Number((seam / mean).toFixed(2)) : null;

  // Judge on the ratio, but only once the seam is big enough to see at all.
  // On near-still footage the motion figure is a rounding error, so a
  // perfectly fine seam of 0.7 divided by a motion of 0.2 reads as a huge
  // ratio and the clip gets condemned for standing still.
  let verdict = 'unknown';
  if (seam !== null) {
    if (seam < 1.5) verdict = 'seamless';
    else if (ratio === null || ratio < 2) verdict = 'seamless';
    else if (ratio < 4) verdict = 'slight step';
    else verdict = 'visible step';
  }

  // Thresholds for a sleep clip, both judged on the finished graded loop:
  //   motion   under 2.5 - anything brisker reads as activity, not drift
  //   bright   under 55 of 255 - dark enough not to light a bedroom
  const pace = mean < 1 ? 'very slow' : (mean < 2.5 ? 'slow' : (mean < 5 ? 'brisk' : 'fast'));
  const level = bright === null ? 'unknown'
    : (bright < 35 ? 'very dark' : (bright < 55 ? 'dark' : (bright < 80 ? 'bright' : 'very bright')));
  const okMotion = mean < 2.5;
  const okBright = bright !== null && bright < 55;

  return {
    duration_sec: Number(dur.toFixed(1)),
    motion: Number(mean.toFixed(2)),
    motion_p90: Number(p90.toFixed(2)),
    brightness: bright,
    brightness_p95: brightP95,
    level,
    seam: seam === null ? null : Number(seam.toFixed(2)),
    seam_vs_motion: ratio,
    verdict,
    pace,
    sleep_ready: okMotion && okBright,
    fails: [].concat(okMotion ? [] : ['too much motion']).concat(okBright ? [] : ['too bright']),
  };
}

/**
 * Average luminance of a finished loop, 0-255.
 */
async function meanBrightness(file) {
  try {
    const r = await run('ffmpeg', [
      '-hide_banner', '-nostats', '-i', file,
      '-vf', 'scale=160:-2,signalstats,metadata=print:key=lavfi.signalstats.YAVG',
      '-f', 'null', '-',
    ], { timeoutMs: 3 * 60 * 1000 });
    const vals = [];
    const rx = /lavfi\.signalstats\.YAVG=([\d.]+)/g;
    let m = rx.exec(r.stderr);
    while (m) { vals.push(Number(m[1])); m = rx.exec(r.stderr); }
    if (!vals.length) return null;
    return Number((vals.reduce((a, b) => a + b, 0) / vals.length).toFixed(1));
  } catch (err) {
    return null;
  }
}

/**
 * Build a loop, then bring it to a target brightness if it lands above one.
 *
 * The dim dial was set by eye and never checked, and five night clips came out
 * at 70-150 out of 255 while still being called "night". Guessing a bigger
 * number would repeat the mistake, so this measures the finished loop and
 * computes the exact luma gain needed, then rebuilds once with that gain.
 *
 * One correction pass, not a loop: luma gain is close enough to linear that a
 * second pass buys almost nothing, and each pass costs a full re-encode.
 */
async function buildLoopToTarget(rawPath, loopPath, scale, look, motion, target) {
  await buildLoop(rawPath, loopPath, scale, look, motion);
  if (!target) return { target: null };

  const before = await meanBrightness(loopPath);
  if (before === null || before <= target) return { target, before, corrected: false };

  const gain = clampNum(target / before, 0.1, 1, 1);
  await buildLoop(rawPath, loopPath, scale, look,
    Object.assign({}, motion, { lumaGain: gain }));
  const after = await meanBrightness(loopPath);
  return { target, before, after, luma_gain: Number(gain.toFixed(3)), corrected: true };
}

/**
 * Measure every loop on the volume. Read-only.
 */
app.post('/jobs/loopcheck', (_req, res) => {
  const job = startJob('loopcheck', {}, async (j) => {
    const files = (await fsp.readdir(DIRS.loops).catch(() => []))
      .filter((f) => f.endsWith('_loop.mp4')).sort();
    if (!files.length) throw new Error('no loops on the volume');

    const loops = [];
    for (const f of files) {
      step(j, `measuring ${f}`);
      const m = await loopMotion(path.join(DIRS.loops, f));
      loops.push(Object.assign({ slug: f.replace(/_loop\.mp4$/, '') }, m || { verdict: 'unreadable' }));
    }

    const tooFast = loops.filter((l) => Number(l.motion) >= 2.5)
      .map((l) => ({ slug: l.slug, motion: l.motion, pace: l.pace }));
    const tooBright = loops.filter((l) => Number(l.brightness) >= 55)
      .map((l) => ({ slug: l.slug, brightness: l.brightness, level: l.level }));
    const stepping = loops.filter((l) => l.verdict === 'visible step')
      .map((l) => ({ slug: l.slug, seam_vs_motion: l.seam_vs_motion }));
    const ready = loops.filter((l) => l.sleep_ready).map((l) => l.slug);

    return {
      loops,
      sleep_ready: ready,
      too_fast_for_sleep: tooFast,
      too_bright_for_sleep: tooBright,
      visible_step: stepping,
    };
  });
  res.status(202).json({ job_id: job.id, status: job.status });
});

/**
 * Integrated loudness of whatever comes out of a filter chain, in LUFS.
 * Analysis only - decodes to null, encodes nothing.
 */
async function integratedAfter(file, chain) {
  const af = chain ? `${chain},loudnorm=print_format=json` : 'loudnorm=print_format=json';
  const r = await run('ffmpeg', ['-hide_banner', '-nostats', '-i', file,
    '-af', af, '-f', 'null', '-'], { timeoutMs: 5 * 60 * 1000 });
  const m = r.stderr.match(/\{[\s\S]*?"input_i"[\s\S]*?\}/);
  if (!m) return null;
  const v = Number(JSON.parse(m[0]).input_i);
  return Number.isFinite(v) ? v : null;
}

/**
 * Level out a music bed that swells.
 *
 * `tide` measured 9.5 LU of loudness range against 1.6-4.2 for the other five
 * beds, with a passage at 0:18 sitting 5.7 dB above its own norm. A listener
 * heard that as a wave crash loud enough to wake them. The bed is not bad, it
 * is just too dynamic for something playing while someone sleeps.
 *
 * dynaudnorm rides the loud passages down without pulling the quiet ones up,
 * which is what separates it from a compressor here - the aim is to shrink the
 * range, not to make the bed louder.
 *
 * The original is kept as <slug>.orig.mp3 and never deleted, so a bad flatten
 * can always be undone by hand. Re-run Audio Report afterwards to see whether
 * the range actually came down.
 */
app.post('/jobs/flatten', (req, res) => {
  const body = req.body || {};
  const slugs = (Array.isArray(body.slugs) && body.slugs.length ? body.slugs : [body.slug])
    .map(slugSafe).filter(Boolean);
  if (!slugs.length) return res.status(400).json({ error: 'slug or slugs is required' });

  // Gentle by default. A slow attack lets the shape of the music through and
  // only rides down what sustains above the threshold.
  const thresh = clampNum(body.threshold_db, -40, -6, -24);
  const ratio = clampNum(body.ratio, 1.5, 20, 4);

  const job = startJob('flatten', { slugs, thresh, ratio }, async (j) => {
    const done = [];
    for (const slug of slugs) {
      const file = path.join(DIRS.tracks, `${slug}.mp3`);
      if (!fs.existsSync(file)) { done.push({ slug, error: 'not found' }); continue; }

      const orig = path.join(DIRS.tracks, `${slug}.orig.mp3`);
      if (!fs.existsSync(orig)) await fsp.copyFile(file, orig);

      step(j, `measuring ${slug} before`);
      const before = await measureTrack(orig);

      // A slow compressor with no makeup gain pulls the loud passages down and
      // leaves the quiet ones alone. That is the whole job.
      //
      // dynaudnorm was the obvious tool and was wrong: it normalises toward a
      // target, so it lifted the quiet parts instead, made the bed 6 dB louder
      // overall, and left the range wider than it started. Measured, not
      // assumed - it went from 12 LU to 14.8 LU.
      //
      // Compressing alone costs about 8 dB of level, so the second half of
      // this is restoring exactly what the compressor took, measured on the
      // compressed signal rather than guessed.
      const comp = `acompressor=threshold=${thresh}dB:ratio=${ratio}`
        + ':attack=100:release=2000:knee=6:makeup=1';

      step(j, `measuring ${slug} after compression`);
      const compLufs = await integratedAfter(orig, comp);
      const makeup = (before.integrated_lufs !== null && compLufs !== null)
        ? Number((before.integrated_lufs - compLufs).toFixed(2)) : 0;
      const chain = makeup ? `${comp},volume=${makeup}dB` : comp;

      const tmp = path.join(DIRS.tmp, `${slug}_flat.mp3`);
      step(j, `flattening ${slug} (restoring ${makeup} dB)`);
      await ffmpeg([
        '-i', orig,
        '-af', chain,
        '-c:a', 'libmp3lame', '-b:a', '192k', '-ar', '44100',
        tmp,
      ], { timeoutMs: 10 * 60 * 1000 });

      await fsp.rename(tmp, file);
      step(j, `measuring ${slug} after`);
      const after = await measureTrack(file);

      done.push({
        slug,
        loudness_range_lu: { before: before.loudness_range_lu, after: after.loudness_range_lu },
        sticks_out_db: {
          before: before.transient ? before.transient.sticks_out_db : null,
          after: after.transient ? after.transient.sticks_out_db : null,
        },
        integrated_lufs: { before: before.integrated_lufs, after: after.integrated_lufs },
        makeup_db: makeup,
        original_kept_at: `${slug}.orig.mp3`,
      });
    }
    return { flattened: done };
  });
  res.status(202).json({ job_id: job.id, status: job.status });
});

/**
 * Free space on demand.
 *
 * Body, all optional:
 *   { dry_run: true }          list what would go, delete nothing
 *   { older_than_days: 7 }     keep anything newer (default 0 = everything)
 *   { sources: false }         keep the fal source clips
 *   { renders: false }         keep orphaned renders
 *   { tmp: false }             keep the scratch directory
 *
 * Loops and tracks are never candidates. Start with a dry run.
 */
app.post('/jobs/sweep', (req, res) => {
  const b = req.body || {};
  const job = startJob('sweep', { dry_run: Boolean(b.dry_run) }, async (j) => {
    const out = await sweepVolume(b);
    step(j, out.dry_run
      ? `${out.candidates} files could go, ${out.would_free_mb} MB`
      : `removed ${out.candidates} files, freed ${out.freed_mb} MB, `
        + `${out.disk_after.avail_gb} GB free`);
    return out;
  });
  res.status(202).json({ job_id: job.id, status: job.status });
});

app.get('/assets', async (_req, res) => {
  const loops = await fsp.readdir(DIRS.loops).catch(() => []);
  const tracks = await fsp.readdir(DIRS.tracks).catch(() => []);
  res.json({ loops, tracks, disk: await diskUsage() });
});

app.use((_req, res) => res.status(404).json({ error: 'not found' }));

ensureDirs()
  .then(() => {
    app.listen(PORT, '::', () => {
      console.log(`saltwater render service listening on ${PORT}, data dir ${DATA_DIR}`);
    });
  })
  .catch((err) => {
    console.error('failed to create data directories', err);
    process.exit(1);
  });
