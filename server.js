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
 * How long the audio track itself runs, which is not the same as how long the
 * file runs.
 *
 * A render whose music ran out early still reports the full duration on the
 * container and still has an audio stream — it is simply silent at the end.
 * Both of the checks in verify() passed on a reel with four seconds of nothing
 * at the end of it, and the person watching found it instead. This is the
 * measurement that would have caught it.
 *
 * Returns null rather than throwing when the stream carries no duration of its
 * own, which some containers do: a missing measurement must not fail a render
 * that is otherwise fine.
 */
async function probeAudioDuration(file) {
  try {
    const { stdout } = await run('ffprobe', [
      '-v', 'error', '-select_streams', 'a:0',
      '-show_entries', 'stream=duration', '-of', 'csv=p=0', file,
    ], { timeoutMs: 60000 });
    const seconds = Number(String(stdout).trim());
    return Number.isFinite(seconds) && seconds > 0 ? seconds : null;
  } catch (err) {
    return null;
  }
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
 * The DEEP SLEEP SOUNDS lockup, burned into every loop as a corner mark.
 *
 * Renamed 2026-09-08 from SALTWATER. Same artwork - the ring and three waves
 * are the original mark measured off it, the wave underline and the tagline
 * are the original artwork untouched - with the name reset over two lines,
 * because sixteen characters will not hold the original letterspacing on one.
 * Two short lines also render LARGER than one long one at the same corner
 * width, so the name is more legible than SALTWATER was, not less.
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
  + 'C7spgAnJSRuampRAsK2gdsMOCqBbshNGNNU1iWBbAXDYLQF00J80jJzq9ZZavdIHthVAJOySAAnoOcFbPbmnYh2pgG0FUBV2RnAc'
  + 'Y+l6Wkx0Qk9G1PHXmZ7biZB03FbJWiuAMdgJwWGRp8r0OCk6X1tyPgK9nI/UifQOYAR2QXBUtJOkkyfGdKtLpnMSqS7bCokWnIUd'
  + 'EByVPqdGJDT9qte2QpoFZ2EHBIfFO2Wn6gSZbmksmnRJbdVtW6VHRFCbYRcExzl1f8/5+4rGYVvpl75d66B2wU4IaQSPg+iHbQVQ'
  + 'PeAQgTSDwQ30w7YCSH84UCAtmR2qz+Wytmx1hG0FkM5wsEDaSt2ouNU/aWBbAaQrHDJQDWAaNf2wrQDSCw4eqFYwKbh+2FYA6QCH'
  + 'EVRT0ZOIyxXr78mNJr1hWwEAgA0Yc2ae0+oI2woAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA'
  + 'AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA'
  + 'AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAqgPGGGPMzJL9+7P/Gj3arrUZiWbkSHX9U6ZkZOiNwA6jR6trvu66xO82u4Un'
  + 'TFDXMm+eviXirYm/RqmdEUa65x412pEjzS87YYL+peJHbeVVfUtH8vsHDdIbdyJnlq5KvJdnZDzwgPru114TBPPrnDfvvPOsfY5o'
  + 'pZaUdOpkZjlVoiWXLlXfOWqU2XXoW1NiGRnGSkr07vivR/sMU6a43cZiNlI653IlXnrKFPXdes9kVQnCsmVqGTNnGova3Kuqhx9W'
  + '16s/y5leWWVaAoj0/PN612b1o2sJvjJjn8Ic4+s1HpuWdiK98kqi5fiuGC+K1avtiTDa8ma+i1Gjoi378MP612rlVatLm//c8Zgt'
  + 'W7vsjDR7tpV1btiQjE+yZ4+55eJvAWPvj72OxGvSx2hZid6t59VoSkqMx66/9PjLzZwZbRl9+6TqtdeilaEn6VnZnto7jHzemNcc'
  + 'fEE91ySVlyCEkPfemz2bkOef79v3f6tJUI667LZtXbuajUZb/5o1Tz1FyMsvd+mi/uWJJ559Nn4E1mjrvvnmBg1efln9LV7ERrew'
  + 'to5t28aOzcz861979tSzHnXZu+/+17+q/n3kyIULY5VQv35JCSHdu2/ZojfCWPHefPOAAXfcoTfWyCUXL3799b17X3756quNLh3r'
  + 'fXpeJSQQyM42u/TNNx886PEQIkn9+k2erL06adL06Ylij4eX/txzK1fm5DRufOyYKB4/nplZUdGu3VtvJVqKEEI2bnzxxe3bb731'
  + 'scfUv+jdljff/PvvmZktW27b1qWLvn1bT6l///sXX4TD3br99NP552vbKfER88QTW7ZkZvp8OTmNGx8+TAghjRv/+9/xlyHk6NEV'
  + 'K/bunTEj0XpGjZKkX39t0uS887Zsyc9/911CCBk6dNu2/PxhwxYvzsv7+mu9nzJRRHq3YKL369kn58zZt08Ui4oKCs45Z+xY7dU/'
  + '/jHevqM3tosvJsTjqVdvy5amTXNyGjU666ySEm0/ibUUIYQcPTp16i+/PPKIkeO7ahn//vdrr115pfbN6s025s4QkeeIESM6dpw1'
  + 'S+9aYxSm/3qLELc7VlY/coT/vUePxGuLvcZE0WRm8nf4/VVfeecdfdcbVvDyzznnzL/Z1RDeoUOs8jZs4H8vKEgcYay/R3+Nf3P6'
  + '4otVcu/e0dYWb7nY36S6dGGhnjVbedXsfhh/SzL22mvx4k7E+F7ctClf5szmNPVTtmljZp0lJdaOqOhL23vERC5hfC80v8ZEGjTQ'
  + '9jFR1B+D3fuket4wVoM0tu5o1M9/ZsvF6tX69klC2rTh7zxyJHo8ibas9TNEixbR1poobsMri/7uyolGlZubuCwWwUw0/PXoJ2D1'
  + 'XsiZJ257dOrEGGNn3oOz86TB39u0abTXBEHv9o319+hlm951CCHdujFW9fSmr8x4h4na/JmTk7gEK6+a3Q/jvcpfs3JSM/598CWi'
  + 'X4DpOSoT7TdGYrGjVKNr7duXMcYuvth8OdY+Z7wS9Z+Rkr1PWrm3aHafrFcv2mvqZWGivgPx3rV8eeKYzG+xQYMYY2zq1OjLZGXF'
  + 'j9twKEbfq+8AopQxxtasMbo8fzUz00qE5vn90cvmX0nsu1h2HuyJ3sE7Z1X9K2+DiFe7MHsPLlY8fJuYvy+Sk5PMg0h91eOJ9S7r'
  + 'ZceOOxGjy1vfa+K9gzHztfP4pb70kvHljL3/sssYi1YXsr5G/SUaPfr5sRotZuyT0V43f7kW79VYr/XoYXJL6l+M77Txr9PnzmUs'
  + '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'
  + 'MT7Qe/U5pd14Y+K95t13GYtflzpznck5zdlxAj6Tx1O/fvQJzPWWZNdZQ23FicVMDIzxplUr+6SeaUfMxBYd7yA6Z0689yxaxFi8'
  + 'W0K8jTP+w1k8qtgD+cdvemYs9pMiOTm5udGnPTC5HY0sZn5XSfQ636iJxlmyvn4rYpdtNWr97zRy2nj33ViJlP+1d2/r2ypZ24Q3'
  + 'GiWKLvZ7Ek3uF2tJfmAmmtXGru/bnuXt2GvOfMe8edaPpTNL4Ns30Yw19m0BI8eLHecNXs6gQS5XdnZWFu9gw5tFW7ZMtI5Yr/Nz'
  + 'o7VbU87sk7H7hqsPi1lZJ2P6yojeOdXs9jK5JY0spm4cjyfaq1lZVjYdi5Bo+ViPC/NXzY5Zk0hBQfTo+Eg5doxpw7vhMBb9ylw9'
  + '+cceaLHqOvmcrtFf5QNTWD21xLqL16cPY/EbpPly0a9E69XTF5v5g8HafhjvVf6a2RGgEpUeb4m2baO9ph6ViXq5nrlO6/uH2VKN'
  + 'rpnf9d25s+rf+T5edSINO9Zophyn90mzs3AlKj0adV7yVq2ivVq3Ln810SNa8db6ww/696Ro59P4S8c6O/IWXROdG41twOxs/v4z'
  + 'V6TuBvFHa0m8M8SPRk11Z76Hz0KSaCxN3p83/tTosfE1aE+dEqLOG2RXE2LsyZB5U6/eMW7USdOjr1nPltaLl1N5CINEV96EaN/k'
  + 'mTUbdSJqPV2I+DtzcyP/ph7EiZeL91q8EmK9yhtnrW5X4yWo01+fuZT690svNbNOq58l2vLqpaTxaBIvUXkZfvlrVzuSHvyWTqx7'
  + 'z7xLX506xmNQt5mZfVJ9jtjS4Aomto/aMln5bKmVpac6xG8TRotdLSP21uTUiuHw4ZF/Pfts/td4aT7a9k58rk9QXG5uZqbLlZHh'
  + 'cglCVlb8+pL2le/ZM2pU//5qAtATQLx3qZPY6btCYYyx1asHDerWLXJYhEQT7lo9nLQ1XXbZqFFqw5qek4bbzZuPRDEz0+WK/3yb'
  + '6t13e/To0CFyjCXjkUYbmlutLdrTvK5F16HDPfdoA3cYWfK11x54YNAg459UPZgZY2zQoB49tBIKCxOvOfprifdD/uoDD3Tq1Lt3'
  + 'jx49ejzwAJ+wQf0s+mI3E1uipRhjbPXqe+655x4jR2X8NGu+Zh6v1HiXi/wdI0d26HDZZZ06XXfdZZe1bt2jx6BBI0YkWoYxxqZM'
  + 'GTlSG6TCSqRGJSpFz14V/TXt24y/9Lx5d97Zv//YsQ88wPsoq4yNiWU08vhLqREY3ScJqVxdWLbs4Ycrfyo9JaipkW8d3ruZa9FC'
  + 'X/R+/6hR/PkZC3sJiyr+MpU/rJGvUs+ukviDaCfCSHqq8ozpefwhUQnGtpbxLcw791SVeM6LaGs186pRxreJis8bYs8nNbL2+O9K'
  + 'VEr0b9SuLWq2nOhHxdKlVtZp7TOZLdXc1rXybdjz3en7XFZeNbNPJroTroe9++TcucbXXZWRhluze4aVPUrXh9CzpPrAuZHr3USl'
  + 'G/kovL8qY4wtW6ZvLA/+7K++0uNp3lyts+l/2N74FtaSbeKexWcaPjzeevRHr9fIkWqNzviVs9bYaizBRq5dLUHfRZS1/fDMb3PD'
  + 'BuuDOeiNLT7tutvIpJGx1tmrl5VoYi17ww1Gt6/eo0a9p2Z0JGZr25wbNoyxWP0qON6TIVYtyu590nodVn9s8WnVMjNnMkIIyczU'
  + 'xpKPPzRPLHyGOePLq0/K6styKRh6MP3xHSUVwzACAEDtomPY7dpBzwDkAAAAxiC5/Jdd9yMBAAAgQrdujDVt6nQUAAAANZL1Tg4A'
  + 'AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAACQPv4/Vi7jF1CgrgUAAAAASUVORK5CYII=';

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

/**
 * Read a line aloud.
 *
 * Same key as the music, a different endpoint and a different order of cost:
 * music bills around 900 credits a minute, speech around one credit a
 * character, so a 150-character beat is roughly 150 credits against 3,600 for
 * a four-minute bed. That difference is the whole reason the voice is
 * affordable on a plan that is being wound down.
 *
 * Returns null rather than throwing when there is no voice configured, so a
 * Short without narration is still a Short.
 */
async function speak(job, { text, voice_id, out }) {
  const vid = String(voice_id || SHORT_VOICE_ID || '').trim();
  if (!vid || !String(text || '').trim()) return null;
  step(job, `speaking ${String(text).length} characters in voice ${vid}`);
  const res = await fetch(`https://api.elevenlabs.io/v1/text-to-speech/${vid}`, {
    method: 'POST',
    headers: { 'xi-api-key': ELEVENLABS_API_KEY, 'Content-Type': 'application/json' },
    body: JSON.stringify({
      text: String(text),
      model_id: 'eleven_multilingual_v2',
      output_format: 'mp3_44100_128',
      // Stability high and style at zero on purpose: this is a sleep channel,
      // and an expressive read is the wrong instrument entirely.
      voice_settings: { stability: 0.70, similarity_boost: 0.75, style: 0.0, use_speaker_boost: true },
    }),
  });
  if (!res.ok) throw new Error(`elevenlabs tts ${res.status}: ${(await res.text()).slice(0, 500)}`);
  await fsp.writeFile(out, Buffer.from(await res.arrayBuffer()));
  return out;
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
// The place line at the top runs for the whole clip and is the quietest thing
// on screen, so it sits below the quote in size.
const PLACE_SIZE = clampNum(Number(process.env.SHORT_PLACE_SIZE), 20, 90, 40);

/*
 * Pale sand, not white.
 *
 * Jack's pick off a four-way render on a real frame, and the reasoning holds
 * up: this is watched on a phone, in the dark, in bed. Pure white is the
 * brightest and coolest thing a screen emits - the exact thing every night
 * mode on every device exists to move away from - and warming it a few percent
 * drops the glare while still reading as white at a glance. It also separates
 * from the picture for free: every scene in this library is cool, blue water
 * under a blue night, and warm type sits forward of a cool image without
 * having to be brighter.
 */
const TEXT_COLOR = String(process.env.SHORT_TEXT_COLOR || '#E6D3B3');

// A calm female read. Overridable per job, because the right voice is a
// judgement made by listening rather than a value to derive - GET /voices
// lists what the account actually has.
const SHORT_VOICE_ID = String(process.env.SHORT_VOICE_ID || '');

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

/**
 * How wide a line of text actually is, in pixels, measured rather than guessed.
 *
 * This exists because a caption ran off both edges of a published Short:
 * "Let your body become heavier with every breath" is 1312 px at 54 px on this
 * font, on a frame 1080 px wide. drawtext centres on `text_w` and will happily
 * centre something wider than the canvas, so the ends simply leave the screen
 * and nothing anywhere reports a problem.
 *
 * Estimating from an average glyph width was the tempting fix and is wrong for
 * exactly the lines that matter: an italic serif varies more than 3:1 between
 * 'i' and 'm', so the estimate is comfortably right on ordinary lines and
 * wrong on the long ones. So ffmpeg draws the text on an oversized black
 * canvas and `cropdetect` reports the ink extent. It is the same renderer that
 * will draw the real thing, which is the only measurement worth having.
 *
 * A failed measurement returns null and the caller leaves the line alone —
 * a Short with an unwrapped caption is worse than one with a wrapped one, but
 * both are better than no Short.
 */
const inkWidthCache = new Map();
async function measureInkWidth(text, size) {
  const font = findFont();
  if (!font || !String(text).trim()) return null;
  const key = `${size}|${text}`;
  if (inkWidthCache.has(key)) return inkWidthCache.get(key);

  const f = path.join(DIRS.tmp,
    `measure_${Date.now().toString(36)}_${Math.random().toString(36).slice(2, 8)}.txt`);
  let width = null;
  try {
    await fsp.writeFile(f, String(text), 'utf8');
    // -v info, not the usual -v error: cropdetect reports on the info channel,
    // so the quiet default that every other call here wants would throw the
    // measurement away.
    const { stderr } = await run('ffmpeg', ['-y', '-v', 'info',
      '-f', 'lavfi', '-i', 'color=black:s=6000x400:d=1:r=5',
      '-vf', `drawtext=fontfile=${font}:textfile=${f}:fontcolor=white`
        + `:fontsize=${size}:x=200:y=120,cropdetect`,
      '-frames:v', '3', '-f', 'null', '-'], { timeoutMs: 30000 });
    // On a short line cropdetect reports a negative height - it finds no
    // vertical run to trim - so the pattern has to allow a minus sign or the
    // measurement silently comes back null for exactly the lines that fit.
    const hits = String(stderr).match(/crop=-?\d+:-?\d+:-?\d+:-?\d+/g) || [];
    const last = hits[hits.length - 1];
    if (last) {
      const m = last.match(/crop=(-?\d+):(-?\d+):(-?\d+):(-?\d+)/);
      const ink = Number(m[1]);
      const leftBearing = Math.max(0, Number(m[3]) - 200);
      // Ink is not advance width: the pen starts left of the first mark and an
      // italic overhangs the last one. Pad by an eighth of the size so the fit
      // test is the pessimistic one.
      if (Number.isFinite(ink) && ink > 0) {
        width = ink + leftBearing + Math.round(size * 0.12);
      }
    }
  } catch (err) {
    width = null;
  }
  await fsp.rm(f, { force: true }).catch(() => {});
  inkWidthCache.set(key, width);
  return width;
}

/** Greedy word wrap against a measured width. One word too wide is left alone. */
async function wrapToWidth(line, size, maxWidth) {
  const full = await measureInkWidth(line, size);
  if (full === null || full <= maxWidth) return [line];
  const words = String(line).split(/\s+/).filter(Boolean);
  if (words.length < 2) return [line];

  const out = [];
  let cur = '';
  for (const word of words) {
    const candidate = cur ? `${cur} ${word}` : word;
    const w = await measureInkWidth(candidate, size);
    if (w !== null && w > maxWidth && cur) { out.push(cur); cur = word; } else { cur = candidate; }
  }
  if (cur) out.push(cur);
  return out;
}

/**
 * Turn a caption into lines that fit, shrinking the type only when wrapping
 * alone cannot do it.
 *
 * Wrapping first and shrinking second is deliberate. Type size is a house
 * decision — 54 px was chosen by looking at a real frame — and a caption that
 * quietly renders at 38 px because it is long is a different design every
 * night. Line count is the cheaper thing to spend: the tip sits in open sky
 * with room for three lines, the call to action has two before it collides
 * with YouTube's own rail.
 */
async function layoutCaption(raw, size, maxWidth, maxLines) {
  const explicit = captionLines(raw);
  if (!explicit.length) return { lines: [], size: size };

  let s = size;
  let best = { lines: explicit, size: s };
  for (let attempt = 0; attempt < 5; attempt += 1) {
    const lines = [];
    for (const line of explicit) {
      for (const piece of await wrapToWidth(line, s, maxWidth)) lines.push(piece);
    }
    let widest = 0;
    for (const line of lines) {
      const w = await measureInkWidth(line, s);
      if (w !== null && w > widest) widest = w;
    }
    best = { lines: lines, size: s };
    if (lines.length <= maxLines && widest <= maxWidth) return best;
    if (s <= 32) return best;
    s = Math.max(32, Math.round(s * 0.88));
  }
  return best;
}

function drawTextClause(file, size, yExpr, alphaExpr, colour) {
  return [
    `drawtext=fontfile=${findFont()}`,
    `textfile=${file}`,
    `fontcolor=${colour || TEXT_COLOR}`,
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
  //
  // But it is not the only thing that matters, which is why it is now a
  // choice. The beach loops are 18.53s, so snapping a 30-second ask rounds it
  // UP to 37.07 — and on Instagram a reel that crosses thirty seconds loses the
  // shorter-video treatment the feed gives clips under it. Trading four seconds
  // of length for an invisible seam is a good deal; trading the format's
  // completion behaviour for it may not be. `snap: false` renders exactly what
  // was asked for.
  //
  // What that costs is honest and small: one step in the picture at the moment
  // the feed replays, on footage that is already drifting slowly. The audio is
  // unaffected either way — the bed is far longer than the clip and never wraps.
  const snap = input.snap === undefined ? true : Boolean(input.snap);
  const loopSeconds = await probeDuration(loopPath).catch(() => 0);
  if (loopSeconds > 1) {
    const cycles = Math.max(1, Math.round(seconds / loopSeconds));
    const snapped = Math.round(cycles * loopSeconds * 1000) / 1000;
    if (!snap) {
      const part = seconds / loopSeconds;
      const off = Math.abs(part - Math.round(part));
      step(job, `holding ${seconds}s exactly (snap off) — `
        + `${part.toFixed(2)} x the ${loopSeconds.toFixed(2)}s picture loop`
        + (off > 0.05
          ? ', so the picture steps once where the feed replays it'
          : ', which happens to land on a whole cycle anyway'));
    } else if (Math.abs(snapped - seconds) > 0.05) {
      step(job, `snapping ${seconds}s to ${snapped}s — `
        + `${cycles} x the ${loopSeconds.toFixed(2)}s picture loop, so it repeats seamlessly`);
      seconds = snapped;
    }
  }
  /*
   * Make sure there is actually enough music to reach the end.
   *
   * This shipped broken. The bed is seeked into by `audio_start_sec` — 40s by
   * default, because the opening of an ambient track is near-silence and makes
   * a dead first second — and then cut to `seconds`. Nothing checked that the
   * bed was long enough to survive both. A 75-second bed seeked to 40 has 35
   * seconds left; the clip was 37; the last two seconds had no audio at all,
   * and the bed's own fade-out made the two before that nearly silent. Four
   * seconds of silence at the end of a 37-second reel, reported by Jack, and
   * invisible to every check the pipeline had.
   *
   * The seek is a preference, not a requirement, so it gives way: pull it back
   * far enough that the clip fits inside the bed. Only when the bed is shorter
   * than the whole clip does the audio have to wrap, and then it says so.
   *
   * Computed after the length is settled, because snapping can lengthen it —
   * checking before the snap would have passed this exact render.
   */
  const trackSeconds = await probeDuration(trackPath).catch(() => 0);
  let seek = Number.isFinite(startAt) ? startAt : 40;
  let loopAudio = false;
  if (trackSeconds > 1) {
    if (trackSeconds <= seconds + 0.25) {
      seek = 0;
      loopAudio = true;
      step(job, `the bed is ${trackSeconds.toFixed(1)}s against a ${seconds}s clip `
        + '— looping it from the start, so it wraps once');
    } else {
      // Stay three seconds clear of the end, not just inside it.
      //
      // Beds are generated with their own fade-out — the session renderer
      // trims those off before joining, and nothing here does. Landing the
      // clip on the bed's last second would put that fade under the render's
      // own two-second fade and the music would sound like it died early,
      // which is the same complaint as running out, only quieter.
      //
      // The guard can only ever pull the seek back, never past zero, so it
      // cannot cause the overrun it exists to prevent.
      const TAIL_GUARD = 3;
      const maxSeek = Math.max(0, trackSeconds - seconds - TAIL_GUARD);
      if (seek > maxSeek) {
        const short = seek + seconds - trackSeconds;
        step(job, `audio_start_sec ${seek}s ${short > 0
          ? `would run a ${trackSeconds.toFixed(1)}s bed out ${short.toFixed(1)}s early`
          : `leaves no room before the end of a ${trackSeconds.toFixed(1)}s bed`}`
          + ` — starting at ${maxSeek.toFixed(1)}s instead`);
        seek = maxSeek;
      }
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
    /*
     * Three things on screen, each with its own job.
     *
     *   top     where this is - the beach and the country, held for the whole
     *           clip, because a viewer who scrolls past should still know they
     *           were somewhere real
     *   middle  the quote, split into beats and read aloud
     *   bottom  the offer, arriving only in the last ten seconds
     *
     * The beats are supplied already split. The renderer times and fits them;
     * it does not decide where a sentence breaks, because that is a judgement
     * about writing and it belongs with the writing.
     */
    const place = String(input.place || '').trim();
    const cta = String(input.cta || '').trim();
    const rawBeats = Array.isArray(input.beats) ? input.beats : null;
    const beats = (rawBeats || [])
      .map((b) => String(b).replace(/\s+/g, ' ').trim())
      .filter(Boolean);

    // The old single-tip shape still works, so WF-B keeps running while the
    // quote format is being wired up.
    const tip = String(input.tip || input.hook || '').trim();
    if (!beats.length && tip) beats.push(tip);

    const TEXT_MAX_W = W - 112;

    let n = 0;
    const drawOne = async (text, size, yExpr, alphaExpr, tag) => {
      const f = path.join(DIRS.tmp, `${runId}_${tag}.txt`);
      await fsp.writeFile(f, text, 'utf8');
      written.push(f);
      n += 1;
      parts.push(`${last}${drawTextClause(f, size, yExpr, alphaExpr)}[x${n}]`);
      last = `[x${n}]`;
    };

    // ------------------------------------------------------------ the place
    if (place) {
      const fit = await layoutCaption(place, PLACE_SIZE, TEXT_MAX_W, 1);
      await drawOne(fit.lines.join(' '), fit.size, 'h*0.085',
        textAlpha(0.4, seconds - 0.5, 1.4, 0.88), 'place');
      step(job, `place: ${JSON.stringify(fit.lines.join(' '))} at ${fit.size}px`);
    }

    // ------------------------------------------------------------ the quote
    //
    // Beats share the clip evenly. Three sentences over thirty seconds is ten
    // seconds each, which is long enough to read a line twice and short enough
    // that nothing sits still - and each one drifts slowly upward while it is
    // up, so the screen is never quite static.
    const ctaHold = clampNum(Number(input.cta_sec ?? input.handover_sec), 4,
      Math.max(5, seconds - 4), 10);
    const ctaAt = Math.max(0, seconds - ctaHold);

    if (beats.length) {
      const per = seconds / beats.length;
      const FADE = 1.1;
      for (let bi = 0; bi < beats.length; bi += 1) {
        const fit = await layoutCaption(beats[bi], TIP_SIZE, TEXT_MAX_W, 3);
        const lead = Math.round(fit.size * 1.5);
        const block = fit.lines.length * lead;
        const t0 = bi * per;
        const t1 = t0 + per;
        const al = textAlpha(t0 + 0.15, t1 - 0.15, FADE, 0.95);
        for (let li = 0; li < fit.lines.length; li += 1) {
          const y = `(h*0.46-${Math.round(block / 2)})+${li * lead}`
            + `-26*(t-${t0.toFixed(2)})/${per.toFixed(2)}`;
          await drawOne(fit.lines[li], fit.size, y, al, `b${bi}_${li}`);
        }
        step(job, `beat ${bi + 1}/${beats.length} at ${fit.size}px, `
          + `${fit.lines.length} line(s), ${t0.toFixed(0)}-${t1.toFixed(0)}s: `
          + JSON.stringify(fit.lines));
      }
    }

    // ------------------------------------------------------------ the offer
    if (cta) {
      const fit = await layoutCaption(cta, CTA_SIZE, TEXT_MAX_W, 2);
      const lead = Math.round(fit.size * 1.5);
      const al = textAlpha(ctaAt, seconds - 0.4, 1.4, 0.92);
      for (let i = 0; i < fit.lines.length; i += 1) {
        await drawOne(fit.lines[i], fit.size, `h*0.72+${i * lead}`, al, `cta${i}`);
      }
      step(job, `offer from ${ctaAt.toFixed(0)}s at ${fit.size}px: ${JSON.stringify(fit.lines)}`);
    }
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

  /*
   * The voice.
   *
   * One request per beat, not one for the whole quote. The characters cost the
   * same either way, and a single long read finishes while the second beat is
   * still on screen - the words and the picture drift apart and the viewer
   * notices immediately. Per beat, each line is spoken as it appears.
   *
   * A failed request drops that line and keeps the Short. Losing narration is
   * a worse Short; losing the render is a lost night.
   */
  const speakBeats = (Array.isArray(input.beats) ? input.beats : [])
    .map((b) => String(b).replace(/\s+/g, ' ').trim())
    .filter(Boolean);
  const voiceId = String(input.voice_id || SHORT_VOICE_ID || '').trim();
  const voices = [];
  if (input.speak !== false && voiceId && speakBeats.length) {
    const per = seconds / speakBeats.length;
    for (let i = 0; i < speakBeats.length; i += 1) {
      const out = path.join(DIRS.tmp, `${runId}_voice${i}.mp3`);
      try {
        const f = await speak(job, { text: speakBeats[i], voice_id: voiceId, out });
        if (f) {
          written.push(f);
          // A second of picture before anyone speaks. Opening on a voice is
          // startling, which is the opposite of the job.
          voices.push({ file: f, at: i * per + 1.0 });
        }
      } catch (err) {
        step(job, `voice failed on beat ${i + 1}: ${err.message} — continuing without it`);
      }
    }
  }

  const fadeOut = Math.max(0, seconds - 2);
  step(job, `cutting a ${seconds}s vertical short${font ? ' with captions' : ''}`);
  // Built as one array rather than spliced together from three. Splicing is
  // how `ambience_slug` and `music_start_sec` each went missing from a session
  // job without anything erroring.
  const args = ['-stream_loop', '-1', '-i', loopPath];
  if (loopAudio) args.push('-stream_loop', '-1');
  args.push('-ss', String(seek), '-t', String(seconds), '-i', trackPath);
  // The scrims as still images.
  //
  // They were the `gradients` lavfi source first, which is correct and
  // unusably slow: as a live source it recomputes the ramp for every frame of
  // the Short, and a three-second test had not finished after five minutes. As
  // a single PNG each takes 0.08s to make once and costs an ordinary overlay
  // thereafter.
  args.push('-loop', '1', '-i', scrims.top);
  args.push('-loop', '1', '-i', scrims.bottom);
  if (drawMark) args.push('-loop', '1', '-i', LOCKUP_PATH);

  // Voice inputs go on the end so the indices of everything before them do not
  // move when the mark is switched off.
  let vi = drawMark ? 5 : 4;
  const tail = `${sleepDrc()}afade=t=in:st=0:d=1.5,afade=t=out:st=${fadeOut}:d=2`;
  if (voices.length) {
    // The bed steps back five decibels for the whole clip rather than ducking
    // under a sidechain. On thirty seconds of near-continuous speech a gate
    // would be opening and closing throughout, and every one of those moves is
    // audible on music this quiet. A constant step is inaudible.
    const chain = [`[1:a]volume=-5dB[bed]`];
    const labels = ['[bed]'];
    for (let i = 0; i < voices.length; i += 1) {
      const ms = Math.round(voices[i].at * 1000);
      args.push('-i', voices[i].file);
      chain.push(`[${vi + i}:a]adelay=${ms}|${ms},volume=1.6[vx${i}]`);
      labels.push(`[vx${i}]`);
    }
    chain.push(`${labels.join('')}amix=inputs=${labels.length}:duration=first`
      + `:dropout_transition=0:normalize=0[mixed]`);
    chain.push(`[mixed]${tail}[a]`);
    parts.push(...chain);
    vi += voices.length;
  }

  args.push(
    '-t', String(seconds),
    '-filter_complex', parts.join(';'),
    '-map', '[v]', '-map', voices.length ? '[a]' : '1:a:0',
    '-c:v', 'libx264', '-preset', 'medium', '-crf', '20', '-r', '30',
    '-c:a', 'aac', '-b:a', '192k', '-ar', '44100',
  );
  if (!voices.length) args.push('-af', tail);
  args.push('-movflags', '+faststart', outPath);

  try {
    await ffmpeg(args, { timeoutMs: 20 * 60 * 1000 });
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

  // "Has an audio stream" is not "has audio all the way to the end". A reel
  // shipped with four silent seconds at the end because the bed ran out, and
  // every check above passed on it. One second of tolerance covers encoder
  // rounding; anything more is music that stopped before the picture did.
  const audioSeconds = await probeAudioDuration(file);
  if (audioSeconds !== null && duration - audioSeconds > 1) {
    throw new Error(`audio stops ${(duration - audioSeconds).toFixed(1)}s before the end `
      + `(${audioSeconds.toFixed(1)}s of sound in a ${duration.toFixed(1)}s file) — `
      + 'the bed was too short, or audio_start_sec seeked too far into it');
  }

  step(job, `verified ${(stat.size / 1048576).toFixed(0)} MB, ${duration.toFixed(0)}s`
    + (audioSeconds === null ? '' : `, audio to ${audioSeconds.toFixed(0)}s`));
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

/**
 * What voices this account actually has.
 *
 * Read-only, and here rather than guessed: ElevenLabs voice ids are opaque
 * strings and picking one from memory is how a job ends up narrated by
 * whoever happens to own that id.
 */
app.get('/voices', async (_req, res) => {
  try {
    const r = await fetch('https://api.elevenlabs.io/v1/voices', {
      headers: { 'xi-api-key': ELEVENLABS_API_KEY },
    });
    if (!r.ok) return res.status(502).json({ error: `elevenlabs ${r.status}`, body: (await r.text()).slice(0, 300) });
    const j = await r.json();
    return res.json({
      configured: SHORT_VOICE_ID || null,
      voices: (j.voices || []).map((v) => ({
        voice_id: v.voice_id,
        name: v.name,
        category: v.category,
        labels: v.labels || {},
        preview_url: v.preview_url,
      })),
    });
  } catch (err) {
    return res.status(500).json({ error: err.message });
  }
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
