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
    const m = r && r.stderr.match(/max_volume:\s*(-?[\d.]+) dB/);
    if (m) peaks.push({ at: t, peak: Number(m[1]) });
  }
  if (!peaks.length) return null;

  const sorted = peaks.map((p) => p.peak).slice().sort((a, b) => a - b);
  const median = sorted[Math.floor(sorted.length / 2)];
  const worst = peaks.reduce((a, b) => (b.peak > a.peak ? b : a));
  const above = Number((worst.peak - median).toFixed(1));
  return {
    loudest_at_sec: worst.at,
    loudest_peak_dbfs: worst.peak,
    typical_peak_dbfs: Number(median.toFixed(1)),
    sticks_out_db: above,
    // 6 dB is a doubling of perceived level against the bed's own norm.
    flag: above >= 9 ? 'transient - likely to wake a sleeper'
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
  return {
    duration_sec: Math.round(duration),
    integrated_lufs: integrated,
    true_peak_dbtp: truePeak,
    loudness_range_lu: range,
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
  job.error = err && err.message ? err.message : String(err);
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

  const filter = [
    `[0:v]${speed}split=3[h][m][t];`,
    `[h]trim=0:${f},setpts=PTS-STARTPTS[head];`,
    `[m]trim=${f}:${midEnd},setpts=PTS-STARTPTS[mid];`,
    `[t]trim=${midEnd}:${tot},setpts=PTS-STARTPTS[tailseg];`,
    `[tailseg][head]xfade=transition=fade:duration=${f}:offset=0[blend];`,
    `[mid][blend]concat=n=2:v=1:a=0,`
      + `scale=${scale}:flags=lanczos${grade}${brand.chain}`,
  ].join('');
  await ffmpeg([
    '-i', rawPath,
    ...brand.inputs,
    '-filter_complex', filter,
    '-map', '[v]', '-an',
    '-c:v', 'libx264', '-preset', 'slow', '-crf', '26',
    '-maxrate', '2500k', '-bufsize', '5000k',
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
async function makeVisual(job, { slug, aspect, prompt, dim, vivid }) {
  const safe = slugSafe(slug);
  const isWide = aspect === '16x9';
  const scale = isWide ? '1920:1080' : '1080:1920';
  const rawPath = path.join(DIRS.visuals, `${safe}.mp4`);
  const loopPath = path.join(DIRS.loops, `${safe}_loop.mp4`);

  step(job, 'requesting generation from fal');
  const res = await fetch(`https://fal.run/${FAL_MODEL}`, {
    method: 'POST',
    headers: { Authorization: `Key ${FAL_KEY}`, 'Content-Type': 'application/json' },
    body: JSON.stringify({
      prompt,
      aspect_ratio: isWide ? '16:9' : '9:16',
      resolution: '720p',
      duration: 10,
      camera_fixed: false,
    }),
  });
  if (!res.ok) throw new Error(`fal ${res.status}: ${(await res.text()).slice(0, 600)}`);
  const body = await res.json();
  const url = body && body.video && body.video.url;
  if (!url) throw new Error(`fal returned no video url: ${JSON.stringify(body).slice(0, 600)}`);

  step(job, 'downloading clip (fal deletes results after ~1h)');
  const bytes = await download(url, rawPath);

  const look = lookFrom({ dim, vivid });
  step(job, `building seamless loop (${describeLook(look)})`);
  await buildLoop(rawPath, loopPath, scale, look);

  const duration = await probeDuration(loopPath);
  return { slug: safe, aspect, file_path: rawPath, loop_path: loopPath, source_bytes: bytes, loop_seconds: Number(duration.toFixed(2)), dim: look.dim, vivid: look.vivid };
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
 * Turn a still into ten seconds of slow movement.
 *
 * The zoom is palindromic — fully in at the midpoint, back out by the end —
 * so the last frame matches the first and buildLoop's crossfade has nothing
 * to hide. A one-way zoom would snap back visibly every ten seconds, which is
 * exactly the kind of repeated jolt that wakes someone up.
 *
 * The source is scaled to double the target first: zoompan samples from the
 * upscaled frame, which is what keeps a slow push from looking like it is
 * stepping between pixels.
 */
async function stillToClip(srcPath, outPath, scale) {
  const parts = scale.split(':');
  const w = Number(parts[0]);
  const h = Number(parts[1]);
  const frames = 300; // 10s at 30fps
  const filter = [
    `scale=${w * 2}:${h * 2}:force_original_aspect_ratio=increase:flags=lanczos`,
    `crop=${w * 2}:${h * 2}`,
    `zoompan=z='1.045+0.045*cos(2*PI*on/${frames})':d=${frames}`
      + `:x='iw/2-(iw/zoom/2)':y='ih/2-(ih/zoom/2)':s=${w}x${h}:fps=30`,
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
async function makeTrack(job, { slug, prompt, length_ms }) {
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

  step(job, 'normalising loudness to -16 LUFS');
  await ffmpeg([
    '-i', rawPath,
    '-af', 'loudnorm=I=-16:TP=-1.5:LRA=11',
    '-c:a', 'libmp3lame', '-b:a', '192k',
    outPath,
  ], { timeoutMs: 10 * 60 * 1000 });
  await fsp.rm(rawPath, { force: true });

  const duration = await probeDuration(outPath);
  return { slug: safe, file_path: outPath, duration_sec: Math.round(duration) };
}

// ------------------------------------------------------------------ renders

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

  const tracks = (input.tracks || []).map((t) => path.join(DIRS.tracks, `${slugSafe(t)}.mp3`));
  if (!tracks.length) throw new Error('no tracks supplied');
  for (const t of tracks) {
    if (!fs.existsSync(t)) throw new Error(`track missing: ${t}`);
  }

  // How long each scene holds before cutting to the next one.
  const segment = Math.max(30, Number(input.segment_sec) || 300);

  const audioListPath = path.join(DIRS.tmp, `${runId}_audio.txt`);
  const videoListPath = path.join(DIRS.tmp, `${runId}_video.txt`);
  const outPath = path.join(DIRS.renders, `${runId}.mp4`);
  await writeConcatList(audioListPath, tracks);
  const plan = await buildVideoList(videoListPath, loops, duration, segment);

  const fadeOutStart = Math.max(0, duration - 12);
  step(job, `rendering ${Math.round(duration / 60)} min session from ${loops.length} `
    + `visual(s) in ${plan.segments} segments of ${segment}s, ${tracks.length} beds`);
  try {
    await ffmpeg([
      '-f', 'concat', '-safe', '0', '-i', videoListPath,
      '-f', 'concat', '-safe', '0', '-i', audioListPath,
      '-t', String(duration),
      '-map', '0:v:0', '-map', '1:a:0',
      '-c:v', 'copy',
      '-c:a', 'aac', '-b:a', '192k', '-ar', '44100', '-ac', '2',
      '-af', `${sleepDrc()}afade=t=in:st=0:d=8,afade=t=out:st=${fadeOutStart}:d=12`,
      '-movflags', '+faststart',
      outPath,
    ], { timeoutMs: 60 * 60 * 1000 });
  } catch (err) {
    // A failed render leaves a partial file that can be gigabytes. Without this
    // the volume fills up and every subsequent night fails too.
    await fsp.rm(outPath, { force: true });
    await fsp.rm(audioListPath, { force: true });
    await fsp.rm(videoListPath, { force: true });
    throw err;
  }
  await fsp.rm(audioListPath, { force: true });
  await fsp.rm(videoListPath, { force: true });

  await verify(job, outPath, duration);
  return outPath;
}

async function renderShort(job, input) {
  const runId = slugSafe(input.run_id);
  const loopPath = path.join(DIRS.loops, `${slugSafe(input.visual_slug)}_loop.mp4`);
  if (!fs.existsSync(loopPath)) throw new Error(`visual loop missing: ${loopPath}`);

  const trackPath = path.join(DIRS.tracks, `${slugSafe(input.track_slug)}.mp3`);
  if (!fs.existsSync(trackPath)) throw new Error(`track missing: ${trackPath}`);

  const outPath = path.join(DIRS.renders, `${runId}.mp4`);
  const startAt = Number(input.audio_start_sec);
  const seek = Number.isFinite(startAt) ? startAt : 40;

  step(job, 'cutting 15s vertical short');
  await ffmpeg([
    '-stream_loop', '-1', '-i', loopPath,
    '-ss', String(seek), '-t', '15', '-i', trackPath,
    '-t', '15',
    '-map', '0:v:0', '-map', '1:a:0',
    '-c:v', 'libx264', '-preset', 'slow', '-crf', '20', '-r', '30', '-pix_fmt', 'yuv420p',
    '-c:a', 'aac', '-b:a', '192k', '-ar', '44100',
    '-af', `${sleepDrc()}afade=t=in:st=0:d=1.5,afade=t=out:st=13:d=2`,
    '-movflags', '+faststart',
    outPath,
  ], { timeoutMs: 15 * 60 * 1000 });

  await verify(job, outPath, 15);
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

  await addToPlaylist(job, youtube, videoId, meta.playlist_id);
  return videoId;
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
    disk: await diskUsage(),
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
  const { slug, aspect, prompt, dim, vivid } = req.body || {};
  if (!slug || !prompt) return res.status(400).json({ error: 'slug and prompt are required' });
  if (aspect !== '16x9' && aspect !== '9x16') return res.status(400).json({ error: 'aspect must be 16x9 or 9x16' });
  const job = startJob('visual', { slug, aspect }, (j) => makeVisual(j, { slug, aspect, prompt, dim, vivid }));
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
      const motion = { slow: group.slow, xfade: group.xfade };
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
        await buildLoop(
          path.join(DIRS.visuals, `${slug}.mp4`),
          path.join(DIRS.loops, `${slug}_loop.mp4`),
          scale,
          look,
          motion,
        );
        rebuilt.push({ slug, dim: look.dim, vivid: look.vivid,
          slow: clampNum(motion.slow, 1, 4, 1), xfade: clampNum(motion.xfade, 0.5, 4, 1) });
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
  const { slug, prompt, length_ms } = req.body || {};
  if (!slug || !prompt) return res.status(400).json({ error: 'slug and prompt are required' });
  const job = startJob('track', { slug }, (j) => makeTrack(j, { slug, prompt, length_ms }));
  res.status(202).json({ job_id: job.id, status: job.status });
});

app.post('/jobs/session', (req, res) => {
  const input = req.body || {};
  if (!input.run_id || !input.visual_slug || !input.duration_sec) {
    return res.status(400).json({ error: 'run_id, visual_slug and duration_sec are required' });
  }
  const job = startJob('session', { run_id: input.run_id, visual_slug: input.visual_slug }, async (j) => {
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

    const spiky = tracks
      .filter((t) => t.transient && t.transient.sticks_out_db >= 6)
      .map((t) => ({ slug: t.slug, at_sec: t.transient.loudest_at_sec,
        sticks_out_db: t.transient.sticks_out_db, flag: t.transient.flag }));

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

  return {
    duration_sec: Number(dur.toFixed(1)),
    motion: Number(mean.toFixed(2)),
    motion_p90: Number(p90.toFixed(2)),
    seam: seam === null ? null : Number(seam.toFixed(2)),
    seam_vs_motion: ratio,
    verdict,
    pace: mean < 1 ? 'very slow' : (mean < 2.5 ? 'slow' : (mean < 5 ? 'brisk' : 'fast')),
  };
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
    const stepping = loops.filter((l) => l.verdict === 'visible step')
      .map((l) => ({ slug: l.slug, seam_vs_motion: l.seam_vs_motion }));

    return { loops, too_fast_for_sleep: tooFast, visible_step: stepping };
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
