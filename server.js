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
async function buildLoop(rawPath, loopPath, scale, dim) {
  const grade = nightGrade(dim === undefined ? DEFAULT_DIM : dim);
  const filter = [
    '[0:v]split[a][b];',
    '[a]trim=0:8,setpts=PTS-STARTPTS[main];',
    '[b]trim=8:10,setpts=PTS-STARTPTS[tail];',
    `[main][tail]xfade=transition=fade:duration=1:offset=7,scale=${scale}:flags=lanczos${grade},format=yuv420p[v]`,
  ].join('');
  await ffmpeg([
    '-i', rawPath,
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
async function makeVisual(job, { slug, aspect, prompt, dim }) {
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

  const dimUsed = dim === undefined ? DEFAULT_DIM : clamp01(Number(dim));
  step(job, `building seamless loop (dim ${dimUsed})`);
  await buildLoop(rawPath, loopPath, scale, dimUsed);

  const duration = await probeDuration(loopPath);
  return { slug: safe, aspect, file_path: rawPath, loop_path: loopPath, source_bytes: bytes, loop_seconds: Number(duration.toFixed(2)), dim: dimUsed };
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
async function makeStockVisual(job, { slug, aspect, query, dim, exclude, page, min_duration }) {
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

  const dimUsed = dim === undefined ? DEFAULT_DIM : clamp01(Number(dim));
  step(job, `building seamless loop (dim ${dimUsed})`);
  await buildLoop(rawPath, loopPath, scale, dimUsed);

  const duration = await probeDuration(loopPath);
  const author = (video.user && video.user.name) || 'Pexels';
  return {
    slug: safe,
    aspect,
    file_path: rawPath,
    loop_path: loopPath,
    source_bytes: bytes,
    loop_seconds: Number(duration.toFixed(2)),
    dim: dimUsed,
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
async function makeImportVisual(job, { slug, aspect, url, dim, start, source, credit }) {
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

  const dimUsed = dim === undefined ? DEFAULT_DIM : clamp01(Number(dim));
  step(job, `building seamless loop (dim ${dimUsed})`);
  await buildLoop(rawPath, loopPath, scale, dimUsed);

  const duration = await probeDuration(loopPath);
  return {
    slug: safe,
    aspect,
    file_path: rawPath,
    loop_path: loopPath,
    source_bytes: bytes,
    loop_seconds: Number(duration.toFixed(2)),
    dim: dimUsed,
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
      '-af', `afade=t=in:st=0:d=8,afade=t=out:st=${fadeOutStart}:d=12`,
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
    '-af', 'afade=t=in:st=0:d=1.5,afade=t=out:st=13:d=2',
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
  return videoId;
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
  const { slug, aspect, prompt, dim } = req.body || {};
  if (!slug || !prompt) return res.status(400).json({ error: 'slug and prompt are required' });
  if (aspect !== '16x9' && aspect !== '9x16') return res.status(400).json({ error: 'aspect must be 16x9 or 9x16' });
  const job = startJob('visual', { slug, aspect }, (j) => makeVisual(j, { slug, aspect, prompt, dim }));
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
  const { slug, aspect, query, dim, page, exclude, min_duration } = req.body || {};
  if (!slug || !query) return res.status(400).json({ error: 'slug and query are required' });
  if (aspect !== '16x9' && aspect !== '9x16') return res.status(400).json({ error: 'aspect must be 16x9 or 9x16' });
  const job = startJob('stock', { slug, aspect, query }, (j) => makeStockVisual(j, {
    slug, aspect, query, dim, page, exclude, min_duration,
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
  const { slug, aspect, url, dim, start, source, credit } = req.body || {};
  if (!slug || !url) return res.status(400).json({ error: 'slug and url are required' });
  if (aspect !== '16x9' && aspect !== '9x16') return res.status(400).json({ error: 'aspect must be 16x9 or 9x16' });
  const job = startJob('import', { slug, aspect }, (j) => makeImportVisual(j, {
    slug, aspect, url, dim, start, source, credit,
  }));
  res.status(202).json({ job_id: job.id, status: job.status });
});

/**
 * Rebuild loops from raw clips already on disk, at the capped bitrate and the
 * current night grade. Costs nothing — no fal call — so it is also how you
 * retune the darkness of the whole library: {"all": true, "dim": 0.7}.
 * Omit "dim" to use LOOP_DIM. Pass {"all": true} to redo every raw clip.
 */
app.post('/jobs/reloop', (req, res) => {
  const body = req.body || {};
  const dim = body.dim === undefined ? DEFAULT_DIM : clamp01(Number(body.dim));
  const job = startJob('reloop', { all: Boolean(body.all), slug: body.slug, dim }, async (j) => {
    const files = await fsp.readdir(DIRS.visuals).catch(() => []);
    const targets = files
      .filter((f) => f.endsWith('.mp4'))
      .map((f) => f.slice(0, -4))
      .filter((s) => (body.all ? true : s === slugSafe(body.slug)));
    if (!targets.length) throw new Error('no raw clips matched');

    const rebuilt = [];
    for (const slug of targets) {
      const isWide = slug.indexOf('-16x9-') !== -1;
      const scale = isWide ? '1920:1080' : '1080:1920';
      step(j, `re-encoding ${slug} at capped bitrate, dim ${dim}`);
      await buildLoop(
        path.join(DIRS.visuals, `${slug}.mp4`),
        path.join(DIRS.loops, `${slug}_loop.mp4`),
        scale,
        dim,
      );
      rebuilt.push(slug);
    }
    return { rebuilt: rebuilt.length, slugs: rebuilt, dim, disk: await diskUsage() };
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
    const videoId = await uploadToYouTube(j, file, input);
    await fsp.rm(file, { force: true });
    step(j, 'deleted local render after successful upload');
    return { video_id: videoId, disk: await diskUsage() };
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
