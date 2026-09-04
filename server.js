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
 
const DIRS = {
  visuals: path.join(DATA_DIR, 'assets', 'visuals'),
  loops: path.join(DATA_DIR, 'assets', 'loops'),
  tracks: path.join(DATA_DIR, 'assets', 'tracks'),
  renders: path.join(DATA_DIR, 'renders'),
  jobs: path.join(DATA_DIR, 'jobs'),
  tmp: path.join(DATA_DIR, 'tmp'),
};
 
const FAL_MODEL = 'fal-ai/bytedance/seedance/v1/pro/fast/text-to-video';
 
// ---------------------------------------------------------------- utilities
 
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
 * Generate a ~10s clip on fal, then cut it down to a 9s seamless loop whose
 * last second crossfades back onto its first, so the repeat point is invisible.
 * Nothing longer is pre-encoded: the session render loops this file with
 * -stream_loop and -c:v copy, which costs almost nothing.
 */
async function makeVisual(job, { slug, aspect, prompt }) {
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
 
  step(job, 'building seamless loop');
  const filter = [
    '[0:v]split[a][b];',
    '[a]trim=0:8,setpts=PTS-STARTPTS[main];',
    '[b]trim=8:10,setpts=PTS-STARTPTS[tail];',
    `[main][tail]xfade=transition=fade:duration=1:offset=7,scale=${scale}:flags=lanczos,format=yuv420p[v]`,
  ].join('');
  await ffmpeg([
    '-i', rawPath,
    '-filter_complex', filter,
    '-map', '[v]', '-an',
    '-c:v', 'libx264', '-preset', 'slow', '-crf', '20',
    '-r', '30', '-g', '60', '-keyint_min', '60', '-sc_threshold', '0',
    '-movflags', '+faststart',
    loopPath,
  ], { timeoutMs: 20 * 60 * 1000 });
 
  const duration = await probeDuration(loopPath);
  return { slug: safe, aspect, file_path: rawPath, loop_path: loopPath, source_bytes: bytes, loop_seconds: Number(duration.toFixed(2)) };
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
 
async function renderSession(job, input) {
  const runId = slugSafe(input.run_id);
  const duration = Number(input.duration_sec);
  if (!Number.isFinite(duration) || duration < 60) throw new Error(`bad duration_sec: ${input.duration_sec}`);
 
  const loopPath = path.join(DIRS.loops, `${slugSafe(input.visual_slug)}_loop.mp4`);
  if (!fs.existsSync(loopPath)) throw new Error(`visual loop missing: ${loopPath}`);
 
  const tracks = (input.tracks || []).map((t) => path.join(DIRS.tracks, `${slugSafe(t)}.mp3`));
  if (!tracks.length) throw new Error('no tracks supplied');
  for (const t of tracks) {
    if (!fs.existsSync(t)) throw new Error(`track missing: ${t}`);
  }
 
  const listPath = path.join(DIRS.tmp, `${runId}_audio.txt`);
  const outPath = path.join(DIRS.renders, `${runId}.mp4`);
  await writeConcatList(listPath, tracks);
 
  const fadeOutStart = Math.max(0, duration - 12);
  step(job, `rendering ${Math.round(duration / 60)} min session from ${tracks.length} beds`);
  await ffmpeg([
    '-stream_loop', '-1', '-i', loopPath,
    '-f', 'concat', '-safe', '0', '-i', listPath,
    '-t', String(duration),
    '-map', '0:v:0', '-map', '1:a:0',
    '-c:v', 'copy',
    '-c:a', 'aac', '-b:a', '192k', '-ar', '44100', '-ac', '2',
    '-af', `afade=t=in:st=0:d=8,afade=t=out:st=${fadeOutStart}:d=12`,
    '-movflags', '+faststart',
    outPath,
  ], { timeoutMs: 60 * 60 * 1000 });
  await fsp.rm(listPath, { force: true });
 
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
      youtube: Boolean(YT_CLIENT_ID && YT_CLIENT_SECRET && YT_REFRESH_TOKEN),
    },
    host: os.hostname(),
  });
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
  const { slug, aspect, prompt } = req.body || {};
  if (!slug || !prompt) return res.status(400).json({ error: 'slug and prompt are required' });
  if (aspect !== '16x9' && aspect !== '9x16') return res.status(400).json({ error: 'aspect must be 16x9 or 9x16' });
  const job = startJob('visual', { slug, aspect }, (j) => makeVisual(j, { slug, aspect, prompt }));
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
 
