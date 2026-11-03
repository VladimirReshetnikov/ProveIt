#!/usr/bin/env python3
"""Bounded author-side check of compact word chosen-rank assembly."""
from hashlib import sha256
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import time

HERE = Path(__file__).resolve().parent
SOURCE = HERE / 'CompactWordChosenRank.lean'
PACKFIELDS = Path('/tmp/compact44-word-packing-fields-author-rmla494o')
LOWFIELDS = Path('/tmp/compact44-word-low-fields-author-73efsca_')
ORIGIN = Path('/tmp/compact44-origin-low-nocarry-author-7ki8y7e9')
PULSE = Path('/tmp/compact44-pulse-packed-cell-author-j8srdneh')
PULSEBIT = Path('/tmp/compact44-pulse-bit-author-kcf5puza')
UNIFORMPACK = Path('/tmp/compact44-uniform-packed-cell-author-576k0hda')
BLOCKS = Path('/tmp/compact44-uniform-blocks-author-x9_2dexw')
UNIFORM = Path('/tmp/compact44-cell-digit-uniform-author-x99hircy')
BASE = Path('/tmp/compact44-base-low-nocarry-author-18mja7xw')
DIGITSUPPORT = Path('/tmp/compact44-cell-digit-supported-author-qrjh3x0o')
PACKED = Path('/tmp/compact44-packed-cell-author-6k4g0ptt')
SUPPORT = Path('/tmp/compact44-cell-support-author-owsc91mv')
DEF = Path('/tmp/compact44-cell-digit-def-author-zrvgi8n3')
DIGIT = Path('/tmp/compact44-cell-digit-author-5ocsnwk4')
COPY = Path('/tmp/compact44-cell-copy-author-xh37hl8r')
WORD_PROVIDER = Path('/tmp/ipra-compact-word-cell-author-01/lib')
PACKING_PROVIDER = Path('/tmp/ipra-compact44-symbolic-unit-join/lib')
PROVIDER = Path('/tmp/compact44-word-rank-overlay-o4nua886')
PACKAGE = Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
LEAN = Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
OBS = HERE / 'observations/attempt02'
SUFFIXES = ('.olean', '.olean.private', '.olean.server', '.ir', '.ilean',
            '.olean.hash', '.olean.private.hash', '.olean.server.hash', '.ir.hash', '.ilean.hash')


def digest(path):
    return sha256(Path(path).read_bytes()).hexdigest()


def record(path):
    path = Path(path)
    if not os.path.lexists(path):
        return None
    if not path.is_file():
        raise RuntimeError(f'dangling dependency: {path}')
    return {'sha256': digest(path), 'resolved': str(path.resolve(strict=True)),
            'link': os.readlink(path) if path.is_symlink() else None}


if OBS.exists():
    raise RuntimeError('refusing to overwrite prior attempt')
if shutil.disk_usage('/tmp').free < 4 * 1024**3:
    raise RuntimeError('less than 4 GiB free')
OBS.mkdir(parents=True)
word_dir = WORD_PROVIDER / 'DiophantineConsistency'
packing_dir = PACKING_PROVIDER / 'DiophantineConsistency'
overlay_dir = PROVIDER / 'DiophantineConsistency'
overlap = sorted(p.relative_to(WORD_PROVIDER).as_posix() for p in WORD_PROVIDER.rglob('*')
                 if p.is_file() and (PACKING_PROVIDER / p.relative_to(WORD_PROVIDER)).is_file())
overlap_records = {name: {'word_sha256': digest(WORD_PROVIDER / name),
                          'packing_sha256': digest(PACKING_PROVIDER / name)} for name in overlap}
if any(v['word_sha256'] != v['packing_sha256'] for v in overlap_records.values()):
    raise RuntimeError('word and packing provider overlap conflict')
expected = {p.name for p in word_dir.iterdir() if p.is_file()} | \
           {p.name for p in packing_dir.iterdir() if p.is_file()}
actual = {p.name for p in overlay_dir.iterdir()}
if actual != expected:
    raise RuntimeError('overlay filenames do not match selected inputs')
overlay_before = {str(p): record(p) for p in overlay_dir.iterdir()}
root_before = {str(p): record(p) for p in PACKING_PROVIDER.iterdir() if p.is_file()}
(OBS / 'overlay-preflight.json').write_text(json.dumps({
    'overlap_count': len(overlap), 'overlap': overlap_records,
    'overlay_count': len(overlay_before), 'overlay_before': overlay_before,
    'packing_root_count': len(root_before), 'packing_root_before': root_before,
}, indent=2, sort_keys=True) + '\n')
run = Path(tempfile.mkdtemp(prefix='compact44-word-chosen-rank-author-'))
source = run / SOURCE.name
shutil.copyfile(SOURCE, source)
source_hash = digest(source)
env = {'PATH': '/usr/bin:/bin', 'LEAN_PATH': f'{PACKFIELDS}:{LOWFIELDS}:{ORIGIN}:{PULSE}:{PULSEBIT}:{UNIFORMPACK}:{BLOCKS}:{UNIFORM}:{BASE}:{DIGITSUPPORT}:{PACKED}:{SUPPORT}:{DEF}:{DIGIT}:{COPY}:{PROVIDER}:{WORD_PROVIDER}:{PACKING_PROVIDER}:{PACKAGE}', 'LEAN_NUM_THREADS': '1'}
deps = subprocess.run([str(LEAN), '--deps', str(source)], env=env,
                      capture_output=True, text=True, timeout=120)
(OBS / 'deps').write_text(deps.stdout)
(OBS / 'deps.stderr').write_text(deps.stderr)
if deps.returncode != 0 or deps.stderr:
    raise RuntimeError('dependency scan failed')
guards = {}
for line in deps.stdout.splitlines():
    path = Path(line)
    if not path.is_absolute() or not path.is_file() or path.suffix != '.olean':
        raise RuntimeError(f'bad dependency: {line}')
    stem = str(path)[:-len('.olean')]
    for suffix in SUFFIXES:
        guards[stem + suffix] = record(stem + suffix)
command = [str(LEAN), '-M3000', '-j1', '-DElab.async=false', f'--root={run}',
           str(source), '-o', str(run / 'CompactWordChosenRank.olean')]
start = time.monotonic()
try:
    proc = subprocess.run(command, env=env, capture_output=True, text=True, timeout=180)
    code, output = proc.returncode, proc.stdout + proc.stderr
except subprocess.TimeoutExpired as exc:
    code, output = None, str(exc.stdout or '') + str(exc.stderr or '')
(OBS / 'compile.log').write_text(output)
after = {path: record(path) for path in guards}
overlay_after = {str(p): record(p) for p in overlay_dir.iterdir()}
root_after = {str(p): record(p) for p in PACKING_PROVIDER.iterdir() if p.is_file()}
object_path = run / 'CompactWordChosenRank.olean'
result = {'command': command, 'run': str(run), 'exit_code': code,
          'duration_seconds': round(time.monotonic() - start, 3),
          'source_sha256': source_hash, 'workspace_source_sha256_after': digest(SOURCE),
          'log_sha256': digest(OBS / 'compile.log'), 'guards_before': guards,
          'guards_unchanged': guards == after,
          'overlay_unchanged': overlay_before == overlay_after,
          'packing_root_unchanged': root_before == root_after,
          'object_sha256': digest(object_path) if object_path.is_file() else None,
          'scope': 'Single-author exploratory compile; inherited provider ancestry.'}
(OBS / 'terminal.json').write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
print(json.dumps({key: result[key] for key in ('run', 'exit_code', 'duration_seconds',
                                                'guards_unchanged', 'object_sha256')}, sort_keys=True))
if code != 0 or not object_path.is_file() or guards != after or overlay_before != overlay_after or root_before != root_after or digest(SOURCE) != source_hash or \
        any(word in output for word in ('error:', 'warning:', 'sorryAx')):
    raise SystemExit(1)
