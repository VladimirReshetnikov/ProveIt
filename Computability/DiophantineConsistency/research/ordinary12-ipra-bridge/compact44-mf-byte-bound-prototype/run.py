#!/usr/bin/env python3
"""Bounded author-side check of once-shifted high-byte bound."""
from hashlib import sha256
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import time

HERE = Path(__file__).resolve().parent
SOURCE = HERE / 'CompactShiftedHighBound.lean'
PACKED = Path('/tmp/compact44-packed-cell-author-6k4g0ptt')
BLOCKS = Path('/tmp/compact44-uniform-blocks-author-x9_2dexw')
DIGIT = Path('/tmp/compact44-cell-digit-author-5ocsnwk4')
UNIFORM = Path('/tmp/compact44-cell-digit-uniform-author-x99hircy')
DEF = Path('/tmp/compact44-cell-digit-def-author-zrvgi8n3')
HIGH = Path('/tmp/compact44-shifted-high-digits-author-2p5ms380')
HIGH_HASH = 'be4f35d915c5e538aac51f2acd257188f15cb32609f16dc5d56bbd75b3b2beac'
SHIFT = Path('/tmp/generic-radix-shifted-author-aqd1n6ia')
SHIFT_HASH = 'b1b24a8da200084184f1e4331fbdfa9390ce1019a6f1c8e05649ba0b67046dac'
GENERIC = Path('/tmp/ipra-byte-window-generic-01/lib')
GENERIC_HASH = 'efe663c787fade899d9e9dcf7bc83924dd0ec49f63fdc8682c5df3afb45c0961'
PROVIDER = Path('/tmp/ipra-compact-word-cell-author-01/lib')
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
if digest(HIGH / 'CompactShiftedHighDigits.olean') != HIGH_HASH or digest(SHIFT / 'RadixShiftedDigits.olean') != SHIFT_HASH:
    raise RuntimeError('shifted-high provider drift')
if digest(GENERIC / 'ByteWindow.olean') != GENERIC_HASH:
    raise RuntimeError('generic object hash mismatch')
roots = [HIGH, SHIFT, Path('/tmp/compact44-rank-residue-join-author-6k2xhews'), Path('/tmp/compact44-constructed-rank-author-g2doc30c'), Path('/tmp/compact44-packing-origin-mod-four-author-b3v6f92j'), Path('/tmp/compact44-low-mod-four-author-o28oleni'), Path('/tmp/ipra-compact44-symbolic-unit-join/lib'), Path('/tmp/ipra-compact-word-cell-author-01/lib'), PACKAGE]
generic_before = {str(p.relative_to(GENERIC)): record(p) for p in GENERIC.rglob('*') if p.is_file()}
for name in generic_before:
    for root in roots:
        q = root / name
        if q.is_file() and digest(q) != generic_before[name]['sha256']:
            raise RuntimeError(f'generic overlap mismatch: {q}')
OBS.mkdir(parents=True)
run = Path(tempfile.mkdtemp(prefix='compact44-mf-byte-bound-author-'))
source = run / SOURCE.name
shutil.copyfile(SOURCE, source)
source_hash = digest(source)
env = {'PATH': '/usr/bin:/bin', 'LEAN_PATH': f'{HIGH}:{SHIFT}:{GENERIC}:/tmp/compact44-rank-residue-join-author-6k2xhews:/tmp/compact44-constructed-rank-author-g2doc30c:/tmp/compact44-packing-origin-mod-four-author-b3v6f92j:/tmp/compact44-low-mod-four-author-o28oleni:/tmp/ipra-compact44-symbolic-unit-join/lib:/tmp/ipra-compact-word-cell-author-01/lib:{PACKAGE}', 'LEAN_NUM_THREADS': '1'}
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
           str(source), '-o', str(run / 'CompactShiftedHighBound.olean')]
start = time.monotonic()
try:
    proc = subprocess.run(command, env=env, capture_output=True, text=True, timeout=180)
    code, output = proc.returncode, proc.stdout + proc.stderr
except subprocess.TimeoutExpired as exc:
    code, output = None, str(exc.stdout or '') + str(exc.stderr or '')
(OBS / 'compile.log').write_text(output)
after = {path: record(path) for path in guards}
object_path = run / 'CompactShiftedHighBound.olean'
result = {'command': command, 'run': str(run), 'exit_code': code,
          'duration_seconds': round(time.monotonic() - start, 3),
          'source_sha256': source_hash, 'workspace_source_sha256_after': digest(SOURCE),
          'log_sha256': digest(OBS / 'compile.log'), 'guards_before': guards,
          'guards_unchanged': guards == after,
          'generic_before': generic_before,
          'generic_unchanged': generic_before == {str(p.relative_to(GENERIC)): record(p) for p in GENERIC.rglob('*') if p.is_file()},
          'object_sha256': digest(object_path) if object_path.is_file() else None,
          'scope': 'Single-author exploratory compile; inherited provider ancestry.'}
(OBS / 'terminal.json').write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
print(json.dumps({key: result[key] for key in ('run', 'exit_code', 'duration_seconds',
                                                'guards_unchanged', 'object_sha256')}, sort_keys=True))
if code != 0 or not object_path.is_file() or not result['generic_unchanged'] or guards != after or digest(SOURCE) != source_hash or \
        any(word in output for word in ('error:', 'warning:', 'sorryAx')):
    raise SystemExit(1)
