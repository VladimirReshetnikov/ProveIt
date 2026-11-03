#!/usr/bin/env python3
"""Bounded author-side check of marked-word cell sum bounds."""
from hashlib import sha256
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import time

HERE = Path(__file__).resolve().parent
SOURCE = HERE / 'CompactMarkedCellSum.lean'
BLOCKSIZE = Path('/tmp/compact44-kernel-block-size-author-6d0hzf9g')
LOW = Path('/tmp/compact44-kernel-low-product-author-xl6f_qx5')
PRESERVE = Path('/tmp/ipra-compact44-symbolic-unit-join/lib')
SPLIT = Path('/tmp/compact44-kernel-split-author-3dcckdqi')
PRODUCT = Path('/tmp/compact44-cell-product-bound-author-6eq960r0')
SIZE = Path('/tmp/compact44-cell-size-bound-author-d72l3hkb')
TOP = Path('/tmp/compact44-k-top-digit-explore/lib')
BYTE = Path('/tmp/ipra-byte-k-specialization-01/lib')
SPARSE = Path('/tmp/ipra-sparse-k-family-01/lib')
RADIX = Path('/tmp/compact44-k-radix-cert-01/lib')
DIGITSUPPORT = Path('/tmp/compact44-cell-digit-supported-author-qrjh3x0o')
SUPPORT = Path('/tmp/compact44-cell-support-author-owsc91mv')
UPACKED = Path('/tmp/compact44-uniform-packed-cell-author-576k0hda')
PACKED = Path('/tmp/compact44-packed-cell-author-6k4g0ptt')
BLOCKS = Path('/tmp/compact44-uniform-blocks-author-x9_2dexw')
DIGIT = Path('/tmp/compact44-cell-digit-author-5ocsnwk4')
UNIFORM = Path('/tmp/compact44-cell-digit-uniform-author-x99hircy')
DEF = Path('/tmp/compact44-cell-digit-def-author-zrvgi8n3')
COPY = Path('/tmp/compact44-cell-copy-author-xh37hl8r')
PROVIDER = Path('/tmp/ipra-compact-word-cell-author-01/lib')
PACKAGE = Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
LEAN = Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
OBS = HERE / 'observations/attempt01'
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
run = Path(tempfile.mkdtemp(prefix='compact44-marked-cell-sum-author-'))
overlay = run / 'overlay' / 'DiophantineConsistency'
overlay.mkdir(parents=True)
providers = [PROVIDER / 'DiophantineConsistency', RADIX / 'DiophantineConsistency',
             PRESERVE / 'DiophantineConsistency']
inventory = {}
for provider in providers:
    for path in sorted(provider.iterdir()):
        if not path.is_file():
            raise RuntimeError(f'unexpected non-file in provider: {path}')
        item = record(path)
        old = inventory.get(path.name)
        if old is None:
            inventory[path.name] = [item]
            (overlay / path.name).symlink_to(path.resolve(strict=True))
        else:
            if old[0]['sha256'] != item['sha256']:
                raise RuntimeError(f'overlapping provider mismatch: {path.name}')
            old.append(item)
(OBS / 'overlay-inventory.json').write_text(json.dumps(inventory, indent=2, sort_keys=True) + '\n')
source = run / SOURCE.name
shutil.copyfile(SOURCE, source)
source_hash = digest(source)
env = {'PATH': '/usr/bin:/bin', 'LEAN_PATH': f'{BLOCKSIZE}:{LOW}:{SPLIT}:{PRODUCT}:{SIZE}:{TOP}:{BYTE}:{SPARSE}:{overlay.parent}:{PRESERVE}:{DIGITSUPPORT}:{SUPPORT}:{UPACKED}:{PACKED}:{BLOCKS}:{UNIFORM}:{DEF}:{DIGIT}:{COPY}:{PROVIDER}:{PACKAGE}', 'LEAN_NUM_THREADS': '1'}
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
           str(source), '-o', str(run / 'CompactMarkedCellSum.olean')]
start = time.monotonic()
try:
    proc = subprocess.run(command, env=env, capture_output=True, text=True, timeout=180)
    code, output = proc.returncode, proc.stdout + proc.stderr
except subprocess.TimeoutExpired as exc:
    code, output = None, str(exc.stdout or '') + str(exc.stderr or '')
(OBS / 'compile.log').write_text(output)
after = {path: record(path) for path in guards}
overlay_unchanged = all(record(Path(item['resolved']))['sha256'] == item['sha256']
                        for items in inventory.values() for item in items)
object_path = run / 'CompactMarkedCellSum.olean'
result = {'command': command, 'run': str(run), 'exit_code': code,
          'duration_seconds': round(time.monotonic() - start, 3),
          'source_sha256': source_hash, 'workspace_source_sha256_after': digest(SOURCE),
          'log_sha256': digest(OBS / 'compile.log'), 'guards_before': guards,
          'guards_unchanged': guards == after, 'overlay_unchanged': overlay_unchanged,
          'object_sha256': digest(object_path) if object_path.is_file() else None,
          'scope': 'Single-author exploratory compile; inherited provider ancestry.'}
(OBS / 'terminal.json').write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
print(json.dumps({key: result[key] for key in ('run', 'exit_code', 'duration_seconds',
                                                'guards_unchanged', 'object_sha256')}, sort_keys=True))
if code != 0 or not object_path.is_file() or guards != after or not overlay_unchanged or digest(SOURCE) != source_hash or \
        any(word in output for word in ('error:', 'warning:', 'sorryAx')):
    raise SystemExit(1)
