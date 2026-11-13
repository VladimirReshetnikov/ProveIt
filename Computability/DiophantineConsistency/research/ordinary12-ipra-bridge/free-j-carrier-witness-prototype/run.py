#!/usr/bin/env python3
"""Bounded author-side check of free-J ordinary-tail witness bridge."""
from hashlib import sha256
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import time

HERE = Path(__file__).resolve().parent
SOURCE = HERE / 'FreeJCarrierWitness.lean'
COPY = Path('/tmp/compact44-cell-copy-author-xh37hl8r')
PROVIDER = Path('/tmp/ipra-ordinary12-coexistence-pair-01/author/child-output/lib')
SIGNED = Path('/tmp/ipra-freej-signed-transport-replay-01/author')
TAIL = Path('/tmp/free-j-ordinary-tail-witness-author-cdbrbrco')
BRIDGE = Path('/tmp/free-j-completeness-factor-author-q9rapr3k')
POWER = Path('/tmp/ipra-freej-power-finish-pair-01/author/lib')
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
run = Path(tempfile.mkdtemp(prefix='free-j-carrier-witness-author-'))
source = run / SOURCE.name
shutil.copyfile(SOURCE, source)
source_hash = digest(source)
env = {'PATH': '/usr/bin:/bin', 'LEAN_PATH': f'{TAIL}:{BRIDGE}:{SIGNED}:{PROVIDER}:{PACKAGE}', 'LEAN_NUM_THREADS': '1'}
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
provider_before = {str(p): record(p) for root in (PROVIDER,POWER) for p in root.rglob('*') if p.is_file()}
overlap = [(p, POWER / p.relative_to(PROVIDER)) for p in PROVIDER.rglob('*') if p.is_file() and (POWER / p.relative_to(PROVIDER)).is_file()]
if any(digest(a) != digest(b) for a,b in overlap):
    raise RuntimeError('provider overlap mismatch')
command = [str(LEAN), '-M3000', '-j1', '-DElab.async=false', f'--root={run}',
           str(source), '-o', str(run / 'FreeJCarrierWitness.olean')]
start = time.monotonic()
try:
    proc = subprocess.run(command, env=env, capture_output=True, text=True, timeout=180)
    code, output = proc.returncode, proc.stdout + proc.stderr
except subprocess.TimeoutExpired as exc:
    code, output = None, str(exc.stdout or '') + str(exc.stderr or '')
(OBS / 'compile.log').write_text(output)
after = {path: record(path) for path in guards}
provider_after = {str(p): record(p) for root in (PROVIDER,POWER) for p in root.rglob('*') if p.is_file()}
object_path = run / 'FreeJCarrierWitness.olean'
result = {'command': command, 'run': str(run), 'exit_code': code,
          'duration_seconds': round(time.monotonic() - start, 3),
          'source_sha256': source_hash, 'workspace_source_sha256_after': digest(SOURCE),
          'log_sha256': digest(OBS / 'compile.log'), 'guards_before': guards,
          'guards_unchanged': guards == after, 'provider_before': provider_before,
          'provider_unchanged': provider_before == provider_after,
          'object_sha256': digest(object_path) if object_path.is_file() else None,
          'scope': 'Single-author exploratory compile; inherited provider ancestry.'}
(OBS / 'terminal.json').write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
print(json.dumps({key: result[key] for key in ('run', 'exit_code', 'duration_seconds',
                                                'guards_unchanged', 'object_sha256')}, sort_keys=True))
if code != 0 or not object_path.is_file() or guards != after or provider_before != provider_after or digest(SOURCE) != source_hash or \
        any(word in output for word in ('error:', 'warning:', 'sorryAx')):
    raise SystemExit(1)
