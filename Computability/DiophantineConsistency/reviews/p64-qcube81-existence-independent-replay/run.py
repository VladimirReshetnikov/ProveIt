#!/usr/bin/env python3
"""Replay the 81-operation positive-zero theorem with guarded direct inputs."""
import hashlib
import json
import os
import subprocess
import time
from pathlib import Path

if not __debug__:
    raise SystemExit('refusing optimized Python')
HERE = Path(__file__).resolve().parent
REPO = HERE.parents[3]
SOURCE = REPO / 'Computability/DiophantineConsistency/research/fourteen-p64-qcube-existence-draft/P64QCubeExistence.lean'
LEAN = Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
OUT = Path('/tmp/p64-qcube81-existence-independent-check01')
OBS = HERE / 'observations/attempt01'
PATHS = ['/tmp/p64-independent-captured-replay/lib', '/tmp',
         '/tmp/trace74-direct-four-block-1zltaw2f/lib',
         '/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib']
GUARDS = {
    str(SOURCE): '40bea77b56a19feb5b8c3145c0d4f6bb069fafb5885f70d52b6e557b1cd67e08',
    '/tmp/P64QCubeBinding.olean': 'b0a32668e5e6869e4067d7813b9142ad3465b941cc174452c08579938deda07d',
    '/tmp/P64NormFirstReplacement.olean': 'da38a424ac91ea386fbe0129b4a700684ebf51e3388ef8c65f1d753f2e25f51e',
    str(LEAN): 'e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550',
}

def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()

def guard():
    actual = {path: sha(path) for path in GUARDS}
    if actual != GUARDS:
        raise RuntimeError('direct input hash mismatch: ' + repr(actual))
    for module in ('P64QCubeBinding', 'P64NormFirstReplacement'):
        selected = next((Path(root) / (module + '.olean') for root in PATHS
                         if (Path(root) / (module + '.olean')).is_file()), None)
        if selected != Path('/tmp') / (module + '.olean'):
            raise RuntimeError('unexpected direct import resolution: ' + repr(selected))
    return actual

if OUT.exists() or OBS.exists():
    raise SystemExit('refusing existing output or observation directory')
before = guard()
OUT.mkdir()
OBS.mkdir(parents=True)
env = os.environ.copy()
env['LEAN_PATH'] = ':'.join(PATHS)
output = OUT / 'P64QCubeExistence.olean'
cmd = [str(LEAN), '-M4000', '-j1', '-DElab.async=false', '--root=' + str(SOURCE.parent),
       str(SOURCE), '-o', str(output)]
start = time.monotonic()
try:
    result = subprocess.run(cmd, env=env, text=True, stdout=subprocess.PIPE,
                            stderr=subprocess.STDOUT, timeout=300)
    log, code = result.stdout, result.returncode
except subprocess.TimeoutExpired as exc:
    log = (exc.stdout or b'').decode(errors='replace') if isinstance(exc.stdout, bytes) else (exc.stdout or '')
    log += '\nTimed out after 300 seconds.\n'
    code = 124
(OBS / 'compile.log').write_text(log)
try:
    after, guard_error = guard(), None
except Exception as exc:
    after, guard_error = None, repr(exc)
names = ['candidate_zero_iff', 'exists_old_of_new', 'exists_new_of_old', 'positive_zero_iff']
expected = ["'P64QCubeExistence." + n + "' depends on axioms: [propext, Classical.choice, Quot.sound]" for n in names]
reports_match = all(log.count(line) == 1 for line in expected)
clean = not any(word in log for word in ('sorryAx', 'error:', 'warning:'))
receipt = {'exit': code, 'seconds': round(time.monotonic() - start, 3), 'command': cmd,
           'lean_path': env['LEAN_PATH'], 'guards_before': before, 'guards_after': after,
           'guard_error': guard_error, 'log_sha256': sha(OBS / 'compile.log'),
           'object_sha256': sha(output) if output.is_file() else None,
           'reports_match': reports_match, 'no_sorry_error_warning': clean,
           'runner_sha256': sha(__file__),
           'scope': 'single replay, direct inputs and path precedence guarded; transitive project/package/dynamic ancestry inherited'}
(OBS / 'result.json').write_text(json.dumps(receipt, indent=2, sort_keys=True) + '\n')
print(log, end='')
if code != 0 or guard_error or not reports_match or not clean or not output.is_file():
    raise SystemExit('FAIL: see captured receipt')
print('PASS: independent 81-operation existence replay')
