#!/usr/bin/env python3
"""Bounded endpoint check with direct source/object guards."""
import hashlib
import json
import os
import subprocess
import time
from pathlib import Path

if not __debug__:
    raise SystemExit('refusing optimized Python')
HERE = Path(__file__).resolve().parent
OUT = Path('/tmp/p64-qcube81-ipra-check01')
LEAN = Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
GUARDS = {
    str(HERE / 'P64QCubeEndpoint.lean'): 'bd571e2b4d0c7d9c8b25d4737dc51bc02890fb7e241a06b30238d66c06bf52e0',
    '/tmp/P64QCubeExistence.olean': '74ef2f50d92729ca37cea7aaa5ea1d21df54eeaa6314aeb0fe5138818f23b8f2',
    '/tmp/p64-independent-captured-replay/lib/DiophantineConsistency/Compact44/IPRAPositive64.olean':
        '9416a700b41ca923ad20ad90ef27fc275d99dae7cc59ad3e91d82bf720b8b59d',
    str(LEAN): 'e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550',
}
def sha(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def guard():
    for path, value in GUARDS.items():
        assert sha(path) == value, path
if OUT.exists():
    raise SystemExit('refusing existing result directory')
guard()
OUT.mkdir()
env = os.environ.copy()
env['LEAN_PATH'] = '/tmp/p64-independent-captured-replay/lib:/tmp:/tmp/trace74-direct-four-block-1zltaw2f/lib:/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib'
output = OUT / 'P64QCubeEndpoint.olean'
cmd = [str(LEAN), '-M4000', '-j1', '-DElab.async=false', '--root=' + str(HERE),
       str(HERE / 'P64QCubeEndpoint.lean'), '-o', str(output)]
start = time.monotonic()
try:
    r = subprocess.run(cmd, env=env, text=True, stdout=subprocess.PIPE,
                       stderr=subprocess.STDOUT, timeout=300)
    log, code = r.stdout, r.returncode
except subprocess.TimeoutExpired as e:
    log = (e.stdout or b'').decode(errors='replace') if isinstance(e.stdout, bytes) else (e.stdout or '')
    log += '\nTimed out after 300 seconds.\n'
    code = 124
(OUT / 'compile.log').write_text(log)
guard()
result = {'exit': code, 'seconds': round(time.monotonic()-start, 3), 'command': cmd,
          'lean_path': env['LEAN_PATH'], 'guards_before_after': GUARDS,
          'log_sha256': sha(OUT / 'compile.log'),
          'object_sha256': sha(output) if output.exists() else None,
          'scope': 'guarded direct inputs; inherited project/package/dynamic ancestry'}
(OUT / 'result.json').write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
print(log, end='')
if code or any(x in log for x in ('sorryAx', 'error:', 'warning:')):
    raise SystemExit(1)
print('PASS: P64 q³ endpoint client')
