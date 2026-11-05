#!/usr/bin/env python3
"""Compile P64's byte client against the prepared selected-provider union."""
import hashlib
import json
import os
import subprocess
import time
from pathlib import Path

if not __debug__:
    raise SystemExit('refusing optimized Python')
HERE = Path(__file__).resolve().parent
OUT = Path('/tmp/p64-byte-endpoint-join02')
LEAN = Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
LEAN_SHA = 'e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550'

def sha(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()

plan = json.loads((OUT / 'plan.json').read_text())
source = HERE / 'P64ByteEndpoint.lean'
direct = {
    OUT / 'lib/CompactFourPortByteAssembly2.olean': plan['byte_assembly_sha256'],
    OUT / 'lib/DiophantineConsistency/Compact44/IPRAPositive64.olean': plan['endpoint_sha256'],
}
out = OUT / 'P64ByteEndpoint.olean'
if out.exists() or out.is_symlink() or (OUT / 'result.json').exists():
    raise SystemExit('refusing existing client output')
def guard():
    assert sha(LEAN) == LEAN_SHA
    assert sha(source) == plan['source_sha256']
    for p, h in direct.items():
        assert sha(p) == h, str(p)
guard()
env = os.environ.copy()
env['LEAN_PATH'] = ':'.join([str(OUT / 'lib'), '/tmp',
    '/tmp/trace74-direct-four-block-1zltaw2f/lib',
    '/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib'])
cmd = [str(LEAN), '-M4000', '-j1', '-DElab.async=false', '--root=' + str(HERE),
       str(source), '-o', str(out)]
start = time.monotonic()
try:
    r = subprocess.run(cmd, env=env, text=True, stdout=subprocess.PIPE,
                       stderr=subprocess.STDOUT, timeout=360)
    output, code = r.stdout, r.returncode
except subprocess.TimeoutExpired as e:
    output = (e.stdout or b'').decode(errors='replace') if isinstance(e.stdout, bytes) else (e.stdout or '')
    output += '\nTimed out after 360 seconds.\n'
    code = 124
log = OUT / 'compile.log'
log.write_text(output)
guard()
result = {'exit': code, 'seconds': round(time.monotonic()-start, 3),
          'command': cmd, 'lean_path': env['LEAN_PATH'], 'lean_sha256': LEAN_SHA,
          'source_sha256': sha(source), 'plan_sha256': sha(OUT / 'plan.json'),
          'direct_before_after': {str(p): h for p, h in direct.items()},
          'log_sha256': sha(log), 'object_sha256': sha(out) if out.exists() else None,
          'scope': 'selected-provider union; inherited project/package/dynamic ancestry'}
(OUT / 'result.json').write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
print(output, end='')
if code or any(x in output for x in ('sorryAx', 'error:', 'warning:')):
    raise SystemExit(1)
print('PASS: P64 byte endpoint client', flush=True)
