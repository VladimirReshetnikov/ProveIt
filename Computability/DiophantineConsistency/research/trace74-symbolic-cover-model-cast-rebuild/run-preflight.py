#!/usr/bin/env python3
"""Capture a pinned read-only compatible-provider preflight and its exit."""
from hashlib import sha256
from pathlib import Path
import json
import os
import subprocess
import sys
import time

if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('use python3 -I -S -B')
H = Path(__file__).resolve().parent
RUN = H / 'run.py'
EXPECTED = '9a1df967e1ff846cac50347510d43148543090d18d9ce1188c900be3525eab2a'
O = H / 'observations/preflight-attempt01'
sha = lambda p: sha256(Path(p).read_bytes()).hexdigest()
if os.path.lexists(O) or sha(RUN) != EXPECTED:
    raise SystemExit('preflight exists or runner drift')
wrapper = sha(__file__)
O.mkdir(parents=True)
cmd = [sys.executable, '-I', '-S', '-B', str(RUN), '--preflight-only']
start = time.time_ns()
with (O / 'stdout').open('x') as out, (O / 'stderr').open('x') as err:
    p = subprocess.run(cmd, stdout=out, stderr=err, env={'PATH': '/usr/bin:/bin'})
result = {'command': cmd, 'exit': p.returncode, 'start_ns': start, 'end_ns': time.time_ns(),
          'runner_before': EXPECTED, 'runner_after': sha(RUN), 'wrapper_before': wrapper,
          'wrapper_after': sha(__file__), 'stdout_sha256': sha(O / 'stdout'),
          'stderr_sha256': sha(O / 'stderr')}
(O / 'terminal.json').write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
print(json.dumps({'exit': p.returncode, 'terminal_sha256': sha(O / 'terminal.json')}))
if p.returncode or result['runner_before'] != result['runner_after'] or result['wrapper_before'] != result['wrapper_after']:
    raise SystemExit(1)
