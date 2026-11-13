#!/usr/bin/env python3
"""Capture the outer runner's completion without overwriting an attempt."""
from pathlib import Path
from hashlib import sha256
import json, os, subprocess, sys, time

p = Path(__file__).resolve().parent
attempt = os.environ.get('ATTEMPT', 'attempt01')
if not attempt.startswith('attempt') or not attempt[7:].isdigit():
    raise SystemExit('bad attempt')
obs = p / 'observations' / ('outer-' + attempt)
obs.mkdir(parents=True, exist_ok=False)
def sha(q): return sha256(q.read_bytes()).hexdigest()
runner = p/'run.py'
source = p/'DirectBFS80FixedIPRA.lean'
pins = {'runner': sha(runner), 'source': sha(source), 'supervisor': sha(Path(__file__))}
start = time.monotonic()
with (obs/'stdout').open('xb') as out, (obs/'stderr').open('xb') as err:
    result = subprocess.run([sys.executable, str(runner)], stdout=out, stderr=err, env=os.environ.copy())
after = {'runner': sha(runner), 'source': sha(source), 'supervisor': sha(Path(__file__))}
receipt = {'exit': result.returncode, 'elapsed': time.monotonic()-start, 'pins': pins, 'after': after,
           'stdout_sha256': sha(obs/'stdout'), 'stderr_sha256': sha(obs/'stderr')}
(obs/'terminal.json').write_text(json.dumps(receipt, indent=2, sort_keys=True)+'\n')
print(json.dumps(receipt))
if result.returncode != 0 or pins != after:
    raise SystemExit(1)
