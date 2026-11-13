#!/usr/bin/env python3
"""Capture the two read-only gap and degree checks without overwriting."""
from hashlib import sha256
import json
from pathlib import Path
import subprocess
import sys

if sys.flags.optimize:
    raise SystemExit('optimized Python refused')
here = Path(__file__).resolve().parent
out = here / 'observations/attempt01'
if out.exists():
    raise SystemExit('observation already exists')
inputs = [here / x for x in ('check.py', 'degree.py', 'capture.py')]
def sha(p):
    return sha256(p.read_bytes()).hexdigest()
before = {str(p): sha(p) for p in inputs}
out.mkdir(parents=True)
results = {}
for name in ('check', 'degree'):
    cmd = [sys.executable, '-I', '-S', '-B', str(here / (name + '.py'))]
    p = subprocess.run(cmd, capture_output=True, timeout=120)
    (out / (name + '.stdout')).write_bytes(p.stdout)
    (out / (name + '.stderr')).write_bytes(p.stderr)
    results[name] = {'command': cmd, 'exit': p.returncode,
                     'stdout_sha256': sha(out / (name + '.stdout')),
                     'stderr_sha256': sha(out / (name + '.stderr'))}
    if p.returncode or p.stderr:
        raise SystemExit(name + ' did not pass')
after = {str(p): sha(p) for p in inputs}
if before != after:
    raise SystemExit('review input changed')
(out / 'terminal.json').write_text(json.dumps({'inputs_before':before, 'inputs_after':after,
                                                'results':results}, indent=2, sort_keys=True) + '\n')
print(json.dumps({'status':'PASS', 'checks': sorted(results), 'inputs_unchanged': True}))
