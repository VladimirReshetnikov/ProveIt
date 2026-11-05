#!/usr/bin/env python3
"""Synthetic missing-child controls; launches no Lean process."""
import hashlib
import json
import subprocess
import sys
from pathlib import Path

if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('use python3 -I -S -B without optimization')
HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
from missing_child import finished_or_raise


class Finished:
    def wait(self, timeout):
        if timeout <= 0:
            raise RuntimeError('nonpositive grace')
        return 0


class Live:
    def wait(self, timeout):
        raise subprocess.TimeoutExpired('synthetic live child', timeout)


if finished_or_raise(Finished()) != 0:
    raise RuntimeError('finished child was not accepted')
try:
    finished_or_raise(Live())
except RuntimeError as exc:
    if 'live child missing from group RSS sample' not in str(exc):
        raise
else:
    raise RuntimeError('unmeasurable live child was accepted')

result = {
    'status': 'PASS',
    'finished_child': 'accepted after wait returned exit 0',
    'unmeasurable_live_child': 'rejected after wait timed out',
    'lean_invoked': False,
    'script_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
    'helper_sha256': hashlib.sha256((HERE/'missing_child.py').read_bytes()).hexdigest(),
}
out = HERE/'sampler-control.json'
with out.open('x') as f:
    json.dump(result, f, indent=2, sort_keys=True)
    f.write('\n')
print(json.dumps(result, sort_keys=True))
