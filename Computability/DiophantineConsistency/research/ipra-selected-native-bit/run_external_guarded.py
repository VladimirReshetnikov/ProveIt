#!/usr/bin/env python3
"""Run the external comparison author extension with a sampled disk reserve."""
import hashlib
import json
import os
import shutil
import signal
import subprocess
import sys
import time
from pathlib import Path

D = Path(__file__).resolve().parent
ROOT = D.parents[3]
manifest = D / 'external-author-additions.json'
manifest_sha = 'eea1923b96112722f8e2a9151cc870250a5b694bd95d772525fabe8127adcb57'
out = Path('/tmp/ipra-selected-external-comparison-author-20261101')
log = Path('/tmp/ipra-selected-external-comparison-author-process.log')
observation = Path('/tmp/ipra-selected-external-comparison-wrapper.json')
floor = 4 * 1024**3
digest = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
if digest(manifest) != manifest_sha:
    raise ValueError('manifest pin')
if out.exists() or out.is_symlink() or log.exists() or observation.exists():
    raise ValueError('output or wrapper evidence already exists')
free_before = shutil.disk_usage('/tmp').free
if free_before < floor:
    raise ValueError('disk reserve already breached')
cmd = ['ionice', '-c', '3', 'nice', '-n', '19', sys.executable, '-u',
       str(ROOT / 'Computability/DiophantineConsistency/research/author-only-extension/run.py'),
       '--manifest', str(manifest), '--manifest-sha256', manifest_sha,
       '--output', str(out)]
minimum = free_before
triggered = False
started = time.monotonic()
with log.open('x') as stream:
    proc = subprocess.Popen(cmd, cwd=ROOT, stdout=stream, stderr=subprocess.STDOUT,
                            start_new_session=True)
    while True:
        try:
            code = proc.wait(timeout=2)
            break
        except subprocess.TimeoutExpired:
            free = shutil.disk_usage('/tmp').free
            minimum = min(minimum, free)
            if free < floor:
                triggered = True
                try:
                    os.killpg(proc.pid, signal.SIGTERM)
                except ProcessLookupError:
                    pass
                try:
                    code = proc.wait(timeout=10)
                except subprocess.TimeoutExpired:
                    try:
                        os.killpg(proc.pid, signal.SIGKILL)
                    except ProcessLookupError:
                        pass
                    code = proc.wait()
                break
minimum = min(minimum, shutil.disk_usage('/tmp').free)
result = {'command': cmd, 'observed_child_exit_code': code, 'reserve_bytes': floor,
          'free_before_bytes': free_before, 'minimum_observed_free_bytes': minimum,
          'reserve_triggered': triggered, 'sampling_seconds': 2,
          'elapsed_seconds': round(time.monotonic() - started, 3),
          'process_log': str(log), 'process_log_sha256': digest(log),
          'scope': 'Historical author-only extension; sampled reserve and input guards are not continuous traces.'}
with observation.open('x') as stream:
    json.dump(result, stream, indent=2, sort_keys=True)
    stream.write('\n')
print(json.dumps(result, sort_keys=True))
if code != 0 or triggered:
    sys.exit(1)
