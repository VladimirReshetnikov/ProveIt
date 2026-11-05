#!/usr/bin/env python3
"""Confirm the launcher refuses to start while a Lean-named process is live."""
import hashlib
import json
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
OUT = HERE / 'busy-control-observation.json'
BUILD = Path('/tmp/current14-standard-fresh-build-20261104')
LOG = Path('/tmp/current14-standard-fresh-build-20261104.log')
RUN_OBS = HERE / 'run-observation.json'
if OUT.exists() or BUILD.exists() or LOG.exists() or RUN_OBS.exists():
    raise SystemExit('refusing existing control or build paths')
fake = subprocess.Popen([sys.executable, '-I', '-S', '-B', '-u', '-c',
    "import ctypes,time; assert ctypes.CDLL(None).prctl(15,b'lean',0,0,0)==0; print('ready',flush=True); time.sleep(60)"],
    stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
try:
    if fake.stdout.readline().strip() != 'ready' or fake.poll() is not None:
        raise RuntimeError('control process did not become live')
    r = subprocess.run([sys.executable, '-I', '-S', '-B', str(HERE / 'run.py')],
                       text=True, capture_output=True, timeout=30)
    absent = not BUILD.exists() and not LOG.exists() and not RUN_OBS.exists()
    result = {'status': 'PASS' if r.returncode != 0 and 'refusing to launch while Lean is running' in r.stderr and absent else 'FAIL',
              'launcher_exit': r.returncode, 'launcher_stdout': r.stdout,
              'launcher_stderr': r.stderr, 'fake_process_pid': fake.pid,
              'build_paths_remain_absent': absent,
              'runner_sha256': hashlib.sha256((HERE / 'run.py').read_bytes()).hexdigest(),
              'scope': 'Controlled launch refusal only; does not test successful compilation or disk-stop handling.'}
    with OUT.open('x') as f:
        json.dump(result, f, indent=2, sort_keys=True)
        f.write('\n')
    print(json.dumps(result, sort_keys=True))
    if result['status'] != 'PASS':
        raise SystemExit(1)
finally:
    fake.terminate()
    fake.wait(timeout=5)
