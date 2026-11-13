#!/usr/bin/env python3
"""Single fresh-project endpoint rebuild, bounded by disk and wall time."""
import hashlib
import json
import os
import shutil
import signal
import subprocess
import sys
import time
from pathlib import Path

if not __debug__:
    raise SystemExit('refusing optimized Python')
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
TASK = ROOT / 'Computability/DiophantineConsistency'
SNAP = Path('/tmp/current14-standard-fresh-source-20261104')
PROVIDER = Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/build-all-receipt.json')
OUTPUT = Path('/tmp/current14-standard-fresh-build-20261104')
LOG = Path('/tmp/current14-standard-fresh-build-20261104.log')
OBS = HERE / 'run-observation.json'
PRE = HERE / 'preflight-observation.json'
DRIVER = TASK / 'research/fresh-project-closure/rebuild.py'
FOUNDATION_INPUT = TASK / 'reviews/foundation-provider-recovery/input-manifest.json'
SNAP_SHA = '1e8b03cac1b2db995091dff13c749faf955fc524bf2da42a637743e9d7a53749'
PROVIDER_SHA = '7cbd49b6d84497c46520e908fc8c4dc105d7a0070fd1323c6c28e26bf4cf00f6'
MAX_SECONDS = 21600
MIN_FREE = 4_000_000_000
def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()
def lean_processes():
    result = []
    for d in Path('/proc').iterdir():
        if not d.name.isdigit():
            continue
        try:
            if (d / 'comm').read_text().strip() == 'lean':
                result.append(int(d.name))
        except (FileNotFoundError, ProcessLookupError, PermissionError):
            pass
    return sorted(result)
if OUTPUT.exists() or LOG.exists() or OBS.exists():
    raise SystemExit('refusing existing build, log or observation path')
pre = json.loads(PRE.read_text())
if pre.get('status') != 'PASS' or pre.get('snapshot_sha256') != SNAP_SHA or pre.get('provider_sha256') != PROVIDER_SHA:
    raise SystemExit('missing matching successful preflight')
if sha(SNAP / 'manifest.json') != SNAP_SHA or sha(PROVIDER) != PROVIDER_SHA:
    raise SystemExit('snapshot or Foundation receipt changed')
free = shutil.disk_usage('/tmp').free
if free < MIN_FREE:
    raise SystemExit('less than 4 GB free')
busy = lean_processes()
if busy:
    raise SystemExit('refusing to launch while Lean is running: ' + repr(busy))
cmd = [sys.executable, '-I', '-S', '-B', str(DRIVER), '--snapshot', str(SNAP), '--output', str(OUTPUT),
       '--provider-receipt', str(PROVIDER), '--snapshot-sha256', SNAP_SHA,
       '--provider-sha256', PROVIDER_SHA, '--foundation-input', str(FOUNDATION_INPUT),
       '--expected-axiom-reports', '4']
state = {'status': 'RUNNING', 'command': cmd, 'max_seconds': MAX_SECONDS,
         'minimum_free_bytes': MIN_FREE, 'preflight_sha256': sha(PRE),
         'driver_sha256': sha(DRIVER), 'runner_sha256': sha(__file__),
         'snapshot_sha256': SNAP_SHA, 'provider_sha256': PROVIDER_SHA,
         'samples': [], 'scope': 'Single fresh project build. Package-transitive, dynamic and between-sample provenance inherited; not a paired replay.'}
def save():
    q = OBS.with_suffix('.tmp')
    q.write_text(json.dumps(state, indent=2, sort_keys=True) + '\n')
    q.replace(OBS)
start = time.monotonic()
with LOG.open('x') as log:
    proc = subprocess.Popen(cmd, cwd=ROOT, stdout=log, stderr=subprocess.STDOUT, start_new_session=True)
    state['pid'] = proc.pid
    save()
    while proc.poll() is None:
        elapsed = time.monotonic() - start
        free = shutil.disk_usage('/tmp').free
        sample = {'elapsed_seconds': round(elapsed, 2), 'free_bytes': free}
        try:
            inner = json.loads((OUTPUT / 'state.json').read_text())
            sample.update({k: inner.get(k) for k in ('status', 'phase', 'index', 'module')})
        except (FileNotFoundError, json.JSONDecodeError):
            pass
        state['samples'].append(sample)
        save()
        if free < MIN_FREE or elapsed >= MAX_SECONDS:
            state['stop_reason'] = 'disk threshold' if free < MIN_FREE else 'wall time limit'
            os.killpg(proc.pid, signal.SIGTERM)
            try:
                proc.wait(timeout=20)
            except subprocess.TimeoutExpired:
                os.killpg(proc.pid, signal.SIGKILL)
            break
        time.sleep(10)
    code = proc.wait()
state.update(exit=code, elapsed_seconds=round(time.monotonic()-start, 2),
             log_sha256=sha(LOG), final_free_bytes=shutil.disk_usage('/tmp').free)
try:
    inner = json.loads((OUTPUT / 'state.json').read_text())
    state['build_status'] = inner.get('status')
    state['build_source_status'] = inner.get('source_status')
    state['build_source_drift'] = inner.get('workspace_source_drift')
    state['build_state_sha256'] = sha(OUTPUT / 'state.json')
except (FileNotFoundError, json.JSONDecodeError):
    state['build_status'] = None
state['status'] = 'PASS' if code == 0 and state.get('build_status') == 'PASS' else 'FAILED'
save()
print(json.dumps({k: state.get(k) for k in ('status', 'pid', 'exit', 'elapsed_seconds', 'stop_reason', 'build_status', 'build_source_status', 'final_free_bytes')}, sort_keys=True), flush=True)
if state['status'] != 'PASS':
    raise SystemExit(1)
