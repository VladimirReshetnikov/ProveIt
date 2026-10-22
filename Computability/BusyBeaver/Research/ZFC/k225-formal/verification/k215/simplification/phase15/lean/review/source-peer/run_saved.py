"""One independent phase15 saved-evidence check; no proof compiler is invoked."""
from pathlib import Path
import datetime
import hashlib
import json
import os
import signal
import subprocess
import time

ROOT = Path('/home/codex/.codex/worktrees/ec20/Proofs')
OUT = Path('/tmp/k215-phase15-publication-peer')
PACKET = Path('/tmp/k215-phase15-published/lean')
PINS = Path('/tmp/k215-phase15-publication-execution/core-hashes.json')
PINS_SHA = 'a9d3c88d35ecdaff265d39b06152757ccac8a069009cfa9dd4b687e4a7561e4c'
CAPTURE = Path('/tmp/k215-phase15-publication-execution/run2/capture-actual.json')
CAPTURE_SHA = 'b825883829e5ae0c647bcac9fe221fdbd29c2528e1ed15989636695c1d82c664'

def digest(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()

def snapshot(names):
    return {n: {'sha256': digest(PACKET/n), 'bytes': (PACKET/n).stat().st_size}
            for n in names}

assert digest(PINS) == PINS_SHA
assert digest(CAPTURE) == CAPTURE_SHA
pin = json.loads(PINS.read_text())
assert pin['status'] == 'HELD_EIGHT_CORE_PACKET_FILES'
assert pin['directory'] == str(PACKET)
assert pin['capture_outer_sha256'] == CAPTURE_SHA
assert set(pin['files']) == {
    'README.md', 'basis.py', 'basis-reference.json', 'packet.py',
    'review_saved.py', 'result.json', 'index.json', 'execution.tar.gz'}
before = snapshot(pin['files'])
assert before == pin['files']
cap = json.loads(CAPTURE.read_text())
assert cap['status'] == 'PASS_OUTER_EXIT_ZERO' and cap['exit_code'] == 0
assert not cap['timed_out'] and cap['frozen_files_unchanged']
assert cap['helper_freeze_sha256'] == '614a81f3ae1ff1d4b7b3c85c590cd89c6ed94cd70fad02358d0796eb79b65d95'

result = OUT/'saved-review.json'
actual = OUT/'saved-reader-actual.json'
stdout = OUT/'saved-reader.stdout.log'
stderr = OUT/'saved-reader.stderr.log'
assert all(not p.exists() for p in [result, actual, stdout, stderr])
argv = ['python3', '-B', str(PACKET/'review_saved.py'), '--packet', str(PACKET),
        '--basis-repo', str(ROOT), '--repo', str(ROOT), '--output', str(result)]
started = datetime.datetime.now(datetime.timezone.utc).isoformat()
clock = time.monotonic()
timed_out = False
error = None
proc = None
try:
    with stdout.open('xb') as so, stderr.open('xb') as se:
        proc = subprocess.Popen(argv, cwd=ROOT, stdout=so, stderr=se,
                                start_new_session=True)
        try:
            code = proc.wait(timeout=240)
        except subprocess.TimeoutExpired:
            timed_out = True
            os.killpg(proc.pid, signal.SIGKILL)
            code = proc.wait()
        except BaseException:
            if proc.poll() is None:
                os.killpg(proc.pid, signal.SIGKILL)
            proc.wait()
            raise
except BaseException as exc:
    error = repr(exc)
    code = None if proc is None else proc.returncode
after = snapshot(pin['files'])
ok = code == 0 and not timed_out and error is None and before == after
record = {
    'status': 'PASS_INDEPENDENT_SAVED_READER' if ok else 'FAIL_INDEPENDENT_SAVED_READER',
    'argv': argv, 'cwd': str(ROOT), 'started_utc': started,
    'seconds': time.monotonic()-clock, 'timeout_seconds': 240,
    'exit_code': code, 'timed_out': timed_out, 'exception': error,
    'core_pin_map': str(PINS), 'core_pin_map_sha256': PINS_SHA,
    'successful_capture_sha256': CAPTURE_SHA,
    'core_before': before, 'core_after': after,
    'core_unchanged': before == after,
    'stdout': str(stdout), 'stdout_sha256': digest(stdout),
    'stderr': str(stderr), 'stderr_sha256': digest(stderr),
    'saved_review': str(result),
    'saved_review_sha256': digest(result) if result.exists() else None,
    'wrapper_sha256': digest(__file__),
    'scope': 'One copied frozen saved-reader --repo invocation; no collector, compiler or producer.'}
with actual.open('x') as f:
    json.dump(record, f, indent=2)
    f.write('\n')
print(json.dumps(record, indent=2))
assert ok
assert json.loads(result.read_text())['status'] == 'PASS_SAVED_PHASE15'
