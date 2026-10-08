"""Diagnose the unchanged large-stdin communicate retry failure; no patching."""
from hashlib import sha256
import inspect
import json
from pathlib import Path
import subprocess
import sys
from time import monotonic

ROOT = Path('/workspace/scratch/010ae78c8df6')
REPO = ROOT/'ProveIt'
BASELINE = ROOT/'research/baseline'
COMMIT = '8a95834940cf77cdab1b39571ffc102ca8b6bede'
QA = ROOT/'research/qa'
files = ('Topology/UnknotRecognition/fast/fastunknot/normal_surface.py',
         'Topology/UnknotRecognition/fast/tests/test_normal_surface.py')
provenance = {}
for relative in files:
    pinned = subprocess.check_output(['git', 'show', COMMIT+':'+relative], cwd=REPO)
    current, baseline = (REPO/relative).read_bytes(), (BASELINE/relative).read_bytes()
    provenance[relative] = dict(current_sha256=sha256(current).hexdigest(),
        baseline_sha256=sha256(baseline).hexdigest(), pinned_sha256=sha256(pinned).hexdigest(),
        current_equals_pinned=current == pinned, baseline_equals_pinned=baseline == pinned)
    assert current == baseline == pinned

command = [sys.executable, '-B', '-c',
    'import sys,time;time.sleep(.12);data=sys.stdin.read();sys.stdout.write(data);sys.stderr.write("note")']
payload = 'x'*500000
records = []
start = monotonic()
child = subprocess.Popen(command, stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                         stderr=subprocess.PIPE, text=True)
try:
    try:
        import fcntl
        pipe_capacity = fcntl.fcntl(child.stdin, fcntl.F_GETPIPE_SZ)
    except (ImportError, AttributeError, OSError):
        pipe_capacity = None
    pending = payload
    for attempt in range(6):
        try:
            out, err = child.communicate(pending, timeout=.05)
            records.append(dict(attempt=attempt, elapsed=monotonic()-start,
                status='COMPLETE', output_bytes=len(out), error_bytes=len(err)))
            break
        except subprocess.TimeoutExpired:
            records.append(dict(attempt=attempt, elapsed=monotonic()-start,
                status='TIMEOUT', input_argument_is_none=pending is None,
                saved_input_bytes=len(child._input), input_offset=child._input_offset,
                stdin_closed=child.stdin.closed, process_status=child.poll()))
            pending = None
finally:
    if child.poll() is None:
        child.kill()
    child.wait()
    for stream in (child.stdin, child.stdout, child.stderr):
        stream.close()

start = monotonic()
single = subprocess.run(command, input=payload, capture_output=True, text=True, timeout=3)
control = dict(seconds=monotonic()-start, returncode=single.returncode,
               output_bytes=len(single.stdout), output_matches=single.stdout == payload,
               stderr=single.stderr)
assert control['returncode'] == 0 and control['output_matches'] and control['stderr'] == 'note'
source = inspect.getsource(subprocess.Popen._communicate)
(QA/'subprocess_communicate_runtime.txt').write_text(source)
result = dict(python=sys.version, executable=sys.executable, baseline_commit=COMMIT,
    source_provenance=provenance, payload_bytes=len(payload), pipe_capacity=pipe_capacity,
    retry_records=records, single_communicate_control=control,
    runtime_registers_stdin_only_for_truthy_current_input='if self.stdin and input:' in source,
    diagnosis='After the first timeout the wrapper passes input=None. This runtime then omits stdin '
      'from its selector although saved input remains unsent. The child waits for EOF; the parent '
      'eventually reaches its three-second deadline. The current and pinned baseline files are identical.')
(QA/'normal_surface_diagnosis.json').write_text(json.dumps(result, indent=2)+'\n')
print(json.dumps(result, indent=2))
