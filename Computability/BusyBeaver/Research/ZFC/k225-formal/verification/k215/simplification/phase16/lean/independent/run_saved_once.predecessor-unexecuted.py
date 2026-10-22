"""Run exactly one reviewed saved-metadata invocation on an isolated core copy."""
from pathlib import Path
import datetime
import hashlib
import json
import shutil
import subprocess
import time

HERE = Path('/tmp/k215-phase16-saved-peer')
SOURCE = Path('/tmp/k215-phase16-published/lean')
OWN = HERE / 'packet'
REPO = Path('/home/codex/.codex/worktrees/ec20/Proofs')
FREEZE = 'c2010688648b3c592044ed3226f7af3aa232b25d73489389f59c2a5e3578fbc9'
CORE = ['README.md', 'basis.py', 'basis-reference.json', 'packet.py',
        'review.py', 'controls.py', 'config.json', 'freeze.json',
        'result.json', 'index.json', 'execution.tar.gz']
digest = lambda data: hashlib.sha256(data).hexdigest()
dump = lambda value: (json.dumps(value, indent=2) + '\n').encode()

def manifest(directory):
    result = {}
    for name in CORE:
        path = directory / name
        assert path.is_file() and not path.is_symlink(), str(path)
        data = path.read_bytes()
        result[name] = {'sha256': digest(data), 'bytes': len(data)}
    return result

assert not OWN.exists()
assert not (HERE / 'saved.json').exists()
assert not (HERE / 'outer.json').exists()
source_before = manifest(SOURCE)
assert source_before['freeze.json']['sha256'] == FREEZE
OWN.mkdir()
copy_map = []
for name in CORE:
    shutil.copyfile(SOURCE / name, OWN / name)
    copy_map.append({'source': str(SOURCE / name), 'destination': str(OWN / name),
                     **source_before[name]})
own_before = manifest(OWN)
assert own_before == source_before
(HERE / 'copy-map.json').write_bytes(dump(copy_map))
(HERE / 'core-before.json').write_bytes(dump({'source': source_before, 'copy': own_before}))
freeze = json.loads((OWN / 'freeze.json').read_bytes())
for name, pin in freeze['files'].items():
    assert own_before[name]['sha256'] == pin
current_path = REPO / 'Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/simplification/phase16/integration/current-review.json'
current_before = digest(current_path.read_bytes())
argv = ['python3', '-B', str(OWN / 'review.py'), 'saved', '--packet', str(OWN),
        '--basis-repo', str(REPO), '--repo', str(REPO), '--output', str(HERE / 'saved.json')]
started = datetime.datetime.now(datetime.timezone.utc).isoformat()
start = time.monotonic()
with (HERE / 'saved.stdout').open('xb') as stdout, (HERE / 'saved.stderr').open('xb') as stderr:
    completed = subprocess.run(argv, cwd=REPO, stdout=stdout, stderr=stderr, check=False)
seconds = time.monotonic() - start
source_after = manifest(SOURCE)
own_after = manifest(OWN)
(HERE / 'core-after.json').write_bytes(dump({'source': source_after, 'copy': own_after}))
unchanged = source_before == source_after == own_before == own_after
current_after = digest(current_path.read_bytes())
receipt = json.loads((HERE / 'saved.json').read_bytes()) if (HERE / 'saved.json').exists() else None
outer = {'status': 'PASS_INDEPENDENT_SAVED_EXIT_ZERO' if completed.returncode == 0 and unchanged else 'FAIL_INDEPENDENT_SAVED',
         'argv': argv, 'cwd': str(REPO), 'started_utc': started, 'exit_code': completed.returncode,
         'timed_out': False, 'seconds': seconds, 'freeze_sha256': FREEZE,
         'core_file_count': len(CORE), 'core_files_unchanged': unchanged,
         'current_review_before_sha256': current_before,
         'current_review_after_sha256': current_after,
         'stdout': str(HERE / 'saved.stdout'), 'stderr': str(HERE / 'saved.stderr'),
         'stdout_sha256': digest((HERE / 'saved.stdout').read_bytes()),
         'stderr_sha256': digest((HERE / 'saved.stderr').read_bytes()),
         'receipt': str(HERE / 'saved.json'),
         'receipt_sha256': digest((HERE / 'saved.json').read_bytes()) if receipt else None,
         'saved_status': receipt['status'] if receipt else None,
         'current_sources_checked': receipt['current_sources_checked'] if receipt else None,
         'scope': 'Exactly one saved metadata reader; no capture, compiler, producer, Rocq, or controls executed.'}
(HERE / 'outer.json').write_bytes(dump(outer))
print(json.dumps(outer, indent=2))
assert completed.returncode == 0 and unchanged and current_before == current_after
assert receipt['status'] == 'PASS_SAVED_PHASE16' and receipt['current_sources_checked']
