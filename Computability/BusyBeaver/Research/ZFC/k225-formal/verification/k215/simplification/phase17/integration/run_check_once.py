"""Run one frozen owned metadata preflight or proof check, preserving raw outer results."""
import argparse
import hashlib
import json
import subprocess
import time
from pathlib import Path

parser = argparse.ArgumentParser()
parser.add_argument('mode', choices=['preflight', 'build'])
args = parser.parse_args()
check = Path('/tmp/k215-phase17-check')
freeze = json.loads((check / 'freeze.json').read_bytes())
sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
for name, pin in freeze['files'].items():
    assert sha(check / name) == pin, name
out = check / (args.mode + '-run1')
assert not out.exists()
stdout = check / (args.mode + '.stdout')
stderr = check / (args.mode + '.stderr')
outer = check / (args.mode + '-outer.json')
assert not any(p.exists() for p in [stdout, stderr, outer])
command = ['python3', '-B', str(check / 'build.py'), '--map', str(check / 'plan.json'),
           '--out', str(out)]
if args.mode == 'preflight':
    command += ['--check-plan']
started = time.monotonic()
with stdout.open('wb') as output, stderr.open('wb') as errors:
    result = subprocess.run(command, stdout=output, stderr=errors)
record = {'status': 'PASS_EXIT_ZERO' if result.returncode == 0 else 'FAIL',
          'exit_code': result.returncode, 'argv': command,
          'seconds': time.monotonic() - started,
          'stdout_sha256': sha(stdout), 'stderr_sha256': sha(stderr),
          'freeze_sha256': sha(check / 'freeze.json')}
outer.write_text(json.dumps(record, indent=2) + '\n')
print(json.dumps(record))
raise SystemExit(result.returncode)
