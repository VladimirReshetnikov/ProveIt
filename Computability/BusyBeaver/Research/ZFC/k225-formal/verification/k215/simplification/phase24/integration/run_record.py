"""Owned launcher for explicit pinned Python validators and inert capture tools."""
from pathlib import Path
import argparse, hashlib, json, subprocess, time
parser = argparse.ArgumentParser()
parser.add_argument('job', type=Path)
parser.add_argument('job_sha256')
args = parser.parse_args()
sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
assert sha(args.job) == args.job_sha256
job = json.loads(args.job.read_text())
assert job['argv'][:2] == ['python3', '-B']
assert job['argv'][2] in job['pins']
for path, hashed in job['pins'].items(): assert sha(path) == hashed
prefix = args.job.absolute().with_suffix('')
stdout = Path(str(prefix) + '.stdout'); stderr = Path(str(prefix) + '.stderr')
outer = Path(str(prefix) + '-outer.json')
assert not any(p.exists() or p.is_symlink() for p in [stdout, stderr, outer])
started = time.monotonic()
with stdout.open('xb') as output, stderr.open('xb') as errors:
    result = subprocess.run(job['argv'], cwd=job['cwd'], stdout=output, stderr=errors)
receipt = {'status': 'PASS_EXIT_ZERO' if result.returncode == 0 else 'FAIL', 'exit_code': result.returncode,
           'seconds': time.monotonic() - started, 'argv': job['argv'], 'job_sha256': args.job_sha256,
           'launcher_sha256': sha(__file__), 'stdout_sha256': sha(stdout), 'stderr_sha256': sha(stderr)}
with outer.open('x') as stream: json.dump(receipt, stream, indent=2); stream.write('\n')
print(json.dumps(receipt), flush=True)
raise SystemExit(result.returncode)
