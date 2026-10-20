from pathlib import Path
import argparse
import hashlib
import json
import subprocess
import time

HERE = Path(__file__).resolve().parent
ap = argparse.ArgumentParser(description='Run one bounded C++ pass in a prepared directory; cost directory must be fresh.')
ap.add_argument('--work', type=Path, required=True)
ap.add_argument('--binary', type=Path, required=True)
ap.add_argument('--cost', type=int, choices=(4, 5), required=True)
a = ap.parse_args()
P = a.work.resolve()
binary = a.binary.resolve()
assert P.is_dir() and binary.is_file()
out = P / f'cost{a.cost}'
out.mkdir(exist_ok=False)
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
paths = [binary, HERE / 'search.cpp', HERE / 'library.py'] + [P / name for name in ('atoms.in', 'atoms.json', 'library-review.json')]
inputs = {str(path): sha(path) for path in paths}
command = ['timeout', '110s', str(binary), str(P / 'atoms.in'), str(out / 'nodes'), str(a.cost)]
started = time.monotonic()
with (out / 'stdout.log').open('w') as log:
    result = subprocess.run(command, stdout=log, stderr=subprocess.STDOUT)
elapsed = time.monotonic() - started
assert all(sha(Path(name)) == h for name, h in inputs.items())
text = (out / 'stdout.log').read_text()
record = {'status': 'COMPLETE' if result.returncode == 0 and text.rstrip().splitlines()[-1].startswith('DONE ') else 'BOUNDED_INCOMPLETE',
          'command': command, 'exit_code': result.returncode, 'seconds': elapsed,
          'inputs': inputs, 'nodes_sha256': sha(out / 'nodes'), 'log_sha256': sha(out / 'stdout.log'),
          'last_log_line': text.rstrip().splitlines()[-1] if text.strip() else None,
          'limits': {'process_seconds': 110, 'internal_seconds': 109, 'stored_nodes': 800000,
                     'signature_grid': [0, 9], 'root_goal_grid': [0, 4], 'root_cost': a.cost,
                     'max_intermediate_cost': a.cost - 1},
          'scope': 'Finite signature discovery with one representative per intermediate signature. No completeness, all-natural proof, source calibration or binary-state claim.'}
(out / 'execution.json').write_text(json.dumps(record, indent=2) + '\n')
print(json.dumps(record, indent=2))
