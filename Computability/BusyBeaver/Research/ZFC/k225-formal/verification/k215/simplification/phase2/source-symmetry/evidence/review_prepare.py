"""Run the candidate preparation script only in an isolated, copied input tree."""
from pathlib import Path
import hashlib, json, shutil, subprocess, sys, time

BASE = Path('/tmp/k215-offset-symmetry')
REPO = Path('/home/codex/.codex/worktrees/ec20/Proofs')
REL = Path('Computability/BusyBeaver/Research/ZFC/k225-formal')
src = REPO / REL
candidate = BASE / 'candidate' / REL
out = BASE / 'prepare-regeneration'
out.mkdir(exist_ok=False)
dst = out / 'tree' / REL
dst.mkdir(parents=True)
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
names = ['generate_boot221_lean.py', 'generate_sites221_lean.py',
         'generate_dense219_lean.py', 'generate_tables_lean.py']
inputs = {}
for name in names:
    p = src / name
    inputs[str(p)] = sha(p)
    shutil.copyfile(p, dst / name)
for name in ['prepare_k215.py', 'generate_source215_lean.py']:
    p = candidate / name
    inputs[str(p)] = sha(p)
    shutil.copyfile(p, dst / name)
(dst.parent / 'candidate-k215').mkdir()
for name in ['k215.native.tm', 'canonicalization.json']:
    p = src.parent / 'candidate-k215' / name
    inputs[str(p)] = sha(p)
    shutil.copyfile(p, dst.parent / 'candidate-k215' / name)
argv = [sys.executable, str(dst / 'prepare_k215.py')]
start = time.monotonic()
run = subprocess.run(argv, capture_output=True, timeout=30)
(out / 'stdout.log').write_bytes(run.stdout)
(out / 'stderr.log').write_bytes(run.stderr)
assert run.returncode == 0, (run.returncode, run.stderr.decode())
outputs = {}
for name in ['generate_boot215_lean.py', 'generate_sites215_lean.py',
             'generate_dense215_lean.py', 'generate_tables_lean.py',
             'lean215/k215_k230labels.tm', 'lean215/labels.json']:
    actual, expected = dst / name, src / name
    assert actual.read_bytes() == expected.read_bytes(), name
    outputs[name] = {'sha256': sha(actual), 'matches_canonical': True}
assert (dst / 'generate_source215_lean.py').read_bytes() == (candidate / 'generate_source215_lean.py').read_bytes()
assert all(sha(Path(p)) == h for p, h in inputs.items())
record = {'status': 'PASS', 'argv': argv, 'exit_code': run.returncode,
          'seconds': time.monotonic() - start, 'inputs': inputs,
          'inputs_unchanged': True, 'outputs': outputs,
          'forward_only_source_generator_preserved': True,
          'scope': 'Disposable preparation only. Direct forward-only generation was separately checked; no Lean invocation.'}
(out / 'review.json').write_text(json.dumps(record, indent=2) + '\n')
print(json.dumps(record, indent=2))
