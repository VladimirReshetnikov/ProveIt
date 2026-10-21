#!/usr/bin/env python3
"""Regenerate the compact direct proof on a disposable copy; no Lean invocation."""
from pathlib import Path
import argparse
import hashlib
import json
import subprocess
import sys
import time

HERE = Path(__file__).resolve().parent
REL = Path('Computability/BusyBeaver/Research/ZFC/k225-formal')
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--out', type=Path, required=True)
args = parser.parse_args()
repo = next(p for p in HERE.parents if (p / REL / 'generate_domrho8_lean.py').is_file())
base = repo / REL
expected = json.loads((HERE / 'summary.json').read_text())
inputs = {
    'generator': base / 'generate_domrho8_lean.py',
    'certificate': base / 'lean217/dominated_rho8_full_certificate.json',
    'source': repo / 'Computability/BusyBeaver/Lean/BusyBeaver/ZFC/DomRho8.lean',
}
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
pins = {name: sha(path) for name, path in inputs.items()}
for name, key in [('generator', 'generator_sha256'), ('certificate', 'original_certificate_sha256'),
                  ('source', 'source_sha256')]:
    if pins[name] != expected[key]:
        raise RuntimeError(f'Changed reviewed {name}')
out = args.out.resolve()
out.mkdir(parents=True, exist_ok=True)
if any(out.iterdir()):
    raise RuntimeError('Output directory must be empty')
for name, path in inputs.items():
    (out / path.name).write_bytes(path.read_bytes())
command = [sys.executable, '-B', str(out / inputs['generator'].name),
           str(out / inputs['certificate'].name), str(out / 'regenerated.lean')]
start = time.monotonic()
with (out / 'stdout.log').open('wb') as stdout, (out / 'stderr.log').open('wb') as stderr:
    child = subprocess.run(command, stdout=stdout, stderr=stderr, timeout=60, check=False)
result = {'command': command, 'input_sha256': pins, 'exit_code': child.returncode,
          'seconds': time.monotonic() - start, 'scope': 'Generator reproduction only; no compiler.'}
result['inputs_unchanged'] = all(sha(path) == pins[name] for name, path in inputs.items())
result['exact_source'] = (out / 'regenerated.lean').is_file() and (out / 'regenerated.lean').read_bytes() == inputs['source'].read_bytes()
result['status'] = 'PASS' if child.returncode == 0 and result['inputs_unchanged'] and result['exact_source'] else 'FAIL'
(out / 'result.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps(result, indent=2))
sys.exit(0 if result['status'] == 'PASS' else 1)
