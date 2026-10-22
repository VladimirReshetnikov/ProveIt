#!/usr/bin/env python3
"""Replay the patched calculus producer and compare all five changed modules.

On an applied checkout, --repo alone supplies every source. An overlay and a
shared overlay may instead supply candidate changes above a read-only checkout.
Only unchanged production sources are taken from the fallback checkout.
"""
from pathlib import Path
import argparse
import hashlib
import importlib.util
import json
import shutil
import sys

p = argparse.ArgumentParser(description=__doc__)
p.add_argument('--repo', type=Path, required=True)
p.add_argument('--overlay', type=Path)
p.add_argument('--shared-overlay', type=Path)
p.add_argument('--out', type=Path, required=True)
a = p.parse_args()
repo = a.repo.resolve()
overlay = (a.overlay or a.repo).resolve()
shared = (a.shared_overlay or a.overlay or a.repo).resolve()
out = a.out.resolve()
if out.exists() and any(out.iterdir()):
    raise SystemExit('--out must be empty or absent')
out.mkdir(parents=True, exist_ok=True)
base = Path('Computability/BusyBeaver/Research/ZFC/k225-formal')
ext = base / 'rocq/rocq-extension'
sha = lambda b: hashlib.sha256(b).hexdigest()
inputs = []
def copy(source, dest):
    data = source.read_bytes()
    dest.parent.mkdir(parents=True, exist_ok=True)
    dest.write_bytes(data)
    inputs.append({'path': str(source), 'sha256': sha(data)})
for name in ('generate_domrho8_cd.py', 'derivation_core.txt'):
    copy(shared / base / 'rho8cd' / name, out / 'producer/rho8cd' / name)
copy(overlay / base / 'rho8cd/render_dominated_core_rocq.py',
     out / 'producer/rho8cd/render_dominated_core_rocq.py')
for name in ('DomRho8', 'EnumPerm', 'L1_SoundPerm', 'CandidateScheduler', 'L1_CompPerm', 'SeedPerm'):
    rel = base / 'rocqperm' / (name + '.v')
    source = overlay / rel if (overlay / rel).exists() else repo / rel
    copy(source, out / 'producer/rocqperm' / (name + '.v'))
regen = overlay / ext / 'regenerate215.py'
sys.path.insert(0, str(repo / ext))
spec = importlib.util.spec_from_file_location('candidate_regenerate215', regen)
m = importlib.util.module_from_spec(spec)
spec.loader.exec_module(m)
# The function itself is the patched production function. Its unchanged 217
# templates remain in the actual checkout; changed templates are overlaid.
m.KF = out / 'producer'
m.PERM_DIR = out / 'producer/rocqperm'
m.V217 = repo / ext / 'coq/217'
generated = out / 'generated'
generated.mkdir()
m.calculus_files(generated)
comparisons = []
for name in ('DominatedImplication', 'DomRho8', 'CandidateScheduler', 'L1_CompPerm', 'SeedPerm'):
    actual = (generated / (name + '.v')).read_bytes()
    expected = (overlay / ext / 'coq/215' / (name + '.v')).read_bytes()
    equal = actual == expected
    comparisons.append({'module': name, 'generated_sha256': sha(actual),
                        'candidate_sha256': sha(expected), 'byte_equal': equal})
receipt = {'producer_sha256': sha(regen.read_bytes()), 'inputs': inputs,
           'comparisons': comparisons, 'scope': 'calculus_files only; not full machine regeneration',
           'status': 'PASS' if all(c['byte_equal'] for c in comparisons) else 'FAIL'}
(out / 'receipt.json').write_text(json.dumps(receipt, indent=2) + '\n')
print(json.dumps(receipt, indent=2))
if receipt['status'] != 'PASS':
    raise SystemExit(1)
