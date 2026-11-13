#!/usr/bin/env python3
"""Independent source and finite norm controls; no Lean invocation."""
from pathlib import Path
import hashlib
import json
import subprocess
import sys

D = Path(__file__).resolve().parents[2]
A = D / 'research/ordinary14-aux-root-model-draft'
R = D / 'reviews/ordinary14-direct-first-root-model-draft-independent'

def sha(data): return hashlib.sha256(data).hexdigest()
def pinned(path, expected):
    data = path.read_bytes()
    assert sha(data) == expected, str(path)
    return data

source = pinned(A / 'AuxRootBridge.lean', '796819c48d53665e1ee9c90d8d1bfd0fbd00cd4ca5535fe4fad1a3462d74c8b7').decode()
readme = (A / 'README.md').read_bytes()
tail = (b'\nIndependent source review is recorded in\n'
        b'`../../reviews/ordinary14-aux-root-model-draft-independent/`.\n')
assert readme.endswith(tail)
assert sha(readme[:-len(tail)]) == '78b064480dc739362ecebd90e62f654bae695dcc971121390e19aaa9602b83b6'
first = pinned(D / 'research/ordinary14-direct-first-root-model-draft/FirstRootBridge.lean',
               '92ace01321c77730c81eba032d1fdd86778e53399a073258cdbd49f7a621718f').decode()
ring = pinned(D / 'Lean/DiophantineConsistency/ModelDifferenceRing.lean',
              '5f8007e437fe309d0801bed075c03dc7ef5e7cba0138210aa1805e43a0869998').decode()
for text in ('theorem oldAux_eq_direct', 'theorem square_gt_of_aux',
             'theorem positive_of_above', 'theorem above_of_positive',
             'theorem positive_aux_coordinate_iff', '(hQ : 1<Q)',
             '(hz : 1<z*z)', '(nonneg_iff).mp', '(ι_lt_ι',
             'fiveSquares first main (oldAux z Q u) strong guard=0',
             'fiveSquares first main (directAux z Q (ι y)) strong guard=0'):
    assert text in source, text
assert 'theorem fiveSquares_eq_zero_iff' in first
assert 'theorem nonneg_iff {x : DiffRing V} : 0 ≤ x ↔ ∃ a, x = ι a' in ring
assert 'theorem ι_lt_ι {a b : V} : ι a < ι b ↔ a < b' in ring

# Exact old-auxiliary equality in Z[z,Q,u].
def const(n): return {(): n} if n else {}
def var(name): return {(name,): 1}
def add(a, b, sign=1):
    out = dict(a)
    for key, val in b.items(): out[key] = out.get(key, 0) + sign*val
    return {key: val for key, val in out.items() if val}
def mul(a, b):
    out = {}
    for ka, va in a.items():
        for kb, vb in b.items():
            key = tuple(sorted(ka + kb))
            out[key] = out.get(key, 0) + va*vb
    return {key: val for key, val in out.items() if val}
z, q, u = map(var, ('z', 'Q', 'u'))
y = add(z, u)
old = add(add(mul(y,y), mul(q, mul(u, add(y,z))), -1), const(1), -1)
direct = add(add(mul(y,y), mul(q, add(mul(y,y),mul(z,z),-1)), -1), const(1), -1)
assert old == direct

cases = 0
old_maps = 0
new_maps = 0
for Q in range(2, 14):
    for z in range(-35, 36):
        if z*z <= 1: continue
        for y in range(-75, 76):
            if y*y-Q*(y*y-z*z) != 1: continue
            assert y*y > z*z
            if y > z:
                assert y > 0 and y-z > 0
                old_maps += 1
            if y > 0:
                assert y > z and y-z > 0
                new_maps += 1
            cases += 1
assert cases > 0 and old_maps > 0 and new_maps > 0
assert 1-4*(1-1) == 1 and not 1 > 1
assert 1-0*(1-4) == 1 and not 1 > 4

def replay(path, receipt):
    run = subprocess.run([sys.executable, '-I', '-S', '-B', str(path)], cwd=D,
                         stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=30, check=True)
    assert not run.stderr and run.stdout == receipt.read_bytes()

replay(A / 'check_source.py', A / 'observation.json')
replay(R / 'check.py', R / 'result.json')
print(json.dumps({'scope': 'source and finite controls only; no Lean or model theorem',
                  'author_readme_prelink_sha256': sha(readme[:-len(tail)]),
                  'exact_auxiliary_identity': True, 'finite_norm_cases': cases,
                  'positive_old_maps': old_maps, 'positive_new_maps': new_maps,
                  'boundary_counterexamples': 2, 'generic_root_review_replayed': True},
                 sort_keys=True, indent=2))
