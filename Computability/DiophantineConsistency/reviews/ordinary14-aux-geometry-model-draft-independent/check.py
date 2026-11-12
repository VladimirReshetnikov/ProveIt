#!/usr/bin/env python3
"""Independent model-source and finite controls; never invokes Lean."""
from pathlib import Path
import hashlib
import json
import subprocess
import sys

D = Path(__file__).resolve().parents[2]
A = D / 'research/ordinary14-aux-geometry-model-draft'
R = D / 'reviews/ordinary14-aux-root-bounds-model-draft-independent'

def sha(data): return hashlib.sha256(data).hexdigest()
def pinned(path, expected):
    data = path.read_bytes()
    assert sha(data) == expected, str(path)
    return data

source = pinned(A / 'AuxGeometry.lean', '88de9d4d0e92e43ca9483dcb90ae96a7e16284e69b8384cd41c9e16a7ad87b77').decode()
readme = (A / 'README.md').read_bytes()
tail = (b'\nIndependent source review is recorded in\n'
        b'`../../reviews/ordinary14-aux-geometry-model-draft-independent/`.\n')
assert readme.endswith(tail)
assert sha(readme[:-len(tail)]) == '7691d96b796a710bfb5a70c9964e025475986bbfce0bc04912a700b90ef837fc'
pell = pinned(D / 'Lean/DiophantineConsistency/ArithmeticPellFirstNorm.lean',
              '374719597b3126504fc7b4daeb8ce08a7bae36c911ed37d8fee3d90ed324a5d5').decode()
bounds = pinned(D / 'research/ordinary14-aux-root-bounds-model-draft/AuxRootBounds.lean',
                'f7e198e882e31c67e915c0c7953f5a37c03e2c8c2ddb0a8c0043d2b8b71ca504').decode()
gap = pinned(D / 'research/ordinary14-model-main-square-gap-draft/MainSquareGap.lean',
             '6639167627e5cf01814d1ae48f3975d42a72a6451863b31c9795b427ec6c5e68').decode()
for text in ('theorem geometry_of_large_k', '(hY : 0<Y)', '(heta : 0<eta)',
             '(hk : 8*X*Y*Y+4≤k)',
             '(hDelta : (X*Y+Y+2)*(X*Y+Y+2)=Delta+1)',
             'A<c ∧ 1<c ∧ 0<Delta ∧ Delta<c*c*c',
             'have hXk : X+4≤k', 'have hAc : A<c', 'have hDeltaPos : 0<Delta'):
    assert text in source, text
assert 'theorem positive_parameter_solution' in pell
assert 'theorem first_ordinate_large' in bounds
assert 'theorem two_ordinate_impossible' in gap

# Exact central source identity in Z[X,Y]; inequalities use positivity separately.
def const(n): return {(): n} if n else {}
def var(name): return {(name,): 1}
def add(a, b):
    out = dict(a)
    for key, val in b.items(): out[key] = out.get(key, 0) + val
    return {key: val for key, val in out.items() if val}
def mul(a, b):
    out = {}
    for ka, va in a.items():
        for kb, vb in b.items():
            key = tuple(sorted(ka + kb))
            out[key] = out.get(key, 0) + va*vb
    return {key: val for key, val in out.items() if val}
x, y = var('X'), var('Y')
assert mul(y, add(x,const(4))) == add(add(mul(x,y),y),mul(const(3),y))

cases = 0
zero_x_cases = 0
for x0 in range(0, 15):
    for y0 in range(1, 16):
        for eta in range(1, 5):
            for extra in (0, 1, 2, 9):
                k = 8*x0*y0*y0+4+extra
                aa = x0*y0+y0+2
                cc = eta+y0*k
                delta = aa*aa-1
                assert x0 <= x0*y0*y0 and x0+4 <= k
                assert aa < y0*(x0+4) <= y0*k < cc
                assert aa >= 2 and 1 < cc and 0 < delta < aa*aa < cc*cc <= cc**3
                cases += 1
                zero_x_cases += x0 == 0
assert zero_x_cases > 0
assert 3*1+1+2 >= 1+1*1  # Large-k premise cannot simply be dropped.

def replay(path, receipt):
    run = subprocess.run([sys.executable, '-I', '-S', '-B', str(path)], cwd=D,
                         stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=30, check=True)
    assert not run.stderr and run.stdout == receipt.read_bytes()

replay(A / 'check_source.py', A / 'observation.json')
replay(R / 'check.py', R / 'result.json')
print(json.dumps({'scope': 'source and finite controls only; no Lean or model theorem',
                  'author_readme_prelink_sha256': sha(readme[:-len(tail)]),
                  'exact_central_identity': True, 'geometry_controls': cases,
                  'zero_x_controls': zero_x_cases, 'bounds_review_replayed': True},
                 sort_keys=True, indent=2))
