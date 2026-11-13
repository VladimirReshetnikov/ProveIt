#!/usr/bin/env python3
"""Independent source composition and exact integer witness; no Lean."""
from pathlib import Path
import hashlib
import json
import subprocess
import sys

D = Path(__file__).resolve().parents[2]
A = D / 'research/ordinary14-aux-norms-to-bounds-draft'

def sha(data): return hashlib.sha256(data).hexdigest()
def pinned(path, expected):
    data = path.read_bytes()
    assert sha(data) == expected, str(path)
    return data

source = pinned(A / 'NormsToBounds.lean', 'c93161930052792db7b9ebb08f04f897e70d70fa84d390926521b7b4e28a70f8').decode()
readme = (A / 'README.md').read_bytes()
tail = (b'\nIndependent source review is recorded in\n'
        b'`../../reviews/ordinary14-aux-norms-to-bounds-draft-independent/`.\n')
assert readme.endswith(tail)
assert sha(readme[:-len(tail)]) == '010ae67243f4a1c15954a662bc138df2802b424be38d4afe3b41bed7ee6a701e'
paths = {
    'research/ordinary14-model-main-square-gap-draft/MainSquareGap.lean': '6639167627e5cf01814d1ae48f3975d42a72a6451863b31c9795b427ec6c5e68',
    'research/ordinary14-aux-root-bounds-model-draft/AuxRootBounds.lean': 'f7e198e882e31c67e915c0c7953f5a37c03e2c8c2ddb0a8c0043d2b8b71ca504',
    'research/ordinary14-aux-geometry-model-draft/AuxGeometry.lean': '88de9d4d0e92e43ca9483dcb90ae96a7e16284e69b8384cd41c9e16a7ad87b77',
}
parts = {name: pinned(D / name, value).decode() for name, value in paths.items()}
for text in ('theorem aux_bounds_of_natural_norms', '(hX : 0<X)', '(hY : 0<Y)',
             '(heta : 0<eta)', '(hzeta : 0<zeta)', '(hi : 0<i)', '(hcdef :',
             '(hDelta :', '(hfirst :', '(hmain :', '(hstrong :',
             '(hQ : Q=(ι i*ι c*ι c)*(ι i*ι c*ι c))',
             '(hz : z+ι c=(ι f*ι f)*t)', ': 1<Q ∧ 1<z*z',
             'two_ordinate_impossible', 'first_ordinate_large', 'geometry_of_large_k',
             'strong_f_square_large', 'strong_Q_gt_one', 'signed_square_gt_one'):
    assert text in source, text
assert 'theorem two_ordinate_impossible' in parts['research/ordinary14-model-main-square-gap-draft/MainSquareGap.lean']
for name in ('first_ordinate_large', 'strong_f_square_large', 'strong_Q_gt_one', 'signed_square_gt_one'):
    assert 'theorem ' + name in parts['research/ordinary14-aux-root-bounds-model-draft/AuxRootBounds.lean']
assert 'theorem geometry_of_large_k' in parts['research/ordinary14-aux-geometry-model-draft/AuxGeometry.lean']

# One exact nonvacuous instance: first Pell index 3 and main index 4.
X, Y, eta, zeta, tau, d, delta, c = 1, 1, 88, 320, 577, 1921, 15, 496
k = eta+zeta
m = X*Y*Y
assert min(X,Y,eta,zeta) > 0 and c == eta+Y*k
assert (X*Y+Y+2)**2 == delta+1
assert tau*tau == 1+m*(m+1)*k*k
assert d*d == 1+delta*c*c
assert k > 2 and k >= 8*m+4 and 0 < delta < c**3

def mul_pair(left, right):
    a,b = left
    c0,d0 = right
    return a*c0 + delta*b*d0, a*d0+b*c0
unit, base, exponent = (1,0), (d,c), c
while exponent:
    if exponent % 2: unit = mul_pair(unit,base)
    base = mul_pair(base,base)
    exponent //= 2
f, ell = unit
assert f*f - delta*ell*ell == 1 and ell % (c*c) == 0
i = delta*ell//(c*c)
assert i > 0 and (i*c*c)**2 + delta == delta*f*f
Q = (i*c*c)**2
z, t = -c, 0
assert z+c == f*f*t and Q > 1 and z*z > 1 and f*f > c+1

def replay(path, receipt):
    run = subprocess.run([sys.executable, '-I', '-S', '-B', str(path)], cwd=D,
                         stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=30, check=True)
    assert not run.stderr and run.stdout == receipt.read_bytes()

replay(A / 'check_source.py', A / 'observation.json')
for name in ('ordinary14-model-main-square-gap-draft-independent',
             'ordinary14-aux-root-bounds-model-draft-independent',
             'ordinary14-aux-geometry-model-draft-independent'):
    p = D / 'reviews' / name
    replay(p / 'check.py', p / 'result.json')
print(json.dumps({'scope': 'source and exact finite witness only; no Lean or model theorem',
                  'author_readme_prelink_sha256': sha(readme[:-len(tail)]),
                  'component_reviews_replayed': 3, 'exact_nonvacuous_instance': True,
                  'first_ordinate': k, 'main_ordinate': c, 'strong_witness_positive': i > 0},
                 sort_keys=True, indent=2))
