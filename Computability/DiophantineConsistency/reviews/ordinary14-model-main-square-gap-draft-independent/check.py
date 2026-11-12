#!/usr/bin/env python3
"""Independent source and exact gap controls; never invokes Lean."""
from pathlib import Path
import hashlib
import json
import math
import subprocess
import sys

D = Path(__file__).resolve().parents[2]
A = D / 'research/ordinary14-model-main-square-gap-draft'

def sha(data): return hashlib.sha256(data).hexdigest()
def pinned(path, expected):
    data = path.read_bytes()
    assert sha(data) == expected, str(path)
    return data

source = pinned(A / 'MainSquareGap.lean', '6639167627e5cf01814d1ae48f3975d42a72a6451863b31c9795b427ec6c5e68').decode()
readme = (A / 'README.md').read_bytes()
tail = (b'\nIndependent source review is recorded in\n'
        b'`../../reviews/ordinary14-model-main-square-gap-draft-independent/`.\n')
assert readme.endswith(tail)
assert sha(readme[:-len(tail)]) == '6bc414f088e86e7ad60e67dd0434c779008b9267e070d2e5334b1caee59ed0f2'
pell = pinned(D / 'Lean/DiophantineConsistency/Compact44/P72Root.lean',
              '066fce52d35ab720519ee8817d9b56c2eacc9ac4f6bb7bf6e92286a87f44d091').decode()
ring = pinned(D / 'Lean/DiophantineConsistency/ModelDifferenceRing.lean',
              '5f8007e437fe309d0801bed075c03dc7ef5e7cba0138210aa1805e43a0869998').decode()
for text in ('theorem no_main_square', '(hA : 0<A)', '(hc : 1<c)',
             '(hbound : c<2*A)', '(hDelta : A*A=Delta+1)',
             '(hnorm : d*d=1+Delta*c*c)', 'P72Root.ι_tsub hac',
             'lt_iff_succ_le.mp htd', 'theorem two_ordinate_impossible',
             '(hX : 0<X) (hY : 0<Y) (heta : 0<eta) (hzeta : 0<zeta)'):
    assert text in source, text
assert 'theorem ι_tsub {a b : V} (h : b ≤ a)' in pell
assert 'theorem ι_lt_ι {a b : V} : ι a < ι b ↔ a < b' in ring

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
a, c = map(var, ('A', 'c'))
n = mul(a,c)
norm = add(const(1), mul(add(mul(a,a),const(1),-1), mul(c,c)))
pred = add(n,const(1),-1)
assert add(norm, mul(pred,pred), -1) == mul(c, add(mul(const(2),a),c,-1))
assert add(mul(n,n), norm, -1) == add(mul(c,c),const(1),-1)

generic_cases = 0
for A0 in range(1, 65):
    for c0 in range(2, 2*A0):
        n0 = A0*c0
        z = 1+(A0*A0-1)*c0*c0
        assert z-(n0-1)**2 == c0*(2*A0-c0) > 0
        assert n0*n0-z == c0*c0-1 > 0
        assert math.isqrt(z)**2 != z
        generic_cases += 1
graph_cases = 0
for x in range(1, 20):
    for y in range(1, 20):
        A0, c0 = x*y+y+2, 1+2*y
        assert 1 < c0 < 2*A0
        z = 1+(A0*A0-1)*c0*c0
        assert math.isqrt(z)**2 != z
        graph_cases += 1
assert 1+(3*3-1)*1 == 3*3  # c=1 destroys the upper strict gap.
assert 2*5*(2*5-2*5) == 0  # c=2A destroys the lower strict gap.

run = subprocess.run([sys.executable, '-I', '-S', '-B', str(A / 'check_source.py')], cwd=D,
                     stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=30, check=True)
assert not run.stderr and run.stdout == (A / 'observation.json').read_bytes()
print(json.dumps({'scope': 'source and finite controls only; no Lean or model theorem',
                  'author_readme_prelink_sha256': sha(readme[:-len(tail)]),
                  'exact_gap_identities': True, 'generic_gap_controls': generic_cases,
                  'graph_specialization_controls': graph_cases, 'strict_boundary_controls': 2},
                 sort_keys=True, indent=2))
