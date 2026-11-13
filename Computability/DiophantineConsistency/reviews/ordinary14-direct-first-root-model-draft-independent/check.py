#!/usr/bin/env python3
"""Independent source/finite review; never invokes Lean or mutates evidence."""
from pathlib import Path
import hashlib
import itertools
import json
import subprocess
import sys

D = Path(__file__).resolve().parents[2]
A = D / 'research/ordinary14-direct-first-root-model-draft'

def sha(data):
    return hashlib.sha256(data).hexdigest()

def pinned(path, digest):
    data = path.read_bytes()
    assert sha(data) == digest, (str(path), sha(data))
    return data

source = pinned(A / 'FirstRootBridge.lean',
                '92ace01321c77730c81eba032d1fdd86778e53399a073258cdbd49f7a621718f').decode()
readme = (A / 'README.md').read_bytes()
tail = (b'\nIndependent source review is recorded in\n'
        b'`../../reviews/ordinary14-direct-first-root-model-draft-independent/`.\n')
assert readme.endswith(tail)
assert sha(readme[:-len(tail)]) == 'baef3e15e32a4b04d6385017924aae49d8e962689ccfb7db538d1ee1a46a6c2d'

pell = pinned(D / 'Lean/DiophantineConsistency/Compact44/P72Root.lean',
              '066fce52d35ab720519ee8817d9b56c2eacc9ac4f6bb7bf6e92286a87f44d091').decode()
ring = pinned(D / 'Lean/DiophantineConsistency/ModelDifferenceRing.lean',
              '5f8007e437fe309d0801bed075c03dc7ef5e7cba0138210aa1805e43a0869998').decode()
squares = pinned(D / 'Lean/DiophantineConsistency/Compact44/FreeJSumSquares.lean',
                 '287c222484f372dfe1ca91d883692a145eadb00d78fe6ca80c92609f10422481').decode()
assert 'theorem ι_magnitude_sq (P N : V)' in pell
assert 'ι (magnitude (P, N)) * ι (magnitude (P, N)) = (ι P - ι N) * (ι P - ι N)' in pell
assert 'theorem ι_injective : Function.Injective (ι : V →+* DiffRing V)' in ring
assert 'instance : NoZeroDivisors (DiffRing V) where' in ring
assert 'private theorem three_squares_iff' in squares
for statement in ('theorem fiveSquares_eq_zero_iff', 'theorem root_of_scaled_residual',
                  'theorem scaled_residual_of_root', 'theorem positive_first_zero_iff'):
    assert statement in source
for required in ('(hM : 0<M)', '(hD : 0<D)', 'P72Root.ι_magnitude_sq',
                 'mul_eq_zero.mp h', 'magnitude (P,N)', '0<P+tau',
                 '(b c d e : DiffRing V)'):
    assert required in source

run = subprocess.run([sys.executable, '-I', '-S', '-B', str(A / 'check_source.py')],
                     cwd=D, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                     timeout=30, check=True)
assert not run.stderr and run.stdout == (A / 'observation.json').read_bytes()

five_cases = 0
for values in itertools.product(range(-2, 3), repeat=5):
    assert (sum(x*x for x in values) == 0) == all(x == 0 for x in values)
    five_cases += 1
root_cases = 0
for m, p, n, d in itertools.product(range(1, 6), range(6), range(1, 7), range(1, 20)):
    root = abs(p-n)
    assert (m*m*((p-n)**2-d) == 0) == (root*root == d)
    if root*root == d:
        assert root > 0
        old = p+root
        assert old > 0 and m*m*((p-old)**2-d) == 0
    root_cases += 1
assert 0*0*((2-1)**2-4) == 0 and abs(2-1)**2 != 4

print(json.dumps({'scope': 'source inspection and finite controls only; no Lean or graph theorem',
                  'author_source_sha256': sha(source.encode()),
                  'author_readme_prelink_sha256': sha(readme[:-len(tail)]),
                  'author_checker_sha256': sha((A / 'check_source.py').read_bytes()),
                  'five_square_cases': five_cases, 'root_cases': root_cases,
                  'zero_scale_counterexample': True}, sort_keys=True, indent=2))
