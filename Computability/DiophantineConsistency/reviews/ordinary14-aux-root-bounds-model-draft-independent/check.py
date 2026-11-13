#!/usr/bin/env python3
"""Independent model-source and bounded arithmetic checks; never runs Lean."""
from pathlib import Path
import hashlib
import json
import subprocess
import sys

D = Path(__file__).resolve().parents[2]
A = D / 'research/ordinary14-aux-root-bounds-model-draft'

def sha(data): return hashlib.sha256(data).hexdigest()
def pinned(path, expected):
    data = path.read_bytes()
    assert sha(data) == expected, str(path)
    return data

source = pinned(A / 'AuxRootBounds.lean', 'f7e198e882e31c67e915c0c7953f5a37c03e2c8c2ddb0a8c0043d2b8b71ca504').decode()
readme = (A / 'README.md').read_bytes()
tail = (b'\nIndependent source review is recorded in\n'
        b'`../../reviews/ordinary14-aux-root-bounds-model-draft-independent/`.\n')
assert readme.endswith(tail)
assert sha(readme[:-len(tail)]) == '7b895974745ae45a741fab3f67341e1012012f15080cc53377593b3988840b41'
pell = pinned(D / 'Lean/DiophantineConsistency/ArithmeticPellFirstNorm.lean',
              '374719597b3126504fc7b4daeb8ce08a7bae36c911ed37d8fee3d90ed324a5d5').decode()
ring = pinned(D / 'Lean/DiophantineConsistency/ModelDifferenceRing.lean',
              '5f8007e437fe309d0801bed075c03dc7ef5e7cba0138210aa1805e43a0869998').decode()
for text in ('theorem first_ordinate_large', '(hm : 0<m)', '(hk : 2<k)',
             'tsub_add_cancel_of_le (pos_iff_one_le.mp hm)', 'descent q tau k',
             'two_le_ordinate q u v', 'theorem strong_f_square_large',
             '(hDeltaSmall : Delta<c*c*c)', 'theorem strong_Q_gt_one',
             'theorem signed_square_gt_one', '(he : z+c=f*f*t)',
             'ModelDifferenceRing.one_le_of_pos'):
    assert text in source, text
assert 'theorem descent (q x k : V) (hk : 0<k)' in pell
assert 'theorem two_le_ordinate (q x k : V) (hk : 0<k)' in pell
assert 'theorem one_le_of_pos (hd : ∀ a : V, 0 < a → 1 ≤ a)' in ring

# Independent recurrence controls, including the indispensable k=2 case.
pell_controls = 0
for m in range(1, 31):
    tau, k = 1, 0
    for index in range(1, 7):
        tau, k = ((2*m+1)*tau + 2*m*(m+1)*k,
                  2*tau + (2*m+1)*k)
        assert tau*tau == 1+m*(m+1)*k*k
        if index == 1:
            assert k == 2 and k < 8*m+4
        else:
            assert k >= 8*m+4
        pell_controls += 1

strong_controls = 0
for c in range(2, 10):
    for delta in range(1, c**3):
        for i in range(1, 4):
            for f in range(1, 41):
                if (i*c*c)**2 + delta != delta*f*f: continue
                assert f*f > c+1 and (i*c*c)**2 > 1
                strong_controls += 1
gap_controls = 0
for c in range(2, 20):
    for f in range(1, 20):
        if f*f <= c+1: continue
        for t in range(-5, 6):
            z = f*f*t-c
            assert z*z > 1
            gap_controls += 1
assert pell_controls == 180 and strong_controls > 0 and gap_controls > 0

run = subprocess.run([sys.executable, '-I', '-S', '-B', str(A / 'check_source.py')], cwd=D,
                     stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=30, check=True)
assert not run.stderr and run.stdout == (A / 'observation.json').read_bytes()
print(json.dumps({'scope': 'source and finite controls only; no Lean or model theorem',
                  'author_readme_prelink_sha256': sha(readme[:-len(tail)]),
                  'pell_recurrence_controls': pell_controls, 'strong_controls': strong_controls,
                  'signed_gap_controls': gap_controls, 'k_eq_two_boundary': True},
                 sort_keys=True, indent=2))
