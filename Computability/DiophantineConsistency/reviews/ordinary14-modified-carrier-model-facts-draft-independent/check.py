#!/usr/bin/env python3
"""Source/finite review only; never runs Lean."""
import hashlib
import json
from pathlib import Path
import subprocess
import sys

D = Path(__file__).resolve().parents[2]
A = D / 'research/ordinary14-modified-carrier-model-facts-draft'
def sha(data):
    return hashlib.sha256(data).hexdigest()
def pin(path, expected):
    data = path.read_bytes()
    assert sha(data) == expected, str(path)
    return data

source = pin(A/'ModifiedCarrierFacts.lean', 'd16c6dca1f5bb5240db5e2b72d6d1895568c9e178c933a68e92f82b6be2be43e').decode()
pin(A/'check_source.py', 'd8db2e175056297dff690e61a277b070bff51620efaa747a7082077a25e11959')
receipt = pin(A/'observation.json', '36f69bcf9535a3e40c795ce611bb701e27a3d9504b72d8a6108a08ec88149919')
readme = (A/'README.md').read_bytes()
tail = (b'\nIndependent source review is recorded in\n'
        b'`../../reviews/ordinary14-modified-carrier-model-facts-draft-independent/`.\n')
assert readme.endswith(tail)
assert sha(readme[:-len(tail)]) == '72f4705f7583692a4217bc9f270ac5d2399c71fd469c4f2c00924796602ff68a'
L = D/'Lean/DiophantineConsistency'
for name, digest in {
    'ArithmeticAdaptiveMainOrientation2011.lean':'ad8a0d17ccf06c2f75ce8b095698b66f79869041ae07cf9ff0a376894b4c3968',
    'ArithmeticAdaptiveFactorThree2011.lean':'7679b8e5b0adb93464ca4489c1e24b288718830470764e2c4058c4cd736a64ce',
    'ArithmeticAdaptiveMersenne2011.lean':'c8a132e1b28bd1cf1ed76d80e953d5568ff0c77f566ad7b2b66715c8be9641ef',
    'Compact44/P72Power.lean':'f46584fb3977ae5fc33b31bee18e8c27435d97bea10138f163af2de5ee66d462',
    'Compact44/CompactFixedBeta.lean':'bcb892e7ae6b0d3cf329a248ca6b468e36a9a1b582d75cacafb7fd49f89025ea',
}.items():
    pin(L/name, digest)
for fragment in ('main_parts_positive U X Y k eta gamma (0:V) R hU hY hk',
                 'cancel_factor_three q Y X _ hq hY',
                 'mul_left_cancel₀ (ne_of_gt hU) (add_right_cancel hbal)',
                 'P72Power.power_of_mod X Y k R H d c a n m eta zeta',
                 'cancel_three t R q J ht hq hdiv',
                 'CompactFixedBeta.beta_identity (V:=V)'):
    assert fragment in source, fragment
run = subprocess.run([sys.executable, '-I', '-S', '-B', str(A/'check_source.py')],
                     cwd=D, stdout=subprocess.PIPE, stderr=subprocess.PIPE, check=True, timeout=120)
assert not run.stderr and run.stdout == receipt

orientation = 0
for U in range(1, 4):
    for X in range(5):
        for Y in range(8, 13):
            for k in range(1, 5):
                for eta in range(3):
                    for gamma in range(3):
                        a = X*Y+Y; c = eta+Y*k; H = 3+4*a
                        assert H*k < U*(X+a*c)+H*U*gamma
                        orientation += 1

balances = 0
gamma_below = gamma_above = 0
for q in (1, 2, 3, 4, 6):
    for X in range(4):
        for s in (1, 2):
            Y = q**3*s; U = q**5*s; H = 3+4*Y*(X+1)
            for R in range(4):
                for W in range(4):
                    for gamma in range(4):
                        # Solve d+H*W=A+H*gamma with nonnegative A,d.
                        d = H*gamma+2; A = H*W+2
                        k = R+1+U*W
                        assert U*d+H*k == U*A+H*(U*gamma+R+1)
                        assert (R+1-k) % q**4 == 0
                        assert d % H == A % H
                        gamma_below += gamma < W
                        gamma_above += gamma > W
                        balances += 1
assert gamma_below and gamma_above
q=3; Y=q**3; H=3+4*Y*2
assert H%3 == 0 and H%9 != 0
assert 3*(2**7) % 3 == 0 and 2**7 % 3 != 0
mersenne_cases = 0
for t in range(4, 9):
    for J in range(10):
        q = (2**t-1)*J+1
        for R in range(21):
            if (3*2**R) % q == 0:
                assert 2**R % q == 0
                mersenne_cases += 1
print(json.dumps({'scope':'source and finite review only; no Lean',
                  'author_readme_prelink_sha256':sha(readme[:-len(tail)]),
                  'orientation_cases':orientation,'balanced_cases':balances,
                  'gamma_below_W':gamma_below,'gamma_above_W':gamma_above,
                  'mersenne_cases':mersenne_cases,'factor_three_boundary':True},
                 sort_keys=True, indent=2))
