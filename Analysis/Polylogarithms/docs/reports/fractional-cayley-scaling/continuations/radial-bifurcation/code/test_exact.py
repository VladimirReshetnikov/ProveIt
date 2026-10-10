"""Standard-library regression tests for the interval and Taylor-jet kernels.

These test implementation properties; they do not replace the written
inclusion proof or the analytic proofs in the article.
"""
from __future__ import annotations
from fractions import Fraction as F
from pathlib import Path
import json
import random
from exact import I, J, SCALE, exp_nonnegative, log_integer
from taylor import T, INDEX

ROOT = Path(__file__).resolve().parents[1]

def contains(x: I, y: F) -> bool:
    return F(x.lo, SCALE) <= y <= F(x.hi, SCALE)

def main() -> None:
    if not __debug__:
        raise RuntimeError('Do not run verifiers with python -O')
    rng = random.Random(20261010)
    for _ in range(1200):
        vals = [F(rng.randint(-200, 200), rng.randint(1, 101)) for j in range(4)]
        a, b = sorted(vals[:2]); c, d = sorted(vals[2:])
        x, y = I.bounds(a, b), I.bounds(c, d)
        assert contains(x, a) and contains(x, b)
        assert contains(x+y, a+c) and contains(x+y, b+d)
        assert contains(x-y, a-d) and contains(x-y, b-c)
        for v in (a*c, a*d, b*c, b*d):
            assert contains(x*y, v)
        for n in range(6):
            assert contains(x**n, a**n) and contains(x**n, b**n)
            if a <= 0 <= b:
                assert contains(x**n, F(1) if n == 0 else F(0))
        if not a <= 0 <= b:
            assert contains(x.reciprocal(), 1/a)
            assert contains(x.reciprocal(), 1/b)
    # Exact values at zero and multiplicative logarithm identities.
    assert contains(exp_nonnegative(I.point(0)), F(1))
    assert contains(log_integer(1), F(0))
    for n in (2,3,4,5):
        x, y = log_integer(n*n), 2*log_integer(n)
        assert max(x.lo,y.lo) <= min(x.hi,y.hi)
    # Truncated reciprocal identities for independently specified polynomials.
    values = [I.point(F(j+1, j+3)) for j in range(10)]
    values[0] = I.point(2)
    x = T(values); product = x*x.reciprocal()
    assert contains(product.v,F(1))
    assert all(contains(v,F(0)) for v in product.c[1:])
    j = J(*[I.point(F(k+2,k+5)) for k in range(6)])
    product2=j*j.reciprocal()
    assert contains(product2.v,F(1))
    assert all(contains(v,F(0)) for v in product2.tuple()[1:])
    result={'status':'PASS','rational_interval_trials':1200,
            'random_seed':20261010,'jet_reciprocal_identity':True,
            'scope':'implementation regression tests, not a substitute for analytic proofs'}
    (ROOT/'certificates/kernel_tests.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__':
    main()
