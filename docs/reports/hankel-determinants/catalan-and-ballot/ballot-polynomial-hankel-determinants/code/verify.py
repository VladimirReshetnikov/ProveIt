"""Deterministic exact tests. Run: python code/verify.py

No floating-point computations or third-party packages are used.
The tests supplement, and do not replace, the proof in the article.
"""
import json
import platform
import random
import time
from collections import Counter
from fractions import Fraction
from math import comb, factorial
from pathlib import Path

from hankel import (adjacent_ratio, admissible, coefficient, delta,
                    denominator, direct_hankel, leading_constant,
                    numerator, rho_coefficients, rho_coefficients_fast, sign_power)


def main() -> None:
    started = time.perf_counter()
    counts = Counter()

    def check(category, condition, context):
        if not condition:
            raise AssertionError(f"{category}: {context}")
        counts[category] += 1

    # Direct fraction-free determinants, independently from ballot moments.
    weights = [(0, 1), (1, 1), (2, 3), (-1, 2), (2, -1), (3, 0), (-2, -3)]
    for u, t in weights:
        for n in range(13):
            check("unshifted_determinants",
                  direct_hankel(0, n, t=t, u=u) == t**(n*(n-1)//2), (n,u,t))
            for k in range(1, 13):
                direct = direct_hankel(k, n, t=t, u=u)
                formula = t**(n*(n-1)//2) * delta(k, n, t=t, u=u)
                check("direct_grid_determinants", direct == formula, (k,n,u,t))
    rng = random.Random(211114492)
    for _ in range(200):
        k, n = rng.randint(1, 20), rng.randint(0, 18)
        u, t = rng.randint(-4, 4), rng.randint(-3, 4)
        check("direct_seeded_determinants",
              direct_hankel(k,n,t=t,u=u) == t**(n*(n-1)//2)*delta(k,n,t=t,u=u),
              (k,n,u,t))

    # Exact rational ratios and strict inequalities.
    for k in range(1, 25):
        for n in range(1, 61):
            b = [coefficient(k,n,a) for a in admissible(k,n)]
            check("fast_coefficient_algorithm",
                  rho_coefficients_fast(k,n) == list(reversed(b)), (k,n))
            for j, c in enumerate(b):
                check("positive_coefficients", c > 0, (k,n,j))
            for j in range(len(b)-1):
                check("adjacent_ratio_identities",
                      Fraction(b[j+1],b[j]) == adjacent_ratio(k,n,j), (k,n,j))
            for j in range(1,len(b)-1):
                check("strict_log_concavity", b[j]**2 > b[j-1]*b[j+1], (k,n,j))

    # Exact polynomial degree and leading coefficient on both parities.
    for k in range(1,11):
        d, r = k*k//4, k//2
        for parity in (0,1):
            aa = admissible(k,parity)
            for j,a in enumerate(aa):
                values = [Fraction(coefficient(k,2*i+parity,a))
                          for i in range(d+2)]
                for _ in range(d):
                    values = [v-u for u,v in zip(values, values[1:])]
                expected = leading_constant(k)*comb(r,j)*2**d*factorial(d)
                check("parity_polynomial_degrees_and_leading_terms",
                      values == [expected,expected], (k,parity,j))

    # Bilateral reflection and the complete negative-index gap.
    parameters = [Fraction(1),Fraction(2),Fraction(-1,2)]
    for k in range(1,17):
        for t in parameters:
            for m in range(49):
                check("negative_index_reflection",
                      delta(k,-m,t) == sign_power((k+1)//2)*t**(-k*(k+1)//2)
                                      *delta(k,m-k,1/t), (k,m,t))
            for h in range(1,k):
                check("negative_index_gap", delta(k,-h,t) == 0, (k,h,t))

    # Prescribed denominator and numerator reciprocity at rational t.
    for k in range(1,17):
        r = k//2
        for t in parameters:
            q = denominator(k,t)
            D = len(q)-1
            degree = D-k
            values = [delta(k,n,t) for n in range(D+13)]
            for n in range(degree+1, D+13):
                convolution = sum(q[j]*values[n-j] for j in range(min(n,D)+1))
                check("generating_function_tail_coefficients", convolution == 0, (k,n,t))
            a, reciprocal_a = numerator(k,t), numerator(k,1/t)
            exponent = 2*r*r*(r-1) if k%2==0 else k*r*r
            sign = 1 if k%2==0 else sign_power(r)
            check("numerator_reciprocity_polynomials",
                  a == [sign*t**exponent*c for c in reversed(reciprocal_a)], (k,t))
            check("exact_numerator_degree", a[-1] != 0, (k,t))

    check("non_real_rooted_example", rho_coefficients(4,2) == [2,8,10]
          and 8**2-4*2*10 == -16, None)
    report = {
        "status": "PASS", "python": platform.python_version(),
        "arithmetic": "exact integers and fractions; no floating-point tests",
        "random_seed": 211114492,
        "checks": dict(sorted(counts.items())), "total_checks": sum(counts.values()),
        "elapsed_seconds": round(time.perf_counter()-started,3),
        "scope": {
            "direct_grid": "1<=k<=12, 0<=n<=12; seven integer (u,t) pairs",
            "direct_seeded": "200 draws: 1<=k<=20, 0<=n<=18; -4<=u<=4, -3<=t<=4",
            "coefficient_tests": "1<=k<=24, 1<=n<=60",
            "finite_differences": "1<=k<=10, both parities, all admissible a",
            "reflection": "1<=k<=16, 0<=m<=48, t in {1,2,-1/2}",
            "generating_functions": "1<=k<=16; t in {1,2,-1/2}; through x^(deg(Q)+12)"
        }
    }
    output = Path(__file__).resolve().parents[1]/"data"/"verification.json"
    output.parent.mkdir(exist_ok=True)
    output.write_text(json.dumps(report,indent=2)+"\n",encoding="utf-8")
    print(json.dumps(report,indent=2))


if __name__ == "__main__":
    main()
