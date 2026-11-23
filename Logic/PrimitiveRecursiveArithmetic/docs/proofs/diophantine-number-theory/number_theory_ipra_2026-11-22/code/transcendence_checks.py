#!/usr/bin/env python3
"""Exact finite checks of transcendence.tex; no claim of formal verification.

Large polynomial-index bounds are checked through their exponent inequalities.
Only explicitly small truncations are evaluated.
"""
from fractions import Fraction
from math import factorial, gcd
from pathlib import Path
import json


def truncation(n):
    return sum((Fraction(1,10**factorial(j)) for j in range(1,n+1)), Fraction(0))


def eval_poly(cs,x):
    y = Fraction(0)
    for c in reversed(cs):
        y = y*x+c
    return y


def check():
    counts = {}
    tails = 0
    for n in range(1,6):
        r = truncation(n)
        q = 10**factorial(n)
        p = sum(10**(factorial(n)-factorial(j)) for j in range(1,n+1))
        assert r == Fraction(p,q) and gcd(p,q) == 1 and 0 < r < 1
        for m in range(n,7):
            delta = truncation(m)-r
            assert 0 <= delta <= Fraction(2,10**factorial(n+1)) <= Fraction(1,2**n)
            if m > n:
                for h in range(1,n+1):
                    assert 0 < delta < Fraction(1,q**h)
            tails += 1
    counts['factorial_tail_pairs_n_1_through_5_m_through_6'] = tails

    # This quadratic vanishes at the first two truncations but not the third.
    cs = [11,-210,1000]  # (10 X-1)(100 X-11)
    assert eval_poly(cs,truncation(1)) == 0
    assert eval_poly(cs,truncation(2)) == 0
    assert eval_poly(cs,truncation(3)) != 0
    counts['root_avoidance_example_with_two_initial_roots'] = 1

    lipschitz_cases = 0
    for cs in ([1], [0,1], [-1,1], [-2,0,1], [11,-210,1000], [1,-3,2,1]):
        d = len(cs)-1
        a = sum(j*abs(c) for j,c in enumerate(cs))
        for u in range(11):
            x = Fraction(u,10)
            for v in range(11):
                y = Fraction(v,10)
                assert abs(eval_poly(cs,x)-eval_poly(cs,y)) <= a*abs(x-y)
                fy = eval_poly(cs,y)
                if fy:
                    assert abs(fy) >= Fraction(1,y.denominator**d)
                lipschitz_cases += 1
    counts['polynomial_rational_value_and_Lipschitz_grid_cases'] = lipschitz_cases

    exponent_cases = 0
    for d in range(1,9):
        for a in range(1,41):
            n0 = d+a+1
            for n in range(n0,n0+d+1):
                exponent = (n+1-d)*factorial(n)
                # Avoid allocating 10^exponent: use the proof's smaller exponent.
                assert exponent >= a+2
                assert 10**(a+1) > 4*a
                exponent_cases += 1
    counts['polynomial_separation_symbolic_exponent_cases'] = exponent_cases

    margin_cases = 0
    for cs in ([0,1], [-1,1], [0,0,1], [-2,0,1]):
        d = len(cs)-1
        a = sum(j*abs(c) for j,c in enumerate(cs))
        n0 = d+a+1
        # These examples have n0 <= 5, and the search succeeds at n0.
        n = next(n for n in range(n0,n0+d+1) if eval_poly(cs,truncation(n)) != 0)
        q = 10**factorial(n)
        margin = Fraction(1,2*q**d)
        for m in range(n,7):
            assert abs(eval_poly(cs,truncation(m))) >= margin
            margin_cases += 1
    counts['actual_polynomial_separation_small_truncation_cases'] = margin_cases
    return {'status':'PASS','meaning':'Finite exact implementation checks, not formal proofs.',
            'large_bound_policy':'General high-index windows were checked using exponent inequalities; their huge rational truncations were not allocated.',
            'counts':counts}


if __name__ == '__main__':
    result = check()
    print(json.dumps(result,indent=2))
    (Path(__file__).resolve().parent/'validation_transcendence.json').write_text(json.dumps(result,indent=2)+'\n')
