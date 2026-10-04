#!/usr/bin/env python3
"""Exact finite checks accompanying Rational Rank and Self-Embeddings.

Only the Python standard library is used. These checks verify finite algebraic
identities, not completeness, real closedness, Q-linear independence of real
exponents, or non-surjectivity of the infinite-dimensional embeddings.
In particular, the shift test retains its final boundary term: it never silently
truncates an infinite shift into a surjective finite-dimensional operator.
"""
from __future__ import annotations
from fractions import Fraction as F
from math import comb
from random import Random
from collections import Counter
import json

COUNTS: Counter[str] = Counter()


def check(condition: bool, family: str) -> None:
    if not condition:
        raise AssertionError(f"Failed check in {family}")
    COUNTS[family] += 1


def add(a: list[F], b: list[F]) -> list[F]:
    n = max(len(a), len(b))
    return [(a[j] if j < len(a) else F(0)) +
            (b[j] if j < len(b) else F(0)) for j in range(n)]


def scale(a: list[F], c: F) -> list[F]:
    return [c*x for x in a]


def mul(a: list[F], b: list[F], degree: int) -> list[F]:
    result = [F(0)]*(degree+1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            if i+j <= degree:
                result[i+j] += x*y
    return result


def power(a: list[F], n: int, degree: int) -> list[F]:
    if n < 0:
        raise ValueError("Use binomial() for negative rational powers")
    result = [F(1)]+[F(0)]*degree
    while n:
        if n & 1:
            result = mul(result, a, degree)
        a = mul(a, a, degree)
        n >>= 1
    return result


def compose(a: list[F], b: list[F], degree: int) -> list[F]:
    result = [F(0)]*(degree+1)
    for c in reversed(a):
        result = mul(result, b, degree)
        result[0] += c
    return result


def binomial(q: F, degree: int) -> list[F]:
    result = [F(1)]
    for j in range(1, degree+1):
        result.append(result[-1]*(q-j+1)/j)
    return result


def order(a: list[F]) -> int | float:
    return next((j for j, c in enumerate(a) if c), float('inf'))


def binomial_tests() -> None:
    degree = 16
    exponents = sorted({F(m,n) for n in range(1,6) for m in range(-3,4)})
    for a in exponents:
        for b in exponents:
            check(mul(binomial(a,degree), binomial(b,degree), degree)
                  == binomial(a+b,degree), 'rational_binomial_product')
    for n in range(1,13):
        expected = [F(1), F(1)]+[F(0)]*(degree-1)
        check(power(binomial(F(1,n),degree), n, degree) == expected,
              'principal_root')


def neumann_tests() -> None:
    degree = 24
    substitution = [F(0), F(1), F(1)]+[F(0)]*(degree-2)
    def tau(a: list[F]) -> list[F]:
        return compose(a,substitution,degree)
    def T(a: list[F]) -> list[F]:
        return add(tau(a),scale(a,F(-1)))
    def inverse(a: list[F]) -> list[F]:
        result = [F(0)]*(degree+1)
        term = a
        for n in range(degree+1):
            result = add(result,scale(term,F((-1)**n)))
            term = T(term)
        check(not any(term), 'neumann_nilpotent_remainder')
        return result
    for j in range(degree+1):
        x = [F(0)]*(degree+1)
        x[j] = F(1)
        check(order(T(x)) >= j+1, 'uniform_gap_on_monomials')
        y = inverse(x)
        check(tau(y)==x, 'neumann_right_inverse')
        check(inverse(tau(x))==x, 'neumann_left_inverse')
    rng = Random(20261004)
    for _ in range(16):
        x = [F(rng.randrange(-5,6),rng.randrange(1,6))
             for j in range(degree+1)]
        check(tau(inverse(x))==x, 'neumann_random_exact')
    t = [F(0),F(1)]+[F(0)]*(degree-1)
    expected = [F(0)]+[F((-1)**(j-1)*comb(2*j-2,j-1),j)
                       for j in range(1,degree+1)]
    check(inverse(t)==expected, 'catalan_inverse_coefficients')


def shift_tests() -> None:
    # Basis symbols are independent FORMAL symbols. No approximate real weights
    # are used as substitutes for Q-linearly independent real exponents.
    for n in range(201):
        result: dict[int,int] = {}
        for j in range(n+1):
            result[j] = result.get(j,0)+(-1)**j
            result[j+1] = result.get(j+1,0)+(-1)**j
        result = {j:c for j,c in result.items() if c}
        check(result=={0:1,n+1:(-1)**n}, 'shift_telescoping_with_boundary')
    for mask in range(32):
        for chain in range(5):
            for n in range(12):
                result: dict[tuple[int,int],int] = {}
                for j in range(n+1):
                    key=(chain,j)
                    result[key] = result.get(key,0)+(-1)**j
                    if mask & (1<<chain):
                        key=(chain,j+1)
                        result[key] = result.get(key,0)+(-1)**j
                result={j:c for j,c in result.items() if c}
                if mask & (1<<chain):
                    expected={(chain,0):1,(chain,n+1):(-1)**n}
                else:
                    expected={(chain,j):(-1)**j for j in range(n+1)}
                check(result==expected, 'independent_chain_selection')


def rational_counterexample_tests() -> None:
    # All compositions below are kept at their full possible degree.
    t=[F(0),F(1)]
    s=[F(0),F(1),F(1)]
    reflection=[F(-1),F(-1)]
    check(compose(s,reflection,2)==s, 'reflection_fixes_t_plus_t_squared')
    check(compose(t,reflection,1)!=t, 'reflection_moves_t')
    for n in range(1,13):
        p=[F(j+1,j+2) for j in range(n+1)]
        p_s=compose(p,s,2*n)
        check(compose(p_s,reflection,2*n)==p_s,
              'polynomial_invariant_under_reflection')


def main() -> None:
    binomial_tests()
    neumann_tests()
    shift_tests()
    rational_counterexample_tests()
    print(json.dumps({
        'status':'PASS',
        'arithmetic':'exact rational arithmetic (fractions.Fraction)',
        'checks':dict(sorted(COUNTS.items())),
        'total_checks':sum(COUNTS.values()),
        'scope':'Finite identities only; no claim of formal theorem verification.'
    },indent=2,sort_keys=True))

if __name__=='__main__':
    main()
