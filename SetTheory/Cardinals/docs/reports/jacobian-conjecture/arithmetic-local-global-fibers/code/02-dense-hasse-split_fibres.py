#!/usr/bin/env python3
"""Exact certificates for split fibres of the ProveIt Keller map.

All algebraic decisions use integers and fractions. No numerical root solver
or p-adic approximation is used. This is a computational companion, not a
Lean/Rocq formalization.
"""
from __future__ import annotations

import argparse
import json
from fractions import Fraction
from itertools import product
from math import gcd, isqrt
from typing import Iterable

Point = tuple[Fraction, Fraction, Fraction]
Target = tuple[int, int, int]


def keller(x, y, z):
    """Evaluate the original polynomial map in any compatible ring."""
    u = 1 + x*y
    h = u*u*z + y*y*(1 + 3*u)
    return u*h, y + 3*x*h, x*(5 - 3*u - x*x*z)


def factor_integer(n: int) -> dict[int, int]:
    """Trial-division factorization, intended for small certificate parameters."""
    n = abs(n)
    if n == 0:
        raise ValueError("Zero has no finite prime factorization.")
    result: dict[int, int] = {}
    p = 2
    while p*p <= n:
        while n % p == 0:
            result[p] = result.get(p, 0) + 1
            n //= p
        p = 3 if p == 2 else p + 2
    if n > 1:
        result[n] = result.get(n, 0) + 1
    return result


def divisors(n: int) -> list[int]:
    n = abs(n)
    if n == 0:
        raise ValueError("Use a nonzero integer.")
    small = [d for d in range(1, isqrt(n) + 1) if n % d == 0]
    return sorted(set(small + [n//d for d in small]))


def v2(n: int) -> int:
    if n == 0:
        raise ValueError("v2(0) is not used here.")
    n = abs(n)
    return (n & -n).bit_length() - 1


def coefficients(c: int, a: int, b: int) -> tuple[Fraction, Fraction, int]:
    if c == 0:
        raise ValueError("The numerator parametrization requires c != 0.")
    return (Fraction(a*b*(2-a-b), 2*c*c),
            Fraction(2*(a+b)-a*a-a*b-b*b, c), c)


def split_fibre(c: int, a: int, b: int) -> tuple[Point, Point, Point]:
    """Return the complete fibre for three distinct numerator roots a,b,2-a-b."""
    if c == 0:
        raise ValueError("c must be nonzero.")
    r = 2-a-b
    if len({a, b, r}) != 3:
        raise ValueError("Repeated roots are excluded from this split-fibre API.")
    points = []
    for j, k, ell in [(a,b,r), (b,a,r), (r,a,b)]:
        D = (j-k)*(j-ell)
        points.append((Fraction(2*c,D), Fraction(2*j-D,2*c),
                       Fraction(D*(10*D-12*j-D*D),8*c*c)))
    return tuple(points)


def dyadic_root_condition(c: int, a: int, b: int) -> bool:
    """Exact local condition at 2, under integral-coefficient assumptions."""
    e = v2(c)
    r = 2-a-b
    if e == 0:
        return sorted([a % 4, b % 4, r % 4]) == [1,2,3]
    if e == 1:
        return a % 2 == b % 2 == 0 and sum((j//2) % 2 for j in [a,b,r]) == 1
    return True  # Theorem: integrality of the coefficients suffices if 4 | c.


def locally_integral(c: int, a: int, b: int) -> bool:
    """Decide integral solubility at every prime, for an integral split target."""
    A, B, _ = coefficients(c,a,b)
    if A.denominator != 1 or B.denominator != 1:
        raise ValueError("The target is not integral.")
    if len({a,b,2-a-b}) != 3:
        raise ValueError("Use distinct roots.")
    g = gcd(abs(a-b), abs(3*a-2))
    # Remove all prime factors supported on 2c without factoring g.
    h = gcd(g, 2*abs(c))
    while h > 1:
        g //= h
        h = gcd(g, 2*abs(c))
    return g == 1 and dyadic_root_condition(c,a,b)


def denominator_primes(points: Iterable[Point]) -> set[int]:
    out: set[int] = set()
    for point in points:
        for value in point:
            out.update(factor_integer(value.denominator))
    return out


def is_p_integral(point: Point, p: int) -> bool:
    return all(value.denominator % p for value in point)


def integral_exceptions(c: int) -> dict[Target, tuple[Point, ...]]:
    """Enumerate ALL distinct completely split fibres meeting Z^3 for fixed c.

    Completeness follows from D_a | 2c at an integral source point.
    """
    if c == 0:
        raise ValueError("The finite-exception theorem assumes c != 0.")
    result = {}
    for Dabs in divisors(2*abs(c)):
        for D in [Dabs, -Dabs]:
            for dabs in divisors(Dabs):
                for d in [dabs, -dabs]:
                    ell = D//d
                    if (d+ell+2) % 3:
                        continue
                    a = (d+ell+2)//3
                    b = a-d
                    A,B,_ = coefficients(c,a,b)
                    if A.denominator != 1 or B.denominator != 1:
                        continue
                    if len({a,b,2-a-b}) != 3:
                        continue
                    pts = split_fibre(c,a,b)
                    integral = tuple(P for P in pts if all(v.denominator == 1 for v in P))
                    if integral:
                        result[(int(A),int(B),c)] = integral
    return result


def universal_family(c: int, q: int, r: int) -> tuple[Target, tuple[Point, ...]]:
    """The everywhere-locally-integral, nowhere-globally-integral family.

    Required: c != 0, q >= 0, r >= 1. Returns target and complete fibre.
    """
    if c == 0 or q < 0 or r < 1:
        raise ValueError("Require c != 0, q >= 0, and r >= 1.")
    n, k = 2*q+1, 4*r+2
    s, t = n*k, n*(k-1)
    A = Fraction(s*t*(2-c*(s+t)),2)
    B = 2*(s+t)-c*(s*s+s*t+t*t)
    assert A.denominator == 1
    target = (int(A),B,c)
    return target, split_fibre(c,c*s,c*t)


def modular_witness(c: int, a: int, b: int, modulus: int) -> tuple[int,int,int]:
    """Produce a solution mod modulus, via exact branch selection and CRT."""
    if modulus < 1:
        raise ValueError("The modulus must be positive.")
    if not locally_integral(c,a,b):
        raise ValueError("The fibre is not everywhere locally integral.")
    points = split_fibre(c,a,b)
    values = [0,0,0]
    accumulated = 1
    for p,e in factor_integer(modulus).items():
        pe = p**e
        point = next(P for P in points if is_p_integral(P,p))
        for j, value in enumerate(point):
            residue = value.numerator*pow(value.denominator,-1,pe) % pe
            delta = (residue-values[j])*pow(accumulated,-1,pe) % pe
            values[j] += accumulated*delta
        accumulated *= pe
    answer = tuple(v % modulus for v in values)
    target = coefficients(c,a,b)
    assert tuple(int(v) % modulus for v in keller(*answer)) == tuple(int(v) % modulus for v in target)
    return answer


def certificate(c: int, a: int, b: int) -> dict:
    A,B,_ = coefficients(c,a,b)
    points = split_fibre(c,a,b)
    target = (A,B,c)
    assert all(keller(*P) == target for P in points)
    integral_target = A.denominator == B.denominator == 1
    local = locally_integral(c,a,b) if integral_target else None
    primes = sorted(denominator_primes(points))
    return {
        "numerator_roots": [a,b,2-a-b],
        "target": [str(v) for v in target],
        "points": [[str(v) for v in P] for P in points],
        "integral_target": integral_target,
        "everywhere_locally_integral": local,
        "globally_integral_branches": [i+1 for i,P in enumerate(points) if all(v.denominator==1 for v in P)],
        "exceptional_denominator_primes": primes,
        "local_branches_at_exceptional_primes": {str(p):[i+1 for i,P in enumerate(points) if is_p_integral(P,p)] for p in primes},
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("c", type=int)
    parser.add_argument("a", type=int)
    parser.add_argument("b", type=int)
    parser.add_argument("--modulus", type=int)
    args = parser.parse_args()
    data = certificate(args.c,args.a,args.b)
    if args.modulus is not None:
        data["modular_witness"] = {"modulus":args.modulus,"point":modular_witness(args.c,args.a,args.b,args.modulus)}
    print(json.dumps(data,indent=2))

if __name__ == "__main__":
    main()
