#!/usr/bin/env python3
"""Exact bounded search for monic quintics; NOT an effective Mordell solver.

Every loop has a supplied finite bound. The output is complete only for
canonical affine rational points of component height at most ``bound``.
No successful finite run certifies that there are no points above that bound.
"""
from dataclasses import asdict, dataclass
from fractions import Fraction
from math import gcd, isqrt
import argparse
import json


@dataclass(frozen=True)
class Quintic:
    # Ascending coefficients; the coefficient of x**5 is 1.
    a0: int
    a1: int
    a2: int
    a3: int
    a4: int

    def homogeneous(self, u: int, v: int) -> int:
        return (u**5 + self.a4*u**4*v + self.a3*u**3*v**2
                + self.a2*u**2*v**3 + self.a1*u*v**4 + self.a0*v**5)

    def evaluate(self, x: Fraction) -> Fraction:
        return ((((x + self.a4)*x + self.a3)*x + self.a2)*x + self.a1)*x + self.a0


@dataclass(frozen=True, order=True)
class Point:
    u: int
    v: int
    r: int
    s: int

    def height(self) -> int:
        return max(abs(self.u), self.v, abs(self.r), self.s)

    def canonical(self) -> bool:
        return (self.v > 0 and self.s > 0 and gcd(abs(self.u), self.v) == 1
                and gcd(abs(self.r), self.s) == 1)


def is_point(f: Quintic, p: Point) -> bool:
    return (p.canonical()
            and p.r**2*p.v**5 == p.s**2*f.homogeneous(p.u, p.v))


def bounded_points(f: Quintic, bound: int) -> list[Point]:
    """Return exactly the canonical affine points with height <= bound."""
    if bound < 0:
        raise ValueError("bound must be nonnegative")
    out = []
    for u in range(-bound, bound + 1):
        for v in range(1, bound + 1):
            if gcd(abs(u), v) != 1:
                continue
            target = f.homogeneous(u, v)
            for r in range(-bound, bound + 1):
                for s in range(1, bound + 1):
                    p = Point(u, v, r, s)
                    if gcd(abs(r), s) == 1 and r*r*v**5 == s*s*target:
                        out.append(p)
    return out


def independent_fraction_search(f: Quintic, bound: int) -> list[Point]:
    """Independent validation route: evaluate f(x), then extract exact roots."""
    if bound < 0:
        raise ValueError("bound must be nonnegative")
    out = set()
    for u in range(-bound, bound + 1):
        for v in range(1, bound + 1):
            if gcd(abs(u), v) != 1:
                continue
            y2 = f.evaluate(Fraction(u, v))
            if y2 < 0:
                continue
            r, s = isqrt(y2.numerator), isqrt(y2.denominator)
            if r*r != y2.numerator or s*s != y2.denominator:
                continue
            if r <= bound and s <= bound:
                out.add(Point(u, v, r, s))
                out.add(Point(u, v, -r, s))
    return sorted(out)


def determinant(matrix: list[list[int]]) -> int:
    """Fraction-free Bareiss elimination with finite pivot searches."""
    n = len(matrix)
    if any(len(row) != n for row in matrix):
        raise ValueError("matrix must be square")
    if n == 0:
        return 1
    a = [row[:] for row in matrix]
    sign, previous = 1, 1
    for k in range(n-1):
        pivot_row = next((i for i in range(k, n) if a[i][k] != 0), None)
        if pivot_row is None:
            return 0
        if pivot_row != k:
            a[k], a[pivot_row] = a[pivot_row], a[k]
            sign = -sign
        pivot = a[k][k]
        for i in range(k+1, n):
            for j in range(k+1, n):
                numerator = a[i][j]*pivot-a[i][k]*a[k][j]
                quotient, remainder = divmod(numerator, previous)
                if remainder != 0:
                    raise ArithmeticError("Bareiss exact-division invariant failed")
                a[i][j] = quotient
            a[i][k] = 0
        previous = pivot
    return sign*a[n-1][n-1]


def discriminant(f: Quintic) -> int:
    row_f = [1, f.a4, f.a3, f.a2, f.a1, f.a0]
    row_d = [5, 4*f.a4, 3*f.a3, 2*f.a2, f.a1]
    matrix = [[0]*i+row_f+[0]*(3-i) for i in range(4)]
    matrix += [[0]*i+row_d+[0]*(4-i) for i in range(5)]
    return determinant(matrix)


def result(f: Quintic, bound: int) -> dict:
    points = bounded_points(f, bound)
    return {
        "status": "bounded_search_only",
        "claim": "complete only for affine points with component height <= bound",
        "not_claimed": "no claim that points of greater height do not exist",
        "coefficients_a0_through_a4": list(asdict(f).values()),
        "discriminant": discriminant(f),
        "bound": bound,
        "raw_candidate_count": (2*bound+1)**2*bound**2,
        "affine_point_count_in_box": len(points),
        "affine_points": [asdict(p) for p in points],
        "projective_infinity": "one rational point if discriminant is nonzero",
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--coefficients", nargs=5, type=int, default=[1,-1,0,0,0],
                        metavar=("a0", "a1", "a2", "a3", "a4"))
    parser.add_argument("--bound", type=int, default=12)
    args = parser.parse_args()
    print(json.dumps(result(Quintic(*args.coefficients), args.bound), indent=2))


if __name__ == "__main__":
    main()
