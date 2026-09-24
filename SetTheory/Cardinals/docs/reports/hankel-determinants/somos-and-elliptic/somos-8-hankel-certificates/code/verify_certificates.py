#!/usr/bin/env python3
"""Exact finite certificates for Barry's Somos-8 Conjectures 11, 12 and 13.

Python 3.10+; standard library only.  No term is computed with a Somos recurrence.
The all-index mathematical input is Hone's Theorem 5.4, as explained in article.tex.
A finite computation alone is NOT an independent proof of that theorem.
"""
from __future__ import annotations
from dataclasses import dataclass
from pathlib import Path
import argparse
import json


@dataclass(frozen=True)
class Poly:
    """An integer polynomial, coefficients in ascending order."""
    c: tuple[int, ...]

    def __post_init__(self) -> None:
        c = tuple(self.c)
        if not all(isinstance(x, int) for x in c):
            raise TypeError("Polynomial coefficients must be integers")
        while len(c) > 1 and c[-1] == 0:
            c = c[:-1]
        object.__setattr__(self, "c", c or (0,))

    @staticmethod
    def cast(value: int | Poly) -> Poly:
        return value if isinstance(value, Poly) else Poly((value,))

    def __bool__(self) -> bool:
        return self.c != (0,)

    def __add__(self, other: int | Poly) -> Poly:
        b = self.cast(other).c
        return Poly(tuple((self.c[i] if i < len(self.c) else 0)
                          + (b[i] if i < len(b) else 0)
                          for i in range(max(len(self.c), len(b)))))

    __radd__ = __add__

    def __neg__(self) -> Poly:
        return Poly(tuple(-x for x in self.c))

    def __sub__(self, other: int | Poly) -> Poly:
        return self + (-self.cast(other))

    def __rsub__(self, other: int | Poly) -> Poly:
        return self.cast(other) + (-self)

    def __mul__(self, other: int | Poly) -> Poly:
        b = self.cast(other).c
        c = [0] * (len(self.c) + len(b) - 1)
        for i, x in enumerate(self.c):
            for j, y in enumerate(b):
                c[i+j] += x*y
        return Poly(tuple(c))

    __rmul__ = __mul__

    def __pow__(self, n: int) -> Poly:
        if not isinstance(n, int) or n < 0:
            raise ValueError("Exponent must be a nonnegative integer")
        ans, base = Poly((1,)), self
        while n:
            if n & 1:
                ans *= base
            base *= base
            n //= 2
        return ans

    def exact_div(self, divisor: Poly) -> Poly:
        """Exact division in Z[r]; raises instead of truncating a remainder."""
        if not divisor:
            raise ZeroDivisionError("Zero polynomial divisor")
        if not self:
            return Poly((0,))
        rem = list(self.c)
        b = divisor.c
        if len(rem) < len(b):
            raise ArithmeticError("Polynomial division has a remainder")
        q = [0] * (len(rem) - len(b) + 1)
        while len(rem) >= len(b) and rem != [0]:
            shift = len(rem) - len(b)
            quotient, residue = divmod(rem[-1], b[-1])
            if residue:
                raise ArithmeticError("Nonintegral polynomial quotient")
            q[shift] += quotient
            for j, x in enumerate(b):
                rem[j+shift] -= quotient*x
            while len(rem) > 1 and rem[-1] == 0:
                rem.pop()
        if rem != [0]:
            raise ArithmeticError("Polynomial division has a remainder")
        return Poly(tuple(q))

    def at(self, r: int) -> int:
        ans = 0
        for x in reversed(self.c):
            ans = ans*r+x
        return ans

    @property
    def degree(self) -> int:
        return len(self.c)-1 if self else -1


ZERO, ONE, R = Poly((0,)), Poly((1,)), Poly((0, 1))


def determinant(matrix: list[list[Poly]]) -> Poly:
    """Fraction-free Bareiss determinant with row pivoting."""
    n = len(matrix)
    if any(len(row) != n for row in matrix):
        raise ValueError("Matrix must be square")
    if n == 0:
        return ONE
    a = [row[:] for row in matrix]
    sign, previous = 1, ONE
    for k in range(n-1):
        pivot_row = next((j for j in range(k, n) if a[j][k]), None)
        if pivot_row is None:
            return ZERO
        if pivot_row != k:
            a[k], a[pivot_row] = a[pivot_row], a[k]
            sign = -sign
        pivot = a[k][k]
        for i in range(k+1, n):
            for j in range(k+1, n):
                a[i][j] = (pivot*a[i][j]-a[i][k]*a[k][j]).exact_div(previous)
            a[i][k] = ZERO
        previous = pivot
    return sign*a[-1][-1]


def integer_determinant(matrix: list[list[int]]) -> int:
    """The same fraction-free algorithm over integers, for numeric audits."""
    n = len(matrix)
    if any(len(row) != n for row in matrix):
        raise ValueError("Matrix must be square")
    if n == 0:
        return 1
    a = [row[:] for row in matrix]
    sign, previous = 1, 1
    for k in range(n-1):
        p = next((i for i in range(k, n) if a[i][k]), None)
        if p is None:
            return 0
        if p != k:
            a[k], a[p] = a[p], a[k]
            sign = -sign
        pivot = a[k][k]
        for i in range(k+1, n):
            for j in range(k+1, n):
                q, rem = divmod(pivot*a[i][j]-a[i][k]*a[k][j], previous)
                if rem:
                    raise ArithmeticError("Nonexact Bareiss division")
                a[i][j] = q
            a[i][k] = 0
        previous = pivot
    return sign*a[-1][-1]


def family(k: int) -> tuple[list[Poly], list[Poly], Poly, list[Poly]]:
    """Return A(x), B(x), D(r), [P1(r),...,P4(r)]."""
    r = R
    B = [ONE, -r]
    if k == 11:
        A = [ONE, -(r+1), -ONE, r]
        D = r**4-2*r**3+8*r**2+2*r-9
        P = [r**8-8*r**7+21*r**6-40*r**5+35*r**4-24*r**3+71*r**2+8*r,
             8*(r**9-6*r**8+17*r**7-30*r**6+15*r**5-14*r**4-r**3-14*r**2),
             8*(r-1)*(r**10-2*r**8+29*r**7-32*r**6+39*r**5
                       +18*r**4+11*r**3-r**2+r),
             2*r**13-13*r**12+48*r**11-85*r**10+83*r**9-11*r**8
             +124*r**7-454*r**6+364*r**5-263*r**4-84*r**3-189*r**2-25*r-9]
    elif k == 12:
        A = [ONE, -(r+1), r-1, ZERO]
        D = r**2-4*r+3
        P = [r**4-11*r**3+26*r**2-16*r-5,
             2*r**5-19*r**4+40*r**3-13*r**2-5*r,
             (r-1)*(3*r**6-12*r**5+15*r**4+25*r**3-62*r**2-36*r-5),
             r**9-8*r**8+26*r**7-43*r**6+40*r**5-17*r**4
             -23*r**3+27*r**2+19*r+3]
    elif k == 13:
        # The continued-fraction definition is authoritative; Barry's displayed
        # Catalan form has a sign typo in the coefficient of x.
        A = [ONE, -(r+1), r-2, r]
        D = 2*(r**3-3*r**2-5*r+7)
        P = [-(r**7-8*r**6+25*r**5-20*r**4-37*r**3+75*r+28),
             (r+1)*(r**8-11*r**7+47*r**6-83*r**5+17*r**4
                    +71*r**3+45*r**2-169*r+210),
             (r**2-1)*(3*r**8-29*r**7+115*r**6-225*r**5+181*r**4
                       +105*r**3-255*r**2-235*r+84),
             -(r**10-17*r**9+96*r**8-212*r**7+54*r**6+594*r**5
               -796*r**4-36*r**3+721*r**2-329*r-588)]
    else:
        raise ValueError("Family must be 11, 12 or 13")
    return A, B, D, P


def moments(A: list, B: list, nmax: int) -> list:
    """Compute from A(x)g=B(x)+x^3 B(x)g^2, never from Somos."""
    if nmax < 0 or A[0] != 1 and A[0] != ONE:
        raise ValueError("Require nmax >= 0 and A[0] = 1")
    one = ONE if isinstance(A[0], Poly) else 1
    zero = one-one
    a, conv = [one], [one]
    for n in range(1, nmax+1):
        value = B[n] if n < len(B) else zero
        for j in range(1, min(n, len(A)-1)+1):
            value -= A[j]*a[n-j]
        for j, b in enumerate(B):
            if n-j-3 >= 0:
                value += b*conv[n-j-3]
        a.append(value)
        conv.append(sum((a[i]*a[n-i] for i in range(n+1)), zero))
    return a


def hankels(a: list, nmax: int) -> list:
    """Return h_-1,h_0,...,h_nmax (empty determinant first)."""
    if len(a) < 2*nmax+1:
        raise ValueError("Insufficient moments")
    poly = isinstance(a[0], Poly)
    result = [ONE if poly else 1]
    det = determinant if poly else integer_determinant
    for n in range(nmax+1):
        result.append(det([[a[i+j] for j in range(n+1)] for i in range(n+1)]))
    return result


WITNESSES = {11: 844298284526087295172008083616,
             12: -1967013462528657296,
             13: -83222140602851259464}


def certify(k: int) -> dict:
    A, B, D, P = family(k)
    a = moments(A, B, 20)
    h = hankels(a, 10)
    H = lambda n: h[n+1]
    residuals = []
    for n in range(7, 11):
        residual = D*H(n)*H(n-8)-sum(
            (P[j-1]*H(n-j)*H(n-8+j) for j in range(1, 5)), ZERO)
        if residual:
            raise AssertionError(f"Family {k}, n={n}: symbolic identity failed")
        residuals.append(list(residual.c))
    M = [[H(n-j).at(2)*H(n-8+j).at(2) for j in range(1, 5)]
         for n in range(7, 11)]
    witness = integer_determinant(M)
    if witness != WITNESSES[k]:
        raise AssertionError(f"Unexpected rank witness for family {k}: {witness}")
    return {"family": k, "coefficient_order": "ascending powers of r",
            "A_by_x_power": [list(x.c) for x in A],
            "B_by_x_power": [list(x.c) for x in B],
            "D": list(D.c), "P": [list(x.c) for x in P],
            "moments_0_to_20": [list(x.c) for x in a],
            "hankels_minus1_to_10": [list(x.c) for x in h],
            "hankel_degrees_0_to_10": [x.degree for x in h[1:]],
            "residuals_n7_to_n10": residuals,
            "witness_r": 2, "witness_matrix": M, "witness_determinant": witness}


def audit(nmax: int = 28) -> dict:
    tests = 0
    for k in (11, 12, 13):
        A, B, D, P = family(k)
        for r in range(-5, 8):
            a = moments([x.at(r) for x in A], [x.at(r) for x in B], 2*nmax)
            h = hankels(a, nmax)
            H = lambda n: h[n+1]
            for n in range(7, nmax+1):
                residual = D.at(r)*H(n)*H(n-8)-sum(
                    P[j-1].at(r)*H(n-j)*H(n-8+j) for j in range(1, 5))
                if residual:
                    raise AssertionError(f"Numeric audit failed: family {k}, r={r}, n={n}")
                tests += 1
    return {"families": [11, 12, 13], "integer_parameters": list(range(-5, 8)),
            "index_range": [7, nmax], "identities_checked": tests,
            "all_passed": True, "includes_denominator_zeros": True,
            "note": "Additional audits; not the all-index proof."}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path,
                        default=Path(__file__).resolve().parents[1]/"data")
    parser.add_argument("--audit", action="store_true", help="Also check exact integer examples")
    args = parser.parse_args()
    args.output.mkdir(parents=True, exist_ok=True)
    results = []
    for k in (11, 12, 13):
        result = certify(k)
        results.append(result)
        print(f"C{k}: four polynomial identities PASS; rank witness {result['witness_determinant']}")
    (args.output/"certificates.json").write_text(json.dumps(results, indent=2)+"\n")
    if args.audit:
        result = audit()
        (args.output/"numeric_audit.json").write_text(json.dumps(result, indent=2)+"\n")
        print(f"Additional integer audits: {result['identities_checked']} / {result['identities_checked']} PASS")


if __name__ == "__main__":
    main()
