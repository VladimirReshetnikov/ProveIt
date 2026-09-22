#!/usr/bin/env python3
"""Exact finite checks accompanying Small Divisors in Surcomplex Dynamics.

Requires Python >= 3.10; standard library only. These checks do NOT prove
summability, convergence radii, arithmetic limsups, or the infinite theorems.
They test the coefficient identities used in the proofs, in Q(i).
"""
from __future__ import annotations
from dataclasses import dataclass
from fractions import Fraction
from math import comb
from typing import Iterator
import sys


@dataclass(frozen=True)
class QI:
    """An exact Gaussian rational."""
    re: Fraction = Fraction(0)
    im: Fraction = Fraction(0)

    def __post_init__(self) -> None:
        object.__setattr__(self, "re", Fraction(self.re))
        object.__setattr__(self, "im", Fraction(self.im))

    @staticmethod
    def cast(x: QI | int | Fraction) -> QI:
        return x if isinstance(x, QI) else QI(Fraction(x))

    def __add__(self, other: QI | int | Fraction) -> QI:
        y = QI.cast(other)
        return QI(self.re + y.re, self.im + y.im)

    __radd__ = __add__

    def __neg__(self) -> QI:
        return QI(-self.re, -self.im)

    def __sub__(self, other: QI | int | Fraction) -> QI:
        return self + (-QI.cast(other))

    def __rsub__(self, other: QI | int | Fraction) -> QI:
        return QI.cast(other) + (-self)

    def __mul__(self, other: QI | int | Fraction) -> QI:
        y = QI.cast(other)
        return QI(self.re * y.re - self.im * y.im,
                  self.re * y.im + self.im * y.re)

    __rmul__ = __mul__

    def __truediv__(self, other: QI | int | Fraction) -> QI:
        y = QI.cast(other)
        norm = y.re * y.re + y.im * y.im
        if not norm:
            raise ZeroDivisionError("division by zero in Q(i)")
        return self * QI(y.re / norm, -y.im / norm)

    def __rtruediv__(self, other: QI | int | Fraction) -> QI:
        return QI.cast(other) / self

    def __pow__(self, n: int) -> QI:
        if not isinstance(n, int):
            raise TypeError("integer exponent required")
        if n < 0:
            return (QI(1) / self) ** (-n)
        ans, base = QI(1), self
        while n:
            if n & 1:
                ans = ans * base
            base = base * base
            n >>= 1
        return ans

    def __bool__(self) -> bool:
        return bool(self.re or self.im)

    def __str__(self) -> str:
        return f"({self.re}) + ({self.im})*i"


ZERO, ONE = QI(), QI(1)
LAM = QI(Fraction(3, 5), Fraction(4, 5))
LAM2 = QI(Fraction(5, 13), Fraction(12, 13))
COUNTS: dict[str, int] = {}


def check(test: bool, group: str, detail: str) -> None:
    if not test:
        raise AssertionError(f"{group}: {detail}")
    COUNTS[group] = COUNTS.get(group, 0) + 1


def compositions(total: int, length: int) -> Iterator[tuple[int, ...]]:
    if length == 0:
        if total == 0:
            yield ()
        return
    if length == 1:
        if total >= 1:
            yield (total,)
        return
    for head in range(1, total - length + 2):
        for tail in compositions(total - head, length - 1):
            yield (head,) + tail


def inverse_coefficients(a: list[QI], order: int) -> list[QI]:
    if not a[0]:
        raise ValueError("series constant term must be nonzero")
    c = [ONE / a[0]]
    for k in range(1, order + 1):
        c.append(-sum((a[j] * c[k-j]
                      for j in range(1, min(k, len(a)-1) + 1)), ZERO) / a[0])
    return c


def explicit_inverse_coefficient(a: list[QI], k: int) -> QI:
    if k == 0:
        return ONE / a[0]
    ans = ZERO
    for r in range(1, k + 1):
        for parts in compositions(k, r):
            term = ONE
            for j in parts:
                term *= a[j] if j < len(a) else ZERO
            ans += ((-1) ** r) * term / (a[0] ** (r + 1))
    return ans


def reciprocal_tests() -> None:
    K = 6
    for n in range(2, 21):
        a = [comb(n, j) * LAM ** (n-j) if j <= n else ZERO
             for j in range(K + 1)]
        a[0] -= LAM
        a[1] -= ONE
        c = inverse_coefficients(a, K)
        for k in range(K + 1):
            check(c[k] == explicit_inverse_coefficient(a, k),
                  "reciprocal explicit formula", f"n={n}, k={k}")
            product = sum((a[j] * c[k-j] for j in range(k+1)), ZERO)
            check(product == (ONE if k == 0 else ZERO),
                  "reciprocal product identity", f"n={n}, k={k}")


# Sparse bivariate polynomials, keys (parameter degree, spatial degree).
Poly = dict[tuple[int, int], QI]


def add(p: Poly, q: Poly) -> Poly:
    ans = dict(p)
    for key, val in q.items():
        ans[key] = ans.get(key, ZERO) + val
        if not ans[key]:
            del ans[key]
    return ans


def scale(p: Poly, c: QI) -> Poly:
    return {key: val * c for key, val in p.items() if val * c}


def mul(p: Poly, q: Poly, T: int, N: int) -> Poly:
    ans: Poly = {}
    for (a, b), x in p.items():
        for (c, d), y in q.items():
            if a+c <= T and b+d <= N:
                key = (a+c, b+d)
                ans[key] = ans.get(key, ZERO) + x*y
    return {key: val for key, val in ans.items() if val}


def compose(h: Poly, f: Poly, T: int, N: int) -> Poly:
    if any(deg_z == 0 for (_, deg_z) in f):
        raise ValueError("inner polynomial must have zero spatial constant")
    powers = [{(0, 0): ONE}]
    for _ in range(N):
        powers.append(mul(powers[-1], f, T, N))
    ans: Poly = {}
    for (a, b), c in h.items():
        shifted = {(a+i, j): c*x for (i, j), x in powers[b].items()
                   if a+i <= T}
        ans = add(ans, shifted)
    return ans


def quadratic_tests() -> None:
    N = 12
    b = [ZERO, ONE]
    for n in range(2, N + 1):
        remainder = sum((b[m] * comb(m, n-m) * LAM ** (2*m-n)
                         for m in range((n+1)//2, n)), ZERO)
        b.append(-remainder / (LAM**n - LAM))
    h = {(0, n): b[n] for n in range(1, N+1)}
    f = {(0, 1): LAM, (0, 2): ONE}
    residual = add(compose(h, f, 0, N), scale(h, -LAM))
    for n in range(N+1):
        check(not residual.get((0, n), ZERO), "quadratic ordinary identity", str(n))
    ht = {(n-1, n): b[n] for n in range(1, N+1)}
    ft = {(0, 1): LAM, (1, 2): ONE}
    residual_t = add(compose(ht, ft, N-1, N), scale(ht, -LAM))
    for a in range(N):
        for n in range(N+1):
            check(not residual_t.get((a, n), ZERO),
                  "quadratic Hahn scaling identity", f"t^{a}z^{n}")
    print("Quadratic example, lambda = 3/5 + (4/5)i:")
    print("  b_2 =", b[2])
    print("  b_3 =", b[3])


def nonlinear_recursion_tests() -> None:
    T, N = 4, 10
    f = {(0, 1): LAM, (1, 1): ONE, (1, 2): ONE, (1, 3): ONE}
    multiplier = {(0, 0): LAM, (1, 0): ONE}
    h: Poly = {(0, 1): ONE}
    for gamma in range(1, T+1):
        residual = add(compose(h, f, T, N), scale(mul(multiplier, h, T, N), -ONE))
        correction: Poly = {}
        for n in range(2, N+1):
            coeff = -residual.get((gamma, n), ZERO) / (LAM**n - LAM)
            if coeff:
                correction[(gamma, n)] = coeff
        h = add(h, correction)
        residual = add(compose(h, f, T, N), scale(mul(multiplier, h, T, N), -ONE))
        for a in range(gamma+1):
            for n in range(N+1):
                check(not residual.get((a, n), ZERO),
                      "nonlinear mixed-parameter recursion", f"stage {gamma}, t^{a}z^{n}")


def multivariable_tests() -> None:
    K = 4
    for n in range(2, 10):
        for alpha1 in range(n+1):
            phase = LAM**alpha1 * LAM2**(n-alpha1)
            for j, eigenvalue in enumerate((LAM, LAM2), 1):
                a = [comb(n, k) * phase if k <= n else ZERO for k in range(K+1)]
                a[0] -= eigenvalue
                a[1] -= eigenvalue
                if not a[0]:
                    raise AssertionError("unexpected resonance in finite test range")
                c = inverse_coefficients(a, K)
                for k in range(K+1):
                    check(c[k] == explicit_inverse_coefficient(a, k),
                          "multivariable reciprocal formula", f"n={n}, alpha1={alpha1}, j={j}, k={k}")


def main() -> None:
    print("Exact finite verification: Small Divisors in Surcomplex Dynamics")
    print("Python", sys.version.split()[0], "; arithmetic: fractions.Fraction in Q(i)")
    reciprocal_tests()
    quadratic_tests()
    nonlinear_recursion_tests()
    multivariable_tests()
    print()
    for name, count in COUNTS.items():
        print(f"PASS  {count:4d} checks: {name}")
    print(f"TOTAL: {sum(COUNTS.values())} exact checks passed.")
    print("NOT a machine-checked proof of the infinite results or novelty.")


if __name__ == "__main__":
    main()
