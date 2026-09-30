#!/usr/bin/env python3
"""Exact finite checks for the accompanying research article.

Only Python's standard library is used. Fractions and Q(sqrt(17)) arithmetic
verify identities, not the infinite-dimensional analytic theorems.
Run: python verify.py --output verification.json
"""
from __future__ import annotations

import argparse
from dataclasses import dataclass
from fractions import Fraction as F
import json
from math import comb
from pathlib import Path
import platform


@dataclass(frozen=True)
class Q17:
    """Exact a + b sqrt(17)."""
    a: F = F(0)
    b: F = F(0)

    def __add__(self, other: Q17) -> Q17:
        return Q17(self.a + other.a, self.b + other.b)

    def __neg__(self) -> Q17:
        return Q17(-self.a, -self.b)

    def __sub__(self, other: Q17) -> Q17:
        return self + (-other)

    def __mul__(self, other: Q17) -> Q17:
        return Q17(self.a * other.a + 17 * self.b * other.b,
                   self.a * other.b + self.b * other.a)

    def __pow__(self, n: int) -> Q17:
        if n < 0:
            raise ValueError("Only nonnegative powers are supported.")
        value, base = Q17(F(1)), self
        while n:
            if n & 1:
                value = value * base
            base = base * base
            n >>= 1
        return value


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ArithmeticError(message)


def sine_coeff(m: int, k: int) -> F:
    if abs(k) > m:
        return F(0)
    return F((-1 if k % 2 else 1) * comb(2 * m, m + k), 4 ** m)


def matrix(b: int, m: int) -> list[list[F]]:
    d = m // (b - 1)
    return [[sine_coeff(m, b * k - j) for j in range(-d, d + 1)]
            for k in range(-d, d + 1)]


def matmul(a: list[list[F]], b: list[list[F]]) -> list[list[F]]:
    return [[sum((a[i][k] * b[k][j] for k in range(len(b))), F(0))
             for j in range(len(b[0]))] for i in range(len(a))]


def characteristic(a: list[list[F]]) -> list[F]:
    """Faddeev-LeVerrier; return descending coefficients, including 1."""
    n = len(a)
    bb = [[F(i == j) for j in range(n)] for i in range(n)]
    result = [F(1)]
    for k in range(1, n + 1):
        ab = matmul(a, bb)
        c = -sum((ab[i][i] for i in range(n)), F(0)) / k
        result.append(c)
        bb = [[ab[i][j] + (c if i == j else 0) for j in range(n)]
              for i in range(n)]
    require(all(x == 0 for row in bb for x in row), "Cayley-Hamilton check")
    return result


def poly_multiply(a: list[F], b: list[F]) -> list[F]:
    c = [F(0)] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            c[i + j] += x * y
    return c


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=Path("verification.json"))
    parser.add_argument("--levels", type=int, default=12,
                        help="largest directly checked dyadic level (0 to 16)")
    args = parser.parse_args()
    if not 0 <= args.levels <= 16:
        parser.error("--levels must lie between 0 and 16")
    nmax = 2 ** args.levels
    eta = [F(0)] * (nmax + 1)
    a = [0] * (nmax + 1)
    eta[0] = F(1)
    if nmax >= 1:
        eta[1], a[1] = F(-1, 3), 1
    for k in range(2, nmax + 1):
        j = k // 2
        if k % 2 == 0:
            eta[k], a[k] = eta[j], -2 * a[j]
        else:
            eta[k], a[k] = -(eta[j] + eta[j + 1]) / 2, a[j] + a[j + 1]

    # Verify four recurrences by direct sums, and two closed forms in Q(sqrt(17)).
    E, C, FF, G = 0, 0, F(1), F(-1, 3)
    energies = []
    ep, em = Q17(F(1, 4), F(5, 68)), Q17(F(1, 4), F(-5, 68))
    fp, fm = Q17(F(5, 18), F(19, 306)), Q17(F(5, 18), F(-19, 306))
    for n in range(args.levels + 1):
        M = 2 ** n
        actual = (sum(x*x for x in a[:M]),
                  sum(a[k]*a[k+1] for k in range(M)),
                  sum((x*x for x in eta[:M]), F(0)),
                  sum((eta[k]*eta[k+1] for k in range(M)), F(0)))
        require(actual == (E, C, FF, G), f"Energy recurrence at level {n}")
        eclosed = ep * Q17(F(1), F(1))**n + em * Q17(F(1), F(-1))**n \
                  - Q17(F(4**n, 2))
        fclosed = fp * Q17(F(1, 4), F(1, 4))**n \
                  + fm * Q17(F(1, 4), F(-1, 4))**n + Q17(F(4, 9))
        require(eclosed == Q17(F(E)), f"Stern closed energy at level {n}")
        require(fclosed == Q17(FF), f"Correlation closed energy at level {n}")
        energies.append({"n": n, "E": str(E), "C": str(C),
                         "F": str(FF), "G": str(G)})
        E, C = 6*E + 2*C + 4**n, -4*E - 4*C - 2*4**n
        FF, G = F(3, 2)*FF + G/2 - F(2, 9), -FF - G + F(4, 9)

    # Independent exact Laurent-polynomial multiplication of Riesz products.
    q = {0: F(1)}
    cutoff_count = 0
    for n in range(args.levels + 1):
        for k in range(-2**n, 2**n + 1):
            value = eta[abs(k)] + F(1, 3)*F(-1, 2)**n*a[abs(k)]
            require(q.get(k, F(0)) == value, f"Cutoff formula n={n}, k={k}")
            cutoff_count += 1
        require(q[0] == 1, f"Unit mass at level {n}")
        if n < args.levels:
            step = 2**n
            new: dict[int, F] = {}
            for k, c in q.items():
                for shift, v in ((0, F(1)), (-step, F(-1, 2)),
                                 (step, F(-1, 2))):
                    new[k+shift] = new.get(k+shift, F(0)) + c*v
            q = {k: v for k, v in new.items() if v}

    # Dual-eigenvector identities on a substantial finite set of Fourier modes.
    dual_count = 0
    for j in range(-nmax, nmax + 1):
        out = {k: sine_coeff(1, 2*k-j)
               for k in range((j-1)//2-1, (j+1)//2+2)}
        mu = sum((v*eta[abs(k)] for k, v in out.items() if v), F(0))
        dp = sum((v*a[k] for k, v in out.items() if v and k > 0), F(0))
        dm = sum((v*a[-k] for k, v in out.items() if v and k < 0), F(0))
        require(mu == eta[abs(j)]/2, f"Leading dual identity at mode {j}")
        require(dp == -F(a[j], 4) if j > 0 else dp == 0,
                f"Positive Stern dual identity at mode {j}")
        require(dm == -F(a[-j], 4) if j < 0 else dm == 0,
                f"Negative Stern dual identity at mode {j}")
        dual_count += 3

    # Finite-band invariance and strict descent outside the terminal band.
    band_checks = 0
    for b in range(2, 9):
        for m in range(1, 7):
            d = m // (b-1)
            for N in range(d, d+31):
                for j in range(-N, N+1):
                    for ell in range(-m, m+1):
                        if (j+ell) % b == 0:
                            k = (j+ell)//b
                            require(abs(k) <= N, "Finite-band invariance")
                            if N > d:
                                require(abs(k) < N, "Strict band descent")
                            band_checks += 1

    A1, A2 = matrix(2, 1), matrix(2, 2)
    expected1 = poly_multiply([F(1), F(-1, 2)],
                             poly_multiply([F(1), F(1, 4)], [F(1), F(1, 4)]))
    expected2 = [F(1)]
    for factor in ([F(1), F(1, 4)], [F(1), F(-1, 16)],
                   [F(1), F(-1, 16)], [F(1), F(-1, 8), F(-1, 16)]):
        expected2 = poly_multiply(expected2, factor)
    require(characteristic(A1) == expected1, "Quadratic-mask characteristic polynomial")
    require(characteristic(A2) == expected2, "Quartic-mask characteristic polynomial")

    rho, kappa = Q17(F(1, 16), F(1, 16)), Q17(F(5, 4), F(-1, 4))
    hv = [Q17(), kappa*Q17(F(1, 2)), Q17(F(1)),
          kappa*Q17(F(1, 2)), Q17()]
    for i, row in enumerate(A2):
        value = Q17()
        for c, v in zip(row, hv):
            value = value + Q17(c)*v
        require(value == rho*hv[i], "Positive eigenfunction identity")

    result = {
        "status": "PASS", "python": platform.python_version(),
        "arithmetic": "exact integers, fractions, and Q(sqrt(17)); no floats",
        "levels": args.levels, "maximum_direct_frequency": nmax,
        "cutoff_coefficient_checks": cutoff_count,
        "dual_eigenfunctional_checks": dual_count,
        "band_invariance_and_descent_checks": band_checks,
        "energy_recurrence_checks": 4*(args.levels+1),
        "closed_energy_checks": 2*(args.levels+1),
        "positive_eigenfunction_checks": 5,
        "characteristic_polynomials_descending": {
            "b2_m1": [str(x) for x in expected1],
            "b2_m2": [str(x) for x in expected2]},
        "energy_data": energies,
        "scope": "Finite algebraic checks only. Infinite-dimensional spectra and sharp asymptotic theorems are proved in article.tex, not certified by finite sampling."
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({k: v for k, v in result.items() if k != "energy_data"}, indent=2))


if __name__ == "__main__":
    main()
