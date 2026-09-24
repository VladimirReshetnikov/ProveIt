#!/usr/bin/env python3
"""Exact finite checks for Small Divisors at Surreal Scales.

Python 3.9+, standard library only. These checks are not a formal proof of
any infinite-support or analytic statement. All arithmetic is in Q(i).
Run: python code/verify.py --output verification.json
"""
from __future__ import annotations
from dataclasses import dataclass
from fractions import Fraction as Q
from math import comb, factorial
from pathlib import Path
import argparse
import json
from typing import Dict, List

@dataclass(frozen=True)
class G:
    re: Q = Q(0)
    im: Q = Q(0)

    def __add__(self, other: G) -> G:
        return G(self.re + other.re, self.im + other.im)

    def __neg__(self) -> G:
        return G(-self.re, -self.im)

    def __sub__(self, other: G) -> G:
        return self + (-other)

    def __mul__(self, other: G) -> G:
        return G(self.re * other.re - self.im * other.im,
                 self.re * other.im + self.im * other.re)

    def scale(self, q: Q) -> G:
        return G(self.re * q, self.im * q)

    def conj(self) -> G:
        return G(self.re, -self.im)

    def zero(self) -> bool:
        return self.re == 0 and self.im == 0

    def __str__(self) -> str:
        return str(self.re) if not self.im else f"({self.re})+({self.im})i"

ZERO, ONE, I = G(), G(Q(1)), G(Q(0), Q(1))
F = Dict[int, G]                    # Fourier polynomial in theta
P = List[F]                        # truncated polynomial in r


def add(a: F, b: F) -> F:
    c = dict(a)
    for k, value in b.items():
        c[k] = c.get(k, ZERO) + value
        if c[k].zero():
            del c[k]
    return c


def scale(a: F, c: G) -> F:
    return {k: v * c for k, v in a.items() if not (v * c).zero()}


def mul(a: F, b: F) -> F:
    c: F = {}
    for k, v in a.items():
        for l, w in b.items():
            m = k + l
            c[m] = c.get(m, ZERO) + v * w
    return {k: v for k, v in c.items() if not v.zero()}


def deriv(a: F) -> F:
    return {k: v * I.scale(Q(k)) for k, v in a.items() if k}


def integrate_zero_mean(a: F) -> F:
    assert a.get(0, ZERO).zero()
    return {k: v * (-I).scale(Q(1, k)) for k, v in a.items() if k}


def pmul(a: P, b: P, degree: int) -> P:
    out: P = [{} for _ in range(degree + 1)]
    for j in range(min(len(a), degree + 1)):
        for k in range(min(len(b), degree + 1 - j)):
            out[j + k] = add(out[j + k], mul(a[j], b[k]))
    return out


def exp_series(h: P, c: G, degree: int) -> P:
    assert not h[0]
    hc = [scale(a, c) for a in h[:degree + 1]]
    out: P = [{0: ONE}] + [{} for _ in range(degree)]
    power: P = [{0: ONE}] + [{} for _ in range(degree)]
    for n in range(1, degree + 1):
        power = pmul(power, hc, degree)
        for j in range(degree + 1):
            out[j] = add(out[j], scale(power[j], G(Q(1, factorial(n)))))
    return out


def sin_composed(h: P, degree: int) -> P:
    ep = exp_series(h, I, degree)
    em = exp_series(h, -I, degree)
    ans: P = []
    for j in range(degree + 1):
        pos = {k + 1: v for k, v in ep[j].items()}
        neg = {k - 1: -v for k, v in em[j].items()}
        ans.append(scale(add(pos, neg), (-I).scale(Q(1, 2))))
    return ans


def circle_check(degree: int = 10) -> dict:
    # (1 + h') nu = 1 + r sin(theta + h), mean(h)=0.
    h: P = [{} for _ in range(degree + 1)]
    nu: List[Q] = [Q(1)] + [Q(0)] * degree
    for n in range(1, degree + 1):
        rhs = sin_composed(h, n - 1)[n - 1]
        for j in range(1, n):
            rhs = add(rhs, scale(deriv(h[n - j]), G(-nu[j])))
        constant = rhs.get(0, ZERO)
        assert constant.im == 0
        nu[n] = constant.re
        rhs = add(rhs, {0: -constant})
        h[n] = integrate_zero_mean(rhs)
        for k, v in h[n].items():
            assert h[n].get(-k, ZERO) == v.conj()

    sin_h = sin_composed(h, degree)
    left = pmul([{0: ONE}] + [deriv(h[n]) for n in range(1, degree + 1)],
                [{0: G(q)} if q else {} for q in nu], degree)
    right = [{0: ONE}] + sin_h[:degree]
    residuals = [add(a, scale(b, G(Q(-1)))) for a, b in zip(left, right)]
    assert all(not a for a in residuals)
    # nu^2 = 1-r^2 and nu(0)=1 characterize sqrt(1-r^2).
    for n in range(degree + 1):
        square_coeff = sum((nu[j] * nu[n-j] for j in range(n+1)), Q(0))
        assert square_coeff == (Q(1) if n == 0 else Q(-1) if n == 2 else Q(0))
    assert h[1] == {1: G(Q(-1, 2)), -1: G(Q(-1, 2))}
    assert h[2] == {2: G(Q(0), Q(1, 8)), -2: G(Q(0), Q(-1, 8))}
    assert h[3] == {1: G(Q(-1, 8)), -1: G(Q(-1, 8)),
                    3: G(Q(1, 24)), -3: G(Q(1, 24))}
    return {
        "degree": degree,
        "all_conjugacy_residual_coefficients_zero": True,
        "frequency_square_identity_verified": True,
        "reality_and_zero_mean_verified": True,
        "frequency_coefficients": [str(q) for q in nu],
        "first_three_conjugacy_Fourier_coefficients": [
            {str(k): str(v) for k, v in sorted(h[n].items())} for n in range(1, 4)
        ],
    }


def rank_two_support_check() -> dict:
    # C(n,m) is the coefficient at t^(n*omega+m) of (1+t+t^omega)^(-1).
    def coefficient(n: int, m: int) -> int:
        return 0 if n < 0 or m < 0 else (-1)**(n+m) * comb(n+m, n)
    tests = 0
    for n in range(9):
        for m in range(13):
            result = coefficient(n, m) + coefficient(n-1, m) + coefficient(n, m-1)
            assert result == int(n == 0 and m == 0)
            tests += 1
    # Three strata for the frequency vector (1,t,t^omega).
    counts = [0, 0, 0]
    for a in range(-5, 6):
        for b in range(-5, 6):
            for c in range(-5, 6):
                if (a, b, c) == (0, 0, 0):
                    continue
                j = 0 if a else 1 if b else 2
                leading = [a, b, c][j]
                assert leading != 0 and abs(leading) >= 1
                counts[j] += 1
    return {"coefficient_recurrences_checked": tests,
            "all_recurrences_pass": True,
            "integer_modes_checked": sum(counts),
            "stratum_counts": counts}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=Path("verification.json"))
    args = parser.parse_args()
    report = {"arithmetic": "Exact rational Gaussian arithmetic; no floating point.",
              "scope": "Finite algebraic checks only; not a machine proof of the article.",
              "circle": circle_check(),
              "rank_two_support": rank_two_support_check()}
    args.output.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(report, indent=2))

if __name__ == "__main__":
    main()
