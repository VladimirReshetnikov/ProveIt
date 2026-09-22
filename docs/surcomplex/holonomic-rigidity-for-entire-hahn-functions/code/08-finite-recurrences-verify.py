#!/usr/bin/env python3
"""Finite exact checks accompanying 'Finite Recurrences versus Surreal Scale'.

Python 3.9+, standard library only. These checks do not establish an infinite
support theorem, cofinality statement, or absence of an annihilating operator.
Run: python code/verify.py --output data/verification.txt
"""
from __future__ import annotations

import argparse
from collections import defaultdict
from fractions import Fraction as F
from pathlib import Path
from random import Random
from typing import Dict, Iterable, List, Sequence, Tuple

Poly = Dict[int, F]
Value = Tuple[int, ...]
COUNTS: Dict[str, int] = defaultdict(int)


def check(group: str, condition: bool, detail: str) -> None:
    if not condition:
        raise AssertionError(f"{group}: {detail}")
    COUNTS[group] += 1


def falling(n: int, r: int) -> int:
    ans = 1
    for j in range(r):
        ans *= n - j
    return ans


def clean(p: Poly) -> Poly:
    return {k: v for k, v in p.items() if v}


def add(*polys: Poly) -> Poly:
    out: Poly = defaultdict(F)
    for p in polys:
        for k, v in p.items():
            out[k] += v
    return clean(out)


def mul(p: Poly, q: Poly) -> Poly:
    out: Poly = defaultdict(F)
    for k, v in p.items():
        for j, w in q.items():
            out[k + j] += v * w
    return clean(out)


def scale(p: Poly, c: F, shift: int = 0) -> Poly:
    return clean({k + shift: c * v for k, v in p.items()})


def power(p: Poly, n: int) -> Poly:
    if n < 0:
        raise ValueError("Only nonnegative finite polynomial powers are allowed")
    ans: Poly = {0: F(1)}
    while n:
        if n & 1:
            ans = mul(ans, p)
        p = mul(p, p)
        n >>= 1
    return ans


def derivative(p: Poly, r: int) -> Poly:
    return {k - r: c * falling(k, r) for k, c in p.items() if k >= r}


def valuation(p: Poly) -> int:
    if not p:
        raise ValueError("Valuation of zero requested in a finite check")
    return min(p)


def vadd(a: Value, b: Value) -> Value:
    if len(a) != len(b):
        raise ValueError("Ordered-group coordinate lengths differ")
    return tuple(x + y for x, y in zip(a, b))


def vmul(n: int, a: Value) -> Value:
    return tuple(n * x for x in a)


def differential_checks(rng: Random) -> None:
    for trial in range(24):
        rmax, m = 4, 4
        a = [F(rng.randint(-5, 5), rng.randint(1, 5)) for _ in range(45)]
        f = {i: x for i, x in enumerate(a) if x}
        coeff = {(r, k): F(rng.randint(-3, 3))
                 for r in range(rmax + 1) for k in range(m + 1)}
        direct: Poly = {}
        for (r, k), c in coeff.items():
            direct = add(direct, scale(derivative(f, r), c, k))
        for n in range(m, 31):
            recurrence = F(0)
            for s in range(-m, rmax + 1):
                q_s = sum((c * falling(n + s, r)
                           for (r, k), c in coeff.items() if r - k == s), F(0))
                recurrence += q_s * a[n + s]
            check("differential coefficient conversion",
                  direct.get(n, F(0)) == recurrence, f"trial {trial}, n={n}")


def dilation_checks(rng: Random) -> None:
    for trial in range(16):
        q = F(3, 2) if trial % 2 else F(-2)
        m, rmax = 4, 3
        a = [F(rng.randint(-5, 5)) for _ in range(35)]
        p = {(ell, k): F(rng.randint(-2, 2))
             for ell in range(rmax + 1) for k in range(m + 1)}
        direct: Poly = {}
        for (ell, k), c in p.items():
            dilated = {i: a_i * q ** (ell * i)
                       for i, a_i in enumerate(a) if a_i}
            direct = add(direct, scale(dilated, c, k))
        for n in range(21):
            rhs = F(0)
            for j in range(m + 1):
                p_j = sum((p[ell, m - j] * q ** (ell * j) *
                           (q ** n) ** ell for ell in range(rmax + 1)), F(0))
                rhs += p_j * a[n + j]
            check("dilation coefficient conversion", direct.get(n + m, F(0)) == rhs,
                  f"trial {trial}, n={n}")


def mixed_checks(rng: Random) -> None:
    for trial in range(12):
        q = F(2) if trial % 2 else F(-3, 2)
        rmax, ellmax, m = 3, 2, 3
        a = [F(rng.randint(-4, 4), rng.randint(1, 3)) for _ in range(40)]
        coefficients = {(r, ell, k): F(rng.randint(-2, 2))
                        for r in range(rmax + 1)
                        for ell in range(ellmax + 1) for k in range(m + 1)}
        direct: Poly = {}
        for (r, ell, k), c in coefficients.items():
            dilated = {i: a_i * q ** (ell * i)
                       for i, a_i in enumerate(a) if a_i}
            direct = add(direct, scale(derivative(dilated, r), c, k))
        for n in range(m, 26):
            rhs = F(0)
            for s in range(-m, rmax + 1):
                p_s = sum((c * q ** (ell * s) * falling(n + s, r) *
                           (q ** n) ** ell
                           for (r, ell, k), c in coefficients.items()
                           if r - k == s), F(0))
                rhs += p_s * a[n + s]
            check("mixed coefficient conversion", direct.get(n, F(0)) == rhs,
                  f"trial {trial}, n={n}")


def unit_checks() -> None:
    one: Poly = {0: F(1)}
    minus_one: Poly = {0: F(-1)}
    for n in range(1, 81):
        qn = power({0: F(-1), 1: F(-1)}, n)
        p1 = add(qn, minus_one)
        expected = 0 if n % 2 else 1
        check("unit residue and cancellation", valuation(p1) == expected,
              f"q=-(1+t), P=X-1, n={n}")
        check("unit residue and cancellation",
              p1[expected] == (-2 if n % 2 else n), f"leading coefficient, n={n}")
        p2 = add(mul(p1, p1), scale(add(qn, one), F(1), 3))
        expected2 = 0 if n % 2 else 2
        check("unit residue and cancellation", valuation(p2) == expected2,
              f"P=(X-1)^2+t^3(X+1), n={n}")
        check("unit residue and cancellation", p2[expected2] == (4 if n % 2 else n*n),
              f"quadratic leading coefficient, n={n}")
        pn = power({0: F(1), 1: F(1)}, n)
        exception = add(pn, {0: F(-1), 1: F(-7)})
        check("unit residue and cancellation", valuation(exception) == (2 if n == 7 else 1),
              f"finite exceptional index, n={n}")


def theta_checks() -> None:
    tri = lambda n: n * (n - 1) // 2
    for n in range(151):
        terms: Poly = defaultdict(F)
        if n >= 1:
            terms[1 + tri(n-1) + 2*(n-1)] += 1
            terms[tri(n-1) + n-1] -= 1
        terms[tri(n) + n] -= 1
        terms[tri(n)] += 1
        check("theta functional identities", not clean(terms), f"positive-shift identity, n={n}")
        inverse: Poly = defaultdict(F)
        if n >= 1:
            inverse[1 - tri(n-1)] += 1
            inverse[n+1 - tri(n-1)] -= 1
        inverse[n - tri(n)] -= 1
        inverse[2*n - tri(n)] += 1
        check("theta functional identities", not clean(inverse), f"inverse-q identity, n={n}")
        if n >= 1:
            check("theta functional identities", tri(n) == tri(n-1) + n-1,
                  f"inhomogeneous identity, n={n}")
    # Exact finite rank-one samples of the quadratic cofinal estimate.
    for alpha in range(-12, 13):
        for target in [-30, 0, 17, 100]:
            n = 100 + 4 * abs(alpha) + abs(target)
            check("theta functional identities", tri(n) + n * alpha > target,
                  f"quadratic bound sample alpha={alpha}, target={target}")


def ordered_group_checks() -> None:
    cases: List[Tuple[Value, List[Value], int, int]] = [
        ((0, 1), [(0, 0), (-1, 0)], 1, 0),
        ((0, 1), [(-1, 0), (0, 0)], 0, 0),
        ((0, 1), [(0, 0), (0, -7), (0, 4)], 0, 8),
        ((1, 0), [(0, 0), (-1, 0), (-2, -3)], 0, 4),
        ((-1, 0), [(3, 2), (-8, 9), (1, -2)], 2, 20),
    ]
    for lam, betas, expected, start in cases:
        for n in range(start, start + 80):
            candidates = [vadd(beta, vmul(k*n, lam)) for k, beta in enumerate(betas)]
            check("higher-rank valuations", candidates[expected] == min(candidates),
                  f"affine winner {lam}, n={n}")
            check("higher-rank valuations", candidates.count(min(candidates)) == 1,
                  f"unique affine winner {lam}, n={n}")
    size = 104
    zero = (0,) * size
    def e(n: int) -> Value:
        a = [0] * size
        a[-1-n] = 1
        return tuple(a)
    H = (1,) + (0,) * (size - 1)
    prior = None
    for n in range(101):
        val = vadd(e(n), vmul(-n, H))
        if prior is not None:
            check("higher-rank valuations", val < prior,
                  f"finite prefix of exterior descending support, n={n}")
        prior = val
    alpha = vadd(vmul(-7, e(5)), vmul(4, e(2)))
    target = vmul(120, e(8))
    for n in range(9, 101):
        check("higher-rank valuations", vadd(e(n), vmul(n, alpha)) > target,
              f"cofinal-series finite sample, n={n}")
    for n in range(1, 151):
        check("higher-rank valuations", (0, n) < (1, 0), f"n epsilon < H, n={n}")
        check("higher-rank valuations", (0, n) > zero[:2], f"positive lower scale, n={n}")


def airy_checks() -> None:
    a = [F(0) for _ in range(153)]
    a[0] = 1
    for n in range(150):
        a[n+3] = a[n] / F((n+3)*(n+2))
    for n in range(150):
        check("sparse Airy recurrence", F((n+3)*(n+2))*a[n+3] == a[n], f"n={n}")
    indices = [i for i, ai in enumerate(a) if ai]
    check("sparse Airy recurrence", indices == list(range(0, 153, 3)), "support class")
    for i, j in zip(indices, indices[1:]):
        check("sparse Airy recurrence", -j < -i, f"escape edge {i}->{j}")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True,
                        help="Path for the finite verification report")
    args = parser.parse_args()
    rng = Random(20260922)
    differential_checks(rng)
    dilation_checks(rng)
    mixed_checks(rng)
    unit_checks()
    theta_checks()
    ordered_group_checks()
    airy_checks()
    lines = ["FINITE RECURRENCES VERSUS SURREAL SCALE", "Exact finite verification report", "",
             "Arithmetic: integers and fractions.Fraction; no floating point.",
             "Pseudo-random seed for finite operator inputs: 20260922.", ""]
    for name, count in COUNTS.items():
        lines.append(f"PASS  {count:5d}  {name}")
    lines.extend(["", f"TOTAL: {sum(COUNTS.values())} checks passed; 0 failed.", "",
                  "These finite checks do NOT prove any infinite-support, cofinality,",
                  "nonexistence, generic-line, or novelty claim. No infinite Hahn family",
                  "is evaluated by this program. The mathematical proofs are in article.tex.",
                  "No Lean or other proof-assistant verification is claimed."])
    report = "\n".join(lines) + "\n"
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(report, encoding="utf-8")
    print(report, end="")


if __name__ == "__main__":
    main()
