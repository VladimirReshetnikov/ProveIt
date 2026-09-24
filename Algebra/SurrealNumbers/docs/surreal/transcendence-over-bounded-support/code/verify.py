#!/usr/bin/env python3
"""Exact finite regression tests for article.tex. Not a formal theorem proof.

Checks sparse rational convolution, coset/functional descent, polynomial support
bands, coding, integer grids, gap inequalities and explicit parameter families.
Python 3.10+; no third-party dependencies or network access.
"""
from __future__ import annotations
import argparse
from collections import Counter
from fractions import Fraction as F
from itertools import product
import json
from math import comb, factorial
from pathlib import Path
import platform
import random
from coefficients import pair, unpair, positions, code_coefficient, encode_table

Series = dict[F, F]
Poly = dict[tuple[int, ...], Series]
SEED = 20260922
rng = random.Random(SEED)
counts: Counter[str] = Counter()


def check(group: str, condition: bool, description: str) -> None:
    if not condition:
        raise AssertionError(f"{group}: {description}")
    counts[group] += 1


def clean(a: Series) -> Series:
    return {F(e): F(c) for e, c in a.items() if c}


def add(a: Series, b: Series) -> Series:
    c = dict(a)
    for e, x in b.items():
        c[e] = c.get(e, F(0)) + x
    return clean(c)


def scale(a: Series, c: F | int) -> Series:
    return clean({e: x * c for e, x in a.items()})


def shift(a: Series, x: F | int) -> Series:
    return {e + F(x): c for e, c in a.items()}


def mul(a: Series, b: Series) -> Series:
    out: Series = {}
    for e, x in a.items():
        for f, y in b.items():
            out[e + f] = out.get(e + f, F(0)) + x * y
    return clean(out)


def power(a: Series, n: int) -> Series:
    out = {F(0): F(1)}
    for _ in range(n):
        out = mul(out, a)
    return out


def evaluate(p: Poly, xs: list[Series]) -> Series:
    out: Series = {}
    for nu, coeff in p.items():
        term = dict(coeff)
        for x, k in zip(xs, nu):
            term = mul(term, power(x, k))
        out = add(out, term)
    return out


def coset(a: Series, r: F) -> Series:
    return {e-r: c for e, c in a.items() if (e-r).denominator == 1}


def random_series(denom: int = 1, low: int = -4, high: int = 6,
                  size: int = 5) -> Series:
    out: Series = {}
    for _ in range(size):
        e = F(rng.randint(low, high), denom)
        out[e] = out.get(e, F(0)) + F(rng.randint(-5, 5), rng.randint(1, 4))
    return clean(out)


def auxiliary(p: Poly, xs: list[Series], cs: list[int]) -> list[Series]:
    d = max(map(sum, p))
    out: list[Series] = [{} for _ in range(d + 1)]
    for nu, coeff in p.items():
        for mu in product(*(range(n + 1) for n in nu)):
            k = sum(mu)
            term = dict(coeff)
            fac = 1
            for n, h, x, c in zip(nu, mu, xs, cs):
                fac *= comb(n, h) * c**h
                term = mul(term, power(x, n-h))
            out[k] = add(out[k], scale(term, fac))
    return out


def test_pairing_coding() -> None:
    for a in range(20):
        for b in range(20):
            check("pairing", unpair(pair(a, b)) == (a, b), "Cantor inverse")
    for _ in range(80):
        universe = rng.randint(2, 5)
        members = rng.sample(range(1 << universe), rng.randint(2, min(5, 1 << universe)))
        target = [rng.randint(1, 7) for _ in members]
        s_mask = 0
        for i, a in enumerate(members):
            for b in members[:i]:
                xor = a ^ b
                s_mask |= xor & -xor
        s = positions(s_mask)
        restrictions = [sum(((a >> k) & 1) << j for j, k in enumerate(s)) for a in members]
        check("finite_pattern_coding", len(set(restrictions)) == len(members),
              "finite symmetric-difference separation")
        table = [1] * (1 << len(s))
        for r, q in zip(restrictions, target):
            table[r] = q
        seen = []
        for repetition in range(4):
            n = encode_table(s_mask, table, repetition)
            seen.append(n)
            for a, q in zip(members, target):
                actual = code_coefficient(lambda k, a=a: bool((a >> k) & 1), n)
                check("finite_pattern_coding", actual == q, "prescribed table entry")
        check("finite_pattern_coding", len(set(seen)) == 4, "distinct repetition indices")


def test_projections() -> None:
    for _ in range(100):
        denom = rng.randint(2, 7)
        f = random_series(1)
        b = random_series(denom)
        r = F(rng.randrange(denom), denom)
        check("coset_projection", coset(mul(f, b), r) == mul(f, coset(b, r)),
              "pi_r(f*b)=f*pi_r(b)")
        # L=Q(i), represented by two Q-series; lambda(z)=a*Re(z)+b*Im(z).
        re, im = random_series(denom), random_series(denom)
        a, beta = F(rng.randint(-3, 3)), F(rng.randint(-3, 3))
        left = coset(add(scale(mul(f, re), a), scale(mul(f, im), beta)), r)
        right = mul(f, add(scale(coset(re, r), a), scale(coset(im, r), beta)))
        check("coefficient_functional", left == right,
              "combined coset and Q-linear coefficient functional")


def test_bands() -> None:
    for case in range(36):
        m, d, n = rng.randint(1, 3), rng.randint(1, 3), 6
        p: Poly = {}
        for nu in product(range(d + 1), repeat=m):
            if sum(nu) <= d and rng.random() < .5:
                c = random_series(2, -6, 8, 3)
                if c:
                    p[nu] = c
        # Ensure a nonzero top homogeneous part with positive coefficients.
        for nu in list(p):
            if sum(nu) == d:
                p[nu] = {e: abs(c) for e, c in p[nu].items()}
        top = (d,) + (0,) * (m - 1)
        p[top] = add(p.get(top, {}), {F(0): F(1)})
        support = [e for c in p.values() for e in c]
        lo, hi = min(support), max(support)
        a, b, next_a = factorial(n), factorial(n-1), factorial(n+1)
        xs = [{F(factorial(k)): F((j+2)**k) for k in range(2, n)} for j in range(m)]
        cs = [(j+2)**n for j in range(m)]
        ts = [add(x, {F(a): F(c)}) for x, c in zip(xs, cs)]
        ys = [add(t, {F(next_a): F((j+2)**(n+1)),
                      F(factorial(n+2)): F((j+2)**(n+2))}) for j, t in enumerate(ts)]
        qs = auxiliary(p, xs, cs)
        rebuilt: Series = {}
        for k, q in enumerate(qs):
            rebuilt = add(rebuilt, shift(q, k*a))
            check("support_bands", all(lo <= e <= hi+d*b for e in q), "Q_k support bound")
        pt = evaluate(p, ts)
        check("auxiliary_polynomial", rebuilt == pt, "finite binomial expansion")
        pd = {nu: c for nu, c in p.items() if sum(nu) == d}
        top_value = evaluate(pd, [{F(0): F(c)} for c in cs])
        check("auxiliary_polynomial", qs[d] == top_value and bool(top_value),
              "top coefficient equals nonzero P_d(c)")
        check("support_bands", a > d*b+hi-lo and next_a > d*a+hi-lo,
              "two strict gaps")
        check("support_bands", bool(pt), "separated highest band survives")
        check("support_bands", all(lo <= e <= hi+d*a for e in pt), "truncation support bound")
        full = evaluate(p, ys)
        tail = add(full, scale(pt, -1))
        check("support_bands", all(e >= lo+next_a for e in tail), "tail valuation lower bound")
        check("support_bands", bool(full), "tail cannot cancel bounded truncation")


def test_grids_parameters() -> None:
    primes = [2, 3, 5]
    for d in range(1, 6):
        mons = [nu for nu in product(range(d+1), repeat=3) if sum(nu) == d]
        qs = [2**nu[0]*3**nu[1]*5**nu[2] for nu in mons]
        check("prime_parameter_family", len(set(qs)) == len(mons),
              "multiplicatively independent monomial parameters")
        for n in range(2, 7):
            coeff = [rng.randint(-4, 4) for _ in mons]
            direct = sum(c * (2**n)**nu[0] * (3**n)**nu[1] * (5**n)**nu[2]
                         for c, nu in zip(coeff, mons))
            exponential = sum(c*q**n for c, q in zip(coeff, qs))
            check("prime_parameter_family", direct == exponential, "P_d(q^n) identity")
    for _ in range(60):
        m, d = rng.randint(1, 3), rng.randint(1, 3)
        p = {nu: {F(0): F(c)} for nu in product(range(d+1), repeat=m)
             if sum(nu) <= d and (c := rng.randint(-3, 3)) != 0}
        if not p:
            p[(0,)*m] = {F(0): F(1)}
        witness = any(evaluate(p, [{F(0): F(q)} for q in point])
                      for point in product(range(1, d+2), repeat=m))
        check("integer_grid", witness, "finite degree-bounded product grid detects P")
    for d in range(1, 13):
        for w in range(0, 31):
            n = d + 8
            check("factorial_gaps", factorial(n) > d*factorial(n-1)+w,
                  "factorial previous gap")
            check("factorial_gaps", factorial(n+1) > d*factorial(n)+w,
                  "factorial next gap")


def test_characters_geometric() -> None:
    for _ in range(50):
        f, g = random_series(2), random_series(2)
        def twist(a: Series) -> Series:
            return {e: c * (-1 if int(2*e) % 2 else 1) for e, c in a.items()}
        check("character_twist", twist(mul(f, g)) == mul(twist(f), twist(g)),
              "diagonal character on half-integer exponents is multiplicative")
    for n in range(1, 21):
        geom = {F(k): F(1) for k in range(n+1)}
        check("geometric_remainder", mul({F(0): F(1), F(1): F(-1)}, geom)
              == {F(0): F(1), F(n+1): F(-1)}, "exact finite geometric remainder")
        check("lexicographic_scale", (F(0), F(n)) < (F(1), F(0)),
              "lower-rank multiples bounded by the higher rank (finite sample only)")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=Path("verification.json"))
    args = parser.parse_args()
    test_pairing_coding()
    test_projections()
    test_bands()
    test_grids_parameters()
    test_characters_geometric()
    result = {
        "title": "Exact finite regression checks for bounded-support Hahn arithmetic",
        "seed": SEED,
        "python_version": platform.python_version(),
        "arithmetic": "exact integers and fractions.Fraction; no floating-point tests",
        "status": "PASS",
        "assertions": sum(counts.values()),
        "groups": dict(sorted(counts.items())),
        "scope": "Finite mechanism checks only; not a proof of transfinite summability, "
                 "cardinal independence, novelty, or the conditional ambient GCD input.",
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
