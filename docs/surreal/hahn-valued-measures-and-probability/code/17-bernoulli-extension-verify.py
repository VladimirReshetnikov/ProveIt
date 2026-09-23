#!/usr/bin/env python3
"""Exact finite checks supporting the accompanying research manuscript.

Python 3.9+, standard library only. These checks verify finite identities,
not the infinite-dimensional theorems, originality, or formal correctness.
"""
from __future__ import annotations

from collections import Counter
from fractions import Fraction as F
from itertools import product
from pathlib import Path
import json
import random

ROOT = Path(__file__).resolve().parents[1]
COUNTS: Counter[str] = Counter()
ZERO = (0, 0)


def check(condition: bool, category: str) -> None:
    if not condition:
        raise AssertionError(f"Failed check in {category}, after {dict(COUNTS)}")
    COUNTS[category] += 1


def add(poly, exponent, value):
    if value:
        poly[exponent] = poly.get(exponent, F(0)) + value
        if not poly[exponent]:
            del poly[exponent]


def multiply(p, q):
    out = {}
    for x, a in p.items():
        for y, b in q.items():
            add(out, (x[0] + y[0], x[1] + y[1]), a * b)
    return out


def total(polys):
    out = {}
    for p in polys:
        for exponent, value in p.items():
            add(out, exponent, value)
    return out


def atom_weight(ps, bits):
    ans = F(1)
    for p, bit in zip(ps, bits):
        ans *= p if bit else 1 - p
    return ans


def atom_poly(ps, rows, bits, density=False):
    ans = {ZERO: F(1)}
    for p, row, bit in zip(ps, rows, bits):
        if density:
            y = (F(bit) - p) / (p * (1 - p))
            fac = {ZERO: F(1)}
            for exponent, a in row.items():
                add(fac, exponent, a * y)
        else:
            fac = {ZERO: p if bit else 1 - p}
            for exponent, a in row.items():
                add(fac, exponent, a if bit else -a)
        ans = multiply(ans, fac)
    return ans


def finite_product_checks(rng):
    exponents = [(0, 1), (0, 2), (1, 0)]
    for case in range(36):
        n = 1 + case % 6
        ps = [F(rng.randint(1, 8), 9) for _ in range(n)]
        rows = [dict(zip(exponents, (F(rng.randint(-3, 3), 7)
                                    for _ in exponents))) for _ in range(n)]
        masses = {}
        for bits in product((0, 1), repeat=n):
            direct = atom_poly(ps, rows, bits)
            density = atom_poly(ps, rows, bits, density=True)
            p0 = atom_weight(ps, bits)
            check(direct == {e: p0 * v for e, v in density.items()},
                  "finite_density_identity")
            masses[bits] = direct
        check(total(masses.values()) == {ZERO: F(1)}, "normalization")
        for k in range(n):
            for prefix in product((0, 1), repeat=k):
                marginalized = total(v for bits, v in masses.items()
                                     if bits[:k] == prefix)
                check(marginalized == atom_poly(ps[:k], rows[:k], prefix),
                      "marginalization")
        for j in range(n):
            moment = total(v for bits, v in masses.items() if bits[j])
            target = {ZERO: ps[j]}
            for e, a in rows[j].items():
                add(target, e, a)
            check(moment == target, "coordinate_marginals")
        for j in range(n):
            for k in range(j + 1, n):
                moment = total(v for bits, v in masses.items() if bits[j] and bits[k])
                targets = []
                for index in (j, k):
                    target = {ZERO: ps[index]}
                    for e, a in rows[index].items():
                        add(target, e, a)
                    targets.append(target)
                check(moment == multiply(*targets), "two_coordinate_independence")


def scalar_checks(rng):
    for _ in range(350):
        p = F(rng.randint(1, 31), 32)
        q, w = 1 - p, p * (1 - p)
        a = F(rng.randint(-25, 25), rng.randint(1, 17))
        ys = (-1 / q, 1 / p)
        check(q * ys[0] + p * ys[1] == 0, "score_mean")
        check(q * ys[0]**2 + p * ys[1]**2 == 1 / w, "score_variance")
        check(q * abs(a * ys[0]) + p * abs(a * ys[1]) == 2 * abs(a),
              "score_absolute_moment")
        check(a * (ys[1] - ys[0]) == a / w, "symmetrized_amplitude")
        b = F(rng.randint(-25, 25), rng.randint(1, 17))
        c = a - b
        phi = min(abs(a), a*a / w)
        check(phi <= 2 * abs(b) + 4 * c*c / w, "sum_space_modular_bound")
        huber = a*a / (w + abs(a))
        check(huber <= phi <= 2 * huber, "smooth_modular_equivalence")


def khintchine_checks(rng):
    for case in range(72):
        n = 1 + case % 7
        a = [F(rng.randint(-5, 5), 3) for _ in range(n)]
        vals = [sum(x * s for x, s in zip(a, signs))
                for signs in product((-1, 1), repeat=n)]
        m1 = sum(map(abs, vals), F(0)) / 2**n
        m2 = sum((x*x for x in vals), F(0)) / 2**n
        m4 = sum((x**4 for x in vals), F(0)) / 2**n
        v = sum((x*x for x in a), F(0))
        check(m2 == v, "rademacher_second_moment")
        check(m4 <= 3*v*v, "rademacher_fourth_moment")
        check(3*m1*m1 >= v, "rademacher_L1_lower_bound")


def first_chaos_checks(rng):
    for case in range(30):
        n = 1 + case % 5
        ps = [F(rng.randint(1, 15), 16) for _ in range(n)]
        aa = [F(rng.randint(-7, 7), 9) for _ in range(n)]
        values = []
        for bits in product((0, 1), repeat=n):
            prob = atom_weight(ps, bits)
            score = sum(a * (F(bit) - p) / (p * (1-p))
                        for a, bit, p in zip(aa, bits, ps))
            values.append((score, prob))
        second = sum((s*s*prob for s, prob in values), F(0))
        expected = sum((a*a/(p*(1-p)) for a,p in zip(aa,ps)), F(0))
        check(second == expected, "first_chaos_orthogonality")
        m1 = sum((abs(s)*prob for s, prob in values), F(0))
        sym = sum((abs(s-t)*u*v for s,u in values for t,v in values), F(0))
        check(sym <= 2*m1, "symmetrization_upper_bound")
        big = [i for i,(a,p) in enumerate(zip(aa,ps)) if abs(a) > p*(1-p)]
        small = [i for i in range(n) if i not in big]
        b = 2 * sum((abs(aa[i]) for i in big), F(0))
        c2 = sum((aa[i]**2/(ps[i]*(1-ps[i])) for i in small), F(0))
        check(m1 <= b or (m1-b)**2 <= c2, "split_first_chaos_upper_bound")


def phase_checks():
    for r in (F(j, 4) for j in range(13)):
        for s in (F(j, 8) for j in range(1, 33)):
            from_regimes = (s > 1) if s < r else (2*s-r > 1)
            from_threshold = s > min(F(1), (r+1)/2)
            check(from_regimes == from_threshold, "power_law_phase_boundary")


def main():
    rng = random.Random(22092026)
    finite_product_checks(rng)
    scalar_checks(rng)
    khintchine_checks(rng)
    first_chaos_checks(rng)
    phase_checks()
    result = {
        "status": "PASS",
        "arithmetic": "exact rational (fractions.Fraction)",
        "seed": 22092026,
        "assertions": sum(COUNTS.values()),
        "by_category": dict(sorted(COUNTS.items())),
        "scope": "Finite algebraic identities and inequalities only. No infinite theorem, originality, or Lean verification is certified."
    }
    dest = ROOT / "data" / "verification_results.json"
    dest.parent.mkdir(parents=True, exist_ok=True)
    dest.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()
