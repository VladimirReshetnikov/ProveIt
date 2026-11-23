#!/usr/bin/env python3
"""Reproduce finite exact-arithmetic checks; not a proof certificate checker."""
import itertools
import json
import random
from fractions import Fraction
from math import gcd, isqrt
from diophantine_algorithms import (
    bounded_norm_pair, continuants, dirichlet_cf, dirichlet_grid,
    pell_exponent, pell_norm_collision, pell_power,
    pythagorean_parameters, rational_cf, simultaneous_grid,
)


def main():
    counts = {}
    count = 0
    for length in range(1, 6):
        for a0 in range(4):
            for tail in itertools.product(range(1, 4), repeat=length - 1):
                cs = (a0,) + tail
                conv = continuants(cs)
                value = Fraction(cs[-1])
                for a in reversed(cs[:-1]):
                    value = a + 1 / value
                assert Fraction(*conv[-1]) == value
                pp, qp = 1, 0
                for i, (p, q) in enumerate(conv):
                    assert p * qp - pp * q == (-1) ** (i + 1)
                    assert gcd(p, q) == 1 and q > 0
                    if i >= 2:
                        assert q >= 2 * conv[i - 2][1]
                    pp, qp = p, q
                count += 1
    counts["continued_fraction_lists"] = count

    count = 0
    for a in range(-20, 41):
        for b in range(1, 21):
            alpha = Fraction(a, b)
            for Q in range(1, 11):
                p, q = dirichlet_grid(alpha, Q)
                assert 1 <= q <= Q and abs(q * alpha - p) < Fraction(1, Q)
                if a >= 0:
                    p, q = dirichlet_cf(a, b, Q)
                    assert 1 <= q <= Q and abs(q * alpha - p) < Fraction(1, Q)
                count += 1
            if a >= 0:
                cs = rational_cf(a, b)
                assert len(cs) <= b + 1
                assert len(cs) == 1 or cs[-1] >= 2
                assert Fraction(*continuants(cs)[-1]) == alpha
    counts["rational_dirichlet_cases"] = count

    rng = random.Random(20261122)
    count = 0
    for d in range(1, 4):
        for N in range(1, 6):
            for _ in range(30):
                alphas = [Fraction(rng.randint(-30, 30), rng.randint(1, 30))
                          for _ in range(d)]
                ps, q = simultaneous_grid(alphas, N)
                assert 1 <= q <= N ** d
                assert all(abs(q * a - p) < Fraction(1, N)
                           for a, p in zip(alphas, ps))
                count += 1
    counts["simultaneous_grid_cases"] = count

    count = 0
    for D in range(2, 61):
        if isqrt(D) ** 2 == D:
            continue
        for Y in range(21):
            bounded_norm_pair(D, Y)
            count += 1
        for Y in range(3):
            bounded_norm_pair(D, Y, use_grid=True)
            count += 1
    counts["bounded_norm_cases"] = count

    collisions = []
    for D in range(2, 101):
        if isqrt(D) ** 2 != D:
            collisions.append(pell_norm_collision(D))
    counts["pell_norm_collisions"] = len(collisions)

    fundamentals = {
        2: (3, 2), 3: (2, 1), 5: (9, 4), 6: (5, 2),
        7: (8, 3), 10: (19, 6), 13: (649, 180),
    }
    count = 0
    for D, fundamental in fundamentals.items():
        for n in range(9):
            target = pell_power(D, fundamental, n)
            assert pell_exponent(D, fundamental, target) == n
            count += 1
    counts["pell_power_descent_cases"] = count

    count = 0
    for m in range(2, 41):
        for n in range(1, m):
            if gcd(m, n) == 1 and (m - n) % 2 == 1:
                for scale in (1, 2, 7):
                    a, b, c = (scale * (m * m - n * n),
                               scale * 2 * m * n,
                               scale * (m * m + n * n))
                    assert pythagorean_parameters(a, b, c) == (
                        scale, False, m, n)
                    assert pythagorean_parameters(b, a, c) == (
                        scale, True, m, n)
                    count += 2
    counts["pythagorean_reconstructions"] = count

    selected = [{key: row[key] for key in
                 ("D", "x", "y", "common_norm", "earlier_index", "later_index")}
                for row in collisions if row["D"] in (2, 3, 5, 13, 61)]
    summary = {
        "status": "all finite checks passed",
        "scope": "Exact finite regression checks, not a Lean or iPRA derivation.",
        "seed": 20261122,
        "counts": counts,
        "total_cases": sum(counts.values()),
        "pell_common_norm_signs_exercised":
            sorted(set(1 if row["common_norm"] > 0 else -1 for row in collisions)),
        "maximum_pell_collision_index":
            max(row["later_index"] for row in collisions),
        "selected_pell_certificates": selected,
    }
    print(json.dumps(summary, indent=2))


if __name__ == "__main__":
    main()
