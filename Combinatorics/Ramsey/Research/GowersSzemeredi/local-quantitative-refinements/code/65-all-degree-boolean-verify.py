#!/usr/bin/env python3
"""Exact regression checks for Sharp Boolean Phase Integration in Every Degree.

Python 3.10+, standard library only. No floating-point arithmetic or optimizer.
Finite checks supplement, and do not replace, the all-dimensional proofs.
All failures are explicit exceptions, so `python3 -O` is supported.
"""
from __future__ import annotations

import argparse
from collections import Counter
from fractions import Fraction as Q
from functools import lru_cache
from itertools import combinations_with_replacement, product
from math import comb
from pathlib import Path
import json
import random
from typing import Sequence


def check(condition: bool, message: str) -> None:
    if not condition:
        raise RuntimeError(message)


@lru_cache(None)
def basis(n: int, d: int) -> tuple[tuple[int, ...], ...]:
    return tuple(combinations_with_replacement(range(n), d))


@lru_cache(None)
def indices(n: int, d: int) -> dict[tuple[int, ...], int]:
    return {a: i for i, a in enumerate(basis(n, d))}


def coefficient(n: int, d: int, mask: int, a: Sequence[int]) -> int:
    return (mask >> indices(n, d)[tuple(sorted(a))]) & 1


@lru_cache(None)
def contraction_rows(n: int, d: int, z: int) -> tuple[int, ...]:
    ix = indices(n, d)
    return tuple(sum(1 << ix[tuple(sorted(a + (i,)))]
                     for i in range(n) if (z >> i) & 1)
                 for a in basis(n, d - 1))


def contract(n: int, d: int, mask: int, z: int) -> int:
    return sum(((mask & row).bit_count() & 1) << j
               for j, row in enumerate(contraction_rows(n, d, z)))


def evaluate(n: int, d: int, mask: int, vectors: Sequence[int]) -> int:
    check(len(vectors) == d, "wrong tensor arity")
    for z in vectors:
        mask = contract(n, d, mask, z)
        d -= 1
    return mask


@lru_cache(None)
def support_groups(n: int, d: int) -> tuple[tuple[int, ...], ...]:
    groups: dict[tuple[int, ...], list[int]] = {}
    for j, a in enumerate(basis(n, d)):
        groups.setdefault(tuple(sorted(set(a))), []).append(j)
    return tuple(tuple(g) for g in groups.values())


def integrable(n: int, d: int, mask: int) -> bool:
    """Independent support-coefficient integration test."""
    return all(len({(mask >> j) & 1 for j in group}) == 1
               for group in support_groups(n, d))


def gf2_rank(rows: Sequence[int]) -> int:
    pivots: dict[int, int] = {}
    for row in rows:
        while row:
            p = row.bit_length() - 1
            if p in pivots:
                row ^= pivots[p]
            else:
                pivots[p] = row
                break
    return len(pivots)


@lru_cache(None)
def defect_entries(n: int, d: int) -> tuple[tuple[tuple[int, int], ...], ...]:
    """Rows of the frozen-slot defect map, before evaluating coefficients."""
    check(d >= 4, "frozen-slot radical requires d >= 4")
    ix = indices(n, d)
    result = []
    for a in range(n):
        for b in range(a + 1, n):
            for w in basis(n, d - 4):
                result.append(tuple((ix[tuple(sorted((a, a, b, z) + w))],
                                     ix[tuple(sorted((a, b, b, z) + w))])
                                    for z in range(n)))
    return tuple(result)


def defect_rows(n: int, d: int, mask: int) -> tuple[int, ...]:
    return tuple(sum((((mask >> a) ^ (mask >> b)) & 1) << j
                     for j, (a, b) in enumerate(row))
                 for row in defect_entries(n, d))


def cubic_rank(n: int, mask: int) -> int:
    return gf2_rank(tuple(sum((coefficient(n, 3, mask, (a, a, b)) ^
                               coefficient(n, 3, mask, (a, b, b))) << b
                              for b in range(n))
                         for a in range(n)))


def canonical(n: int, d: int, u: int, v: int) -> int:
    out = 0
    for j, a in enumerate(basis(n, d)):
        value = 0
        for i in range(d):
            term = (v >> a[i]) & 1
            for k in range(d):
                if k != i:
                    term &= (u >> a[k]) & 1
            value ^= term
        out |= value << j
    return out


def recover(n: int, d: int, mask: int, rows: Sequence[int]) -> tuple[int, int, int]:
    check(gf2_rank(rows) == 1, "recovery requires radical codimension one")
    u = next(row for row in rows if row)
    c = (u & -u).bit_length() - 1
    w = (c,) * (d - 3)
    v = sum((coefficient(n, d, mask, (j, j, c) + w) ^
             coefficient(n, d, mask, (j, c, c) + w)) << j
            for j in range(n))
    check(v not in (0, u), "reconstructed forms are not independent")
    residual = mask ^ canonical(n, d, u, v)
    check(integrable(n, d, residual), "reconstructed residual is not integrable")
    return u, v, residual


@lru_cache(None)
def constant_energy(n: int, d: int, mask: int) -> Q:
    """Exact contraction recurrence, independent of the energy bound."""
    if d == 1:
        return Q(int(mask == 0))
    return sum((constant_energy(n, d - 1, contract(n, d, mask, z))
                for z in range(1 << n)), Q()) / (1 << n)


def b(d: int) -> Q:
    return 1 - Q(d + 1, 1 << d)


def cap(n: int, d: int, mask: int) -> Q:
    if integrable(n, d, mask):
        return Q(1)
    if d == 3:
        return Q(1, 1 << (cubic_rank(n, mask) // 2))
    r = gf2_rank(defect_rows(n, d, mask))
    if r == 1:
        return b(d)
    return 1 - (1 - Q(1, 1 << r)) * Q(d, 1 << (d - 1))


def integrable_dimension(n: int, d: int) -> int:
    return sum(comb(n, j) for j in range(1, min(n, d) + 1))


def inspect_family(n: int, d: int, masks: Sequence[int], exhaustive: bool) -> dict:
    counts: Counter[int] = Counter()
    max_const = Q(0)
    recovery_count = 0
    for mask in masks:
        is_int = integrable(n, d, mask)
        if d == 3:
            r = cubic_rank(n, mask)
            check(r % 2 == 0, "odd alternating rank")
            check((r == 0) == is_int, "cubic integration disagreement")
        else:
            rows = defect_rows(n, d, mask)
            r = gf2_rank(rows)
            check((r == 0) == is_int, "integration/defect disagreement")
            # Independent support-coefficient test on every contraction.
            good = sum(integrable(n, d - 1, contract(n, d, mask, z))
                       for z in range(1 << n))
            check(good == 1 << (n - r), "wrong integrable-slice count")
            if r == 1:
                recover(n, d, mask, rows)
                recovery_count += 1
        counts[r] += 1
        value = constant_energy(n, d, mask)
        check(value <= cap(n, d, mask), "constant exceeds proved tensor cap")
        if not is_int:
            max_const = max(max_const, value)
            check(value <= b(d), "constant exceeds universal cap")
    if exhaustive:
        int_count = 1 << integrable_dimension(n, d)
        check(counts[0] == int_count, "wrong integrable tensor count")
        if d == 3:
            classes = ((1 << n) - 1) * ((1 << n) - 2) // 6
            check(counts[2] == classes * int_count, "wrong cubic endpoint count")
        else:
            classes = ((1 << n) - 1) * ((1 << (n - 1)) - 1)
            check(counts[1] == classes * int_count, "wrong endpoint count")
        check(max_const == b(d), "canonical lower bound missing from census")
    return {"dimension": n, "degree": d, "exhaustive": exhaustive,
            "tensors": len(masks), "rank_counts": dict(sorted(counts.items())),
            "rank_meaning": "alternating rank" if d == 3 else "defect-radical codimension",
            "canonical_recoveries": recovery_count,
            "maximum_nonintegrable_constant_energy": str(max_const)}


# Exact Gaussian rationals, represented as pairs of Fractions.
G = tuple[Q, Q]
ZERO: G = (Q(0), Q(0))
ONE: G = (Q(1), Q(0))


def add(z: G, w: G) -> G:
    return z[0] + w[0], z[1] + w[1]


def mul(z: G, w: G) -> G:
    return z[0] * w[0] - z[1] * w[1], z[0] * w[1] + z[1] * w[0]


def conj(z: G) -> G:
    return z[0], -z[1]


def scale(z: G, q: Q) -> G:
    return z[0] * q, z[1] * q


def norm2(z: G) -> Q:
    return z[0] ** 2 + z[1] ** 2


def derivative(f: Sequence[G], h: int) -> tuple[G, ...]:
    return tuple(mul(f[x ^ h], conj(f[x])) for x in range(len(f)))


def many_derivatives(f: Sequence[G], hs: Sequence[int]) -> tuple[G, ...]:
    out = tuple(f)
    for h in hs:
        out = derivative(out, h)
    return out


def energy(n: int, d: int, mask: int, f: Sequence[G]) -> Q:
    total = Q(0)
    N = 1 << n
    for hs in product(range(N), repeat=d - 1):
        freq, k = mask, d
        for h in hs:
            freq = contract(n, k, freq, h)
            k -= 1
        g = many_derivatives(f, hs)
        coeff = ZERO
        # Degree-one coefficient mask is the actual frequency bit vector.
        for x in range(N):
            coeff = add(coeff, scale(g[x], Q((-1) ** ((freq & x).bit_count() & 1), N)))
        total += norm2(coeff)
    return total / N ** (d - 1)


def cube_energy(n: int, d: int, mask: int, f: Sequence[G]) -> G:
    total = ZERO
    N = 1 << n
    # Direct labelled-vertex expression, not iterated derivative evaluation.
    for hs in product(range(N), repeat=d):
        sign = (-1) ** evaluate(n, d, mask, hs)
        for x in range(N):
            term = ONE
            for eps in range(1 << d):
                y = x
                for i, h in enumerate(hs):
                    if (eps >> i) & 1:
                        y ^= h
                z = f[y]
                if (d - eps.bit_count()) & 1:
                    z = conj(z)
                term = mul(term, z)
            total = add(total, scale(term, Q(sign)))
    return scale(total, Q(1, N ** (d + 1)))


def analytic_checks(rng: random.Random) -> dict:
    choices: tuple[G, ...] = (ZERO, ONE, (Q(-1), Q(0)), (Q(0), Q(1)),
                             (Q(3, 5), Q(4, 5)), (Q(1, 3), Q(1, 4)))
    count = slices = periods = cubes = constrained = 0
    for n, d, trials in ((2, 3, 12), (2, 4, 12), (2, 5, 4), (3, 3, 4), (3, 4, 2)):
        N = 1 << n
        for j in range(trials):
            f = tuple(rng.choice(choices) for _ in range(N))
            mask = rng.randrange(1 << len(basis(n, d)))
            e = energy(n, d, mask, f)
            check(Q(0) <= e <= cap(n, d, mask), "Gaussian-rational energy bound")
            sliced = sum((energy(n, d - 1, contract(n, d, mask, z), derivative(f, z))
                          for z in range(N)), Q()) / N
            check(e == sliced, "exact energy-slicing identity")
            slices += 1
            if n == 2 and d <= 4 and j < 2:
                check(cube_energy(n, d, mask, f) == (e, Q(0)), "cube identity")
                cubes += 1
            for _ in range(4):
                hs = tuple(rng.randrange(N) for _ in range(d - 1))
                g = many_derivatives(f, hs)
                for h in hs:
                    check(all(g[x ^ h] == conj(g[x]) for x in range(N)),
                          "derivative conjugation period")
                    periods += 1
            count += 1
    for n in (2, 3):
        N = 1 << n
        for m in (2, 3, 4):
            pure = sum(int(all(i == 0 for i in a)) << j
                       for j, a in enumerate(basis(n, m)))
            # Exactly the symmetric basis coefficients of u^m, u(x)=x_1.
            for z in range(0, N, 2):
                f = tuple(rng.choice(choices) for _ in range(N))
                val = energy(n, m, pure, derivative(f, z))
                check(val <= 1 - Q(1, 1 << (m - 1)), "fixed-derivative cap")
                check(energy(n, m, pure, (ONE,) * N) == 1 - Q(1, 1 << (m - 1)),
                      "fixed-derivative lower bound")
                constrained += 1
    return {"rational_function_energy_and_slice_tests": count,
            "slicing_equalities": slices, "direct_cube_equalities": cubes,
            "conjugation_period_checks": periods, "fixed_derivative_tests": constrained,
            "coefficient_field": "exact Gaussian rationals"}


def primitive_checks(rng: random.Random) -> dict:
    top = degree = 0
    for n in (1, 2, 3):
        N = 1 << n
        for d in range(2, 7):
            modulus = 1 << d
            for _ in range(4):
                support_values = {s: rng.randrange(2) for s in range(1, N)
                                  if s.bit_count() <= d}
                mask = sum(support_values[sum(1 << i for i in set(a))] << j
                           for j, a in enumerate(basis(n, d)))
                numerators = [sum(c * (1 << (s.bit_count() - 1))
                                  for s, c in support_values.items() if (x & s) == s) % modulus
                              for x in range(N)]
                for _ in range(8):
                    hs = tuple(rng.randrange(N) for _ in range(d))
                    values = numerators[:]
                    for h in hs:
                        values = [(values[x ^ h] - values[x]) % modulus for x in range(N)]
                    target = evaluate(n, d, mask, hs) * (modulus // 2)
                    check(all(v == target for v in values), "explicit primitive top derivative")
                    top += 1
                    h = rng.randrange(N)
                    check(all((values[x ^ h] - values[x]) % modulus == 0 for x in range(N)),
                          "explicit primitive degree")
                    degree += 1
    return {"top_derivative_tuples_all_basepoints": top,
            "next_derivative_tuples_all_basepoints": degree,
            "dimensions": [1, 2, 3], "degrees": list(range(2, 7))}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path,
                        default=Path(__file__).resolve().parents[1] / "data/verification.json")
    args = parser.parse_args()
    rng = random.Random(20261006)
    report: dict = {"status": "passed", "seed": 20261006,
                    "arithmetic": "integers, GF(2), rational and Gaussian-rational arithmetic",
                    "limitations": ["No numerical optimization over arbitrary functions.",
                                    "Finite regressions are not a Lean verification or a proof in all dimensions.",
                                    "The rank-sensitive noncanonical cap is not claimed sharp."]}
    census = []
    for n, ds in ((2, range(3, 11)), (3, (3, 4))):
        for d in ds:
            masks = range(1 << len(basis(n, d)))
            census.append(inspect_family(n, d, masks, True))
    for n, d in ((3, 5), (3, 7), (4, 4), (4, 6)):
        masks = [rng.randrange(1 << len(basis(n, d))) for _ in range(40)]
        masks += [canonical(n, d, u, v) for u, v in ((1, 2), (3, 4), (2, 5))]
        census.append(inspect_family(n, d, masks, False))
    report["tensor_census"] = census
    recurrence = []
    for d in range(4, 1001):
        check(Q(1, 4) + Q(1, 4) * (1 - Q(1, 1 << (d - 2))) + Q(1, 2) * b(d - 1) == b(d),
              "canonical recurrence")
        gamma = Q(d - 2, 1 << (d + 1))
        check(1 - Q(3, 4) * (1 - b(d - 1)) == b(d) - gamma,
              "universal strict-gap recurrence")
        if d <= 12:
            recurrence.append({"degree": d, "sharp_threshold": str(b(d)),
                               "noncanonical_cap": str(b(d) - gamma), "rigidity_gap": str(gamma)})
    report["recurrence_degrees_checked"] = [4, 1000]
    report["threshold_table"] = recurrence
    report["analytic_checks"] = analytic_checks(rng)
    report["primitive_checks"] = primitive_checks(rng)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"status": report["status"], "tensors": sum(c["tensors"] for c in census),
                      "analytic_checks": report["analytic_checks"], "output": str(args.output)}, indent=2))


if __name__ == "__main__":
    main()
