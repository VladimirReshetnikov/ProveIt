#!/usr/bin/env python3
"""Exact finite checks for the ideal-density separation theorem.

No floating point arithmetic and no third-party packages are used.  The
infinite-density assertions are proved in the accompanying manuscript;
this program checks its finite witness and its explicit Q(sqrt(-23)) bound.
"""
from __future__ import annotations
import argparse
import itertools
import json
from fractions import Fraction
from math import isqrt
from pathlib import Path


def ternary01(n: int) -> bool:
    while n:
        if n % 3 == 2:
            return False
        n //= 3
    return True


def blockers(n: int) -> tuple[int, int]:
    a = b = 0
    power = 1
    while n:
        digit = n % 3
        if digit == 1:
            a += power
            b += power
        elif digit == 2:
            b += power
        n //= 3
        power *= 3
    return a, b


def free_of_3aps(points: set[tuple[int, ...]]) -> bool:
    for x, y in itertools.combinations(points, 2):
        # x and y are the endpoints, so this also checks signed steps.
        if all((a + b) % 2 == 0 for a, b in zip(x, y)):
            midpoint = tuple((a + b) // 2 for a, b in zip(x, y))
            if midpoint in points:
                return False
    return True


def free_of_monotone_3aps(points: set[tuple[int, ...]]) -> bool:
    for x in points:
        for y in points:
            if x == y or any(a > b for a, b in zip(x, y)):
                continue
            if all((a + b) % 2 == 0 for a, b in zip(x, y)):
                midpoint = tuple((a + b) // 2 for a, b in zip(x, y))
                if midpoint in points:
                    return False
    return True


def smooth_vectors(norms: tuple[int, ...], bound: int):
    def rec(i: int, norm: int, vector: tuple[int, ...]):
        if i == len(norms):
            yield vector
            return
        exponent = 0
        while norm <= bound:
            yield from rec(i + 1, norm, vector + (exponent,))
            exponent += 1
            norm *= norms[i]
    return set(rec(0, 1, ()))


def primes_up_to(n: int):
    sieve = bytearray(b"\x01") * (n + 1)
    sieve[:2] = b"\x00\x00"
    for p in range(2, isqrt(n) + 1):
        if sieve[p]:
            start = p * p
            sieve[start:n + 1:p] = b"\x00" * ((n - start) // p + 1)
    return (p for p in range(2, n + 1) if sieve[p])


def quadratic_minus23_product_lower(y: int, digits: int = 40):
    """Lower bound for product over prime ideals of norm <=y.

    For K=Q(sqrt(-23)), p=23 ramifies, quadratic residues modulo 23
    split, and other rational primes are inert.  This includes p=2.
    Floor after every factor, using 10**digits as a common denominator.
    """
    scale = 10 ** digits
    lower = scale
    residues = {a * a % 23 for a in range(1, 23)}
    counts = {"split_rational_primes": 0, "inert_prime_ideals": 0,
              "ramified_prime_ideals": 0, "product_factors": 0}
    for p in primes_up_to(y):
        if p == 23:
            local_norms = [p]
            counts["ramified_prime_ideals"] += 1
        elif p % 23 in residues:
            local_norms = [p, p]
            counts["split_rational_primes"] += 1
        elif p * p <= y:
            local_norms = [p * p]
            counts["inert_prime_ideals"] += 1
        else:
            local_norms = []
        for norm in local_norms:
            lower = lower * (norm - 1) // norm
            counts["product_factors"] += 1
    return Fraction(lower, scale), counts


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--cutoff", type=int, default=10_000_000)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    witness = {0, 1, 3, 7, 8}
    baseline = {i for i in range(9) if ternary01(i)}
    assert baseline == {0, 1, 3, 4}
    assert free_of_3aps({(i,) for i in witness})
    for n in range(10_000):
        a, b = blockers(n)
        assert ternary01(a) and ternary01(b) and 2 * b - a == n
        assert (a == b == n) if ternary01(n) else (0 <= a < b < n)

    # Finite instances of the cube exchange; the proof handles all exponents.
    cube_checks = []
    for k in (2, 3, 4):
        old = set(itertools.product([0, 1, 3, 4], repeat=k))
        changed = {v for v in old if 0 in v}
        changed |= set(itertools.product([1, 2], repeat=k)) - {(1,) * k}
        assert free_of_monotone_3aps(changed)
        bad = [(0, 3) + (1,) * (k - 2),
               (1, 2) + (1,) * (k - 2),
               (2, 1) + (1,) * (k - 2)]
        assert all(v in changed for v in bad)
        cube_checks.append({"dimension": k, "checked_points": len(changed),
                            "fractional_ratio_counterexample": bad})
    ws = [Fraction(1, 2)] * 2 + [Fraction(1, 3)] * 2
    def product(xs):
        value = Fraction(1)
        for x in xs:
            value *= x
        return value
    t_upper = lambda w: 1 + w*w + w**3 + w**8/(1-w)
    bracket = product(1+w for w in ws) - 1 - product(t_upper(w) for w in ws)
    prefactor = product((1-w)*w for w in ws)
    assert sum(Fraction(1, n*n) for n in range(1, 6)) + Fraction(1, 5) < Fraction(5, 3)
    outside_lower = Fraction(9, 25) / product(1-w*w for w in ws)
    natural_gain = outside_lower * prefactor * bracket
    assert natural_gain > Fraction(11957, 10_000_000)

    examples = []
    for norms in [(2,), (2, 2), (2, 3), (2, 2, 3, 3), (3, 3, 4)]:
        bound = norms[0] ** 8
        universe = smooth_vectors(norms, bound)
        greedy = {v for v in universe if all(map(ternary01, v))}
        old = {(a,) + (0,) * (len(norms) - 1) for a in baseline}
        new = {(a,) + (0,) * (len(norms) - 1) for a in witness}
        changed = (greedy - old) | new
        assert len(changed) == len(greedy) + 1
        assert free_of_3aps(greedy) and free_of_3aps(changed)
        examples.append({"generator_norms": norms, "cutoff": bound,
                         "universe_size": len(universe),
                         "greedy_size": len(greedy), "improved_size": len(changed)})

    c_lower, counts = quadratic_minus23_product_lower(args.cutoff)
    witness_cutoff = 2 ** 8
    local_loss = Fraction(1, witness_cutoff * (witness_cutoff + 1))
    # There are at most [K:Q]=2 prime ideals of any given integer norm.
    tail_upper = Fraction(2, args.cutoff)
    certified_gap = c_lower * local_loss - tail_upper
    assert certified_gap > 0
    record = {
        "status": "all exact finite checks passed",
        "witness": sorted(witness), "old_exponents": sorted(baseline),
        "saturation_checks": 10_000, "smooth_monoid_checks": examples,
        "cube_exchange_checks": cube_checks,
        "natural_integral_ratio_gain": {
            "prime_ideal_norms": [2, 2, 3, 3],
            "bracket_lower": str(bracket), "prefactor": str(prefactor),
            "outside_density_lower": str(outside_lower),
            "density_gain_lower": str(natural_gain),
            "density_gain_exceeds": "0.0011957",
            "not_valid_for_fractional_ideal_ratios": True
        },
        "field": "Q(sqrt(-23))", "Y": args.cutoff,
        "product_lower": str(c_lower), "product_counts": counts,
        "local_loss": str(local_loss), "tail_upper": str(tail_upper),
        "certified_gap_lower": str(certified_gap),
        "gap_exceeds_1_over_20million": certified_gap > Fraction(1, 20_000_000),
        "scope": "both integral-ideal and nontrivial fractional-ideal ratios; no RH assumption"
    }
    text = json.dumps(record, indent=2)
    print(text)
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(text + "\n")


if __name__ == "__main__":
    main()
