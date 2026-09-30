#!/usr/bin/env python3
"""Exact finite checks accompanying Optimal Kummer Atlases.

This is an ordinary Python checker, NOT a proof-assistant verification of
intersection theory, the Chow-ring computation, or the chart lower bound.
No external packages or network access are required. Run from any directory.
"""
from __future__ import annotations

import argparse
import itertools
import json
import math
from pathlib import Path
import random
import sys
from typing import Iterable, Sequence


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def partitions(n: int) -> Iterable[tuple[int, ...]]:
    """Restricted-growth encodings, one for each partition of {0,...,n-1}."""
    if n < 1:
        raise ValueError("n must be positive")
    def extend(a: tuple[int, ...], maximum: int):
        if len(a) == n:
            yield a
        else:
            for label in range(maximum + 2):
                yield from extend(a + (label,), max(maximum, label))
    yield from extend((0,), 0)


def canonical(a: Sequence[int]) -> tuple[int, ...]:
    labels: dict[int, int] = {}
    return tuple(labels.setdefault(x, len(labels)) for x in a)


def shift_partition(a: tuple[int, ...]) -> tuple[int, ...]:
    return canonical((a[-1],) + a[:-1])


def stirling(n: int, b: int) -> int:
    row = [1] + [0] * n
    for m in range(1, n + 1):
        row = [0] + [row[k - 1] + k * row[k] for k in range(1, n + 1)]
    return row[b]


def check_partitions(p: int) -> dict:
    remaining = set(partitions(p))
    total = len(remaining)
    counts: dict[int, dict[int, int]] = {}
    fixed = []
    while remaining:
        a = min(remaining)
        orbit = {a}
        nxt = shift_partition(a)
        while nxt not in orbit:
            orbit.add(nxt)
            nxt = shift_partition(nxt)
        require(nxt == a, "Shift did not return to its initial partition")
        require(orbit <= remaining, "Overlapping partition orbits")
        remaining -= orbit
        b = max(a) + 1
        length = len(orbit)
        counts.setdefault(b, {})[length] = counts.setdefault(b, {}).get(length, 0) + 1
        if length == 1:
            fixed.append(a)
        if b not in (1, p):
            require(length == p, f"Unexpected stabilizer for prime p={p}")
    require(set(fixed) == {tuple([0] * p), tuple(range(p))}, "Wrong fixed partitions")
    rows = []
    for b in range(1, p + 1):
        partition_count = sum(length * count for length, count in counts[b].items())
        require(partition_count == stirling(p, b), "Stirling/orbit count mismatch")
        rows.append({"blocks": b, "partitions": partition_count,
                     "orbits_by_length": counts[b]})
    return {"p": p, "total_partitions": total, "rows": rows,
            "fixed_partitions": fixed}


def dft(x: Sequence[int], matrix: Sequence[Sequence[int]], q: int) -> tuple[int, ...]:
    return tuple(sum(a * b for a, b in zip(row, x)) % q for row in matrix)


def matrices(p: int, q: int, zeta: int):
    forward = [[pow(zeta, (-i * j) % p, q) for i in range(p)] for j in range(p)]
    inverse = [[pow(p, -1, q) * pow(zeta, (i * j) % p, q) % q
                for j in range(p)] for i in range(p)]
    return forward, inverse


def check_fourier(p: int, q: int, exhaustive: bool, count: int, seed: int) -> dict:
    require((q - 1) % p == 0, "Field does not contain the required roots of unity")
    zeta = next(z for z in range(2, q) if pow(z, p, q) == 1)
    require(all(pow(zeta, r, q) != 1 for r in range(1, p)), "Nonprimitive root")
    forward, inverse = matrices(p, q, zeta)
    rng = random.Random(seed)
    values = (itertools.product(range(q), repeat=p) if exhaustive else
              (tuple(rng.randrange(q) for _ in range(p)) for _ in range(count)))
    checked = nonconstant = distinct = branch_cases = 0
    for x in values:
        x = tuple(x)
        modes = dft(x, forward, q)
        require(dft(modes, inverse, q) == x, "Fourier inversion failed")
        is_constant = len(set(x)) == 1
        require(all(u == 0 for u in modes[1:]) == is_constant,
                "Wrong common-zero locus")
        shifted = x[1:] + x[:1]
        shift_modes = dft(shifted, forward, q)
        require(shift_modes == tuple(pow(zeta, j, q) * modes[j] % q for j in range(p)),
                "Character covariance failed")
        powers = tuple(pow(modes[j], pow(j, -1, p), q) for j in range(1, p))
        shift_powers = tuple(pow(shift_modes[j], pow(j, -1, p), q) for j in range(1, p))
        require(shift_powers == tuple(zeta * v % q for v in powers),
                "Fixed-character generator covariance failed")
        require(all(v == 0 for v in powers) == is_constant, "Generator cover failed")
        if not is_constant:
            nonconstant += 1
        if len(set(x)) == p:
            distinct += 1
        # All branch choices are checked on at most 128 nonconstant inputs per field.
        if not is_constant and branch_cases < 128:
            j = next(j for j in range(1, p) if modes[j])
            j_inv = pow(j, -1, p)
            exponents = [0] + [(k * j_inv) % p for k in range(1, p)]
            ratios = [modes[0]] + [modes[k] * pow(pow(modes[j], exponents[k], q), -1, q) % q
                                   for k in range(1, p)]
            shifted_ratios = [shift_modes[0]] + [
                shift_modes[k] * pow(pow(shift_modes[j], exponents[k], q), -1, q) % q
                for k in range(1, p)]
            require(shifted_ratios == ratios, "Invariant ratio failed")
            for r in range(p):
                rho = pow(zeta, r, q) * modes[j] % q
                recovered_modes = [modes[0]] + [
                    ratios[k] * pow(rho, exponents[k], q) % q for k in range(1, p)]
                reconstructed = dft(recovered_modes, inverse, q)
                target = tuple(x[(i + r * j_inv) % p] for i in range(p))
                require(reconstructed == target, "Coherent branch reconstruction failed")
            branch_cases += 1
        checked += 1
    # Pure-mode points witness nonemptiness of every Fourier-coordinate cycle.
    for j in range(1, p):
        modes = [0] * p
        modes[j] = 1
        x = dft(modes, inverse, q)
        require(len(set(x)) == p, "A nonzero pure mode does not give distinct points")
    return {"p": p, "q": q, "zeta": zeta, "exhaustive": exhaustive,
            "tuples_checked": checked, "nonconstant_tuples": nonconstant,
            "pairwise_distinct_tuples": distinct,
            "branch_inputs": branch_cases, "branches_checked": p * branch_cases,
            "pure_modes_checked": p - 1, "seed_for_sampling": None if exhaustive else seed}


def check_vector_configurations() -> dict:
    rng = random.Random(20260929)
    rows = []
    for p, q in [(3, 7), (5, 11), (7, 29)]:
        zeta = next(z for z in range(2, q) if pow(z, p, q) == 1)
        forward, _ = matrices(p, q, zeta)
        for d in [2, 3]:
            for _ in range(256):
                points = [tuple(rng.randrange(q) for _ in range(d)) for _ in range(p)]
                modes = [dft([point[a] for point in points], forward, q) for a in range(d)]
                require(all(u == 0 for mode in modes for u in mode[1:]) == (len(set(points)) == 1),
                        "Vector-valued Fourier common-zero failure")
            rows.append({"p": p, "q": q, "d": d, "tuples_checked": 256})
    return {"seed": 20260929, "rows": rows}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path,
                        default=Path(__file__).resolve().parents[1] / "data" / "finite_checks.json")
    args = parser.parse_args()
    euler_rows = []
    for p in [2, 3, 5, 7, 11, 13]:
        for d in [1, 2, 3, 4]:
            coefficient = math.factorial(p - 1) ** d
            require(coefficient % p == pow(-1, d, p), "Wilson coefficient failed")
            require(math.gcd(coefficient, p) == 1, "Nonunit Euler coefficient")
            euler_rows.append({"p": p, "d": d, "N": d * (p - 1),
                               "euler_coefficient": coefficient, "residue_mod_p": coefficient % p})
    # A composite-degree warning: the proper partition {{0,2},{1,3}} is C4-stable.
    composite = (0, 1, 0, 1)
    require(shift_partition(composite) == composite, "Composite warning failed")
    report = {
        "status": "PASS",
        "scope": "Exact finite corroboration only; no verification of Chow theory or the general lower bound.",
        "python_version": sys.version.split()[0],
        "partition_checks": [check_partitions(p) for p in [2, 3, 5, 7]],
        "euler_checks": euler_rows,
        "fourier_checks": [check_fourier(3, 7, True, 0, 0),
                           check_fourier(5, 11, True, 0, 0),
                           check_fourier(7, 29, False, 4096, 20260929)],
        "vector_configuration_checks": check_vector_configurations(),
        "composite_warning": {"n": 4, "fixed_proper_partition": composite}
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(f"PASS: exact finite checks written to {args.output}")
    print("The intersection-theoretic proofs are not computationally or formally verified.")


if __name__ == "__main__":
    main()
