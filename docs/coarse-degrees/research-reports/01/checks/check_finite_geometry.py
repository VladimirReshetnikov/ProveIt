#!/usr/bin/env python3
"""Exact, finite regression checks for paper.tex.

These checks do NOT verify infinite density-zero limits, Baire category,
Turing reducibility, genericity, or the claimed infinite minimal pairs.
No third-party Python package is required. Outputs are deterministic.
"""
from __future__ import annotations

import argparse
from fractions import Fraction
from itertools import product
import json
from pathlib import Path
from typing import Sequence

Bits = tuple[int, ...]


def bitstrings(n: int) -> list[Bits]:
    return list(product((0, 1), repeat=n))


def prefix_distance(a: Sequence[int], b: Sequence[int]) -> Fraction:
    """Maximum normalized prefix mismatch for two equally long strings."""
    if len(a) != len(b):
        raise ValueError("Lengths must be equal")
    errors = 0
    result = Fraction(0)
    for n, (x, y) in enumerate(zip(a, b), start=1):
        errors += x != y
        result = max(result, Fraction(errors, n))
    return result


def check_metrics(max_n: int) -> dict[str, int]:
    pairs = triangles = prefix_separations = 0
    for n in range(1, max_n + 1):
        words = bitstrings(n)
        distances = [[prefix_distance(a, b) for b in words] for a in words]
        for i, a in enumerate(words):
            for j, b in enumerate(words):
                d = distances[i][j]
                assert d == distances[j][i]
                assert (d == 0) == (a == b)
                pairs += 1
                for position, (x, y) in enumerate(zip(a, b)):
                    if x != y:
                        assert d >= Fraction(1, position + 1)
                        prefix_separations += 1
                for k in range(len(words)):
                    assert distances[i][k] <= d + distances[j][k]
                    triangles += 1
    return {
        "maximum_length": max_n,
        "symmetry_and_separation_pairs": pairs,
        "triangle_inequalities": triangles,
        "coordinate_separation_bounds": prefix_separations,
    }


def check_decoder_completion(max_n: int) -> dict[str, int]:
    """Check the 1/4 + 1/2 < 1 completion estimate for finite centers.

Completing tau by Z makes all later mismatches fixed, so their normalized
counts decrease. Infinite tails would add no further mismatches.
"""
    tested = tail_bounds = 0
    radii = (Fraction(1, 2), Fraction(1), Fraction(3, 2), Fraction(2))
    for n in range(1, max_n + 1):
        words = bitstrings(n)
        for y in words:
            for z in words:
                dyz = prefix_distance(y, z)
                for r in radii:
                    if dyz >= r / 4:
                        continue
                    for length in range(1, n + 1):
                        for tau in bitstrings(length):
                            if prefix_distance(tau, y[:length]) >= r / 2:
                                continue
                            completed = tau + z[length:]
                            assert prefix_distance(completed, z) < 3 * r / 4
                            tested += 1
                            mismatches = sum(x != w for x, w in zip(tau, z))
                            for m in range(length, n + 5):
                                assert Fraction(mismatches, m) <= Fraction(
                                    mismatches, length
                                )
                                tail_bounds += 1
    assert tested > 0
    return {
        "maximum_length": max_n,
        "radii": [str(r) for r in radii],
        "valid_completions": tested,
        "constant_tail_error_bounds": tail_bounds,
    }


def check_patching(max_n: int) -> dict[str, int]:
    tested = 0
    for n in range(1, max_n + 1):
        for y in bitstrings(n):
            for z in bitstrings(n):
                for cutoff in range(n + 1):
                    patched = z[:cutoff] + y[cutoff:]
                    assert patched[:cutoff] == z[:cutoff]
                    for m in range(max(1, cutoff), n + 1):
                        new = sum(a != b for a, b in zip(patched[:m], z[:m]))
                        old = sum(a != b for a, b in zip(y[:m], z[:m]))
                        assert new <= old
                    tested += 1
    return {"maximum_length": max_n, "patches": tested}


def check_sparse_coding() -> dict[str, int]:
    tested = 0
    # Four explicitly coded bits; the infinite zero-density claim is in the proof.
    slots = [2 ** (i + 1) for i in range(4)]
    n = slots[-1] + 1
    bases = [tuple((k // period) % 2 for k in range(n)) for period in range(1, 7)]
    for base in bases:
        for encoded in bitstrings(4):
            result = list(base)
            for position, value in zip(slots, encoded):
                result[position] = value
            assert tuple(result[p] for p in slots) == encoded
            assert all(result[k] == base[k] for k in range(n) if k not in slots)
            tested += 1
    # Exact counting of sparse positions in every bounded prefix.
    for end in range(1, 4097):
        count = sum(2 ** (i + 1) < end for i in range(12))
        assert count <= max(0, (end - 1).bit_length() - 1)
    return {"readback_cases": tested, "prefix_counts": 4096}


def check_majority(max_length: int) -> dict[str, int]:
    cases = bad = 0
    for length in range(1, max_length + 1):
        for word in bitstrings(length):
            majority = int(2 * sum(word) > length)  # Tie -> 0.
            for original_bit in (0, 1):
                errors = sum(bit != original_bit for bit in word)
                if majority != original_bit:
                    assert 2 * errors >= length
                    bad += 1
                cases += 1
    return {"maximum_block_length": max_length, "cases": cases, "bad_majorities": bad}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=Path(__file__).with_name("results.json"))
    args = parser.parse_args()
    results = {
        "status": "all finite assertions passed",
        "arithmetic": "exact Python integers and fractions.Fraction",
        "scope_warning": (
            "Finite regression tests only: no infinite density, Baire category, "
            "oracle reducibility, genericity, or minimal-pair theorem is machine-verified."
        ),
        "metrics": check_metrics(6),
        "decoder_completion": check_decoder_completion(5),
        "finite_patching": check_patching(5),
        "sparse_coding": check_sparse_coding(),
        "block_majority": check_majority(10),
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(results, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(results, indent=2))


if __name__ == "__main__":
    main()
