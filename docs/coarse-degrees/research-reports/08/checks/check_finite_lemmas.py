#!/usr/bin/env python3
"""Exact, finite diagnostics for coarse_degree_attack.tex.

These tests do NOT verify an infinitary Turing-degree or category theorem.
The toy program family is explicitly finite and is not a universal enumeration.

Run from the archive root:
    python3 checks/check_finite_lemmas.py --output checks/results.json
Only the Python standard library is used.
"""
from __future__ import annotations

import argparse
import json
from fractions import Fraction
from pathlib import Path
from typing import Callable


class Checks:
    """Record explicit checks, without relying on optimizable assert statements."""

    def __init__(self) -> None:
        self.counts: dict[str, int] = {}

    def require(self, group: str, condition: bool, message: str) -> None:
        self.counts[group] = self.counts.get(group, 0) + 1
        if not condition:
            raise AssertionError(f"{group}: {message}")


def positions(mask: int) -> tuple[int, ...]:
    if mask < 0:
        raise ValueError("A finite-set bit mask must be nonnegative.")
    return tuple(i for i in range(mask.bit_length()) if (mask >> i) & 1)


def norm_formula(mask: int) -> Fraction:
    """Prefix-sup norm of the finite error set encoded by mask."""
    return max(
        (Fraction(j, k + 1) for j, k in enumerate(positions(mask), start=1)),
        default=Fraction(0),
    )


def norm_prefixes(mask: int) -> Fraction:
    """Independent direct scan; prefixes past the support can only decrease."""
    if mask < 0:
        raise ValueError("A finite-set bit mask must be nonnegative.")
    count = 0
    largest = Fraction(0)
    for n in range(1, mask.bit_length() + 1):
        count += (mask >> (n - 1)) & 1
        largest = max(largest, Fraction(count, n))
    return largest


def embed(mask: int, parity: int) -> int:
    if parity not in (0, 1):
        raise ValueError("Parity must be 0 or 1.")
    return sum(1 << (2 * i + parity) for i in positions(mask))


def valuation2(n: int) -> int:
    if n <= 0:
        raise ValueError("The valuation is used only for positive integers.")
    return (n & -n).bit_length() - 1


def test_metric(checks: Checks) -> None:
    norms = [norm_formula(mask) for mask in range(1 << 8)]
    for mask, value in enumerate(norms):
        checks.require("finite_norm_formula", value == norm_prefixes(mask), str(mask))
        checks.require("metric_positivity", (value == 0) == (mask == 0), str(mask))
        for bit in positions(mask):
            checks.require("coordinate_control", value >= Fraction(1, bit + 1),
                           f"mask={mask}, bit={bit}")
    # Translation invariance reduces all triangle inequalities to this two-mask form.
    for a in range(1 << 8):
        for b in range(1 << 8):
            checks.require("triangle_inequality", norms[a ^ b] <= norms[a] + norms[b],
                           f"a={a}, b={b}")
    # Compare all two-oracle prefixes through length 7.
    for p in range(1 << 7):
        for z in range(1 << 7):
            difference = p ^ z
            for m in range(8):
                prefix = (1 << m) - 1
                q = (p & prefix) | (z & ~prefix)
                checks.require("prefix_splicing", norm_formula(q ^ z) <= norms[difference],
                               f"p={p}, z={z}, m={m}")


def test_dyadic_counts(checks: Checks) -> None:
    # Actual counts are accumulated independently of the formulas under test.
    columns = [0] * 13
    tails = [0] * 13
    for n in range(4097):
        if n:
            e = valuation2(n)  # Newly included integer is n - 1.
            if e < len(columns):
                columns[e] += 1
            for k in range(len(tails)):
                if n % (1 << k) == 0:
                    tails[k] += 1
        for e in range(len(columns)):
            expected = (n + (1 << e)) // (1 << (e + 1))
            checks.require("dyadic_column_counts", columns[e] == expected,
                           f"e={e}, n={n}")
        for k in range(len(tails)):
            checks.require("dyadic_tail_counts", tails[k] == n // (1 << k),
                           f"k={k}, n={n}")
            checks.require("dyadic_tail_bounds", tails[k] * (1 << k) <= n,
                           f"k={k}, n={n}")


def test_join_and_majority(checks: Checks) -> None:
    for mask in range(1 << 9):
        checks.require("odd_coordinate_scaling",
                       norm_formula(embed(mask, 1)) == norm_formula(mask) / 2,
                       f"mask={mask}")
        for parity in (0, 1):
            expanded = embed(mask, parity)
            for m in range(1, 10):
                old_count = (mask & ((1 << m) - 1)).bit_count()
                new_count = (expanded & ((1 << (2 * m)) - 1)).bit_count()
                checks.require("projection_prefix_counts", old_count == new_count,
                               f"mask={mask}, parity={parity}, m={m}")
    # Exhaustively test all observed strings on dyadic blocks of lengths 1,2,4,8,16.
    for n in range(5):
        length = 1 << n
        endpoint = 1 << (n + 1)
        for observed in range(1 << length):
            ones = observed.bit_count()
            majority = int(2 * ones > length)  # Ties go to zero.
            for target in (0, 1):
                errors = ones if target == 0 else length - ones
                checks.require("majority_error_bound",
                               majority == target or Fraction(errors, endpoint) >= Fraction(1, 4),
                               f"n={n}, observed={observed}, target={target}")


# A toy program returns (eventual output, halting time), or None for divergence.
ToyProgram = Callable[[int], tuple[int, int] | None]


def toy_programs() -> tuple[ToyProgram, ...]:
    return (
        lambda n: (0, 1),
        lambda n: (1, n + 2),
        lambda n: (n % 2, 2 * n + 1),
        lambda n: None if n == 20 else (0, n + 1),
        lambda n: (2, 3) if n == 40 else (0, n + 1),
        lambda n: (0, (n + 1) ** 2),
        lambda n: None,
        lambda n: (1 - n % 2, n + 3),
    )


def gated_stage(programs: tuple[ToyProgram, ...], length: int, stage: int) -> set[int]:
    """Finite stage fragment of the formula, restricted to the declared programs."""
    output: set[int] = set()
    for n in range(length):
        e = valuation2(n + 1)
        if e >= len(programs):
            continue
        results = [programs[e](i) for i in range(n + 1)]
        valid = all(r is not None and r[0] in (0, 1) and r[1] <= stage for r in results)
        if valid and results[n] is not None and results[n][0] == 0:
            output.add(n)
    return output


def test_gated_enumeration(checks: Checks) -> None:
    programs = toy_programs()
    length = 96
    previous: set[int] = set()
    for stage in range(101):
        current = gated_stage(programs, length, stage)
        checks.require("toy_enumeration_monotonicity", previous <= current, f"stage={stage}")
        for n in current:
            e = valuation2(n + 1)
            values = [programs[e](i) for i in range(n + 1)]
            checks.require("toy_positive_witnesses",
                           all(r is not None and r[0] in (0, 1) and r[1] <= stage for r in values)
                           and values[n] is not None and values[n][0] == 0,
                           f"stage={stage}, n={n}")
        previous = current
    final = gated_stage(programs, length, length ** 2 + 100)
    for n in range(length):
        e = valuation2(n + 1)
        if e in (0, 1, 2, 5, 7):
            result = programs[e](n)
            checks.require("toy_total_binary_diagonal", result is not None
                           and (n in final) == (result[0] == 0), f"n={n}, e={e}")
        if e == 3 and n >= 20:
            checks.require("toy_divergent_column_cutoff", n not in final, f"n={n}")
        if e == 4 and n >= 40:
            checks.require("toy_nonbinary_column_cutoff", n not in final, f"n={n}")


    # A later column input can halt with zero even though an earlier input was bad.
    # The gate must still exclude it; merely testing the output at n would be wrong.
    for e, n in ((3, 23), (4, 47)):
        result = programs[e](n)
        checks.require("toy_gate_is_essential", result is not None and result[0] == 0
                       and n not in final, f"e={e}, n={n}")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, help="Write the JSON result to this path.")
    args = parser.parse_args()
    checks = Checks()
    test_metric(checks)
    test_dyadic_counts(checks)
    test_join_and_majority(checks)
    test_gated_enumeration(checks)
    result = {
        "status": "passed",
        "arithmetic": "exact integer and fractions.Fraction arithmetic",
        "total_checked_instances": sum(checks.counts.values()),
        "groups": checks.counts,
        "scope": {
            "metric_masks_bits": 8,
            "splicing_masks_bits": 7,
            "dyadic_prefixes_through": 4096,
            "dyadic_columns": 13,
            "join_masks_bits": 9,
            "majority_block_lengths": [1, 2, 4, 8, 16],
            "toy_program_count": 8,
            "toy_prefix_length": 96,
            "toy_stage_range": [0, 100],
        },
        "not_verified": [
            "Infinite asymptotic-density limits",
            "Baire-category or perfect-set constructions",
            "Quantification over all partial computable or oracle programs",
            "Turing nonreducibility, minimal pairs, or exact pairs",
            "Literature novelty",
            "Any Lean or other formal proof",
        ],
    }
    text = json.dumps(result, indent=2, sort_keys=True) + "\n"
    if args.output is not None:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(text, encoding="utf-8")
    print(text, end="")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
