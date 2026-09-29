#!/usr/bin/env python3
"""Finite diagnostics for article.tex; not a computability-theoretic proof.

Uses only the Python standard library. Run from any working directory.
Writes results.json next to this program. No halting or totality oracle is
implemented, and no finite experiment certifies an infinite degree assertion.
"""
from __future__ import annotations

import itertools
import json
from pathlib import Path
from typing import Optional, Sequence

Bit = int
PartialBit = Optional[int]


def column(n: int) -> int:
    if n < 0:
        raise ValueError("The column function requires a nonnegative integer.")
    m = n + 1
    return (m & -m).bit_length() - 1


def check_columns(limit: int = 4096, levels: int = 16) -> dict[str, int]:
    """Compare independently accumulated prefix counts with floor formulas."""
    counts = [0] * levels
    cases = 0
    for n in range(limit + 1):
        if n:
            i = column(n - 1)
            if i < levels:
                counts[i] += 1
        for i in range(levels):
            assert counts[i] == n // (2**i) - n // (2 ** (i + 1))
            # The chosen limit is below 2**levels, so no tail is uncounted.
            assert sum(counts[i:]) == n // (2**i)
            assert (2**i) * sum(counts[i:]) <= n
            cases += 1
    return {"prefixes": limit + 1, "levels": levels, "cases": cases}


def check_majority() -> dict[str, int]:
    cases = wrong = 0
    for block_exponent in range(4):
        size = 2**block_exponent
        endpoint = 2 * size - 1  # I_n ends at this exclusive endpoint.
        for bits in itertools.product((0, 1), repeat=size):
            majority = int(sum(bits) * 2 > size)  # ties go to 0
            for true_bit in (0, 1):
                cases += 1
                if majority != true_bit:
                    wrong += 1
                    errors = sum(b != true_bit for b in bits)
                    assert 2 * errors >= size
                    assert 4 * errors > endpoint
    return {"truth_table_cases": cases, "wrong_majorities_checked": wrong}


def bits(n: int, width: int) -> tuple[int, ...]:
    return tuple((n >> i) & 1 for i in range(width))


def in_reservoir(y: Sequence[Bit], stem: Sequence[Bit],
                 protected: int, target: Sequence[Bit]) -> bool:
    return (tuple(y[:len(stem)]) == tuple(stem)
            and all(not (protected & (1 << n)) or y[n] == target[n]
                    for n in range(len(stem), len(y))))


def admissible(new: Sequence[Bit], old: Sequence[Bit], protected: int,
               target: Sequence[Bit]) -> bool:
    return (len(new) >= len(old)
            and tuple(new[:len(old)]) == tuple(old)
            and all(not (protected & (1 << n)) or new[n] == target[n]
                    for n in range(len(old), len(new))))


def check_reservoirs(width: int = 4) -> dict[str, int]:
    """Exhaustively check finite analogues of shrinking and nonemptiness."""
    words = [bits(i, width) for i in range(2**width)]
    stems = [bits(i, length) for length in range(width + 1)
             for i in range(2**length)]
    conditions = inclusions = members = 0
    for target in words:
        for protected in range(2**width):
            for old in stems:
                old_members = {y for y in words
                               if in_reservoir(y, old, protected, target)}
                assert old_members
                conditions += 1
                for new in stems:
                    if not admissible(new, old, protected, target):
                        continue
                    for stronger in range(2**width):
                        if stronger & protected != protected:
                            continue
                        new_members = {y for y in words
                                       if in_reservoir(y, new, stronger, target)}
                        assert new_members
                        assert new_members <= old_members
                        inclusions += 1
                        members += len(new_members)
    return {"width": width, "conditions": conditions,
            "inclusions": inclusions, "member_checks": members}


def check_overlap() -> dict[str, int | bool]:
    """f(x,y) and g(y,z), with y the SAME shared coordinate on both sides.

    Entries may be undefined. A no-disagreement pair with an actual common
    convergent value must give that value at every convergent candidate with
    the same shared bit. This is the precise conditional form used in the
    manuscript, not a claim of uniform totality on all oracle inputs.
    """
    tables = list(itertools.product((None, 0, 1), repeat=4))
    pairs = negative = common_checks = 0
    for f in tables:
        for g in tables:
            pairs += 1
            disagreements = [
                (x, y, z)
                for x, y, z in itertools.product((0, 1), repeat=3)
                if f[2*x+y] is not None and g[2*y+z] is not None
                and f[2*x+y] != g[2*y+z]
            ]
            if disagreements:
                continue
            negative += 1
            for x, y, z in itertools.product((0, 1), repeat=3):
                value = f[2*x+y]
                if value is None or g[2*y+z] is None:
                    continue
                assert value == g[2*y+z]
                for candidate_x in (0, 1):
                    candidate = f[2*candidate_x+y]
                    if candidate is not None:
                        assert candidate == value
                        common_checks += 1
                for candidate_z in (0, 1):
                    candidate = g[2*y+candidate_z]
                    if candidate is not None:
                        assert candidate == value
                        common_checks += 1
    # Counterexample to allowing separate, incompatible shared bits.
    f_shared = (0, 1, 0, 1)  # f(x,y)=y
    g_shared = (0, 0, 1, 1)  # g(y,z)=y
    assert all(f_shared[2*x+y] == g_shared[2*y+z]
               for x, y, z in itertools.product((0, 1), repeat=3))
    assert f_shared[0] != g_shared[2]  # spurious split: y=0 versus y=1
    return {"partial_table_pairs": pairs,
            "no_disagreement_pairs": negative,
            "common_value_checks": common_checks,
            "independent_shared_bit_error_detected": True}


def main() -> None:
    results = {
        "status": "PASS",
        "scope": "Finite combinatorial diagnostics only; no infinite or oracle theorem certified.",
        "dyadic_columns": check_columns(),
        "block_majority": check_majority(),
        "reservoir_preservation": check_reservoirs(),
        "shared_coordinate_amalgamation": check_overlap(),
    }
    destination = Path(__file__).resolve().with_name("results.json")
    destination.write_text(json.dumps(results, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(results, indent=2))


if __name__ == "__main__":
    main()
