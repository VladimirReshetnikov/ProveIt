#!/usr/bin/env python3
"""Exact finite checks for Filter Complexity and Booleanization.

These finite Boolean algebras are NOT finite approximations proving the
infinite cardinal theorems. In particular, there is no test of p, u, or
any forcing-model consistency assertion. Python 3.10+, standard library.
"""
from __future__ import annotations

import argparse
import itertools
import json
from pathlib import Path
from typing import Iterator


def submasks(mask: int) -> list[int]:
    """Return all nonzero submasks of a nonnegative integer."""
    if mask < 0:
        raise ValueError("mask must be nonnegative")
    out: list[int] = []
    current = mask
    while current:
        out.append(current)
        current = (current - 1) & mask
    return out


def join(masks: Iterator[int] | list[int] | tuple[int, ...]) -> int:
    out = 0
    for mask in masks:
        out |= mask
    return out


def check_filters() -> dict[str, int]:
    counts = dict(order_and_compatibility_pairs=0, relative_families=0,
                  sieves=0, dense_sieves=0)
    for n in range(1, 5):
        top = (1 << n) - 1
        kernels = list(range(1, top + 1))
        actual_filters = {
            k: frozenset(a for a in range(top + 1) if a & k == k)
            for k in kernels
        }
        for k, h in itertools.product(kernels, repeat=2):
            assert (actual_filters[h] >= actual_filters[k]) == (h & k == h)
            common = any(actual_filters[t] >= actual_filters[h] | actual_filters[k]
                         for t in kernels)
            assert common == bool(k & h)
            counts["order_and_compatibility_pairs"] += 1
        for k in kernels:
            below = submasks(k)
            index = {h: j for j, h in enumerate(below)}
            lower_bits = {
                h: sum(1 << index[t] for t in submasks(h)) for h in below
            }
            for family_bits in range(1 << len(below)):
                counts["relative_families"] += 1
                family = [h for h in below if family_bits & (1 << index[h])]
                is_sieve = all((family_bits & lower_bits[h]) == lower_bits[h]
                               for h in family)
                if not is_sieve:
                    continue
                counts["sieves"] += 1
                dense_direct = all(any(g & h == g for g in family) for h in below)
                union_covers = join(family) == k
                atoms_cover = all((1 << i) in family for i in range(n) if k >> i & 1)
                assert dense_direct == union_covers == atoms_cover
                counts["dense_sieves"] += int(dense_direct)
    return counts


def check_frame_points() -> dict[str, int]:
    counts = dict(candidate_maps=0, actual_points=0)
    for n in range(1, 5):
        top = (1 << n) - 1
        valid: list[tuple[int, ...]] = []
        for code in range(1 << (top + 1)):
            counts["candidate_maps"] += 1
            q = tuple((code >> a) & 1 for a in range(top + 1))
            if q[0] != 0 or q[top] != 1:
                continue
            if any(q[top ^ a] != 1 - q[a] for a in range(top + 1)):
                continue
            if any(q[a | b] != (q[a] | q[b]) or q[a & b] != (q[a] & q[b])
                   for a in range(top + 1) for b in range(top + 1)):
                continue
            valid.append(q)
        expected = [tuple(int(bool(a & (1 << i))) for a in range(top + 1))
                    for i in range(n)]
        assert set(valid) == set(expected)
        counts["actual_points"] += len(valid)
    return counts


def partitions(n: int) -> list[tuple[int, ...]]:
    """All set partitions of n, as canonical tuples of nonzero bitmasks."""
    result: list[tuple[int, ...]] = [()]
    for i in range(n):
        following: list[tuple[int, ...]] = []
        bit = 1 << i
        for blocks in result:
            following.append(blocks + (bit,))
            for j in range(len(blocks)):
                following.append(blocks[:j] + (blocks[j] | bit,) + blocks[j + 1:])
        result = following
    assert len(set(result)) == len(result)
    return result


def check_mixing() -> dict[str, int]:
    counts = dict(representations=0, equality_comparisons=0,
                  global_values=0)
    for n in range(1, 4):
        top = (1 << n) - 1
        names: list[tuple[tuple[tuple[int, int], ...], int]] = []
        for blocks in partitions(n):
            assert join(blocks) == top
            assert all(not a & b for a, b in itertools.combinations(blocks, 2))
            for labels in itertools.product(range(top + 1), repeat=len(blocks)):
                name = tuple(zip(blocks, labels))
                value = join([b & f for b, f in name])
                names.append((name, value))
        counts["representations"] += len(names)
        assert set(v for _, v in names) == set(range(top + 1))
        counts["global_values"] += top + 1
        for (x, xv), (y, yv) in itertools.product(names, repeat=2):
            eq_formula = join([b & c & (top ^ (f ^ g))
                               for b, f in x for c, g in y])
            assert eq_formula == (top ^ (xv ^ yv))
            counts["equality_comparisons"] += 1
    return counts


def truth_mask(values: tuple[int, ...], predicate) -> int:
    return sum(1 << i for i, x in enumerate(values) if predicate(x))


def check_fields() -> dict[str, int | dict[str, object]]:
    counts: dict[str, int | dict[str, object]] = dict(
        generalized_inverses=0, idempotents=0, idempotent_pairs=0,
        existential_instances=0, witness_candidates=0)
    for n in range(1, 6):
        top = (1 << n) - 1
        vectors = list(itertools.product(range(3), repeat=n))
        idempotents = []
        for x in vectors:
            y = tuple(0 if z == 0 else pow(z, -1, 3) for z in x)
            assert tuple(a * b * a % 3 for a, b in zip(x, y)) == x
            counts["generalized_inverses"] += 1
            if all(z * z % 3 == z for z in x):
                idempotents.append(x)
        assert len(idempotents) == 1 << n
        counts["idempotents"] += len(idempotents)
        for x, y in itertools.product(idempotents, repeat=2):
            bx = truth_mask(x, lambda z: z == 1)
            by = truth_mask(y, lambda z: z == 1)
            meet = tuple(a * b % 3 for a, b in zip(x, y))
            boolean_join = tuple((a + b - a * b) % 3 for a, b in zip(x, y))
            assert truth_mask(meet, lambda z: z == 1) == (bx & by)
            assert truth_mask(boolean_join, lambda z: z == 1) == (bx | by)
            counts["idempotent_pairs"] += 1
        if n > 4:
            continue
        for x in vectors:
            for a in range(3):
                # Formula: exists y, y*y + x*y + a = 0, in F_3 at each atom.
                existential_value = 0
                for y in vectors:
                    event = sum(1 << i for i in range(n)
                                if (y[i] ** 2 + x[i] * y[i] + a) % 3 == 0)
                    existential_value |= event
                    counts["witness_candidates"] += 1
                witness = tuple(next((z for z in range(3)
                                      if (z * z + x[i] * z + a) % 3 == 0), 0)
                                for i in range(n))
                attained = sum(1 << i for i in range(n)
                               if (witness[i] ** 2 + x[i] * witness[i] + a) % 3 == 0)
                assert attained == existential_value
                counts["existential_instances"] += 1
    # A global nonzero nonunit; the internal field disjunction still has value 1.
    x = (0, 1)
    zero_event = truth_mask(x, lambda z: z == 0)
    inverse_event = truth_mask(x, lambda z: z != 0)
    assert zero_event | inverse_event == 3
    assert zero_event != 3 and inverse_event != 3
    counts["internal_external_example"] = {
        "global_element": list(x), "zero_event": zero_event,
        "invertibility_event": inverse_event, "disjunction_event": 3,
        "externally_zero": False, "externally_a_unit": False}
    return counts


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=Path("verification_results.json"))
    args = parser.parse_args()
    report = {
        "status": "all checks passed",
        "arithmetic": "exact integers; finite fields reduced modulo 3",
        "scope": "Finite Boolean interface checks only; not proofs of the infinite theorems.",
        "filters": check_filters(),
        "frame_points": check_frame_points(),
        "mixing": check_mixing(),
        "fields": check_fields(),
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    text = json.dumps(report, indent=2, sort_keys=True) + "\n"
    args.output.write_text(text, encoding="utf-8")
    print(text, end="")


if __name__ == "__main__":
    main()
