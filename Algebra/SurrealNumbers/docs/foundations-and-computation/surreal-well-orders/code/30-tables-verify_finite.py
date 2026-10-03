#!/usr/bin/env python3
"""Exhaustive finite sanity checks for selected constructions in the article.

These computations are NOT proofs of any infinite, proper-class, foundational,
or novelty claim.  They check all partial orientations of distinct unordered
pairs on carriers of sizes 0 through 5; selected diagonal and contradictory
directed-bit cases; all sign words of length at most 5; and all independent
pair-orientation words with at most 5 pairs.  Only Python's standard library
is used.  The results are reproducible and contain no timing-dependent fields.

Run from any directory:
    python3 verify_finite.py
    python3 verify_finite.py --output another_results.json

The default output is verification_results.json next to this script.
Exit status is zero exactly when every recorded check passes.
"""

from __future__ import annotations

import argparse
import itertools
import json
from pathlib import Path
from typing import Iterable, Sequence


def compare(left: object, right: object) -> int:
    """Three-way comparison, used only on mutually comparable objects."""
    return (left > right) - (left < right)


def canonical_pairs(size: int) -> list[tuple[int, int]]:
    """Unordered pairs represented forward; scan maximum label, then minimum."""
    return [(low, high) for high in range(size) for low in range(high)]


def ranks(permutation: Sequence[int]) -> tuple[int, ...]:
    inverse = [0] * len(permutation)
    for position, label in enumerate(permutation):
        inverse[label] = position
    return tuple(inverse)


def relation_bits(permutation: Sequence[int]) -> tuple[int, ...]:
    inverse = ranks(permutation)
    return tuple(int(inverse[a] < inverse[b])
                 for a, b in canonical_pairs(len(permutation)))


def relation_mask(permutation: Sequence[int]) -> int:
    return sum(bit << index
               for index, bit in enumerate(relation_bits(permutation)))


def acyclic(size: int, edges: Iterable[tuple[int, int]]) -> bool:
    """Kahn elimination, independently of the permutation-extension search."""
    outgoing = [set() for _ in range(size)]
    indegrees = [0] * size
    for source, target in edges:
        if target not in outgoing[source]:
            outgoing[source].add(target)
            indegrees[target] += 1
    available = [v for v in range(size) if indegrees[v] == 0]
    removed = 0
    while available:
        source = available.pop()
        removed += 1
        for target in outgoing[source]:
            indegrees[target] -= 1
            if indegrees[target] == 0:
                available.append(target)
    return removed == size


def check_partial_orientations() -> dict:
    """All 3^(n choose 2) partial orientations for each n <= 5."""
    by_size = []
    failures = []
    for size in range(6):
        pairs = canonical_pairs(size)
        permutation_masks = [relation_mask(p)
                             for p in itertools.permutations(range(size))]
        checked = acyclic_count = extendible_count = 0
        size_pass = True
        # 0: unspecified; 1: lower label before higher; 2: reverse direction.
        for states in itertools.product(range(3), repeat=len(pairs)):
            specified = forward = 0
            edges = []
            for index, (state, (low, high)) in enumerate(zip(states, pairs)):
                if state:
                    specified |= 1 << index
                    if state == 1:
                        forward |= 1 << index
                        edges.append((low, high))
                    else:
                        edges.append((high, low))
            graph_is_acyclic = acyclic(size, edges)
            has_extension = any((mask & specified) == forward
                                for mask in permutation_masks)
            checked += 1
            acyclic_count += graph_is_acyclic
            extendible_count += has_extension
            if graph_is_acyclic != has_extension:
                size_pass = False
                if len(failures) < 10:
                    failures.append({"size": size, "states": list(states),
                                     "acyclic": graph_is_acyclic,
                                     "extendible": has_extension})
        by_size.append({
            "carrier_size": size,
            "unordered_pairs": len(pairs),
            "permutations_searched": len(permutation_masks),
            "partial_orientation_tables": checked,
            "acyclic_tables": acyclic_count,
            "extendible_tables": extendible_count,
            "nonextendible_tables": checked - extendible_count,
            "all_pass": size_pass and checked == 3 ** len(pairs),
        })
    return {
        "method": "Independent Kahn acyclicity and exhaustive permutation search",
        "state_convention": ["unspecified", "forward", "reverse"],
        "by_carrier_size": by_size,
        "total_tables_checked": sum(row["partial_orientation_tables"]
                                    for row in by_size),
        "failures": failures,
        "all_pass": all(row["all_pass"] for row in by_size),
    }


def partial_table_condition(size: int,
                            table: dict[tuple[int, int], int]) -> bool:
    """The theorem's finite condition, including reversed negative bits."""
    edges = set()
    for (first, second), bit in table.items():
        if first == second:
            if bit:
                return False
        elif bit:
            edges.add((first, second))
        else:
            edges.add((second, first))
    return acyclic(size, edges)


def partial_table_has_extension(size: int,
                               table: dict[tuple[int, int], int]) -> bool:
    for permutation in itertools.permutations(range(size)):
        inverse = ranks(permutation)
        if all(int(inverse[a] < inverse[b]) == bit
               for (a, b), bit in table.items()):
            return True
    return False


def check_directed_boundary_cases() -> dict:
    counts = {"true_diagonal_rejected": 0, "false_diagonal_accepted": 0,
              "both_opposite_bits_true_rejected": 0,
              "both_opposite_bits_false_rejected": 0,
              "complementary_opposite_bits_accepted": 0}
    failures = []

    def test(size: int, table: dict[tuple[int, int], int],
             expected: bool, category: str) -> None:
        condition = partial_table_condition(size, table)
        extension = partial_table_has_extension(size, table)
        counts[category] += 1
        if condition != expected or extension != expected:
            failures.append({"carrier_size": size, "category": category,
                             "table": [[a, b, bit]
                                       for (a, b), bit in table.items()],
                             "expected": expected,
                             "condition": condition, "extension": extension})

    for size in range(6):
        for vertex in range(size):
            test(size, {(vertex, vertex): 1}, False, "true_diagonal_rejected")
            test(size, {(vertex, vertex): 0}, True, "false_diagonal_accepted")
        for first, second in canonical_pairs(size):
            test(size, {(first, second): 1, (second, first): 1}, False,
                 "both_opposite_bits_true_rejected")
            test(size, {(first, second): 0, (second, first): 0}, False,
                 "both_opposite_bits_false_rejected")
            for bit in (0, 1):
                test(size, {(first, second): bit, (second, first): 1 - bit}, True,
                     "complementary_opposite_bits_accepted")
    return {"scope": "Supplementary diagonal and opposite-direction cases",
            "counts": counts, "total_cases_checked": sum(counts.values()),
            "failures": failures, "all_pass": not failures}


def native_sign_compare(left: Sequence[int], right: Sequence[int]) -> int:
    """Native sign comparison uses -1 < termination (0) < +1."""
    for position in range(max(len(left), len(right))):
        a = left[position] if position < len(left) else 0
        b = right[position] if position < len(right) else 0
        if a != b:
            return compare(a, b)
    return 0


def sign_code(signs: Sequence[int]) -> str:
    return "".join("00" if sign == -1 else "11" for sign in signs) + "01"


def check_sign_codes() -> dict:
    words = [word for length in range(6)
             for word in itertools.product((-1, 1), repeat=length)]
    codes = {word: sign_code(word) for word in words}
    comparisons = 0
    failures = []
    for left, right in itertools.product(words, repeat=2):
        comparisons += 1
        if native_sign_compare(left, right) != compare(codes[left], codes[right]):
            failures.append({"left": list(left), "right": list(right),
                             "left_code": codes[left], "right_code": codes[right]})
    prefix_pairs = 0
    prefix_failures = []
    for left, right in itertools.combinations(words, 2):
        prefix_pairs += 1
        if codes[left].startswith(codes[right]) or codes[right].startswith(codes[left]):
            prefix_failures.append([codes[left], codes[right]])
    return {"maximum_sign_length": 5,
            "encoding": {"-": "00", "+": "11", "terminator": "01"},
            "sign_words": len(words),
            "ordered_comparisons_including_equality": comparisons,
            "distinct_unordered_prefix_checks": prefix_pairs,
            "maximum_code_length": max(map(len, codes.values())),
            "comparison_failures": failures, "prefix_failures": prefix_failures,
            "all_pass": not failures and not prefix_failures}


def pair_permutation(word: Sequence[int], *, forward_bit: int) -> tuple[int, ...]:
    result = []
    for index, bit in enumerate(word):
        pair = (2 * index, 2 * index + 1)
        result.extend(pair if bit == forward_bit else pair[::-1])
    return tuple(result)


def check_independent_pair_swaps() -> dict:
    rows = []
    failures = []
    for pairs in range(6):
        words = list(itertools.product((0, 1), repeat=pairs))
        enumerations = {word: pair_permutation(word, forward_bit=0) for word in words}
        tables = {word: relation_bits(pair_permutation(word, forward_bit=1))
                  for word in words}
        enumeration_pass = table_pass = cross_block_pass = True
        for left, right in itertools.product(words, repeat=2):
            expected = compare(left, right)
            enum_good = compare(enumerations[left], enumerations[right]) == expected
            table_good = compare(tables[left], tables[right]) == expected
            enumeration_pass &= enum_good
            table_pass &= table_good
            if not enum_good or not table_good:
                failures.append({"pair_count": pairs, "left": left, "right": right,
                                 "enumeration_pass": enum_good, "table_pass": table_good})
        cross_checks = 0
        for word in words:
            for (low, high), bit in zip(canonical_pairs(2 * pairs), tables[word]):
                if low // 2 != high // 2:
                    cross_checks += 1
                    cross_block_pass &= bit == 1
        rows.append({"pair_count": pairs, "orientation_words": len(words),
                     "ordered_comparisons_per_representation": len(words) ** 2,
                     "cross_block_bits_checked": cross_checks,
                     "enumeration_lex_pass": enumeration_pass,
                     "canonical_table_lex_pass": table_pass,
                     "cross_block_relations_unchanged": cross_block_pass,
                     "all_pass": enumeration_pass and table_pass and cross_block_pass})
    return {
        "enumeration_convention": "bit 0 = forward pair; bit 1 = reversed pair",
        "relation_table_convention": "bit 0 = reversed pair; bit 1 = forward pair",
        "note": "The bit conventions differ because table bit 1 means baseline forward.",
        "by_pair_count": rows, "failures": failures,
        "all_pass": all(row["all_pass"] for row in rows),
    }


def check_three_element_orders() -> dict:
    permutations = list(itertools.permutations(range(3)))
    ordered = {
        "enumeration_lex": sorted(permutations),
        "inverse_rank_lex": sorted(permutations, key=ranks),
        "canonical_relation_table_lex": sorted(permutations, key=relation_bits),
    }
    labels = {name: ["".join(map(str, p)) for p in sequence]
              for name, sequence in ordered.items()}
    all_distinct = len({tuple(order) for order in labels.values()}) == 3
    comparisons = []
    for first, second in itertools.combinations(ordered, 2):
        positions_a = {word: i for i, word in enumerate(ordered[first])}
        positions_b = {word: i for i, word in enumerate(ordered[second])}
        witnesses = [(left, right)
                     for left, right in itertools.combinations(permutations, 2)
                     if compare(positions_a[left], positions_a[right])
                     != compare(positions_b[left], positions_b[right])]
        comparisons.append({"orders_compared": [first, second],
                            "disagreeing_unordered_pairs": len(witnesses),
                            "first_witness": ["".join(map(str, p))
                                              for p in witnesses[0]] if witnesses else None})
    return {
        "canonical_scan": [list(pair) for pair in canonical_pairs(3)],
        "table_bit_convention": "1 iff the lower baseline label precedes the higher",
        "rows": [{"enumeration": "".join(map(str, p)),
                  "inverse_ranks": list(ranks(p)),
                  "canonical_relation_table": "".join(map(str, relation_bits(p)))}
                 for p in permutations],
        "increasing_orders": labels,
        "pairwise_comparison_checks": comparisons,
        "table_order_is_reverse_enumeration": (
            ordered["canonical_relation_table_lex"] == ordered["enumeration_lex"][::-1]),
        "table_order_is_reverse_inverse_rank": (
            ordered["canonical_relation_table_lex"] == ordered["inverse_rank_lex"][::-1]),
        "all_three_labelled_comparisons_distinct": all_distinct,
        "all_pass": all_distinct and all(row["disagreeing_unordered_pairs"] > 0
                                         for row in comparisons),
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path,
                        default=Path(__file__).resolve().with_name("verification_results.json"))
    args = parser.parse_args()
    results = {
        "status_description": "Finite exhaustive sanity checks only; not proofs of class-level results.",
        "standard_library_only": True,
        "partial_orientations": check_partial_orientations(),
        "directed_boundary_cases": check_directed_boundary_cases(),
        "finite_surreal_sign_codes": check_sign_codes(),
        "independent_pair_swaps": check_independent_pair_swaps(),
        "three_element_comparisons": check_three_element_orders(),
    }
    sections = [value for value in results.values() if isinstance(value, dict)]
    results["all_pass"] = all(section["all_pass"] for section in sections)
    args.output.write_text(json.dumps(results, indent=2, sort_keys=True) + "\n",
                           encoding="utf-8")
    print(json.dumps({"all_pass": results["all_pass"],
                      "partial_orientation_tables": results["partial_orientations"]["total_tables_checked"],
                      "directed_boundary_cases": results["directed_boundary_cases"]["total_cases_checked"],
                      "sign_word_comparisons": results["finite_surreal_sign_codes"]["ordered_comparisons_including_equality"],
                      "output": str(args.output.resolve())}, indent=2))
    return 0 if results["all_pass"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
