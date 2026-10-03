#!/usr/bin/env python3
"""Reproduce finite checks accompanying the surreal lexicographic-orders article.

This standard-library-only program exhausts the stated finite search spaces.
Its results are finite evidence and illustrations. They do not prove any
infinite-cardinal theorem, proper-class statement, density claim, or theorem
about recursion strength. In particular, every finite linear order is a
discrete order space; the six-point block check verifies the block mechanism,
not the infinite theorem about the number of isolated points.

Run:
    python finite_checks.py --output finite_checks.json

Checks use explicit exceptions, not ``assert``, and remain active under -O.
The JSON output is deterministic and contains no timing or machine data.
"""

from __future__ import annotations

import argparse
import itertools
import json
import math
from pathlib import Path
import sys
from typing import Any, Iterable, Sequence


class VerificationError(RuntimeError):
    """An explicitly checked finite claim failed."""


def require(condition: bool, message: str, **context: Any) -> None:
    """Check a condition even when Python optimization disables assertions."""
    if not condition:
        suffix = ""
        if context:
            suffix = ": " + json.dumps(context, sort_keys=True)
        raise VerificationError(message + suffix)


def compare(a: Any, b: Any) -> int:
    """Return -1, 0, or 1 according to the comparison of a and b."""
    return (a > b) - (a < b)


def relation_bits(
    permutation: Sequence[int], scan: Iterable[tuple[int, int]]
) -> tuple[int, ...]:
    """Encode the strict well-order specified by a finite enumeration."""
    positions = {label: index for index, label in enumerate(permutation)}
    return tuple(int(positions[x] < positions[y]) for x, y in scan)


def effective_scan(
    scan: Iterable[tuple[int, int]],
) -> tuple[tuple[int, int], ...]:
    """Keep the first direction of each unordered pair; discard diagonals."""
    seen: set[tuple[int, int]] = set()
    result: list[tuple[int, int]] = []
    for x, y in scan:
        if x == y:
            continue
        edge = (min(x, y), max(x, y))
        if edge not in seen:
            seen.add(edge)
            result.append((x, y))
    return tuple(result)


def labeled_order(
    permutations: Sequence[tuple[int, ...]],
    scan: Sequence[tuple[int, int]],
) -> tuple[tuple[int, ...], ...]:
    """The exact labeled order, not merely its finite cardinality."""
    return tuple(sorted(permutations, key=lambda p: relation_bits(p, scan)))


def check_three_labels() -> dict[str, Any]:
    """Exhaust all 3! * 2^3 = 48 effective scans on three labels."""
    labels = tuple(range(3))
    permutations = tuple(itertools.permutations(labels))
    unordered_edges = tuple(itertools.combinations(labels, 2))
    induced_orders: set[tuple[tuple[int, ...], ...]] = set()
    effective_scans: set[tuple[tuple[int, int], ...]] = set()

    for priority in itertools.permutations(range(3)):
        for flips in itertools.product((0, 1), repeat=3):
            directions = tuple(
                edge[::-1] if flip else edge
                for edge, flip in zip(unordered_edges, flips)
            )
            scan = tuple(directions[index] for index in priority)
            effective_scans.add(scan)
            induced_orders.add(labeled_order(permutations, scan))

    require(len(effective_scans) == 48, "Incorrect effective-scan count")
    require(len(induced_orders) == 36, "Incorrect induced labeled-order count")

    # Exhaust all six off-diagonal directed-coordinate orderings. Insert
    # diagonals at fixed, nonadjacent positions, retaining a full 9-entry scan.
    # This exhausts 6! cases, not all 9! placements of the diagonals.
    off_diagonal = tuple((x, y) for x in labels for y in labels if x != y)
    reduced_orders: set[tuple[tuple[int, ...], ...]] = set()
    directed_cases = 0
    for directed in itertools.permutations(off_diagonal):
        full_scan = (
            ((0, 0),)
            + directed[:2]
            + ((1, 1),)
            + directed[2:4]
            + ((2, 2),)
            + directed[4:]
        )
        reduced = effective_scan(full_scan)
        actual = labeled_order(permutations, full_scan)
        expected = labeled_order(permutations, reduced)
        require(actual == expected, "Effective scan changed the labeled order")
        require(reduced in effective_scans, "Unexpected reduced scan")
        reduced_orders.add(actual)
        directed_cases += 1
    require(directed_cases == 720, "Incorrect directed-scan reduction count")
    require(reduced_orders == induced_orders, "Reduction missed labeled orders")

    first = (0, 2, 1)
    second = (1, 0, 2)
    first_query = ((0, 1),)
    bits = (relation_bits(first, first_query)[0], relation_bits(second, first_query)[0])
    require(compare(first, second) == -1, "Enumeration example has wrong sign")
    require(bits == (1, 0), "Table example has wrong first bits")

    return {
        "status": "PASS",
        "labels": 3,
        "well_orders": 6,
        "effective_scans": len(effective_scans),
        "distinct_labeled_orders": len(induced_orders),
        "directed_scan_reduction_cases": directed_cases,
        "directed_scan_scope": (
            "All 6! off-diagonal priorities, with the three diagonals inserted "
            "in fixed nonadjacent positions; not all 9! diagonal placements."
        ),
        "comparison_reversal": {
            "first_enumeration": list(first),
            "second_enumeration": list(second),
            "enumeration_comparison": "<",
            "first_table_query": [0, 1],
            "first_table_bits": list(bits),
            "table_comparison": ">",
        },
    }


def check_delayed_six_coordinates() -> dict[str, Any]:
    """Check exact convex six-point fibers in the six-label finite analogue."""
    labels = tuple(range(6))
    y_labels = tuple(range(3))
    z_labels = tuple(range(3, 6))
    delayed = tuple((x, y) for x in z_labels for y in z_labels if x != y)
    delayed_set = set(delayed)
    early = tuple(
        (x, y) for x in labels for y in labels if (x, y) not in delayed_set
    )
    scan = early + delayed
    require(len(early) == 30 and len(delayed) == 6, "Incorrect delayed scan")
    require(len(set(scan)) == 36, "Scan does not cover all directed pairs")

    permutations = tuple(itertools.permutations(labels))
    codes = {p: relation_bits(p, scan) for p in permutations}
    ordered = tuple(sorted(permutations, key=codes.__getitem__))
    positions = {p: index for index, p in enumerate(ordered)}
    fibers: dict[tuple[int, ...], set[tuple[int, ...]]] = {}
    for p, code in codes.items():
        fibers.setdefault(code[: len(early)], set()).add(p)

    reports = []
    for q in itertools.permutations(y_labels):
        expected_fiber = {q + z for z in itertools.permutations(z_labels)}
        prefixes = {codes[p][: len(early)] for p in expected_fiber}
        require(len(prefixes) == 1, "The six orders have different early prefixes", q=q)
        prefix = next(iter(prefixes))
        actual_fiber = fibers[prefix]
        require(actual_fiber == expected_fiber, "The prefix fiber is not exactly six", q=q)
        indices = sorted(positions[p] for p in actual_fiber)
        require(
            indices == list(range(indices[0], indices[0] + 6)),
            "The six-point fiber is not contiguous",
            q=q,
            positions=indices,
        )
        for middle in indices[1:-1]:
            require(
                ordered[middle - 1] in actual_fiber
                and ordered[middle + 1] in actual_fiber,
                "A middle point lacks its two fiber neighbors",
                q=q,
                position=middle,
            )
        reports.append({"q_on_y": list(q), "positions_in_sorted_order": indices})

    return {
        "status": "PASS",
        "labels": 6,
        "well_orders_sorted": len(ordered),
        "early_coordinates": len(early),
        "delayed_coordinates": len(delayed),
        "specified_fibers_checked": len(reports),
        "orders_in_each_specified_fiber": 6,
        "middle_points_checked": 4 * len(reports),
        "fibers": reports,
        "scope": (
            "Finite verification of exact prefix fibers and contiguity only; "
            "the infinite isolation/cardinality theorem requires its written proof."
        ),
    }


def word_compare(
    first: Sequence[int], second: Sequence[int], *, prefix_smaller: bool
) -> int:
    """Compare words by letters, specifying how a proper prefix is ordered."""
    for x, y in zip(first, second):
        if x != y:
            return compare(x, y)
    result = compare(len(first), len(second))
    return result if prefix_smaller else -result


def check_increasing_word_cuts() -> dict[str, Any]:
    """Exhaust the cut-factorization identity on 64 increasing finite words."""
    alphabet = tuple(range(6))
    words = tuple(
        tuple(letter for letter in alphabet if mask & (1 << letter))
        for mask in range(1 << len(alphabet))
    )
    require(len(set(words)) == 64, "Incorrect increasing-word count")
    cut_reports = []
    total_comparisons = 0

    for cut in range(7):
        terminal_rank = 2 * cut - 1
        encoded = {
            word: tuple(2 * letter for letter in word) + (terminal_rank,)
            for word in words
        }
        split = {
            word: (
                tuple(letter for letter in word if letter < cut),
                tuple(letter for letter in word if letter >= cut),
            )
            for word in words
        }
        comparisons = 0
        for first in words:
            first_left, first_right = split[first]
            for second in words:
                second_left, second_right = split[second]
                direct = compare(encoded[first], encoded[second])
                factorized = word_compare(
                    first_left, second_left, prefix_smaller=False
                )
                if factorized == 0:
                    factorized = word_compare(
                        first_right, second_right, prefix_smaller=True
                    )
                require(
                    direct == factorized,
                    "Increasing-word cut factorization failed",
                    cut=cut,
                    first=first,
                    second=second,
                    direct=direct,
                    factorized=factorized,
                )
                comparisons += 1
        require(comparisons == 4096, "Incorrect pair count at a cut")
        total_comparisons += comparisons
        cut_reports.append(
            {
                "cut": cut,
                "terminal_rank": terminal_rank,
                "ordered_word_pairs_checked": comparisons,
            }
        )

    return {
        "status": "PASS",
        "alphabet": list(alphabet),
        "increasing_words": len(words),
        "cuts_checked": len(cut_reports),
        "ordered_word_pairs_checked": total_comparisons,
        "equal_pairs_included": True,
        "encoding": "Letter x has rank 2*x; the distinct terminal has rank 2*k-1.",
        "factorization": (
            "Compare the subword below k with a larger proper prefix first; "
            "if equal, compare the subword at least k with a smaller proper prefix."
        ),
        "cuts": cut_reports,
    }


def bit_height(mask: int) -> int:
    """Strict support bound max(support)+1, or 0 for empty support."""
    return mask.bit_length()


def check_finite_partial_injections() -> dict[str, Any]:
    """Exhaust restrictions of every permutation on carriers of size 0 through 6.

    A is the prescribed domain. D={a in A:h(a)!=a} is the MOVED prescribed
    domain, not all of A. Put R=h[D] and S=D union R. For finite injections
    |R\\D|=|D\\R|, so the reserve cardinal tau is always 0. We check all
    partial injections, including identities with arbitrarily high fixed
    prescribed labels, by finding their extensions through brute force.
    """
    reports = []
    total_extensions = 0
    total_injections = 0
    total_bound_checks = 0

    for n in range(7):
        labels = tuple(range(n))
        # A key uses -1 off the prescribed domain and h(a) on the domain.
        # Each record aggregates ALL permutation extensions found by brute force.
        records: dict[tuple[int, ...], dict[str, Any]] = {}
        extension_cases = 0
        permutation_count = 0
        for permutation in itertools.permutations(labels):
            permutation_count += 1
            support_mask = sum(
                1 << a for a in labels if permutation[a] != a
            )
            height = bit_height(support_mask)
            for domain_mask in range(1 << n):
                key = tuple(
                    permutation[a] if domain_mask & (1 << a) else -1
                    for a in labels
                )
                if key not in records:
                    records[key] = {
                        "min_height": height,
                        "height_mask": 1 << height,
                        "supports": {support_mask},
                    }
                else:
                    record = records[key]
                    record["min_height"] = min(record["min_height"], height)
                    record["height_mask"] |= 1 << height
                    record["supports"].add(support_mask)
                extension_cases += 1

        expected_injections = sum(
            math.comb(n, k) * math.factorial(n) // math.factorial(n - k)
            for k in range(n + 1)
        )
        require(permutation_count == math.factorial(n), "Missed a permutation", n=n)
        require(
            extension_cases == math.factorial(n) * (1 << n),
            "Incorrect permutation/domain-subset case count",
            n=n,
        )
        require(
            len(records) == expected_injections,
            "Did not enumerate all finite partial injections",
            n=n,
            found=len(records),
            expected=expected_injections,
        )

        bound_checks = 0
        identity_cases = 0
        minimum_height_histogram = {str(height): 0 for height in range(n + 1)}
        for key, record in records.items():
            domain = {a for a in labels if key[a] != -1}
            moved_domain = {a for a in domain if key[a] != a}
            moved_range = {key[a] for a in moved_domain}
            forced_support = moved_domain | moved_range
            forced_mask = sum(1 << a for a in forced_support)
            predicted_height = bit_height(forced_mask)
            u = len(moved_range - moved_domain)
            v = len(moved_domain - moved_range)

            require(u == v, "Finite reserve is unexpectedly nonzero", n=n, injection=key)
            require(
                not ((domain - moved_domain) & moved_range),
                "A prescribed fixed point was forced to move",
                n=n,
                injection=key,
            )
            require(
                record["min_height"] == predicted_height,
                "Minimum support height does not equal the forced-support height",
                n=n,
                injection=key,
                observed=record["min_height"],
                predicted=predicted_height,
            )
            require(
                forced_mask in record["supports"],
                "No extension has exactly the forced finite support",
                n=n,
                injection=key,
            )

            for beta in range(n + 1):
                observed_exists = bool(record["height_mask"] & ((1 << (beta + 1)) - 1))
                predicted_exists = all(a < beta for a in forced_support)
                require(
                    observed_exists == predicted_exists,
                    "Specified-bound extension criterion failed",
                    n=n,
                    injection=key,
                    beta=beta,
                )
                bound_checks += 1

            if not moved_domain:
                identity_cases += 1
                require(record["min_height"] == 0, "Prescribed identity forced motion")
            minimum_height_histogram[str(record["min_height"])] += 1

        require(identity_cases == 1 << n, "Missed a partial identity", n=n)
        total_extensions += extension_cases
        total_injections += len(records)
        total_bound_checks += bound_checks
        reports.append(
            {
                "carrier_size": n,
                "permutations_enumerated": permutation_count,
                "permutation_domain_subset_cases": extension_cases,
                "distinct_partial_injections": len(records),
                "specified_bound_checks": bound_checks,
                "partial_identity_cases": identity_cases,
                "minimum_height_histogram": minimum_height_histogram,
                "status": "PASS",
            }
        )

    return {
        "status": "PASS",
        "carrier_sizes": list(range(7)),
        "permutation_domain_subset_cases": total_extensions,
        "distinct_partial_injections": total_injections,
        "specified_bound_checks": total_bound_checks,
        "reserve_tau": 0,
        "forced_support_definition": "D={a in dom(h):h(a)!=a}; S=D union h[D].",
        "minimum_height_formula": "max(S)+1 when S is nonempty; 0 when S is empty.",
        "specified_bound_formula": "An extension supported below beta exists iff S is a subset of beta.",
        "scope": (
            "Only finite reserve tau=0 is tested. Infinite cardinal imbalance, "
            "fresh infinite reserves, and class permutations are not tested."
        ),
        "carriers": reports,
    }


def run_checks() -> dict[str, Any]:
    """Run all exhaustive finite checks, failing on the first discrepancy."""
    return {
        "status": "PASS",
        "format_version": 1,
        "scope": (
            "Reproducible exhaustive finite checks only. These results do not prove "
            "the infinite, proper-class, topological, or foundational theorems."
        ),
        "checks_active_under_python_optimization": True,
        "three_label_relation_tables": check_three_labels(),
        "delayed_six_coordinate_fibers": check_delayed_six_coordinates(),
        "increasing_word_cut_factorization": check_increasing_word_cuts(),
        "finite_partial_injection_completion": check_finite_partial_injections(),
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--output",
        type=Path,
        help="Write the deterministic JSON report here; otherwise print it to stdout.",
    )
    args = parser.parse_args()
    exit_code = 0
    try:
        report = run_checks()
    except VerificationError as error:
        report = {"status": "FAIL", "error": str(error)}
        exit_code = 1
    rendered = json.dumps(report, indent=2, sort_keys=True) + "\n"
    if args.output is None:
        sys.stdout.write(rendered)
    else:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(rendered, encoding="utf-8")
        print(f"{report['status']}: {args.output}")
    return exit_code


if __name__ == "__main__":
    raise SystemExit(main())
