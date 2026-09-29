#!/usr/bin/env python3
"""Exact, finite cross-checks for The Gamma-Vector of Every Finite Preorder.

Standard library only; Python >= 3.10. These tests do not prove the theorems.
Relations are tuples of integer bitmasks: bit j of row i means i <= j.
The direct lattice enumerator knows nothing about the gamma formula.
The matching checker uses recursive assignment, not Hall inequalities.

Usage: python3 code/verify.py --max-n 5 --output results/verification.json
"""
from __future__ import annotations

import argparse
from functools import lru_cache
from itertools import product
import json
from math import comb
from pathlib import Path
import random
import sys
import time
from typing import Iterator

Relation = tuple[int, ...]


def bits(mask: int) -> Iterator[int]:
    while mask:
        bit = mask & -mask
        yield bit.bit_length() - 1
        mask ^= bit


def submasks(mask: int) -> Iterator[int]:
    current = mask
    while True:
        yield current
        if current == 0:
            return
        current = (current - 1) & mask


def validate_preorder(rows: Relation) -> None:
    n = len(rows)
    full = (1 << n) - 1
    if any(r < 0 or r & ~full for r in rows):
        raise ValueError("Relation row has an out-of-range bit.")
    if any(not (r >> i & 1) for i, r in enumerate(rows)):
        raise ValueError("Relation is not reflexive.")
    if any(rows[j] & ~r for r in rows for j in bits(r)):
        raise ValueError("Relation is not transitive.")


def closure(n: int, edges: list[tuple[int, int]]) -> Relation:
    rows = [1 << i for i in range(n)]
    for i, j in edges:
        if not 0 <= i < n or not 0 <= j < n:
            raise ValueError("Edge endpoint out of range.")
        rows[i] |= 1 << j
    for k in range(n):
        for i in range(n):
            if rows[i] >> k & 1:
                rows[i] |= rows[k]
    return tuple(rows)


def all_preorders(n: int) -> Iterator[Relation]:
    """Visit EVERY labeled reflexive relation, retain exactly transitive ones."""
    if n == 0:
        yield ()
        return
    row_options = []
    for i in range(n):
        optional = [j for j in range(n) if j != i]
        row_options.append(tuple((1 << i) | sum(1 << optional[k]
            for k in bits(mask)) for mask in range(1 << (n - 1))))
    for rows in product(*row_options):
        if all(not (rows[j] & ~r) for r in rows for j in bits(r)):
            yield rows


def weak_vectors(n: int, bound: int) -> Iterator[tuple[int, ...]]:
    """All nonnegative n-vectors with sum AT MOST bound, once each."""
    if n == 0:
        yield ()
    else:
        for value in range(bound + 1):
            for tail in weak_vectors(n - 1, bound - value):
                yield (value,) + tail


@lru_cache(maxsize=None)
def vector_cache(n: int) -> tuple[tuple[int, tuple[int, ...]], ...]:
    data = []
    for x in weak_vectors(n, n):
        support = sum(1 << i for i, v in enumerate(x) if v)
        sums = [0] * (1 << n)
        for mask in range(1, 1 << n):
            bit = mask & -mask
            sums[mask] = sums[mask ^ bit] + x[bit.bit_length() - 1]
        data.append((support, tuple(sums)))
    return tuple(data)


def direct_support_counts(rows: Relation) -> list[int]:
    """Enumerate lattice points using ONLY the original lower-ideal inequalities."""
    n = len(rows)
    predecessors = [sum(1 << i for i, r in enumerate(rows) if r >> j & 1)
                    for j in range(n)]
    ideals = [(mask, mask.bit_count()) for mask in range(1, 1 << n)
              if all(not (predecessors[j] & ~mask) for j in bits(mask))]
    counts = [0] * (1 << n)
    for support, sums in vector_cache(n):
        if all(sums[mask] <= capacity for mask, capacity in ideals):
            counts[support] += 1
    return counts


def matching_function(rows: Relation):
    """Existence of a bijection from masks U to V along the supplied rows."""
    @lru_cache(maxsize=None)
    def matches(U: int, V: int) -> bool:
        if U.bit_count() != V.bit_count():
            return False
        if not U:
            return True
        first = U & -U
        i = first.bit_length() - 1
        for j in bits(rows[i] & V):
            if matches(U ^ first, V ^ (1 << j)):
                return True
        return False
    return matches


def gamma_from_h(h: list[int]) -> list[int]:
    n = len(h) - 1
    residual = h.copy()
    gamma = []
    for k in range(n // 2 + 1):
        coefficient = residual[k]
        gamma.append(coefficient)
        for j in range(n - 2 * k + 1):
            residual[k + j] -= coefficient * comb(n - 2 * k, j)
    if any(residual):
        raise AssertionError(("No symmetric gamma expansion", h, residual))
    return gamma


def comparability_matching_number(rows: Relation) -> int:
    n = len(rows)
    adj = [sum(1 << j for j in range(n) if i != j and
               ((rows[i] >> j & 1) or (rows[j] >> i & 1))) for i in range(n)]
    @lru_cache(maxsize=None)
    def maximum(mask: int) -> int:
        if not mask:
            return 0
        first = mask & -mask
        i = first.bit_length() - 1
        tail = mask ^ first
        answer = maximum(tail)
        for j in bits(adj[i] & tail):
            answer = max(answer, 1 + maximum(tail ^ (1 << j)))
        return answer
    return maximum((1 << n) - 1)


def check_one(rows: Relation) -> dict[str, object]:
    validate_preorder(rows)
    n = len(rows)
    full = (1 << n) - 1
    direct = direct_support_counts(rows)
    predicted = [0] * (1 << n)
    h = [0] * (n + 1)
    for mask, count in enumerate(direct):
        h[mask.bit_count()] += count
    matches = matching_function(rows)
    gamma = [0] * (n // 2 + 1)
    for U in range(1 << n):
        complement = full ^ U
        for V in submasks(complement):
            if U.bit_count() == V.bit_count() and matches(U, V):
                gamma[V.bit_count()] += 1
                for C in submasks(full ^ (U | V)):
                    predicted[V | C] += 1
    if direct != predicted:
        raise AssertionError(("Multivariate identity", rows, direct, predicted))
    if gamma != gamma_from_h(h):
        raise AssertionError(("Gamma identity", rows, h, gamma))
    # Independent relation-graph model: overlap IS allowed in A and B.
    relation_supports = [0] * (1 << n)
    for A in range(1 << n):
        for B in range(1 << n):
            if A.bit_count() == B.bit_count() and matches(A, B):
                relation_supports[B] += 1
                if not matches(A & ~B, B & ~A):
                    raise AssertionError(("Overlap compression", rows, A, B))
    if direct != relation_supports:
        raise AssertionError(("Relation graph identity", rows))
    nu = comparability_matching_number(rows)
    if max(k for k, c in enumerate(gamma) if c) != nu:
        raise AssertionError(("Matching-number degree", rows, gamma, nu))
    # Direct Taylor coefficients of h at -1 check the exact multiplicity.
    taylor = [sum(h[j] * comb(j, d) * (-1) ** (j - d)
                  for j in range(d, n + 1)) for d in range(n + 1)]
    deficiency = n - 2 * nu
    if min(d for d, c in enumerate(taylor) if c) != deficiency:
        raise AssertionError(("Minus-one multiplicity", rows, h, nu))
    if taylor[deficiency] != (-1) ** nu * gamma[nu]:
        raise AssertionError(("Leading Taylor coefficient", rows))
    dual = tuple(sum(1 << j for j in range(n) if rows[j] >> i & 1)
                 for i in range(n))
    dual_counts = direct_support_counts(dual)
    if any(direct[S] != dual_counts[full ^ S] for S in range(1 << n)):
        raise AssertionError(("Multivariate duality", rows))
    # Deletion--differentiation law, using direct lattice counts on deletions.
    deck = [0] * n
    for removed in range(n):
        keep = [i for i in range(n) if i != removed]
        induced = tuple(sum(1 << b for b, j in enumerate(keep)
                            if rows[i] >> j & 1) for i in keep)
        deletion_counts = direct_support_counts(induced)
        for S, count in enumerate(deletion_counts):
            deck[S.bit_count()] += count
    for j in range(n + 1):
        d_j = deck[j] if j < n else 0
        d_prev = deck[j - 1] if j else 0
        if d_j - d_prev != (n - 2 * j) * h[j]:
            raise AssertionError(("Deletion differential law", rows, j))
    return {"n": n, "rows": list(rows), "h": h, "gamma": gamma,
            "matching_number": nu, "minus_one_multiplicity": n - 2 * nu,
            "lattice_points": sum(h)}


def bipartite_lemma_suite(p: int = 3, q: int = 3) -> dict[str, int]:
    """All bipartite graphs on fixed labeled shores p and q."""
    checked = 0
    for mask in range(1 << (p * q)):
        rows = tuple((mask >> (i * q)) & ((1 << q) - 1) for i in range(p))
        demands_by_support = [0] * (1 << q)
        neighborhoods = [sum(1 << i for i, row in enumerate(rows) if row & S)
                         for S in range(1 << q)]
        for c in weak_vectors(q, p):
            if all(sum(c[j] for j in bits(S)) <= neighborhoods[S].bit_count()
                   for S in range(1 << q)):
                demands_by_support[sum(1 << j for j, v in enumerate(c) if v)] += 1
        supports_by_right = [0] * (1 << q)
        matches = matching_function(rows)
        for U in range(1 << p):
            for V in range(1 << q):
                if U.bit_count() == V.bit_count() and matches(U, V):
                    supports_by_right[V] += 1
        if demands_by_support != supports_by_right:
            raise AssertionError(("Classical counting lemma", p, q, mask))
        checked += 1
    return {"left_shore": p, "right_shore": q, "graphs": checked}


def blowup(quotient: Relation, sizes: tuple[int, ...]) -> Relation:
    validate_preorder(quotient)
    if len(quotient) != len(sizes) or any(m < 1 for m in sizes):
        raise ValueError("One positive size is required for each quotient vertex.")
    labels = [i for i, m in enumerate(sizes) for _ in range(m)]
    return tuple(sum(1 << b for b, j in enumerate(labels) if quotient[i] >> j & 1)
                 for i in labels)


def block_gamma(quotient: Relation, sizes: tuple[int, ...]) -> list[int]:
    n, b = sum(sizes), len(sizes)
    output = [0] * (n // 2 + 1)
    neighborhoods = [tuple(i for i in range(b) if any(quotient[i] >> j & 1
                     for j in bits(T))) for T in range(1 << b)]
    options = [[(a, d, comb(m, a) * comb(m - a, d))
                for a in range(m + 1) for d in range(m - a + 1)] for m in sizes]
    for profile in product(*options):
        a = [v[0] for v in profile]
        d = [v[1] for v in profile]
        k = sum(d)
        if sum(a) != k:
            continue
        if any(sum(d[j] for j in bits(T)) > sum(a[i] for i in neighborhoods[T])
               for T in range(1 << b)):
            continue
        weight = 1
        for _, _, w in profile:
            weight *= w
        output[k] += weight
    return output


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-n", type=int, default=5)
    parser.add_argument("--output", type=Path, default=Path("results/verification.json"))
    args = parser.parse_args()
    if not 0 <= args.max_n <= 5:
        parser.error("Exhaustive enumeration is deliberately limited to 0 <= max-n <= 5.")
    started = time.perf_counter()
    report: dict[str, object] = {
        "description": "Finite checks, not proof-assistant verification or an infinite proof",
        "python": sys.version.split()[0], "seed": 20260929,
        "checked_properties": [
            "exact-support multivariate disjoint-pair expansion",
            "triangular gamma extraction versus disjoint-pair count",
            "reflexive relation-graph matching-support model",
            "transitive overlap cancellation",
            "complement-duality for every exact support",
            "gamma degree versus ordinary comparability matching number",
            "exact minus-one multiplicity and leading Taylor coefficient",
            "deletion-differentiation law via direct deleted lattice counts",
            "bipartite demand lemma refined by exact receiver support",
            "weighted equivalence-block profile formula",
        ],
        "exhaustive_preorders": [], "bipartite_graphs": [], "examples": {},
    }
    expected = [1, 1, 4, 29, 355, 6942]
    for n in range(args.max_n + 1):
        count = 0
        start = time.perf_counter()
        for rows in all_preorders(n):
            check_one(rows)
            count += 1
        if count != expected[n]:
            raise AssertionError(("Preorder enumeration count", n, count, expected[n]))
        item = {"n": n, "preorders": count,
                "seconds": round(time.perf_counter() - start, 3)}
        report["exhaustive_preorders"].append(item)
        print("EXHAUSTIVE", item, flush=True)
    for p, q in [(0, 0), (0, 3), (3, 0), (2, 3), (3, 3), (3, 4)]:
        item = bipartite_lemma_suite(p, q)
        report["bipartite_graphs"].append(item)
        print("BIPARTITE", item, flush=True)
    rng = random.Random(20260929)
    random_unique: set[Relation] = set()
    for n in [6, 7]:
        for _ in range(60):
            edges = [(i, j) for i in range(n) for j in range(n)
                     if i != j and rng.random() < 0.12]
            random_unique.add(closure(n, edges))
    for rows in sorted(random_unique, key=lambda r: (len(r), r)):
        check_one(rows)
    report["random_preorders"] = {"generated": 120,
        "distinct": len(random_unique), "sizes": [6, 7]}
    print("RANDOM", report["random_preorders"], flush=True)
    examples = {
        "chain_3": closure(3, [(0, 1), (1, 2)]),
        "equivalence_3": tuple([7] * 3),
        "block_chain_2_1_2": blowup(closure(3, [(0, 1), (1, 2)]), (2, 1, 2)),
        "block_star_2_1_3": blowup(closure(3, [(0, 2), (1, 2)]), (2, 1, 3)),
        "diamond_4": closure(4, [(0, 1), (0, 2), (1, 3), (2, 3)]),
    }
    for name, rows in examples.items():
        report["examples"][name] = check_one(rows)
        print("EXAMPLE", name, report["examples"][name], flush=True)
    block_cases = 0
    for qrows in all_preorders(3):
        # Here permit a preorder quotient too; the capacity formula still works.
        for sizes in [(1, 1, 1), (2, 1, 2), (2, 2, 2)]:
            result = check_one(blowup(qrows, sizes))
            if result["gamma"] != block_gamma(qrows, sizes):
                raise AssertionError(("Block formula", qrows, sizes))
            block_cases += 1
    report["block_cases"] = block_cases
    report["seconds_total"] = round(time.perf_counter() - started, 3)
    report["status"] = "ALL CHECKS PASSED"
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print("ALL CHECKS PASSED; results written to", args.output, flush=True)


if __name__ == "__main__":
    main()
