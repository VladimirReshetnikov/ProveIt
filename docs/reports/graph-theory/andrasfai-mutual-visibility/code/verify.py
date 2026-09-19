#!/usr/bin/env python3
"""Independent checks for article.pdf (standard library only).

Run after the optional C++ exhaustive checker; checks its JSON if present.
"""
from __future__ import annotations

import json
import random
from collections import Counter, deque
from pathlib import Path
from time import perf_counter

from visibility import (EDGES, UniformSampler, fixed_deficit, graph, is_visible,
                        polynomial, polynomial_blocks, sequence, total)

DATA = Path(__file__).resolve().parent.parent / "data"
OEIS_TERMS = [4, 21, 127, 749, 4455, 26725, 161007, 971613,
              5866487, 35426517, 213940607, 1291991757,
              7802356615, 47118492485, 284548794383]


def distances(adjacency, source, blocked_mask=0):
    """BFS may reach selected vertices but cannot expand them (except source)."""
    result = [-1] * len(adjacency)
    result[source] = 0
    queue = deque([source])
    while queue:
        vertex = queue.popleft()
        if vertex != source and ((blocked_mask >> vertex) & 1):
            continue
        for target in adjacency[vertex]:
            if result[target] < 0:
                result[target] = result[vertex] + 1
                queue.append(target)
    return result


def bfs_visible(adjacency, original, mask):
    selected = [i for i in range(len(adjacency)) if (mask >> i) & 1]
    for source in selected:
        restricted = distances(adjacency, source, mask)
        if any(restricted[target] != original[source][target] for target in selected):
            return False
    return True


def closed_walk_masks(length):
    """Enumerate actual labeled closed walks, retaining their multiplicities."""
    result = Counter()
    for start in range(4):
        def visit(state, position, mask):
            if position == length:
                if state == start:
                    result[mask] += 1
                return
            for target, bit in EDGES[state]:
                visit(target, position + 1, mask | (bit << position))
        visit(start, 0, 0)
    return result


def main():
    start_time = perf_counter()
    assert sequence(15) == OEIS_TERMS
    assert [total(n) for n in range(1, 251)] == sequence(250)
    bfs_rows = []
    for n in range(1, 6):
        adjacency = graph(n)
        length = len(adjacency)
        original = [distances(adjacency, source) for source in range(length)]
        coefficients = [0] * (length + 1)
        accepted = set()
        for mask in range(1 << length):
            direct = bfs_visible(adjacency, original, mask)
            word = [(mask >> i) & 1 for i in range(length)]
            assert direct == is_visible(n, word), (n, mask)
            if direct:
                coefficients[bin(mask).count("1")] += 1
                accepted.add(mask)
        while coefficients[-1] == 0:
            coefficients.pop()
        assert coefficients == polynomial(n)
        walks = closed_walk_masks(length)
        expected = accepted if n > 1 else accepted - {3}
        assert set(walks) == expected
        assert all(multiplicity == 1 for multiplicity in walks.values())
        bfs_rows.append({"n": n, "subsets": 1 << length,
                         "total": len(accepted), "closed_walks_unique": True})

    for n in range(2, 41):
        coefficients = polynomial(n)
        assert coefficients == polynomial_blocks(n), n
        assert len(coefficients) == 2 * n
        assert coefficients[-1] == 3 * n - 1
        assert sum(coefficients) == total(n)
        for h in range(min(10, 2 * n - 1)):
            assert fixed_deficit(n, h) == coefficients[2 * n - 1 - h], (n, h)

    cpp = None
    if (DATA / "exhaustive.json").exists():
        cpp = json.loads((DATA / "exhaustive.json").read_text())
        assert cpp["mismatches"] == 0
        for row in cpp["rows"]:
            assert row["coefficients"] == polynomial(row["n"])
            assert row["total"] == total(row["n"])

    rng = random.Random(20260919)
    sample_count = 0
    for n in [1, 2, 3, 5, 8, 20, 50]:
        sampler = UniformSampler(n, rng)
        for _ in range(1000):
            assert is_visible(n, sampler.sample())
            sample_count += 1
    report = {
        "status": "PASS", "oeis_terms_matched": len(OEIS_TERMS),
        "recurrence_matrix_agreement_through_n": 250,
        "BFS_checks": bfs_rows,
        "BFS_subsets_tested": sum(row["subsets"] for row in bfs_rows),
        "block_formula_agreement_n": [2, 40],
        "deficit_formula_checked_h": "0..min(9,2*n-2), for n=2..40",
        "C++_subsets_tested": None if cpp is None else cpp["subsets_tested"],
        "sampled_words_checked": sample_count,
        "elapsed_seconds": perf_counter() - start_time,
    }
    DATA.mkdir(exist_ok=True)
    (DATA / "verification.json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
