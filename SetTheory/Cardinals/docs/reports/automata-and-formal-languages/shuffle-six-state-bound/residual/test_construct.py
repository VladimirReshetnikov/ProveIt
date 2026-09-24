#!/usr/bin/env python3
"""Replay constructive witnesses. These are regression tests, not coverage proof."""
from __future__ import annotations
import itertools
import json
import random
from pathlib import Path
from construct import Constructor
from verify import cells


def main() -> None:
    engine = Constructor()
    results = {}
    count, max_length = 0, 0
    # Every grid subset, every valid origin, for m,n <= 3.
    for m in range(1, 4):
        for n in range(1, 4):
            for mask in range(1, 1 << (m * n)):
                S = {(i, j) for i in range(m) for j in range(n)
                     if mask & (1 << (i * n + j))}
                for origin in itertools.product(range(m), range(n)):
                    if any(i == origin[0] for i, _ in S) and any(j == origin[1] for _, j in S):
                        word = engine.reach(m, n, S, origin)
                        max_length = max(max_length, len(word)); count += 1
    results["all_valid_origins_through_3x3"] = count
    # Every certificate target, from every origin, including transposition.
    count2 = 0
    for record in engine.records:
        m, n = record["m"], record["n"]
        S = cells(record["columns"], m)
        for origin in itertools.product(range(m), range(n)):
            word = engine.reach(m, n, S, origin)
            max_length = max(max_length, len(word)); count2 += 1
        engine.reach(n, m, {(j, i) for i, j in S}, (n - 1, m - 1))
        count2 += 1
    results["certificate_targets_all_origins_plus_transposes"] = count2
    # Reproducibly chosen examples with widths well past the finite core.
    rng = random.Random(20260920)
    count3 = 0
    for n in (7, 11, 20, 37, 64):
        for _ in range(20):
            S = {(i, j) for i in range(6) for j in range(n) if rng.randrange(3) == 0}
            origin = (rng.randrange(6), rng.randrange(n))
            S.add((origin[0], rng.randrange(n)))
            S.add((rng.randrange(6), origin[1]))
            word = engine.reach(6, n, S, origin)
            max_length = max(max_length, len(word)); count3 += 1
    results["deterministic_random_wide_targets"] = count3
    results["maximum_word_length_observed"] = max_length
    results["all_word_replays_and_length_bounds_passed"] = True
    Path(__file__).with_name("construction_tests.json").write_text(json.dumps(results, indent=2) + "\n")
    print(json.dumps(results, indent=2))

if __name__ == "__main__":
    main()
