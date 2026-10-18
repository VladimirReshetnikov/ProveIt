#!/usr/bin/env python3
"""Independent finite audit of the induced HF-membership embedding lemma.

The mathematical proof is in foundation_seed_review.md. This exhaustive check
validates the construction on all directed loop-free graphs through four
vertices; finite testing is not the proof of the general lemma.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path


def ordinal(n: int) -> frozenset:
    values = []
    for _ in range(n):
        values.append(frozenset(values))
    return frozenset(values)


def embed(vertices: int, edges: set[tuple[int, int]]) -> list[frozenset] | None:
    tags = [frozenset((ordinal(i), ordinal(vertices))) for i in range(vertices)]
    active: set[int] = set()
    done: dict[int, frozenset] = {}

    def visit(i: int) -> frozenset:
        if i in done:
            return done[i]
        if i in active:
            raise ValueError("cycle")
        active.add(i)
        value = frozenset([tags[i]] + [visit(j) for j in range(vertices) if (j, i) in edges])
        active.remove(i)
        done[i] = value
        return value

    try:
        return [visit(i) for i in range(vertices)]
    except ValueError:
        return None


def check(max_vertices: int) -> dict:
    results = []
    for n in range(max_vertices + 1):
        pairs = [(i, j) for i in range(n) for j in range(n) if i != j]
        successes = cycles = 0
        for mask in range(1 << len(pairs)):
            edges = {pair for k, pair in enumerate(pairs) if mask & (1 << k)}
            values = embed(n, edges)
            if values is None:
                cycles += 1
                continue
            assert len(set(values)) == n
            assert all((values[i] in values[j]) == ((i, j) in edges)
                       for i in range(n) for j in range(n))
            successes += 1
        results.append({"vertices": n, "graphs": 1 << len(pairs),
                        "successful_induced_HF_embeddings": successes,
                        "cycles_detected": cycles})
    return {"scope": "independent finite validation of the general written HF embedding lemma",
            "graphs_by_size": results,
            "all_embeddings_distinct_and_induced": True}


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--max-vertices", type=int, default=4)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    if not __debug__:
        raise SystemExit("run with assertions enabled")
    if not 0 <= args.max_vertices <= 5:
        raise SystemExit("choose at most five vertices for this finite audit")
    payload = json.dumps(check(args.max_vertices), indent=2) + "\n"
    if args.output:
        args.output.write_text(payload)
    else:
        print(payload, end="")


if __name__ == "__main__":
    main()
