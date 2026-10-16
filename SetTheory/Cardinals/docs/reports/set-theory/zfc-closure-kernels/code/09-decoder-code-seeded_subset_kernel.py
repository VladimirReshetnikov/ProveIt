#!/usr/bin/env python3
"""Exact HF regression for the subset-only seeded-closure construction.

An integer n codes the hereditarily finite set whose members have codes at
the one-bit positions of n. This checks the transitive-container gadget
in ordinary finite sets; the universal theory proof is in the report.
No consistency of ZFC, axiom independence, or TM state bound follows from
these finite calculations.
"""
from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path


def members(code: int):
    while code:
        least = code & -code
        yield least.bit_length() - 1
        code ^= least


def subsets(code: int):
    part = code
    while True:
        yield part
        if part == 0:
            return
        part = (part - 1) & code


def fiber(root: int, x: int) -> tuple[int, tuple[int, ...]]:
    """Return a subset bound and the exact output fiber of R_root(x,-)."""
    if x == 0:
        return root, tuple(subsets(root))
    if x & (x - 1) == 0:
        z = x.bit_length() - 1
        return z, (z,)
    return x, tuple(subsets(x))


def container(root: int) -> tuple[set[int], dict[int, int], int]:
    reached: set[int] = set()
    predecessor: dict[int, int] = {}
    todo = [0]
    expanded: set[int] = set()
    edges = 0
    while todo:
        x = todo.pop()
        if x in expanded:
            continue
        expanded.add(x)
        bound, outputs = fiber(root, x)
        for y in outputs:
            assert y & ~bound == 0, "claimed subset fiber bound is false"
            edges += 1
            if y not in reached:
                reached.add(y)
                predecessor[y] = x
                todo.append(y)
    return reached, predecessor, edges


def checks(limit: int) -> dict:
    if limit < 1:
        raise ValueError("limit must be positive")
    total_edges = total_members = 0
    largest = 0
    digest = hashlib.sha256()
    for root in range(limit):
        c, pred, edges = container(root)
        # The seed is a trigger; inclusion of it follows here from its own
        # fiber, rather than from silently assuming seeded points are outputs.
        assert 0 in c and root in c
        assert set(subsets(root)) <= c
        for x in c:
            assert set(members(x)) <= c, "container is not transitive"
            _, outputs = fiber(root, x)
            assert set(outputs) <= c, "container is not R-closed"
            # A predecessor demonstrates no junk in the global image.
            assert x in fiber(root, pred[x])[1]
        total_edges += edges
        total_members += len(c)
        largest = max(largest, len(c))
        digest.update((str(root) + ':' + ','.join(map(str, sorted(c))) + '\n').encode())
    return {
        "status": "PASS",
        "hf_roots": limit,
        "fiber_edges_checked": total_edges,
        "total_container_members": total_members,
        "largest_container_cardinality": largest,
        "ordered_container_data_sha256": digest.hexdigest(),
        "checks": ["exact subset bounds", "root inclusion", "all root subsets included",
                   "transitivity", "relation closure", "global range purity"],
        "scope": "HF regression only; the report gives the all-model proof and consistency calibration.",
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--limit", type=int, default=4096)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    result = json.dumps(checks(args.limit), indent=2) + '\n'
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(result, encoding="utf-8")
    print(result, end="")


if __name__ == "__main__":
    if not __debug__:
        raise SystemExit("Run without -O: this regression relies on assertions.")
    main()
