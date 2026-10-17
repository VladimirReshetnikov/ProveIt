#!/usr/bin/env python3
"""Independently certify termination of the supplied allocation's epsilon graph.

Only records with recipe ``erase`` or ``control`` are treated as zero-step
edges. The source graph is checked to be functional on those vertices and
to have no additional outgoing alternatives there. A natural rank is then
computed from the complete finite graph and checked on every epsilon edge.

This is a control-progress certificate for the exact abstract graph bytes.
It neither counts binary states nor verifies a subsequent binary compiler.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from collections import Counter
from pathlib import Path


def main() -> None:
    if not __debug__:
        raise SystemExit("run with assertions enabled")
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("certificate", type=Path)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    source_bytes = args.certificate.read_bytes()
    source = json.loads(source_bytes)
    records = source["records"]
    sites = {r["source"] for r in records} | {r["target"] for r in records}
    outgoing = Counter(r["source"] for r in records)
    epsilon: dict[int, int] = {}
    modes = Counter()
    for record in records:
        recipe = record["recipe"][0]
        if recipe not in ("erase", "control"):
            continue
        u, v = record["source"], record["target"]
        assert outgoing[u] == 1, ("epsilon_source_has_an_alternative", u)
        assert u not in epsilon, ("duplicate_epsilon_source", u)
        epsilon[u] = v
        modes[recipe] += 1

    rank: dict[int, int] = {v: 0 for v in sites if v not in epsilon}
    cycles: list[list[int]] = []
    for start in sorted(epsilon):
        if start in rank:
            continue
        path: list[int] = []
        index: dict[int, int] = {}
        v = start
        while v not in rank:
            if v in index:
                cycles.append(path[index[v] :])
                break
            index[v] = len(path)
            path.append(v)
            v = epsilon[v]
        if cycles:
            break
        for u in reversed(path):
            rank[u] = rank[epsilon[u]] + 1

    assert not cycles, ("epsilon_cycle", cycles)
    assert set(rank) == sites
    for u, v in epsilon.items():
        assert rank[u] == rank[v] + 1

    result = {
        "status": "PASS exact finite epsilon-graph rank certificate",
        "input_sha256": hashlib.sha256(source_bytes).hexdigest(),
        "coarse_sites": len(sites),
        "coarse_edges": len(records),
        "epsilon_edges": len(epsilon),
        "epsilon_edge_kinds": dict(sorted(modes.items())),
        "epsilon_cycles": 0,
        "max_consecutive_epsilon_edges": max(rank.values(), default=0),
        "rank_histogram": {
            str(k): v for k, v in sorted(Counter(rank.values()).items())
        },
        "all_epsilon_sources_have_exactly_one_outgoing_edge": True,
        "rank_decreases_strictly_on_every_epsilon_edge": True,
        "rank": {str(k): v for k, v in sorted(rank.items())},
        "scope": (
            "Progress for the supplied abstract allocation graph only. "
            "Source extraction, masks, storage, initial frame, halting labels "
            "and emitted binary code retain their separate proof obligations."
        ),
    }
    args.output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({k: v for k, v in result.items() if k != "rank"}, indent=2))


if __name__ == "__main__":
    main()
