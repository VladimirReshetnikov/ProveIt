#!/usr/bin/env python3
"""Independently verify a serialized natural-counter invariant.

Usage:
  python verify_zones.py --graph program_cases.json --zone zones8.txt

This checker needs only the two supplied data files.  It does not import the
worklist generator, repeat its cap rounding, or trust its postfix check.  For
each enabled edge it computes the exact (uncapped) difference-bound postimage
and checks inclusion in the supplied successor invariant.  Graph extraction
from the source program and the later TM simulation are separate obligations.
"""
from __future__ import annotations

import argparse
from collections import Counter
import hashlib
import json
from math import inf
from pathlib import Path

DIM = 10
ENCODED_INFINITY = 999999


def require(condition, message):
    if not condition:
        raise ValueError(message)


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def canonicalize(matrix):
    """Floyd--Warshall closure of xi-xj <= matrix[i][j]."""
    result = [row[:] for row in matrix]
    for k in range(DIM):
        for i in range(DIM):
            for j in range(DIM):
                result[i][j] = min(result[i][j], result[i][k] + result[k][j])
    if any(result[i][i] < 0 for i in range(DIM)):
        return None
    return result


def load_graph(path):
    graph = json.loads(path.read_text())
    sites, cases, targets = (graph[k] for k in ("sites", "cases", "targets"))
    require(len(cases) == len(targets), "different case and target counts")
    require(type(graph["first"]) is int and 0 <= graph["first"] < len(sites),
            "invalid entry site")
    require(len(graph.get("source_sha256", "")) == 64, "missing source digest")
    seen = [Counter() for _ in sites]
    for index, (case, target) in enumerate(zip(cases, targets)):
        require(len(case) == 5, f"case {index}: wrong arity")
        site, path_string, op, register, zero = case
        require(type(site) is int and 0 <= site < len(sites),
                f"case {index}: invalid site")
        require(sites[site] == [path_string, op, register],
                f"case {index}: disagrees with its site")
        require(op in ("CI", "CD", "CB", "CC", "CH"),
                f"case {index}: unknown operation")
        if op in ("CI", "CD"):
            require(type(register) is int and 0 <= register < 9,
                    f"case {index}: invalid register")
        require(type(zero) is bool if op == "CD" else zero is None,
                f"case {index}: invalid branch marker")
        if op == "CH":
            require(target is None, f"case {index}: halt has a successor")
        else:
            require(type(target) is int and 0 <= target < len(sites),
                    f"case {index}: invalid target")
        seen[site][zero] += 1
    for site, (_, op, _) in enumerate(sites):
        require(seen[site] == (Counter({True: 1, False: 1}) if op == "CD"
                              else Counter({None: 1})),
                f"site {site}: missing or repeated cases")
    return graph


def load_zones(path, expected_count):
    lines = path.read_text().splitlines()
    count, cap, pops, updates = map(int, lines[0].split())
    require(count == expected_count and len(lines) == count + 1,
            "zone and graph site counts differ")
    require(1 <= cap <= 10000, "invalid cap")
    zones = []
    for site, line in enumerate(lines[1:]):
        values = list(map(int, line.split()))
        if values == [0]:
            zones.append(None)
            continue
        require(len(values) == 101 and values[0] == 1,
                f"site {site}: invalid zone row")
        require(all(v == ENCODED_INFINITY or -cap <= v <= cap
                    for v in values[1:]), f"site {site}: invalid finite bound")
        values = [inf if v == ENCODED_INFINITY else v for v in values[1:]]
        matrix = [values[i:i + DIM] for i in range(0, DIM * DIM, DIM)]
        require(all(matrix[i][i] == 0 for i in range(DIM)),
                f"site {site}: nonzero diagonal")
        require(all(matrix[0][i] <= 0 for i in range(DIM)),
                f"site {site}: missing natural-counter restriction")
        zones.append(matrix)
    return zones, cap, pops, updates


def verify(graph_path, zone_path):
    graph = load_graph(graph_path)
    zones, cap, pops, updates = load_zones(zone_path, len(graph["sites"]))
    initial = zones[graph["first"]]
    require(initial is not None and all(v >= 0 for row in initial for v in row),
            "the all-zero entry valuation is excluded")
    closed = []
    for site, matrix in enumerate(zones):
        result = None if matrix is None else canonicalize(matrix)
        require(matrix is None or result is not None,
                f"site {site}: marked live but inconsistent")
        closed.append(result)
    excluded = []
    edge_count = 0
    halt_count = 0
    op_counts = Counter()
    finite_bounds_checked = 0
    for index, (case, target) in enumerate(zip(graph["cases"], graph["targets"])):
        site, _, op, register, zero = case
        if closed[site] is None:
            excluded.append(index)
            continue
        pre = [row[:] for row in closed[site]]
        if op == "CD":
            r = register + 1
            if zero:
                pre[r][0] = min(pre[r][0], 0)  # xr <= 0 and xr >= 0.
            else:
                pre[0][r] = min(pre[0][r], -1)  # xr >= 1.
            pre = canonicalize(pre)
        if pre is None:
            excluded.append(index)
            continue
        delta = [0] * DIM
        if op == "CI":
            delta[register + 1] = 1
        elif op == "CD" and not zero:
            delta[register + 1] = -1
        # Translation is the exact postimage of this guarded counter command.
        # No finite cap or postimage relaxation is used here.
        post = [[pre[i][j] + delta[i] - delta[j] for j in range(DIM)]
                for i in range(DIM)]
        require(all(post[0][i] <= 0 for i in range(DIM)),
                f"case {index}: command could make a counter negative")
        op_counts[op + ("0" if zero else "1") if op == "CD" else op] += 1
        if target is None:
            halt_count += 1
            continue
        require(zones[target] is not None, f"case {index}: successor is not live")
        for i in range(DIM):
            for j in range(DIM):
                bound = zones[target][i][j]
                if bound != inf:
                    finite_bounds_checked += 1
                    require(post[i][j] <= bound,
                            f"case {index}: exact postimage violates successor "
                            f"bound ({i},{j}): {post[i][j]} > {bound}")
        edge_count += 1
    return {
        "status": "PASS",
        "scope": "serialized source graph; all-zero entry; exact uncapped DBM postimages",
        "checker_sha256": digest(Path(__file__)),
        "graph_sha256": digest(graph_path),
        "source_sha256_recorded_in_graph": graph["source_sha256"],
        "zone_sha256": digest(zone_path),
        "cap": cap,
        "sites": len(zones),
        "live_sites": sum(z is not None for z in zones),
        "cases": len(graph["cases"]),
        "excluded_cases": excluded,
        "enabled_cases": len(graph["cases"]) - len(excluded),
        "postfix_edges": edge_count,
        "enabled_halt_cases": halt_count,
        "enabled_operations": dict(op_counts),
        "finite_successor_bounds_checked": finite_bounds_checked,
        "generator_worklist_pops_untrusted": pops,
        "generator_updates_untrusted": updates,
        "limitations": [
            "Graph extraction from Prog254.v is not checked by this program.",
            "The generator and this checker are not proof-assistant verified.",
            "The invariant alone does not prove nonhalting or any TM fold correct.",
            "The all-zero entry invariant does not automatically apply to nonzero seeds."
        ]
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--graph", type=Path, required=True)
    parser.add_argument("--zone", type=Path, required=True)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    result = verify(args.graph, args.zone)
    rendered = json.dumps(result, indent=2) + "\n"
    if args.output is not None:
        args.output.write_text(rendered)
    print(rendered, end="")


if __name__ == "__main__":
    main()
