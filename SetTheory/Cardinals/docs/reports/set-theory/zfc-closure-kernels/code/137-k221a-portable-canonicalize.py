#!/usr/bin/env python3
"""Validate, canonically renumber, and independently replay each blank startup.

The endpoint is constructed from the published logical initialization contract.
No variant step count is presumed. Native and canonical runs each stop only
upon exact state, head, and entire nonzero-support equality with that endpoint.
The finite replay is an initialization check, not a nonhalting proof.
"""
from pathlib import Path
from collections import Counter
import argparse
import hashlib
import json


def need(condition, message):
    if not condition:
        raise ValueError(message)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read(path):
    table, starts = {}, []
    for line in path.read_text(encoding="ascii").splitlines():
        if line.startswith("#! start "):
            starts.append(int(line[9:]))
        elif line and not line.startswith("#"):
            q, b, w, d, z = line.split()
            q, b, w, z = map(int, (q, b, w, z))
            need((q, b) not in table and b in (0, 1) and w in (0, 1)
                 and d in ("L", "R"), "Malformed or duplicate row")
            table[q, b] = w, d, z
    states = {q for q, _ in table}
    need(starts == [0] and len(states) == 221, "Incorrect start/state count")
    need(set(table) == {(q, b) for q in states for b in (0, 1)}, "Incomplete table")
    need({z for w, d, z in table.values()} - states == {254}, "Incorrect halt")
    order, mapping = [0], {0: 0}
    for q in order:
        for b in (0, 1):
            z = table[q, b][2]
            if z in states and z not in mapping:
                mapping[z] = len(order)
                order.append(z)
    need(set(order) == states, "Some working states are graph-unreachable")
    mapping[254] = 221
    return table, mapping


def endpoint():
    logical = [3, 0, 0, 0, 3, 0, 0, 0, 0]
    physical = [None] * 9
    for i, j in enumerate([6, 2, 0, 4, 3, 7, 8, 5, 1]):
        physical[j] = logical[i]
    ones, cursor = {-6, 176}, 177
    for n in physical + [1] * 167:
        cursor += 1
        ones.update(range(cursor, cursor + n + 1))
        cursor += n + 1
    return logical, physical, ones


def replay(table, dispatcher, expected, max_steps):
    state, head, ones, visits = 0, 0, set(), Counter()
    for steps in range(1, max_steps + 1):
        bit = int(head in ones)
        need((state, bit) in table, "Unexpected early halt")
        visits[state, bit] += 1
        write, direction, state = table[state, bit]
        if write:
            ones.add(head)
        else:
            ones.discard(head)
        head += 1 if direction == "R" else -1
        if state == dispatcher and head == -5 and ones == expected:
            return steps, state, head, ones, visits
    raise ValueError("Initialization endpoint not reached within replay resource limit")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--table", type=Path, required=True)
    parser.add_argument("--source", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--max-steps", type=int, default=2000000)
    args = parser.parse_args()
    table, mapping = read(args.table)
    canonical = {(mapping[q], b): (w, d, mapping[z])
                 for (q, b), (w, d, z) in table.items()}
    need({q for q, b in canonical} == set(range(221)), "Canonical state set")
    encoded = "#! start 0\n" + "".join(
        f"{q} {b} {w} {d} {z}\n"
        for (q, b), (w, d, z) in sorted(canonical.items())
    )
    logical, physical, expected = endpoint()
    n, q, h, ones, visits = replay(table, 84, expected, args.max_steps)
    cn, cq, ch, cones, cvisits = replay(canonical, mapping[84], expected, args.max_steps)
    need((n, mapping[q], h, ones) == (cn, cq, ch, cones), "Replay mismatch")
    need(cvisits == Counter({(mapping[q], b): v for (q, b), v in visits.items()}),
         "Row-visit mapping mismatch")
    args.output.mkdir(parents=True, exist_ok=True)
    (args.output / "k221.tm").write_bytes(encoded.encode("ascii"))
    receipt = {
        "status": "EXACT_CANONICALIZATION_AND_COMPLETE_BLANK_STARTUP_PASS",
        "working_states": 221, "graph_reachable_working_states": 221, "rows": 442,
        "start": 0, "halt": 221, "native_halt": 254, "dispatcher": mapping[84],
        "rule": "Breadth first, read 0 before read 1; terminal 254 maps to 221.",
        "native_to_canonical": mapping,
        "canonical_to_native": {v: k for k, v in mapping.items()},
        "native_sha256": sha(args.table),
        "canonical_sha256": hashlib.sha256(encoded.encode("ascii")).hexdigest(),
        "source_sha256": sha(args.source),
        "startup": {
            "steps": n, "native_state": q, "canonical_state": cq, "head": h,
            "one_cells": sorted(ones), "all_other_cells": 0,
            "logical_registers": logical, "physical_registers": physical,
            "spares": [1] * 167, "extra_gap": 117,
            "used_native_rows": [list(k) + [v] for k, v in sorted(visits.items())],
        },
        "scope": "Literal bijection and exact initialization only. The all-tape "
                 "positive-block proof transports the baseline logical endpoint.",
    }
    (args.output / "canonicalization.json").write_text(
        json.dumps(receipt, indent=2, sort_keys=True) + "\n")
    print(json.dumps({k: v for k, v in receipt.items()
                      if k not in ("native_to_canonical", "canonical_to_native", "startup")},
                     indent=2))
    print("Observed blank-startup steps:", n)


if __name__ == "__main__":
    main()
