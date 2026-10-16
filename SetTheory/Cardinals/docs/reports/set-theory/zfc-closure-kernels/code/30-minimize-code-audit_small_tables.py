#!/usr/bin/env python3
"""Audit exact binary TM tables and their stepwise state quotients.

This computes the greatest state bisimulation that preserves each written
symbol and move and matches successors for each possible read symbol. It
does not decide blank-tape reachability or general halting equivalence.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path


def audit(path: Path) -> dict:
    data = path.read_bytes()
    rows = {}
    start = None
    for line in data.decode("ascii").splitlines():
        if line.startswith("#! start "):
            if start is not None:
                raise ValueError("duplicate start directive")
            start = int(line[9:])
        elif line and not line.startswith("#"):
            q, s, w, d, t = line.split()
            q, s, w, t = map(int, (q, s, w, t))
            if (q, s) in rows or s not in (0, 1) or w not in (0, 1) or d not in ("L", "R"):
                raise ValueError(f"invalid or duplicate row: {line}")
            rows[q, s] = w, d, t
    n = len(rows) // 2
    if start is None or set(rows) != {(q, s) for q in range(n) for s in (0, 1)}:
        raise ValueError("expected contiguous working states and two rows per state")
    if not all(0 <= t <= n for _, _, t in rows.values()):
        raise ValueError("expected one separate terminal state n")
    if not 0 <= start < n:
        raise ValueError("invalid start")

    reachable, todo = {start}, [start]
    while todo:
        q = todo.pop()
        if q == n:
            continue
        for s in (0, 1):
            t = rows[q, s][2]
            if t not in reachable:
                reachable.add(t)
                todo.append(t)

    partition = {q: int(q == n) for q in range(n + 1)}
    rounds = 0
    while True:
        keys, new = {}, {}
        for q in range(n + 1):
            key = ("halt",) if q == n else tuple(
                (w, d, partition[t]) for s in (0, 1)
                for w, d, t in [rows[q, s]]
            )
            new[q] = keys.setdefault(key, len(keys))
        rounds += 1
        if all((partition[x] == partition[y]) == (new[x] == new[y])
               for x in range(n + 1) for y in range(n + 1)):
            break
        partition = new
    blocks = [[q for q in new if new[q] == b] for b in sorted(set(new.values()))]
    return {
        "machine": str(path),
        "sha256": hashlib.sha256(data).hexdigest(),
        "working_states": n,
        "terminal_state": n,
        "start_state": start,
        "transitions": len(rows),
        "graph_reachable_labels_including_terminal": len(reachable),
        "stepwise_state_bisimulation_blocks_including_terminal": len(blocks),
        "refinement_rounds": rounds,
        "nontrivial_blocks": [b for b in blocks if len(b) > 1],
        "scope": "All-symbol stepwise state quotient only; no minimality or blank-tape reachability claim.",
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("tables", type=Path, nargs="+")
    args = parser.parse_args()
    print(json.dumps([audit(p) for p in args.tables], indent=2))


if __name__ == "__main__":
    main()
