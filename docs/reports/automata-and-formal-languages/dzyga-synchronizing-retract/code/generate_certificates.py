#!/usr/bin/env python3
"""Generate exact pair-distance certificates and a CSV summary.

An independent verifier is in verify_certificates.py. This generator uses
reverse breadth-first search; its certificate has no executable content.
"""
from __future__ import annotations
import argparse
from array import array
from collections import deque
import csv
import gzip
import json
from pathlib import Path
import time
from automata import Automaton, make_family, reset_length

ROOT = Path(__file__).resolve().parents[1]


def pair_index(x: int, y: int) -> int:
    if x > y:
        x, y = y, x
    return y * (y + 1) // 2 + x


def distances(aut: Automaton) -> array:
    """Reverse BFS, using linked adjacency arrays to keep memory quadratic."""
    count = aut.n * (aut.n + 1) // 2
    head = array("i", [-1]) * count
    source = array("i")
    next_edge = array("i")
    idx = 0
    for y in range(aut.n):
        for x in range(y + 1):
            for letter in (aut.a, aut.b):
                target = pair_index(letter[x], letter[y])
                source.append(idx)
                next_edge.append(head[target])
                head[target] = len(source) - 1
            idx += 1
    result = array("i", [-1]) * count
    queue: deque[int] = deque()
    for q in range(aut.n):
        idx = pair_index(q, q)
        result[idx] = 0
        queue.append(idx)
    while queue:
        target = queue.popleft()
        edge = head[target]
        while edge != -1:
            origin = source[edge]
            if result[origin] == -1:
                result[origin] = result[target] + 1
                queue.append(origin)
            edge = next_edge[edge]
    return result


def diameter_candidate(k: int) -> int:
    return ((5 * k * k + 32 * k + 47) if k % 2 else
            (5 * k * k + 34 * k + 44)) // 4


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-k", type=int, default=200)
    parser.add_argument("--min-k", type=int, default=1)
    args = parser.parse_args()
    if args.min_k < 1 or args.max_k < args.min_k:
        parser.error("Require 1 <= min-k <= max-k")
    (ROOT / "certificates").mkdir(exist_ok=True)
    (ROOT / "results").mkdir(exist_ok=True)
    start = time.perf_counter()
    fields = ["k", "n", "pair_count", "all_pairs_merge", "cwa_q0", "d_0_1",
              "optimal_partners", "pair_diameter", "diameter_candidate",
              "diameter_matches", "explicit_reset_length"]
    total_pairs = 0
    mode = "w" if args.min_k == 1 else "a"
    with (ROOT / "results" / "summary.csv").open(mode, newline="") as out:
        writer = csv.DictWriter(out, fieldnames=fields)
        if args.min_k == 1:
            writer.writeheader()
        for k in range(args.min_k, args.max_k + 1):
            aut = make_family(k)
            dist = distances(aut)
            total_pairs += len(dist)
            threshold = min(dist[pair_index(0, j)] for j in range(1, aut.n))
            partners = [j for j in range(1, aut.n)
                        if dist[pair_index(0, j)] == threshold]
            diameter = max(dist)
            record = {"format": "dzyga-pair-distance-v1", "k": k, "n": aut.n,
                      "index": "max(x,y)*(max(x,y)+1)//2+min(x,y)",
                      "distance": list(dist)}
            path = ROOT / "certificates" / f"k_{k:04d}.json.gz"
            with path.open("wb") as raw:
                with gzip.GzipFile(filename="", fileobj=raw, mode="wb", mtime=0) as gz:
                    gz.write(json.dumps(record, separators=(",", ":")).encode("ascii"))
            writer.writerow({
                "k": k, "n": aut.n, "pair_count": len(dist),
                "all_pairs_merge": all(value >= 0 for value in dist),
                "cwa_q0": threshold, "d_0_1": dist[pair_index(0, 1)],
                "optimal_partners": ";".join(map(str, partners)),
                "pair_diameter": diameter, "diameter_candidate": diameter_candidate(k),
                "diameter_matches": diameter == diameter_candidate(k),
                "explicit_reset_length": reset_length(k)})
            out.flush()
            if threshold != 4 * k + 8 or diameter != diameter_candidate(k):
                print(f"EXCEPTION at k={k}: threshold={threshold}, diameter={diameter}", flush=True)
            if k % 20 == 0:
                print(f"Generated k={args.min_k}..{k}, elapsed={time.perf_counter()-start:.2f}s", flush=True)
    print(f"DONE: k={args.min_k}..{args.max_k}; {total_pairs} pair entries; "
          f"{time.perf_counter()-start:.2f}s", flush=True)

if __name__ == "__main__":
    main()
