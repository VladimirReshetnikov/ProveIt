#!/usr/bin/env python3
"""Independently verify exact pair distances by local Bellman identities.

This program does not import the generator or its automaton constructor.
It builds transitions from disjoint transpositions and three exceptional
arrows. No breadth-first search, theorem prover, or numerical tolerance
is used here. Verification failures raise ValueError (also under python -O).
"""
from __future__ import annotations
import argparse
import csv
import gzip
import json
from pathlib import Path
import time

ROOT = Path(__file__).resolve().parents[1]


def independent_model(k: int, shortened: bool = False) -> tuple[list[int], list[int]]:
    if type(k) is not int or k < 1:
        raise ValueError("Bad parameter")
    n, m = 3 * k + 6 - int(shortened), 2 * k + 4
    a, b = list(range(n)), list(range(n))
    for q in range(1, m - 1, 2):
        a[q], a[q + 1] = q + 1, q
    a[m - 1], a[m], a[m + 1] = m, m + 1, 3
    for q in range(m + 2, n - 1, 2):
        a[q], a[q + 1] = q + 1, q
    for q in range(0, m, 2):
        b[q], b[q + 1] = q + 1, q
    b[m] = 2
    for q in range(m + 1, n - 1, 2):
        b[q], b[q + 1] = q + 1, q
    return a, b


def index(x: int, y: int) -> int:
    low, high = (x, y) if x <= y else (y, x)
    return high * (high + 1) // 2 + low


def verify_record(record: dict) -> dict:
    if record.get("format") != "dzyga-pair-distance-v1":
        raise ValueError("Unsupported certificate format")
    if record.get("index") != "max(x,y)*(max(x,y)+1)//2+min(x,y)":
        raise ValueError("Unexpected pair-index convention")
    k = record["k"]
    a, b = independent_model(k)
    n = len(a)
    if record["n"] != n:
        raise ValueError("Wrong state count")
    d = record["distance"]
    if len(d) != n * (n + 1) // 2:
        raise ValueError("Wrong number of pair entries")
    if any(type(v) is not int or v < 0 for v in d):
        raise ValueError("Distances must be nonnegative integers")
    idx = 0
    for y in range(n):
        for x in range(y + 1):
            value = d[idx]
            if x == y:
                if value != 0:
                    raise ValueError(f"Nonzero diagonal at {x}")
            else:
                da, db = d[index(a[x], a[y])], d[index(b[x], b[y])]
                if value <= 0 or value != 1 + min(da, db):
                    raise ValueError(f"Bellman failure: k={k}, pair=({x},{y})")
            idx += 1
    threshold = min(d[index(0, j)] for j in range(1, n))
    partners = [j for j in range(1, n) if d[index(0, j)] == threshold]
    return {"k": k, "n": n, "pair_count": len(d), "cwa_q0": threshold,
            "d_0_1": d[index(0, 1)], "optimal_partners": partners,
            "pair_diameter": max(d)}


def read_record(k: int) -> dict:
    with gzip.open(ROOT / "certificates" / f"k_{k:04d}.json.gz", "rt") as file:
        return json.load(file)


def negative_controls() -> None:
    original = read_record(1)
    for pos, change in [(0, 1), (1, 1), (1, -original["distance"][1])]:
        bad = dict(original)
        bad["distance"] = list(original["distance"])
        bad["distance"][pos] += change
        try:
            verify_record(bad)
        except ValueError:
            pass
        else:
            raise ValueError("A deliberately corrupted certificate was accepted")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--min-k", type=int, default=1)
    parser.add_argument("--max-k", type=int, default=200)
    args = parser.parse_args()
    if not 1 <= args.min_k <= args.max_k:
        parser.error("Require 1 <= min-k <= max-k")
    start = time.perf_counter()
    with (ROOT / "results" / "summary.csv").open(newline="") as file:
        summary = {int(row["k"]): row for row in csv.DictReader(file)}
    count = 0
    for k in range(args.min_k, args.max_k + 1):
        result = verify_record(read_record(k))
        count += result["pair_count"]
        for name in ["n", "pair_count", "cwa_q0", "d_0_1", "pair_diameter"]:
            if result[name] != int(summary[k][name]):
                raise ValueError(f"CSV mismatch: k={k}, column={name}")
        partners = ";".join(map(str, result["optimal_partners"]))
        if partners != summary[k]["optimal_partners"]:
            raise ValueError("CSV partner mismatch")
        expected_diameter = ((5*k*k + 32*k + 47) if k % 2 else
                             (5*k*k + 34*k + 44)) // 4
        if result["cwa_q0"] != 4*k+8 or result["d_0_1"] != 4*k+9:
            raise ValueError(f"Threshold formula exception at k={k}")
        if result["optimal_partners"] != [2, 2*k+5]:
            raise ValueError(f"Optimal partner exception at k={k}")
        if result["pair_diameter"] != expected_diameter:
            raise ValueError(f"Pair diameter exception at k={k}")
        if (summary[k]["all_pairs_merge"] != "True" or
                summary[k]["diameter_matches"] != "True" or
                int(summary[k]["diameter_candidate"]) != expected_diameter or
                int(summary[k]["explicit_reset_length"]) != 8*k*k+54*k+92):
            raise ValueError(f"Additional CSV field mismatch at k={k}")
    negative_controls()
    print(f"PASS: exact pair-distance certificates for k={args.min_k}..{args.max_k}")
    print(f"PASS: {count:,} Bellman/diagonal entries; CSV agreement")
    print("PASS: threshold 4k+8; d(0,1)=4k+9; partners {2,2k+5}; diameter formula")
    print("PASS: three deliberately corrupted certificates rejected")
    print(f"Elapsed seconds: {time.perf_counter()-start:.2f}")

if __name__ == "__main__":
    main()
