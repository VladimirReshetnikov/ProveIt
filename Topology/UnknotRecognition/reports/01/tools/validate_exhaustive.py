"""Exhaustive connected rectangular diagrams, modulo cyclic shifts.

Run from project root: python -m tools.validate_exhaustive --max-size 6
Each unoriented grid is produced twice by the ordered X/O descriptions. This
program counts distinct grids and solves one representative per shift orbit.
Search uses NO determinant shortcut; the determinant is an independent check.
"""
from __future__ import annotations
import argparse
import itertools
import json
import platform
from time import monotonic

from unknot import Grid, recognize, verify_certificate
from unknot.determinant import determinant


def validate(n):
    start = monotonic()
    raw = set()
    orbits = set()
    for x in itertools.permutations(range(n)):
        for tail in itertools.permutations(range(1, n)):
            cycle = (0,) + tail
            o = [0] * n
            for i, row in enumerate(cycle):
                o[row] = x[cycle[(i + 1) % n]]
            grid = Grid.from_rows(list(zip(x, o)))
            if grid.rows not in raw:
                raw.add(grid.rows)
                orbits.add(grid.canonical())
    counts = {"UNKNOT": 0, "KNOTTED": 0}
    largest = 0
    determinant_one_knotted = 0
    for grid in sorted(orbits, key=lambda g: g.rows):
        result = recognize(grid, use_determinant=False)
        verdict = result["verdict"]
        if verdict not in counts:
            raise AssertionError("unlimited exact search did not decide")
        verified = verify_certificate(result["certificate"], grid)
        if verified["verdict"] != verdict:
            raise AssertionError("search and verifier disagree")
        value = determinant(grid)
        if value != 1 and verdict != "KNOTTED":
            raise AssertionError("a nontrivial determinant was declared unknotted")
        determinant_one_knotted += verdict == "KNOTTED" and value == 1
        largest = max(largest, result["states_seen"])
        counts[verdict] += 1
    return {"grid_size": n, "distinct_connected_grids": len(raw),
            "cyclic_shift_orbits": len(orbits), "verdicts_by_orbit": counts,
            "determinant_one_knotted_orbits": determinant_one_knotted,
            "largest_search_states": largest, "seconds": monotonic() - start}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-size", type=int, default=6)
    parser.add_argument("--output")
    args = parser.parse_args()
    if not 2 <= args.max_size <= 7:
        parser.error("choose max-size in 2..7; size 7 already has millions of grids")
    results = []
    for n in range(2, args.max_size + 1):
        row = validate(n)
        results.append(row)
        print(json.dumps(row), flush=True)
    if args.output:
        from pathlib import Path
        Path(args.output).write_text(json.dumps({"python": platform.python_version(),
                                                "results": results}, indent=2) + "\n")


if __name__ == "__main__":
    main()
