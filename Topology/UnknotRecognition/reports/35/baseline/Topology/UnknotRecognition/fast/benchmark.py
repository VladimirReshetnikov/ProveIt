"""Timing benchmark for fastunknot.  Regenerates results/benchmark.json.

Small timings are not a complexity proof.  The point of the tables is the
dependence on the scan boundary rather than on the crossing number.
"""
from __future__ import annotations

import json
import os
import platform
import random
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from fastunknot import Diagram, recognize  # noqa: E402
from fastunknot.scan import ScanLimit, khovanov_rank  # noqa: E402


def one_component(strands, word):
    p = list(range(strands))
    for g in word:
        i = abs(g) - 1
        p[i], p[i + 1] = p[i + 1], p[i]
    seen, count = set(), 0
    for s in range(strands):
        if s in seen:
            continue
        count += 1
        x = s
        while x not in seen:
            seen.add(x)
            x = p[x]
    return count == 1


def timed_rank(diagram, seconds=600):
    t = time.perf_counter()
    try:
        r = khovanov_rank(diagram.pd, seconds=seconds)
    except ScanLimit:
        r = {"reduced_rank": None, "stats": {"max_objects_before_elimination": None,
             "max_objects_after_elimination": None, "eliminations": None, "max_boundary": None,
             "compositions": None, "timed_out": True}}
    return round(time.perf_counter() - t, 3), r


def main():
    rng = random.Random(20260917)
    rows = []
    # 1. the unknot family sigma_1...sigma_n (exponential for the cube: 2^n states, 3^n generators)
    for n in (8, 16, 32, 64, 128, 256):
        d = Diagram.from_braid(n + 1, list(range(1, n + 1)))
        seconds, r = timed_rank(d)
        rows.append({"family": "unknot sigma_1..sigma_n", "crossings": n, "reduced_rank": r["reduced_rank"],
                     "seconds": seconds, **r["stats"]})
        print(rows[-1], flush=True)
    # 2. torus knots T(2,n) and T(3,n)
    for n in (5, 11, 21, 41):
        d = Diagram.from_braid(2, [1] * n)
        seconds, r = timed_rank(d)
        rows.append({"family": "T(2,n)", "crossings": n, "reduced_rank": r["reduced_rank"],
                     "seconds": seconds, **r["stats"]})
        print(rows[-1], flush=True)
    for n in (4, 5, 7, 8, 10, 11):
        d = Diagram.from_braid(3, [1, 2] * n)
        seconds, r = timed_rank(d)
        rows.append({"family": "T(3,n)", "crossings": 2 * n, "reduced_rank": r["reduced_rank"],
                     "seconds": seconds, **r["stats"]})
        print(rows[-1], flush=True)
    # 3. random braid closures on 3..6 strands
    # odd lengths on an even number of strands: an even-length word closes to a link
    for strands, length in ((3, 20), (3, 40), (4, 15), (4, 21), (4, 31), (4, 41), (5, 24), (5, 36), (6, 31)):
        while True:
            word = [rng.choice([-1, 1]) * rng.randint(1, strands - 1) for _ in range(length)]
            if one_component(strands, word):
                break
        d = Diagram.from_braid(strands, word)
        seconds, r = timed_rank(d)
        rows.append({"family": f"random {strands}-braid", "crossings": length, "word": word,
                     "reduced_rank": r["reduced_rank"], "seconds": seconds, **r["stats"]})
        print(rows[-1], flush=True)
    # 4. the full pipeline on the examples
    pipeline = []
    for name in sorted(os.listdir("examples")):
        with open(os.path.join("examples", name), encoding="utf-8") as handle:
            d = Diagram.from_json(json.load(handle))
        result = recognize(d)
        pipeline.append({"example": name, "crossings": d.crossings, "status": result.status,
                         "method": result.method, "seconds": round(result.seconds, 4)})
        print(pipeline[-1], flush=True)
    os.makedirs("results", exist_ok=True)
    with open("results/benchmark.json", "w", encoding="utf-8") as handle:
        json.dump({"python": platform.python_version(), "platform": platform.platform(),
                   "quasipolynomial_bound_established": False,
                   "scan_families": rows, "pipeline": pipeline}, handle, indent=1)


if __name__ == "__main__":
    main()
