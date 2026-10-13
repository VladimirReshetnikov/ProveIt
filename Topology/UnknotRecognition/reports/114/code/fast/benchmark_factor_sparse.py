"""Paired factorization/Alexander kernel timings; no full-recognition claim."""
import argparse
from collections import Counter
import json
from pathlib import Path
import platform
import random
import statistics
from time import perf_counter

from fastunknot import Diagram
from fastunknot.factor import visible_factors
from fastunknot.interlace import visible_factors_interlacement, verify_interlacement_certificate
from fastunknot.filters import alexander_obstruction


def trefoil_sum(copies):
    diagram = Diagram.from_braid(2, [1, 1, 1])
    rows = [[-1] * 4 for _ in range(3 * copies)]
    position = 0
    for offset in range(0, len(rows), 3):
        for dart in diagram.traversal():
            crossing, slot = divmod(dart, 4)
            rows[offset + crossing][slot] = position
            rows[offset + crossing][(slot + 2) % 4] = (position + 1) % (2 * len(rows))
            position += 1
    return Diagram.from_pd(rows)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    rng = random.Random(2026100713)
    cases = []
    for copies in (32, 128, 256):
        d = trefoil_sum(copies)
        cases.append((f"factor_{copies}_trefoils", d, "factor"))
    for repeats in (31, 131, 257):
        cases.append((f"alexander_torus3_{repeats}", Diagram.from_braid(3, [1, 2] * repeats), "alexander"))
    rows = []
    for name, diagram, kind in cases:
        samples = []
        for _ in range(7):
            arms = ["old", "control", "new"]
            rng.shuffle(arms)
            sample = {"execution_order": arms}
            answers = []
            for arm in arms:
                fresh = Diagram(diagram.pd)
                start = perf_counter()
                if kind == "factor":
                    call = visible_factors_interlacement if arm == "new" else visible_factors
                    result = call(fresh)
                else:
                    result = alexander_obstruction(fresh, backend="sparse" if arm == "new" else "dense")
                sample[arm] = perf_counter() - start
                if kind == "factor":
                    answers.append(Counter(f.crossings for f in result[0]))
                    if arm == "new":
                        verify_interlacement_certificate(tuple(d // 4 for d in fresh.traversal()), result[1])
                else:
                    answers.append(result)
            assert answers[0] == answers[1] == answers[2]
            samples.append(sample)
        row = dict(name=name, kind=kind, crossings=diagram.crossings, samples=samples,
                   median_speedup=statistics.median(s["old"] / s["new"] for s in samples),
                   median_aa=statistics.median(s["old"] / s["control"] for s in samples))
        if kind == "alexander":
            counters = []
            alexander_obstruction(Diagram(diagram.pd), backend="sparse", statistics=counters)
            row["sparse_work"] = counters
        rows.append(row)
        print(name, round(row["median_speedup"], 2), round(row["median_aa"], 3), flush=True)
    report = dict(python=platform.python_version(), platform=platform.platform(), seed=2026100713,
                  rounds=7, timing_boundary="fresh validated Diagram; kernel call only; verification excluded",
                  speedup_definition="median paired old/new; above one is faster", cases=rows)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2) + "\n")


if __name__ == "__main__":
    main()
