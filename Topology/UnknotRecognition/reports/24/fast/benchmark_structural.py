"""Paired timings and exact compression checks for the integrated report 07.

Run from any directory: python benchmark_structural.py --output results/structural.json
Fresh Diagram records are used after validation, with imports, parsing, validation,
and serialization outside the timed region. A/A controls accompany each A/B pair.
Scanner measurements bypass recognition filters and geometric factorization.
"""
import argparse
import json
from pathlib import Path
import platform
import random
import statistics
import subprocess
from time import perf_counter

from fastunknot import Diagram, khovanov_rank, recognize
from fastunknot.component_scan import compressed_khovanov_rank
from fastunknot.euler_scan import euler_compressed_khovanov_decide


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--rounds", type=int, default=7)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if args.rounds < 1:
        parser.error("rounds must be positive")
    root = Path(__file__).resolve().parent
    rng = random.Random(2026100708)
    cases = [("weaving_1000", Diagram.from_braid(3, [1, -2] * 500)),
             ("positive_1000", Diagram.from_braid(3, [1, 2] * 500)),
             ("positive_1004", Diagram.from_braid(5, [1, 2, 3, 4] * 251))]
    for name in ("conway", "hard_unknot_8", "grid_scrambled_unknot"):
        cases.append((name, Diagram.from_json(json.loads(
            (root / "examples" / (name + ".json")).read_text()))))
    records = []
    for name, diagram in cases:
        samples = []
        for _ in range(args.rounds):
            arms = ["old", "control", "new"]
            rng.shuffle(arms)
            sample = {"execution_order": arms}
            statuses = []
            for arm in arms:
                # A batch makes the timer boundary useful on tiny inputs too.
                start = perf_counter()
                for _ in range(5):
                    result = recognize(Diagram(diagram.pd), use_seifert=arm == "new")
                    statuses.append(result.status)
                sample[arm] = (perf_counter() - start) / 5
            assert len(set(statuses)) == 1
            sample["status"] = statuses[0]
            samples.append(sample)
        records.append(dict(name=name, crossings=diagram.crossings, samples=samples,
                            median_speedup=statistics.median(s["old"] / s["new"] for s in samples),
                            median_aa=statistics.median(s["old"] / s["control"] for s in samples)))
    scans = []
    for copies in (1, 2, 8):
        name = "conway" if copies == 1 else f"conway_sum_{copies}"
        diagram = Diagram.from_json(json.loads((root / "examples" / (name + ".json")).read_text()))
        shared = compressed_khovanov_rank(diagram.pd)
        assert shared["rank"] == 2 * 33 ** copies
        row = dict(name=name, shared=shared, euler=euler_compressed_khovanov_decide(diagram.pd))
        if copies < 8:
            standard = khovanov_rank(diagram.pd)
            assert shared["by_degree"] == standard["by_degree"]
            row["standard"] = standard
        scans.append(row)
    report = dict(python=platform.python_version(), platform=platform.platform(),
                  revision=subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=root, text=True).strip(),
                  working_tree_may_differ=True, seed=2026100708, rounds=args.rounds,
                  timing_boundary="five fresh validated-Diagram recognition calls per arm; seconds per call",
                  speedup_definition="median of paired old/new; greater than one is faster",
                  recognition=records, scanner_checks=scans)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2) + "\n")
    for row in records:
        print(f'{row["name"]}: {row["median_speedup"]:.2f}x, A/A {row["median_aa"]:.3f}')


if __name__ == "__main__":
    main()

