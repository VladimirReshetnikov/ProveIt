"""Paired recurrence/direct Euler comparisons, separate from default recognition."""
import argparse
import json
from pathlib import Path
import platform
import random
import statistics
import subprocess
from time import perf_counter
from types import ModuleType

from fastunknot import Diagram
from fastunknot import euler_scan


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    here = Path(__file__).resolve().parent
    revision = subprocess.check_output(["git", "rev-parse", "1fe98cb7e"], cwd=here, text=True).strip()
    source = subprocess.check_output(
        ["git", "show", revision + ":Topology/UnknotRecognition/fast/fastunknot/euler_scan.py"],
        cwd=here, text=True)
    old = ModuleType("fastunknot._recurrence_baseline")
    old.__package__ = "fastunknot"
    exec(compile(source, f"{revision}:euler_scan.py", "exec"), old.__dict__)
    rng = random.Random(2026100712)
    rows = []
    for name in ("conway", "conway_sum_2", "conway_sum_8", "hard_unknot_8"):
        diagram = Diagram.from_json(json.loads((here / "examples" / (name + ".json")).read_text()))
        samples = []
        metrics = {}
        for _ in range(7):
            arms = ["old", "control", "new"]
            rng.shuffle(arms)
            sample = {"execution_order": arms}
            for arm in arms:
                module = euler_scan if arm == "new" else old
                start = perf_counter()
                result = module.euler_compressed_khovanov_decide(diagram.pd)
                sample[arm] = perf_counter() - start
                metrics[arm] = result
            for key in ("status", "method", "stage", "rank_capped", "rank_lower_bound_capped"):
                assert metrics["old"].get(key) == metrics["new"].get(key), (name, key)
            samples.append(sample)
        row = dict(name=name, samples=samples, metrics=metrics,
                   median_speedup=statistics.median(s["old"] / s["new"] for s in samples),
                   median_aa=statistics.median(s["old"] / s["control"] for s in samples))
        rows.append(row)
        print(name, round(row["median_speedup"], 3), round(row["median_aa"], 3),
              metrics["old"]["euler_stats"]["states"], metrics["new"]["euler_stats"]["states"], flush=True)
    long = Diagram.from_braid(2, [1] * 1201)
    order = list(range(1201))
    recurrence = old.SuffixEuler(long.pd, order, max_states=None)
    direct = euler_scan.ClosureEuler(long.pd, order, max_states=1)
    assert recurrence.evaluate(0, ()) == direct.evaluate(0, ()) == -2
    report = dict(baseline_revision=revision, python=platform.python_version(),
                  seed=2026100712, rounds=7, timing_boundary="raw Euler-assisted shared scan",
                  cases=rows, long_suffix=dict(crossings=1201, value=-2,
                      recurrence=recurrence.stats, direct=direct.stats))
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2) + "\n")


if __name__ == "__main__":
    main()
