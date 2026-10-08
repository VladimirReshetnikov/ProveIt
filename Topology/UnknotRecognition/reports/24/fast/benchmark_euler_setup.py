"""Isolate suffix-Euler setup under a tiny inference budget, including memory.

This measures inference construction and its first rejected evaluation, not
complete knot recognition. Peak tracemalloc bytes are measured separately from
timing. Other implementation modules are shared with the baseline revision.
"""
import argparse
import gc
import json
from pathlib import Path
import platform
import random
import statistics
import subprocess
from time import perf_counter
import tracemalloc
from types import ModuleType

from fastunknot import Diagram
from fastunknot import euler_scan


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--baseline", default="9765612b8")
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    here = Path(__file__).resolve().parent
    revision = subprocess.check_output(
        ["git", "rev-parse", "--verify", args.baseline + "^{commit}"], cwd=here, text=True).strip()
    source = subprocess.check_output(
        ["git", "show", revision + ":Topology/UnknotRecognition/fast/fastunknot/euler_scan.py"],
        cwd=here, text=True)
    old = ModuleType("fastunknot._baseline_euler")
    old.__package__ = "fastunknot"
    exec(compile(source, f"{revision}:euler_scan.py", "exec"), old.__dict__)
    rng = random.Random(2026100711)
    rows = []
    for n in (1201, 4801):
        pd = Diagram.from_braid(2, [1] * n).pd
        order = list(range(n))
        for budget in (0, 1):
            def run(module):
                engine = module.SuffixEuler(pd, order, max_states=budget)
                try:
                    engine.evaluate(0, ())
                except module.EulerBudget:
                    pass
                else:
                    raise AssertionError("inference should exhaust this budget")
                assert engine.stats["states"] == budget
                return engine
            modules = {"old": old, "control": old, "new": euler_scan}
            samples = []
            for _ in range(7):
                arms = list(modules)
                rng.shuffle(arms)
                sample = {"execution_order": arms}
                for arm in arms:
                    gc.collect()
                    start = perf_counter()
                    engine = run(modules[arm])
                    sample[arm] = perf_counter() - start
                    del engine
                samples.append(sample)
            peaks = {}
            for arm in ("old", "new"):
                gc.collect()
                tracemalloc.start()
                engine = run(modules[arm])
                peaks[arm] = tracemalloc.get_traced_memory()[1]
                tracemalloc.stop()
                del engine
            row = dict(crossings=n, budget=budget, samples=samples, peak_traced_bytes=peaks,
                       median_speedup=statistics.median(s["old"] / s["new"] for s in samples),
                       median_aa=statistics.median(s["old"] / s["control"] for s in samples))
            rows.append(row)
            print(n, budget, row["median_speedup"], peaks, flush=True)
    report = dict(baseline_revision=revision, baseline_scope="euler_scan.py only",
                  python=platform.python_version(), platform=platform.platform(), seed=2026100711,
                  rounds=7, timing_boundary="construction and first budget-exhausted Euler evaluation",
                  speedup_definition="median paired old/new", cases=rows)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2) + "\n")


if __name__ == "__main__":
    main()

