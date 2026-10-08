"""Paired raw scans against the pinned pre-shortcut Planar implementation.

No recognition filters are timed. Fresh scans and algebra objects are used;
the common input and scan order are prepared outside the timing boundary.
Additional composition counts are collected in a separate untimed pass.
"""
import argparse
from collections import Counter
import json
from pathlib import Path
import platform
import random
import statistics
import subprocess
from time import perf_counter
from types import ModuleType

from fastunknot import Diagram
from fastunknot.ordering import best_scan_order, repeated_stages
from fastunknot.planar import Planar
from fastunknot.scan_fast import FastScan


def run(pd, order, algebra_class, shape_cache):
    scan = FastScan(shape_cache=shape_cache)
    scan.algebra = algebra_class(shape_cache=shape_cache)
    for i in order:
        scan.add_crossing(pd[i])
    scan.total_rank()
    return scan.ranks_by_degree()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--rounds", type=int, default=9)
    args = parser.parse_args()
    here = Path(__file__).resolve().parent
    revision = subprocess.check_output(["git", "rev-parse", "e34ddc751"], cwd=here, text=True).strip()
    source = subprocess.check_output(
        ["git", "show", revision + ":Topology/UnknotRecognition/fast/fastunknot/planar.py"],
        cwd=here, text=True)
    old = ModuleType("fastunknot._pre_scalar_shortcuts")
    old.__package__ = "fastunknot"
    exec(compile(source, f"{revision}:planar.py", "exec"), old.__dict__)
    rng = random.Random(2026100715)
    rows = []
    for name in ("conway", "kinoshita_terasaka", "conway_sum_2", "hard_unknot_8", "torus_3_5",
                 "unknot_braid40"):
        diagram = Diagram.from_json(json.loads((here / "examples" / (name + ".json")).read_text()))
        pd = list(diagram.pd)
        order = best_scan_order(pd, tries=min(len(pd), 12))
        shape = len(order) >= 16 and 8 * repeated_stages(pd, order) >= len(order)
        expected = run(pd, order, old.Planar, shape)
        assert run(pd, order, Planar, shape) == expected
        samples = []
        for _ in range(args.rounds):
            arms = ["old", "control", "new"]
            rng.shuffle(arms)
            sample = {"order": arms}
            for arm in arms:
                started = perf_counter()
                result = run(pd, order, Planar if arm == "new" else old.Planar, shape)
                sample[arm] = perf_counter() - started
                assert result == expected
            samples.append(sample)
        counts = Counter()

        class Profile(Planar):
            def compose(self, a, b, c, f, g):
                if not f or not g:
                    counts["zero"] += 1
                elif f == 1 and a == b:
                    counts["left_identity"] += 1
                elif g == 1 and b == c:
                    counts["right_identity"] += 1
                elif a == b == c and f == g:
                    counts["scalar_square"] += 1
                else:
                    counts["general"] += 1
                return super().compose(a, b, c, f, g)

        assert run(pd, order, Profile, shape) == expected
        row = dict(name=name, samples=samples, by_degree=expected, compose_calls=dict(counts),
                   median_speedup=statistics.median(s["old"] / s["new"] for s in samples),
                   median_aa=statistics.median(s["old"] / s["control"] for s in samples))
        rows.append(row)
        print(name, round(row["median_speedup"], 3), round(row["median_aa"], 3), dict(counts), flush=True)
    kernels = []
    for arcs in (4, 6, 8):
        pairs = tuple((2*i, 2*i+1) for i in range(arcs))
        f = rng.getrandbits(1 << arcs) | 1
        samples = []
        for _ in range(args.rounds):
            arms = ["old", "control", "new"]
            rng.shuffle(arms)
            sample = {"order": arms}
            for arm in arms:
                algebra = (Planar if arm == "new" else old.Planar)(shape_cache=False)
                a = algebra.intern(pairs)
                started = perf_counter()
                result = algebra.compose(a, a, a, f, f)
                sample[arm] = perf_counter() - started
                assert result == 1
            samples.append(sample)
        kernels.append(dict(arcs=arcs, coefficient=f, samples=samples,
            old_monomial_pairs=f.bit_count()**2,
            median_speedup=statistics.median(s["old"] / s["new"] for s in samples),
            median_aa=statistics.median(s["old"] / s["control"] for s in samples)))
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(dict(baseline_revision=revision, python=platform.python_version(),
        rounds=args.rounds, seed=2026100715, timing_scope=__doc__, cases=rows,
        scalar_square_kernels=kernels), indent=2) + "\n")


if __name__ == "__main__":
    main()

