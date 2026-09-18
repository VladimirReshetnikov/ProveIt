"""Quick in-process performance check used while optimizing.

Usage:  python perf.py [label] [--repeats N] [--profile CASE]
Prints the best-of-N time per case and appends the run to results/perf_log.json.
Caches are per call, so repeated calls in one process are comparable.
"""
from __future__ import annotations

import cProfile
import json
import os
import pstats
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from fastunknot import Diagram, khovanov_rank, recognize  # noqa: E402
from fastunknot.filters import jones_obstruction  # noqa: E402


def example(name):
    with open(os.path.join(HERE, "examples", name), encoding="utf-8") as handle:
        return Diagram.from_json(json.load(handle))


def corpus():
    bench = json.load(open(os.path.join(HERE, "results", "benchmark_0.1.json"), encoding="utf-8"))
    words = {(r["family"], r["crossings"]): r["word"] for r in bench["scan_families"] if "word" in r}

    def braid(s, n):
        return Diagram.from_braid(s, words[f"random {s}-braid", n])

    exact = dict(use_modular=False, use_jones=False, use_alexander=False)
    return [
        ("scan conway", lambda d=example("conway.json"): khovanov_rank(d.pd)["reduced_rank"]),
        ("scan T(3,11)", lambda d=Diagram.from_braid(3, [1, 2] * 11): khovanov_rank(d.pd)["reduced_rank"]),
        ("scan braid3_40", lambda d=braid(3, 40): khovanov_rank(d.pd)["reduced_rank"]),
        ("scan braid4_41", lambda d=braid(4, 41): khovanov_rank(d.pd)["reduced_rank"]),
        ("scan braid6_31", lambda d=braid(6, 31): khovanov_rank(d.pd)["reduced_rank"]),
        ("scan braid5_36", lambda d=braid(5, 36): khovanov_rank(d.pd)["reduced_rank"]),
        ("scan conway_sum_2", lambda d=example("conway_sum_2.json"): khovanov_rank(d.pd)["reduced_rank"]),
        ("scan chain256", lambda d=Diagram.from_braid(257, list(range(1, 257))): khovanov_rank(d.pd)["reduced_rank"]),
        ("recognize hard_unknot_8", lambda d=example("hard_unknot_8.json"): recognize(d).status),
        ("recognize conway (exact only)", lambda d=example("conway.json"): recognize(d, **exact).status),
        ("recognize conway", lambda d=example("conway.json"): recognize(d).status),
        ("recognize conway_sum_3", lambda d=example("conway_sum_3.json"): recognize(d).status),
        ("recognize T(3,61)", lambda d=Diagram.from_braid(3, [1, 2] * 61): recognize(d).status),
        ("jones braid5_36", lambda d=braid(5, 36): jones_obstruction(d) is not None),
    ]


def main():
    args = sys.argv[1:]
    label = args[0] if args and not args[0].startswith("--") else "unlabelled"
    repeats = int(args[args.index("--repeats") + 1]) if "--repeats" in args else 5
    cases = corpus()
    if "--profile" in args:
        wanted = args[args.index("--profile") + 1]
        name, fn = next(c for c in cases if wanted in c[0])
        profiler = cProfile.Profile()
        profiler.enable()
        fn()
        profiler.disable()
        pstats.Stats(profiler).sort_stats("tottime").print_stats(22)
        return
    row = {"label": label, "times_ms": {}, "results": {}}
    total = 0.0
    for name, fn in cases:
        best = None
        for _ in range(repeats if "braid5_36" not in name or "jones" in name else max(2, repeats // 2)):
            t = time.perf_counter()
            result = fn()
            t = time.perf_counter() - t
            best = t if best is None else min(best, t)
        row["times_ms"][name] = round(best * 1000, 3)
        row["results"][name] = result
        total += best
        print(f"{name:32s} {best * 1000:10.3f} ms   {result}")
    row["total_ms"] = round(total * 1000, 1)
    print(f"{'TOTAL':32s} {total * 1000:10.1f} ms")
    path = os.path.join(HERE, "results", "perf_log.json")
    log = json.load(open(path, encoding="utf-8")) if os.path.exists(path) else []
    log.append(row)
    json.dump(log, open(path, "w", encoding="utf-8"), indent=1)


if __name__ == "__main__":
    main()
