"""Interleaved A/B timing of the working tree against a git revision.

Usage:  python ab.py [REV] [--pairs N]        (REV defaults to HEAD)

Wall-clock on a desktop drifts by tens of percent within a minute (background
load, clock throttling), which makes sequential before/after runs of perf.py
misleading.  Here the package at REV is extracted next to the working tree under
another name, and the two are timed alternately in one process, swapping which
goes first; the statistic is the median of the paired ratios new/old with its
quartiles.  A gain is only claimed when the whole interquartile range is below 1.
Results (ranks by degree, verdicts) are asserted equal on every pair.
"""
from __future__ import annotations

import importlib
import io
import json
import os
import shutil
import statistics
import subprocess
import sys
import tarfile
import tempfile
import time

HERE = os.path.dirname(os.path.abspath(__file__))


def load_base(rev: str, where: str):
    data = subprocess.run(["git", "archive", rev, "fastunknot"], cwd=HERE, check=True,
                          capture_output=True).stdout
    with tarfile.open(fileobj=io.BytesIO(data)) as tar:
        tar.extractall(where)
    os.rename(os.path.join(where, "fastunknot"), os.path.join(where, "fastunknot_base"))
    sys.path.insert(0, where)
    return importlib.import_module("fastunknot_base")


def corpus(pkg):
    D = pkg.Diagram
    bench = json.load(open(os.path.join(HERE, "results", "benchmark_0.1.json"), encoding="utf-8"))
    words = {(r["family"], r["crossings"]): r["word"] for r in bench["scan_families"] if "word" in r}

    def example(name):
        with open(os.path.join(HERE, "examples", name), encoding="utf-8") as handle:
            return D.from_json(json.load(handle))

    def scan(d):
        return lambda: pkg.khovanov_rank(d.pd)["by_degree"]

    def rec(d, **kw):
        return lambda: pkg.recognize(d, **kw).status

    exact = dict(use_modular=False, use_jones=False, use_alexander=False)
    return {
        "scan conway": scan(example("conway.json")),
        "scan T(3,11)": scan(D.from_braid(3, [1, 2] * 11)),
        "scan braid3_40": scan(D.from_braid(3, words["random 3-braid", 40])),
        "scan braid4_41": scan(D.from_braid(4, words["random 4-braid", 41])),
        "scan braid6_31": scan(D.from_braid(6, words["random 6-braid", 31])),
        "scan braid5_36": scan(D.from_braid(5, words["random 5-braid", 36])),
        "scan conway_sum_2": scan(example("conway_sum_2.json")),
        "scan chain256": scan(D.from_braid(257, list(range(1, 257)))),
        "recognize hard_unknot_8": rec(example("hard_unknot_8.json")),
        "recognize conway (exact only)": rec(example("conway.json"), **exact),
        "recognize conway": rec(example("conway.json")),
        "recognize T(3,61)": rec(D.from_braid(3, [1, 2] * 61)),
    }


def timed(fn):
    t = time.perf_counter()
    result = fn()
    return time.perf_counter() - t, result


def main():
    args = sys.argv[1:]
    rev = args[0] if args and not args[0].startswith("--") else "HEAD"
    pairs = int(args[args.index("--pairs") + 1]) if "--pairs" in args else 15
    where = tempfile.mkdtemp(prefix="fastunknot_ab_")
    try:
        sys.path.insert(0, HERE)
        new, old = corpus(importlib.import_module("fastunknot")), corpus(load_base(rev, where))
        rows = []
        for name in new:
            n = max(4, pairs // 3) if "braid5_36" in name else pairs
            ratios = []
            for k in range(n):
                if k % 2:
                    (tn, rn), (to, ro) = timed(new[name]), timed(old[name])
                else:
                    (to, ro), (tn, rn) = timed(old[name]), timed(new[name])
                if rn != ro:
                    raise SystemExit(f"RESULT MISMATCH on {name}: {rn} != {ro}")
                ratios.append(tn / to)
            ratios.sort()
            q1, med, q3 = ratios[n // 4], statistics.median(ratios), ratios[-1 - n // 4]
            verdict = "faster" if q3 < 1 else "slower" if q1 > 1 else "no claim"
            rows.append({"case": name, "median": round(med, 3), "q1": round(q1, 3), "q3": round(q3, 3),
                         "pairs": n, "verdict": verdict})
            print(f"{name:32s} new/old {med:6.3f}   quartiles {q1:.3f}..{q3:.3f}   n={n:2d}   {verdict}")
        path = os.path.join(HERE, "results", "ab_log.json")
        log = json.load(open(path, encoding="utf-8")) if os.path.exists(path) else []
        head = subprocess.run(["git", "rev-parse", "--short", rev], cwd=HERE, capture_output=True, text=True).stdout.strip()
        log.append({"base": head, "rows": rows})
        json.dump(log, open(path, "w", encoding="utf-8"), indent=1)
    finally:
        shutil.rmtree(where, ignore_errors=True)


if __name__ == "__main__":
    main()
