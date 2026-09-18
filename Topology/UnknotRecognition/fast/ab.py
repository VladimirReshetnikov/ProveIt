"""Interleaved A/B timing of the working tree against a git revision.

Usage:  python ab.py [REV] [--pairs N]        working tree (new) against REV (old, default HEAD)
        python ab.py OLD_REV NEW_REV [--pairs N]   two revisions, to re-test a past claim

Wall-clock on a desktop drifts by tens of percent within a minute (background
load, clock throttling), which makes sequential before/after runs of perf.py
misleading.  Here the package at REV is extracted next to the working tree under
another name, and the two are timed alternately in one process, rotating which
goes first.  Results (ranks by degree, verdicts) are asserted equal every time.

Each round also times the old code a second time.  The ratio old2/old is an A/A
control: it shows how far a ratio strays from 1 on this case when nothing
changed.  A difference is claimed only if (a) the 95% confidence interval of
the median of new/old, from order statistics, excludes 1, and (b) that median
lies outside the interquartile range of the A/A ratios.  The first version of
this tool used "interquartile range of new/old entirely on one side of 1" and
produced false claims in both directions on mid-sized scans (a change confined
to 1% of the run time was reported as 14% slower on one input and 4% faster on
another); see the README.
"""
from __future__ import annotations

import importlib
import io
import json
import math
import os
import shutil
import statistics
import subprocess
import sys
import tarfile
import tempfile
import time

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import hard_unknots  # noqa: E402


def load_base(rev: str, where: str, name: str = "fastunknot_base"):
    data = subprocess.run(["git", "archive", rev, "fastunknot"], cwd=HERE, check=True,
                          capture_output=True).stdout
    with tarfile.open(fileobj=io.BytesIO(data)) as tar:
        tar.extractall(where)
    os.rename(os.path.join(where, "fastunknot"), os.path.join(where, name))
    if where not in sys.path:
        sys.path.insert(0, where)
    return importlib.import_module(name)


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
        "recognize conway_sum_3": rec(example("conway_sum_3.json")),
        "recognize unknot 4/38 (27)": rec(D.from_braid(4, hard_unknots.make(4, seed=38))),
        "recognize unknot 4/11 (25)": rec(D.from_braid(4, hard_unknots.make(4, seed=11))),
        "recognize unknot 4/20 (25)": rec(D.from_braid(4, hard_unknots.make(4, seed=20))),
        "jones braid5_36": (lambda d=D.from_braid(5, words["random 5-braid", 36]):
                            pkg.filters.jones_obstruction(d)),
    }


def median_interval(sorted_values, level: float = 0.95):
    """Distribution-free confidence interval of the median: order statistics k and n+1-k,
    k the largest rank with P(Binomial(n, 1/2) < k) <= (1 - level) / 2."""
    n = len(sorted_values)
    tail, cumulative, k = (1 - level) / 2, 0.0, 0
    while k < n // 2:
        cumulative += math.comb(n, k) / 2 ** n
        if cumulative > tail:
            break
        k += 1
    k = max(k, 1)
    return sorted_values[k - 1], sorted_values[n - k]


def timed(fn):
    t = time.perf_counter()
    result = fn()
    return time.perf_counter() - t, result


def main():
    args = sys.argv[1:]
    revs = []
    for a in args:
        if a.startswith("--"):
            break
        revs.append(a)
    rev = revs[0] if revs else "HEAD"
    new_rev = revs[1] if len(revs) > 1 else None
    pairs = int(args[args.index("--pairs") + 1]) if "--pairs" in args else 15
    where = tempfile.mkdtemp(prefix="fastunknot_ab_")
    try:
        sys.path.insert(0, HERE)
        new_pkg = load_base(new_rev, where, "fastunknot_new") if new_rev else importlib.import_module("fastunknot")
        new, old = corpus(new_pkg), corpus(load_base(rev, where))
        rows = []
        for name in new:
            n = max(9, pairs // 2) if name == "scan braid5_36" else pairs      # the one slow case
            ratios, control = [], []
            for k in range(n):
                arms = [("old", old[name]), ("new", new[name]), ("old2", old[name])]
                arms = arms[k % 3:] + arms[:k % 3]            # rotate the starting arm
                times = {}
                for tag, fn in arms:
                    times[tag], result = timed(fn)
                    if times.setdefault("result", result) != result:
                        raise SystemExit(f"RESULT MISMATCH on {name}: {result} != {times['result']}")
                ratios.append(times["new"] / times["old"])
                control.append(times["old2"] / times["old"])
            ratios.sort()
            control.sort()
            lo, hi = median_interval(ratios)
            med = statistics.median(ratios)
            a1, a3 = control[n // 4], control[-1 - n // 4]
            if hi < 1 and med < a1:
                verdict = "faster"
            elif lo > 1 and med > a3:
                verdict = "slower"
            else:
                verdict = "no claim"
            rows.append({"case": name, "median": round(med, 3), "ci95": [round(lo, 3), round(hi, 3)],
                         "aa_median": round(statistics.median(control), 3), "aa_quartiles": [round(a1, 3), round(a3, 3)],
                         "rounds": n, "verdict": verdict})
            print(f"{name:32s} new/old {med:6.3f}  CI95 {lo:.3f}..{hi:.3f}   A/A {statistics.median(control):.3f} "
                  f"({a1:.3f}..{a3:.3f})   n={n:2d}   {verdict}")
        path = os.path.join(HERE, "results", "ab_log.json")
        log = json.load(open(path, encoding="utf-8")) if os.path.exists(path) else []
        head = subprocess.run(["git", "rev-parse", "--short", rev], cwd=HERE, capture_output=True, text=True).stdout.strip()
        log.append({"base": head, "new": new_rev or "working tree", "rows": rows})
        json.dump(log, open(path, "w", encoding="utf-8"), indent=1)
    finally:
        shutil.rmtree(where, ignore_errors=True)


if __name__ == "__main__":
    main()
