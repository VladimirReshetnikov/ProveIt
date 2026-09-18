"""Whole-process timing of the command line: working tree against a git revision, interleaved.

Usage:  python cli_ab.py [REV] [--pairs N]

What a command-line user waits for is the whole process: interpreter start, imports, argument
parsing, the work, the output.  The in-process tools (``perf.py``, ``ab.py``) do not see the first
three, which were more than half of it.  The revision is extracted to a temporary directory and
each arm is run *from its own directory*, with PYTHONPATH removed, and is checked to import its
own package: ``python -m`` puts the current directory first on ``sys.path``, so running both arms
from here compares the working tree with itself (that mistake produced a false "no difference").
"""
from __future__ import annotations

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


def run(root: str, args: list[str]):
    env = {k: v for k, v in os.environ.items() if k != "PYTHONPATH"}
    started = time.perf_counter()
    done = subprocess.run([sys.executable, "-m", "fastunknot"] + args, capture_output=True, text=True, env=env, cwd=root)
    elapsed = time.perf_counter() - started
    if done.returncode not in (0, 3):
        raise SystemExit(f"{args} failed in {root}: {done.stderr[-300:]}")
    return elapsed, json.loads(done.stdout)


def median_interval(values: list[float]):
    n, k, cumulative = len(values), 0, 0.0
    while k < n // 2:
        cumulative += math.comb(n, k) / 2 ** n
        if cumulative > 0.025:
            break
        k += 1
    k = max(k, 1)
    return values[k - 1], values[n - k]


def main():
    args = sys.argv[1:]
    rev = args[0] if args and not args[0].startswith("--") else "HEAD"
    pairs = int(args[args.index("--pairs") + 1]) if "--pairs" in args else 41
    where = tempfile.mkdtemp(prefix="fastunknot_cli_")
    try:
        data = subprocess.run(["git", "archive", rev, "fastunknot"], cwd=HERE, check=True, capture_output=True).stdout
        with tarfile.open(fileobj=io.BytesIO(data)) as tar:
            tar.extractall(where)
        for root in (where, HERE):
            probe = "import fastunknot, os; print(os.path.dirname(os.path.abspath(fastunknot.__file__)))"
            env = {k: v for k, v in os.environ.items() if k != "PYTHONPATH"}
            got = subprocess.run([sys.executable, "-c", probe], capture_output=True, text=True, cwd=root, env=env).stdout.strip()
            if os.path.normcase(os.path.realpath(got)) != os.path.normcase(os.path.realpath(os.path.join(root, "fastunknot"))):
                raise SystemExit(f"the arm in {root} imports {got}")
        bare = statistics.median(_bare() for _ in range(15))
        print(f"bare interpreter {bare * 1000:.1f} ms")
        examples = os.path.join(HERE, "examples")
        cases = [["recognize", os.path.join(examples, "conway.json")],
                 ["recognize", os.path.join(examples, "hard_unknot_8.json")],
                 ["recognize", os.path.join(examples, "unknot_braid40.json")],
                 ["khovanov", os.path.join(examples, "trefoil.json")],
                 ["khovanov", os.path.join(examples, "stress_braid5_36.json")]]
        rows = []
        for case in cases:
            ratios, old, new = [], [], []
            for k in range(pairs):
                if k % 2:
                    (b, rb), (a, ra) = run(HERE, case), run(where, case)
                else:
                    (a, ra), (b, rb) = run(where, case), run(HERE, case)
                if (ra.get("status"), ra.get("rank")) != (rb.get("status"), rb.get("rank")):
                    raise SystemExit(f"RESULT MISMATCH on {case}")
                ratios.append(b / a)
                old.append(a)
                new.append(b)
            ratios.sort()
            low, high = median_interval(ratios)
            name = case[0] + " " + os.path.basename(case[1])
            rows.append({"case": name, "old_ms": round(statistics.median(old) * 1000, 1),
                         "new_ms": round(statistics.median(new) * 1000, 1), "ratio": round(statistics.median(ratios), 3),
                         "ci95": [round(low, 3), round(high, 3)], "pairs": pairs})
            print(f"{name:36s} {rows[-1]['old_ms']:7.1f} ms -> {rows[-1]['new_ms']:7.1f} ms   "
                  f"ratio {rows[-1]['ratio']:.3f}  CI95 {low:.3f}..{high:.3f}")
        path = os.path.join(HERE, "results", "cli_ab_log.json")
        log = json.load(open(path, encoding="utf-8")) if os.path.exists(path) else []
        head = subprocess.run(["git", "rev-parse", "--short", rev], cwd=HERE, capture_output=True, text=True).stdout.strip()
        log.append({"base": head, "bare_interpreter_ms": round(bare * 1000, 1), "rows": rows})
        json.dump(log, open(path, "w", encoding="utf-8"), indent=1)
    finally:
        shutil.rmtree(where, ignore_errors=True)


def _bare() -> float:
    started = time.perf_counter()
    subprocess.run([sys.executable, "-c", "pass"])
    return time.perf_counter() - started


if __name__ == "__main__":
    main()
