"""Ablation of the ideas adopted in fastunknot 0.2.  Regenerates results/ablation.json.

Every measurement runs in a fresh process with a hard timeout; timers exclude
interpreter start-up, imports and input construction.  Medians of three runs
(one run when a run takes more than five seconds).
"""
from __future__ import annotations

import json
import os
import platform
import statistics
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))

WORKER = r"""
import json, sys, time
sys.path.insert(0, sys.argv[1])
job = json.loads(sys.stdin.read())
from fastunknot.diagram import Diagram
d = Diagram.from_json(job["input"])
kind, opts = job["kind"], job.get("options", {})
if kind == "scan_reference":
    from fastunknot.scan_reference import khovanov_rank
    t = time.perf_counter(); r = khovanov_rank(d.pd); t = time.perf_counter() - t
    out = {"result": r["reduced_rank"]}
elif kind == "scan":
    from fastunknot.scan import khovanov_rank
    t = time.perf_counter(); r = khovanov_rank(d.pd, **opts); t = time.perf_counter() - t
    out = {"result": r["reduced_rank"], "max_objects_after": r["stats"]["max_objects_after_elimination"],
           "compositions": r["stats"]["compositions"]}
elif kind == "factored":
    from fastunknot import factored_khovanov_rank
    t = time.perf_counter(); r = factored_khovanov_rank(d); t = time.perf_counter() - t
    out = {"result": str(r["reduced_rank"])}
elif kind == "recognize":
    from fastunknot import recognize
    t = time.perf_counter(); r = recognize(d, **opts); t = time.perf_counter() - t
    out = {"result": r.status, "method": r.method}
elif kind == "order":
    from fastunknot import ordering, scan_reference
    f = ordering.best_scan_order if opts["heap"] else scan_reference.best_scan_order
    pd = list(d.pd)
    t = time.perf_counter(); o = f(pd, 12); t = time.perf_counter() - t
    out = {"result": len(o)}
elif kind == "descending":
    from fastunknot import simplify
    f = simplify.descending_start if opts["linear"] else simplify.descending_start_quadratic
    t = time.perf_counter(); o = f(d); t = time.perf_counter() - t
    out = {"result": o is not None}
elif kind == "simplify":
    from fastunknot import simplify
    f = simplify.simplify if opts["incremental"] else simplify.simplify_reference
    t = time.perf_counter(); o, _ = f(d); t = time.perf_counter() - t
    out = {"result": o.crossings}
elif kind == "alexander":
    from fastunknot.filters import alexander_obstruction
    from fastunknot.alexander import alexander_polynomial
    t = time.perf_counter()
    o = alexander_obstruction(d) is not None if opts["modular"] else alexander_polynomial(d) != [1]
    t = time.perf_counter() - t
    out = {"result": o}
out["seconds"] = t
print(json.dumps(out))
"""


def run(job, timeout):
    try:
        p = subprocess.run([sys.executable, "-c", WORKER, HERE], input=json.dumps(job), text=True,
                           capture_output=True, timeout=timeout, env=dict(os.environ, PYTHONHASHSEED="0"))
    except subprocess.TimeoutExpired:
        return {"timeout": timeout}
    if p.returncode:
        return {"error": (p.stderr.strip().splitlines() or ["?"])[-1]}
    return json.loads(p.stdout.strip().splitlines()[-1])


def measure(job, timeout, repeats=3):
    samples, last = [], None
    for _ in range(repeats):
        last = run(job, timeout)
        if "seconds" not in last:
            return last
        samples.append(last["seconds"])
        if last["seconds"] > 5:
            break
    last["seconds"] = statistics.median(samples)
    last["samples"] = samples
    return last


def main():
    bench = json.load(open(os.path.join(HERE, "results", "benchmark_0.1.json"), encoding="utf-8"))
    words = {(r["family"], r["crossings"]): r["word"] for r in bench["scan_families"] if "word" in r}

    def braid(strands, length):
        return {"braid": {"strands": strands, "word": words[f"random {strands}-braid", length]}}

    def example(name):
        return json.load(open(os.path.join(HERE, "examples", name), encoding="utf-8"))

    scans = [("conway", example("conway.json")), ("braid3_40", braid(3, 40)), ("braid4_41", braid(4, 41)),
             ("braid6_31", braid(6, 31)), ("braid5_36", braid(5, 36))]
    configs = [("0.1 reference scanner", "scan_reference", {}),
               ("sets, LIFO, series inverse", "scan", {"algebra": "sets", "pivot": "lifo", "self_inverse": False}),
               ("sets, LIFO, self-inverse", "scan", {"algebra": "sets", "pivot": "lifo"}),
               ("sets, min-fill", "scan", {"algebra": "sets"}),
               ("bits, LIFO", "scan", {"pivot": "lifo"}),
               ("bits, min-fill (default)", "scan", {}),
               ("bits, min-fill, tail 1", "scan", {"tail": 1}),
               ("bits, min-fill, tail 2", "scan", {"tail": 2})]
    rows = []
    for case, data in scans:
        for label, kind, options in configs:
            row = {"group": "scan", "case": case, "config": label,
                   **measure({"kind": kind, "input": data, "options": options}, 300)}
            rows.append(row)
            print(row, flush=True)
    chain = {"braid": {"strands": 2049, "word": list(range(1, 2049))}}
    conway3 = example("conway_sum_3.json")
    others = [
        ("order", "greedy order, 2048 crossings", "heap O(n log n)", {"kind": "order", "input": chain, "options": {"heap": True}}),
        ("order", "greedy order, 2048 crossings", "0.1 rescoring O(n^2)", {"kind": "order", "input": chain, "options": {"heap": False}}),
        ("descending", "descending test, 2048 crossings", "linear sweep", {"kind": "descending", "input": chain, "options": {"linear": True}}),
        ("descending", "descending test, 2048 crossings", "0.1 quadratic", {"kind": "descending", "input": chain, "options": {"linear": False}}),
        ("simplify", "R1/R2 reduction, 2048 crossings", "incremental", {"kind": "simplify", "input": chain, "options": {"incremental": True}}),
        ("simplify", "R1/R2 reduction, 2048 crossings", "0.1 rebuild per move", {"kind": "simplify", "input": chain, "options": {"incremental": False}}),
        ("alexander", "T(3,61) rejection, 122 crossings", "modular minor", {"kind": "alexander", "input": {"braid": {"strands": 3, "word": [1, 2] * 61}}, "options": {"modular": True}}),
        ("alexander", "T(3,61) rejection, 122 crossings", "0.1 exact Z[t]", {"kind": "alexander", "input": {"braid": {"strands": 3, "word": [1, 2] * 61}}, "options": {"modular": False}}),
        ("jones", "recognize Conway", "with Jones filter", {"kind": "recognize", "input": example("conway.json")}),
        ("jones", "recognize Conway", "without Jones filter", {"kind": "recognize", "input": example("conway.json"), "options": {"use_jones": False}}),
        ("factor", "recognize Conway#Conway#Conway, no Jones", "with factorization", {"kind": "recognize", "input": conway3, "options": {"use_jones": False}}),
        ("factor", "recognize Conway#Conway#Conway, no Jones", "without factorization", {"kind": "recognize", "input": conway3, "options": {"use_jones": False, "use_factorization": False}}),
        ("factor", "rank of Conway#Conway#Conway", "factored", {"kind": "factored", "input": conway3}),
        ("factor", "rank of Conway#Conway#Conway", "one scan", {"kind": "scan", "input": conway3}),
    ]
    for group, case, label, job in others:
        row = {"group": group, "case": case, "config": label, **measure(job, 300)}
        rows.append(row)
        print(row, flush=True)
    with open(os.path.join(HERE, "results", "ablation.json"), "w", encoding="utf-8") as handle:
        json.dump({"python": platform.python_version(), "platform": platform.platform(), "rows": rows},
                  handle, indent=1)


if __name__ == "__main__":
    main()
