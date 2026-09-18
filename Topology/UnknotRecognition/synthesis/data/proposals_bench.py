"""Same-machine comparison of fast/ (any revision) and the nine proposals.

Every (engine, case) pair runs in a fresh Python process with a hard timeout.
Timers exclude interpreter start-up, imports and input construction.
Usage:  python proposals_bench.py [--engines base,01,..] [--timeout 120] [--repeats 3] [--output FILE]
"""
from __future__ import annotations

import argparse
import json
import os
import statistics
import subprocess
import sys
import time

ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", ".."))
ENGINES = {
    "base": "proposals/01/baseline", "new": "fast", "01": "proposals/01/fast", "02": "proposals/02", "03": "proposals/03",
    "04": "proposals/04/fast", "05": "proposals/05", "06": "proposals/06/fast",
    "07": "proposals/07", "08": "proposals/08", "09": "proposals/09",
}
BENCH = json.load(open(os.path.join(ROOT, "fast", "results", "benchmark_0.1.json"), encoding="utf-8")) \
    if os.path.exists(os.path.join(ROOT, "fast", "results", "benchmark_0.1.json")) else {"scan_families": []}


def word(strands, crossings):
    for r in BENCH["scan_families"]:
        if r["family"] == f"random {strands}-braid" and r["crossings"] == crossings:
            return r["word"]
    raise KeyError((strands, crossings))


def example(name):
    return json.load(open(os.path.join(ROOT, "fast", "examples", name), encoding="utf-8"))


def conway_sum(k):
    return json.load(open(os.path.join(ROOT, "proposals", "05", "examples", f"conway_sum_{k}.json"),
                          encoding="utf-8"))


def cases():
    out = []
    raw = [("conway", example("conway.json")), ("kinoshita_terasaka", example("kinoshita_terasaka.json")),
           ("T(3,11)", {"braid": {"strands": 3, "word": [1, 2] * 11}}),
           ("braid3_40", {"braid": {"strands": 3, "word": word(3, 40)}}),
           ("braid4_41", {"braid": {"strands": 4, "word": word(4, 41)}}),
           ("braid6_31", {"braid": {"strands": 6, "word": word(6, 31)}}),
           ("braid5_36", {"braid": {"strands": 5, "word": word(5, 36)}}),
           ("chain256", {"braid": {"strands": 257, "word": list(range(1, 257))}}),
           ("conway_sum_2", conway_sum(2))]
    for name, data in raw:
        out.append({"case": name, "mode": "raw", "input": data})
    out.append({"case": "conway_sum_8", "mode": "rank", "input": conway_sum(8)})
    rec = [("trefoil", example("trefoil.json")), ("torus_3_5", example("torus_3_5.json")),
           ("hard_unknot_8", example("hard_unknot_8.json")), ("unknot_braid40", example("unknot_braid40.json")),
           ("conway", example("conway.json")), ("kinoshita_terasaka", example("kinoshita_terasaka.json")),
           ("conway_sum_2", conway_sum(2)), ("conway_sum_3", conway_sum(3)),
           ("T(3,61)", {"braid": {"strands": 3, "word": [1, 2] * 61}}),
           ("braid5_36", {"braid": {"strands": 5, "word": word(5, 36)}})]
    for name, data in rec:
        out.append({"case": name, "mode": "recognize", "input": data})
    return out


WORKER = r"""
import inspect, json, sys, time
sys.path.insert(0, sys.argv[1])
job = json.loads(sys.stdin.read())
from fastunknot import Diagram, khovanov_rank, recognize
d = Diagram.from_json(job["input"])
if job["mode"] == "recognize":
    t = time.perf_counter(); r = recognize(d); t = time.perf_counter() - t
    out = {"seconds": t, "status": r.status, "method": r.method}
else:
    kwargs = {}
    if job["mode"] == "raw":
        for name in inspect.signature(khovanov_rank).parameters:
            if name in ("factor", "factor_connected", "decompose"):
                kwargs[name] = False
    t = time.perf_counter(); r = khovanov_rank(d.pd, **kwargs); t = time.perf_counter() - t
    out = {"seconds": t, "reduced_rank": str(r["reduced_rank"]),
           "max_objects_after": (r.get("stats") or {}).get("max_objects_after_elimination")}
print(json.dumps(out))
"""


def run(engine_path, job, timeout):
    env = dict(os.environ, PYTHONHASHSEED="0")
    try:
        p = subprocess.run([sys.executable, "-c", WORKER, engine_path], input=json.dumps(job),
                           capture_output=True, text=True, timeout=timeout, env=env)
    except subprocess.TimeoutExpired:
        return {"timeout": timeout}
    if p.returncode != 0:
        return {"error": p.stderr.strip().splitlines()[-1] if p.stderr.strip() else f"exit {p.returncode}"}
    return json.loads(p.stdout.strip().splitlines()[-1])


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--engines", default=",".join(ENGINES))
    ap.add_argument("--timeout", type=float, default=120)
    ap.add_argument("--repeats", type=int, default=3)
    ap.add_argument("--only", default="")
    ap.add_argument("--output", default=os.path.join(os.path.dirname(__file__), "proposals_bench.json"))
    ap.add_argument("--engine-path", action="append", default=[], help="extra NAME=PATH engine")
    args = ap.parse_args()
    engines = {k: ENGINES[k] for k in args.engines.split(",") if k in ENGINES}
    for spec in args.engine_path:
        name, path = spec.split("=", 1)
        engines[name] = path
    results = []
    for job in cases():
        if args.only and args.only not in job["case"]:
            continue
        for name, rel in engines.items():
            samples, last = [], None
            for _ in range(args.repeats):
                last = run(os.path.join(ROOT, rel), job, args.timeout)
                if "seconds" not in last:
                    break
                samples.append(last["seconds"])
                if last["seconds"] > 5:
                    break
            row = {"case": job["case"], "mode": job["mode"], "engine": name, **(last or {})}
            if samples:
                row["seconds"] = statistics.median(samples)
                row["samples"] = samples
            results.append(row)
            print(json.dumps(row), flush=True)
            json.dump(results, open(args.output, "w", encoding="utf-8"), indent=1)


if __name__ == "__main__":
    main()
