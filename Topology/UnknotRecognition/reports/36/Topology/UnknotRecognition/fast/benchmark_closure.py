"""Classical closure resets versus complete recognizers and raw scanners.

Recognition keeps every default filter enabled. Raw decisions bypass those
filters and compare saturated, Euler and classical closure scans directly, including a no-reset control.
Both scopes time fresh PD construction, setup, inference and fallback, excluding
imports and one warmup. Each case has seven shuffled paired rounds and an
identical control arm. UNKNOWN suppresses timing ratios for that entire case.
"""
import argparse
import hashlib
import json
from pathlib import Path
import platform
import random
import statistics
import subprocess
from time import perf_counter
from types import ModuleType

from fastunknot import Diagram, recognize
from fastunknot.component_scan import compressed_khovanov_decide
from fastunknot.euler_scan import euler_compressed_khovanov_decide
from fastunknot.geometry import ScanLimit
from fastunknot.closure_scan import closure_khovanov_decide

HERE = Path(__file__).resolve().parent


def cases():
    for name in ("unknot", "trefoil", "conway", "kinoshita_terasaka", "hard_unknot_8",
                 "grid_scrambled_unknot", "stress_braid5_36", "conway_sum_2", "conway_sum_8"):
        yield name, json.loads((HERE / "examples" / (name + ".json")).read_text())
    for path in sorted((HERE.parent / "reports/28/examples").glob("*.json")):
        if not path.name.endswith(".result.json"):
            yield "report28_" + path.stem, json.loads(path.read_text())
    for power in (5, 7, 11):
        yield f"torus_3_{power}", {"braid": {"strands": 3, "word": [1, 2] * power}}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--rounds", type=int, default=7)
    args = parser.parse_args()
    if args.rounds < 1:
        parser.error("rounds must be positive")
    revision = subprocess.check_output(["git", "rev-parse", "e6f975521^{commit}"],
                                       cwd=HERE, text=True).strip()
    source = subprocess.check_output(["git", "show", revision +
        ":Topology/UnknotRecognition/fast/fastunknot/recognize.py"], cwd=HERE, text=True)
    old = ModuleType("fastunknot._closure_baseline")
    old.__package__ = "fastunknot"
    exec(compile(source, revision + ":recognize.py", "exec"), old.__dict__)
    rng = random.Random(2804)
    result = dict(scope=__doc__, baseline_revision=revision,
                  baseline_scope="recognize.py only; other unchanged modules shared",
                  python=platform.python_version(), rounds=args.rounds, seed=2804,
                  sources={str(p.relative_to(HERE)): hashlib.sha256(p.read_bytes()).hexdigest()
                           for p in [Path(__file__)] + [HERE / "fastunknot" / n for n in
                           ("closure_scan.py", "euler_scan.py", "component_scan.py",
                            "recognize.py", "__main__.py")]}, rows=[])
    for name, data in cases():
        for scope in ("recognition", "raw-decision"):
            arms = (["baseline", "control", "current", "saturated", "euler", "closure"]
                    if scope == "recognition" else ["saturated", "control", "euler", "closure", "no-reset"])
            base = arms[0]

            def run(arm):
                diagram = Diagram.from_json(data)
                try:
                    if scope == "recognition":
                        call = old.recognize if arm in ("baseline", "control") else recognize
                        backend = "standard" if arm in ("baseline", "control", "current") else arm
                        out = call(diagram, backend=backend, seconds=5, max_objects=50000)
                        kh = out.evidence.get("khovanov", {})
                        return dict(status=out.status, method=out.method, stage=kh.get("stage"),
                                    closure_stats=kh.get("closure_stats"), events=kh.get("events"))
                    call = (euler_compressed_khovanov_decide if arm == "euler" else
                            closure_khovanov_decide if arm in ("closure", "no-reset") else
                            compressed_khovanov_decide)
                    out = call(diagram.pd, seconds=5, max_objects=50000,
                               **({"reset": False} if arm == "no-reset" else {}))
                    return dict(status=out["status"], method=out.get("method", "closed-rank"),
                                    stage=out.get("stage", out.get("closure_stats", {}).get("scanned", diagram.crossings)),
                                closure_stats=out.get("closure_stats"), events=out.get("events"))
                except (ScanLimit, MemoryError) as error:
                    return dict(status="UNKNOWN", reason=str(error))

            warm = {}
            for arm in arms:
                start = perf_counter()
                run(arm)
                warm[arm] = perf_counter() - start
            repetitions = max(1, min(20, int(.005 / max(warm.values()))))
            samples, evidence = [], {}
            for _ in range(args.rounds):
                order = list(arms)
                rng.shuffle(order)
                times, statuses = {}, {}
                for arm in order:
                    observed = []
                    start = perf_counter()
                    for _ in range(repetitions):
                        out = run(arm)
                        observed.append(out["status"])
                    times[arm] = (perf_counter() - start) / repetitions
                    assert len(set(observed) - {"UNKNOWN"}) <= 1
                    statuses[arm] = "UNKNOWN" if "UNKNOWN" in observed else observed[-1]
                    evidence[arm] = out
                assert len(set(statuses.values()) - {"UNKNOWN"}) <= 1
                samples.append(dict(order=order, seconds=times,
                                    statuses=statuses))
            complete = all(all(status != "UNKNOWN" for status in s["statuses"].values()) for s in samples)
            speedups = {arm: statistics.median(s["seconds"][base] / s["seconds"][arm]
                                               for s in samples) for arm in arms[1:]} if complete else None
            row = dict(name=name, input=data, scope=scope, repetitions=repetitions,
                       evidence=evidence, samples=samples, complete=complete, median_speedups=speedups)
            result["rows"].append(row)
            print(scope, name, {k: round(v, 3) for k, v in (speedups or {}).items()},
                  {k: (v["status"], v.get("stage")) for k, v in evidence.items()}, flush=True)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + "\n")


if __name__ == "__main__":
    main()
