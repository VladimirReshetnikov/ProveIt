"""Paired RIII timings and reproducible searches for actual-diagram gains.

Timing includes fresh input construction and all recognition stages; the
separate simplifier rows include construction but bypass recognition filters.
Imports and one warmup per arm are excluded. An identical baseline/control
pair measures noise. The pinned baseline loads recognize.py and simplify.py;
all other modules are shared. Discovery counts are not timing comparisons.
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
from fastunknot.simplify import simplify, replay
from hard_unknots import SURVIVORS, make

HERE = Path(__file__).resolve().parent
ARMS = ("baseline", "control", "last", "clustered", "adaptive",
        "deeper_last", "deeper_adaptive")


def source_hashes():
    return {str(p.relative_to(HERE)): hashlib.sha256(p.read_bytes()).hexdigest()
            for p in [Path(__file__), HERE / "hard_unknots.py"] +
            [HERE / "fastunknot" / n for n in
             ("causal_r3.py", "simplify.py", "recognize.py", "__main__.py")]}


def cases():
    for name in ("unknot", "trefoil", "conway", "kinoshita_terasaka", "hard_unknot_8",
                 "grid_scrambled_unknot", "unknot_braid40", "stress_braid5_36"):
        yield name, json.loads((HERE / "examples" / (name + ".json")).read_text())
    for i, (_, strands, word) in enumerate(SURVIVORS):
        yield f"survivor_{i}", {"braid": {"strands": strands, "word": word}}
    yield "many_triangles", {"braid": {"strands": 3, "word": [1, 2] * 31}}


def discover(baseline):
    rng = random.Random(2703)
    revision = subprocess.check_output(
        ["git", "rev-parse", baseline + "^{commit}"], cwd=HERE, text=True).strip()
    old_simplify, _ = load_baseline(revision)
    result = {"seed": 2703, "sources": source_hashes(), "baseline": revision, "families": {}}
    for family in ("random_braids", "scrambled_unknots"):
        summary = dict(attempts=12000 if family == "random_braids" else 1200,
                       validated=0, stalled_above_six=0, improved=[],
                       comparisons={mode: dict(better=0, equal=0, worse=0)
                                    for mode in ("clustered", "adaptive")})
        if family == "scrambled_unknots":
            summary.update(conjugator_length=15, steps=800)
        for index in range(summary["attempts"]):
            if family == "random_braids":
                strands = rng.choice((4, 5, 6))
                word = [rng.choice((-1, 1)) * rng.randrange(1, strands)
                        for _ in range(rng.randrange(15, 36))]
            else:
                strands = 4 + index % 3
                word = make(strands, conjugator_length=15, steps=800, seed=index)
            try:
                diagram = Diagram.from_braid(strands, word)
            except ValueError:
                continue
            summary["validated"] += 1
            reduced_last, last_trace = simplify(diagram)
            old, old_trace = old_simplify(diagram)
            assert old.pd == reduced_last.pd
            assert [m.to_json() for m in old_trace] == [m.to_json() for m in last_trace]
            if reduced_last.crossings < 7:
                continue
            summary["stalled_above_six"] += 1
            for mode in ("clustered", "adaptive"):
                reduced, trace = simplify(diagram, r3_search=mode)
                assert replay(diagram, trace).pd == reduced.pd
                key = ("better" if reduced.crossings < reduced_last.crossings else
                       "worse" if reduced.crossings > reduced_last.crossings else "equal")
                summary["comparisons"][mode][key] += 1
                if key == "better":
                    summary["improved"].append(dict(index=index, strands=strands, word=word,
                                                   mode=mode, before=reduced_last.crossings,
                                                   after=reduced.crossings))
        result["families"][family] = summary
        summary["baseline_exact_trace_comparisons"] = summary["validated"]
        print(family, json.dumps(summary), flush=True)
    return result


def load_baseline(revision):
    modules = []
    for filename in ("simplify.py", "recognize.py"):
        source = subprocess.check_output([
            "git", "show", revision + ":Topology/UnknotRecognition/fast/fastunknot/" + filename],
            cwd=HERE, text=True)
        module = ModuleType("fastunknot._causal_baseline_" + filename[:-3])
        module.__package__ = "fastunknot"
        exec(compile(source, revision + ":" + filename, "exec"), module.__dict__)
        modules.append(module)
    modules[1].simplify = modules[0].simplify
    return modules[0].simplify, modules[1].recognize


def benchmark(args):
    revision = subprocess.check_output(
        ["git", "rev-parse", args.baseline + "^{commit}"], cwd=HERE, text=True).strip()
    old_simplify, old_recognize = load_baseline(revision)
    rng = random.Random(2704)
    result = dict(scope=__doc__, baseline=revision, sources=source_hashes(), seed=2704,
                  python=platform.python_version(), rounds=args.rounds, repetitions=3, rows=[])
    for name, data in cases():
        for scope in ("recognition", "simplifier"):
            evidence = {}

            def run(arm):
                diagram = Diagram.from_json(data)
                old = arm in ("baseline", "control")
                mode = arm.removeprefix("deeper_")
                options = {} if old else dict(r3_search=mode,
                                              r3_depth=6 if arm.startswith("deeper_") else 4)
                if scope == "recognition":
                    out = (old_recognize if old else recognize)(diagram, seconds=5, **options)
                    return dict(status=out.status, method=out.method,
                                r3_search=out.evidence.get("r3_search"))
                stats = {}
                out, trace = (old_simplify if old else simplify)(
                    diagram, **({} if old else dict(options, stats=stats)))
                return dict(crossings=out.crossings, moves=len(trace), stats=stats)

            for arm in ARMS:
                run(arm)
            samples = []
            for _ in range(args.rounds):
                order = list(ARMS)
                rng.shuffle(order)
                times = {}
                for arm in order:
                    start = perf_counter()
                    for _ in range(3):
                        observed = run(arm)
                    times[arm] = (perf_counter() - start) / 3
                    if arm in evidence:
                        assert evidence[arm] == observed
                    evidence[arm] = observed
                samples.append(dict(order=order, seconds=times))
            complete = scope == "simplifier" or all(v["status"] != "UNKNOWN" for v in evidence.values())
            if scope == "recognition":
                assert len({v["status"] for v in evidence.values()} - {"UNKNOWN"}) <= 1
            speedups = {arm: statistics.median(s["seconds"]["baseline"] / s["seconds"][arm]
                                               for s in samples) for arm in ARMS[1:]} if complete else None
            row = dict(name=name, input=data, scope=scope, evidence=evidence, samples=samples,
                       complete=complete, median_speedups=speedups)
            result["rows"].append(row)
            print(scope, name, {k: round(v, 3) for k, v in (speedups or {}).items()}, flush=True)
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--discovery", action="store_true")
    parser.add_argument("--baseline", default="28c974650")
    parser.add_argument("--rounds", type=int, default=7)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if args.rounds < 1:
        parser.error("rounds must be positive")
    result = discover(args.baseline) if args.discovery else benchmark(args)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + "\n")


if __name__ == "__main__":
    main()
