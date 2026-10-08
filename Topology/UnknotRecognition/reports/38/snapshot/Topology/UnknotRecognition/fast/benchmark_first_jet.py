"""Paired actual-diagram raw comparisons for pre-Schur first-jet observation.

Every arm validates the same PD and uses the same supplied crossing order,
shape_cache=False, a 3-second deadline, and a 50000-object ceiling. Timings
include validation, scanner construction, observation and elimination; exclude
input construction, crossing-order selection, imports and one warmup. All
early front-end knot filters are bypassed. Seven shuffled paired rounds and
an identical standard-control arm expose timing noise. No synthetic input is
claimed to be a knot diagram. A timeout suppresses the whole case's ratios.
"""
import argparse
import hashlib
import json
from pathlib import Path
import platform
import random
import statistics
from time import monotonic, perf_counter

from fastunknot import Diagram
from fastunknot.first_jet_scan import first_jet_khovanov_decide
from fastunknot.geometry import ScanLimit
from fastunknot.ordering import best_scan_order
from fastunknot.scan_fast import FastScan

HERE = Path(__file__).resolve().parent


def cases():
    for name in ("trefoil", "conway", "kinoshita_terasaka", "hard_unknot_8",
                 "grid_scrambled_unknot", "stress_braid5_36", "conway_sum_2"):
        yield name, json.loads((HERE / "examples" / (name + ".json")).read_text())
    for strands in (12, 36):
        yield f"coxeter_{strands-1}", {"braid": {"strands": strands,
                                               "word": list(range(1, strands))}}
    for pairs in (8, 24):
        yield f"trefoil_cancel_pairs_{pairs}", {"braid": {"strands": 2,
                                               "word": [1, 1, 1] + [1, -1] * pairs}}
    yield "torus_3_5", {"braid": {"strands": 3, "word": [1, 2] * 5}}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--rounds", type=int, default=7)
    args = parser.parse_args()
    rng = random.Random(29005)
    sources = [Path(__file__)] + [HERE / "fastunknot" / name for name in
                                  ("first_jet.py", "first_jet_scan.py", "scan_fast.py")]
    result = dict(scope=__doc__, seed=29005, rounds=args.rounds,
                  python=platform.python_version(), rows=[],
                  source_sha256={str(p.relative_to(HERE)): hashlib.sha256(p.read_bytes()).hexdigest()
                                 for p in sources})
    arms = ["standard", "control", "jet", "no-geometry", "observe-only", "zero-budget"]
    for name, data in cases():
        diagram = Diagram.from_json(data)
        supplied_order = best_scan_order(diagram.pd, tries=min(diagram.crossings, 12))

        def run(arm):
            try:
                if arm in ("standard", "control"):
                    deadline = monotonic() + 3
                    checked = Diagram.from_pd(diagram.pd)
                    scan = FastScan(max_objects=50000, deadline=deadline, shape_cache=False)
                    for index in supplied_order:
                        scan.add_crossing(checked.pd[index])
                    rank = scan.total_rank() if checked.pd else 2
                    return dict(status="UNKNOT" if rank == 2 else "KNOTTED",
                                rank_capped=min(3, rank), method="closed-rank",
                                stats=dict(scan.stats, **scan.algebra.stats))
                return first_jet_khovanov_decide(
                    diagram.pd, order=supplied_order, max_objects=50000, seconds=3,
                    shape_cache=False, first_jet_max_work=0 if arm == "zero-budget" else 1000000,
                    replacements=arm != "observe-only", closure_bounds=arm != "no-geometry")
            except (ScanLimit, MemoryError) as error:
                return dict(status="UNKNOWN", reason=str(error))

        warm_times = {}
        for arm in arms:
            start = perf_counter()
            run(arm)
            warm_times[arm] = perf_counter() - start
        repetitions = max(1, min(30, int(.012 / max(warm_times.values()))))
        samples, evidence = [], {}
        for _ in range(args.rounds):
            arm_order = list(arms)
            rng.shuffle(arm_order)
            elapsed, statuses = {}, {}
            for arm in arm_order:
                observed = []
                start = perf_counter()
                for _ in range(repetitions):
                    output = run(arm)
                    observed.append(output["status"])
                elapsed[arm] = (perf_counter() - start) / repetitions
                statuses[arm] = "UNKNOWN" if "UNKNOWN" in observed else observed[-1]
                evidence[arm] = output
            decisive = {value for value in statuses.values() if value != "UNKNOWN"}
            if len(decisive) > 1:
                raise AssertionError("paired arms disagree")
            samples.append(dict(order=arm_order, seconds=elapsed, statuses=statuses))
        complete = all(all(s != "UNKNOWN" for s in trial["statuses"].values())
                       for trial in samples)
        ratios = ({arm: statistics.median(trial["seconds"]["standard"] /
                                         trial["seconds"][arm] for trial in samples)
                   for arm in arms[1:]} if complete else None)
        row = dict(name=name, input=data, pd=diagram.pd, order=supplied_order,
                   crossings=diagram.crossings, repetitions=repetitions,
                   complete=complete, median_standard_over_arm=ratios,
                   samples=samples, evidence=evidence)
        result["rows"].append(row)
        print(json.dumps(dict(name=name, crossings=diagram.crossings,
                              ratios=ratios,
                              jet_stats=evidence["jet"].get("first_jet_stats"),
                              standard_compositions=evidence["standard"].get("stats", {}).get("compositions"),
                              jet_compositions=evidence["jet"].get("stats", {}).get("compositions"))),
              flush=True)
    final_hashes = {str(p.relative_to(HERE)): hashlib.sha256(p.read_bytes()).hexdigest()
                    for p in sources}
    if final_hashes != result["source_sha256"]:
        raise AssertionError("source changed during paired measurements")
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + "\n")


if __name__ == "__main__":
    main()

