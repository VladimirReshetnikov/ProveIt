"""Paired complete full-Jones queries: faithful Potts, A/A, and binary tensors.

All arms return the same full polynomial and construct a fresh Diagram. Timing
includes every order-preparation step. The integer-ordinary arm is a deliberate
ordering ablation without a universal width promise. Capped measurements are
retained and excluded from completed-query speedup ratios. These are invariant
queries; no claim is made about complete unknot-recognition speed.
"""
import argparse
from hashlib import sha256
import json
from pathlib import Path
import platform
import random
from statistics import median
import sys
from time import perf_counter

from fastunknot import Diagram
from fastunknot.faithful_jones import faithful_potts_exact
from fastunknot.filters import FilterLimit
from fastunknot.geometry import ScanLimit
from fastunknot.integer_codec import json_safe
from fastunknot.tensor_jones import tensor_jones
from check_potts_independent import laurent_jones
from separator_research.graphs import tree_medial

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT/"tests"))
from disk_grid import descending_grid


def coefficients(result):
    return {e: int(c, 16) for e, c in result["jones_polynomial"]["coefficients_hex"]}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--rounds", type=int, default=7)
    parser.add_argument("--seconds", type=float, default=2)
    args = parser.parse_args()
    if args.rounds < 1 or args.seconds <= 0:
        parser.error("rounds and seconds must be positive")
    rng = random.Random(2645)
    cases = []
    for name in ("trefoil", "conway", "kinoshita_terasaka", "hard_unknot_8",
                 "stress_braid5_36"):
        pd = Diagram.from_json(json.loads((ROOT/"examples"/(name+".json")).read_text())).pd
        cases.append((name, pd, None))
    cases += [(f"weaving-{m}", Diagram.from_braid(3, [1, -2]*m).pd, None)
              for m in (5, 13, 17)]
    cases += [(f"tree-{h}", tree_medial(h).pd, None) for h in (6, 7)]
    for m in (4, 6, 8, 10):
        cases.append((f"grid-{m}", descending_grid(m), None))
    pd = descending_grid(8)
    supplied = list(range(len(pd)))
    rng.shuffle(supplied)
    cases.append(("grid-8-shuffled", pd, supplied))
    rows = []
    for name, pd, order in cases:
        oracle = ({-e: c for e, c in laurent_jones(Diagram.from_pd(pd)).items()}
                  if len(pd) <= 12 else None)
        samples = []
        for repetition in range(args.rounds+1):
            arms = ["faithful", "control", "laurent", "integer-global", "integer", "integer-ordinary"]
            rng.shuffle(arms)
            elapsed, results, polynomials = {}, {}, []
            for arm in arms:
                start = perf_counter()
                def check():
                    if perf_counter()-start > args.seconds:
                        raise ScanLimit("complete polynomial query time allowance")
                try:
                    options = dict(order=order, max_states=4096, max_transitions=200000,
                                   check=check)
                    if arm in ("faithful", "control"):
                        result = faithful_potts_exact(Diagram.from_pd(pd),
                                                      include_polynomial=True, **options)
                    else:
                        result = tensor_jones(Diagram.from_pd(pd),
                                              arithmetic=arm if arm in ("laurent", "integer-global") else "integer",
                                              certified=arm != "integer-ordinary", **options)
                    polynomial = coefficients(result)
                    if oracle is not None:
                        assert polynomial == oracle
                    polynomials.append(polynomial)
                    results[arm] = dict(status="COMPLETE", result=result)
                except (FilterLimit, ScanLimit) as error:
                    results[arm] = dict(status="CAPPED", reason=str(error),
                                        transitions=getattr(error, "transitions", None),
                                        peak_states=getattr(error, "peak_states", None))
                elapsed[arm] = perf_counter()-start
            assert all(p == polynomials[0] for p in polynomials)
            if repetition:
                samples.append(dict(arm_order=arms, seconds=elapsed, results=results))
        complete = [arm for arm in arms if all(s["results"][arm]["status"] == "COMPLETE"
                                               for s in samples)]
        ratios = ({arm: median(s["seconds"]["faithful"]/s["seconds"][arm] for s in samples)
                   for arm in complete if arm != "faithful"} if "faithful" in complete else {})
        row = dict(name=name, crossings=len(pd), pd=pd, supplied_order=order,
                   independent_cube_checked=oracle is not None, samples=samples,
                   complete_arms=complete, median_faithful_over=ratios,
                   median_seconds={arm: median(s["seconds"][arm] for s in samples) for arm in arms})
        rows.append(row)
        print(name, {a: round(1000*t, 3) for a, t in row["median_seconds"].items()},
              complete, flush=True)
    paths = ["benchmark_tensor_jones.py", "fastunknot/tensor_jones.py",
             "fastunknot/faithful_jones.py", "fastunknot/potts_exact.py",
             "fastunknot/adaptive_potts.py", "fastunknot/separator_order.py"]
    result = dict(seed=2645, rounds=args.rounds, warmups=1,
                  seconds_per_query=args.seconds, max_states=4096, max_transitions=200000,
                  python=sys.version, platform=platform.platform(), scope=__doc__,
                  source_sha256={p: sha256((ROOT/p).read_bytes()).hexdigest() for p in paths}, rows=rows)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(json_safe(result), indent=2)+"\n")


if __name__ == "__main__":
    main()
