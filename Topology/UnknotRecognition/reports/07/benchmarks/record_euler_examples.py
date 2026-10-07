"""Record exact early-certificate stages and operation counters (not timings)."""
import argparse
import json
from pathlib import Path
import sys

FAST_ROOT = Path(__file__).resolve().parents[1] / "fast"
if FAST_ROOT.is_dir():
    sys.path.insert(0, str(FAST_ROOT))

from fastunknot import Diagram
try:
    from fastunknot.component_scan import compressed_khovanov_decide
    from fastunknot.euler_scan import euler_compressed_khovanov_decide
except ModuleNotFoundError as exc:
    if exc.name not in ("fastunknot.component_scan", "fastunknot.euler_scan"):
        raise
    from component_scan import compressed_khovanov_decide
    from euler_scan import euler_compressed_khovanov_decide


def record(examples):
    output = {}
    for name in ["conway", "torus_3_5", "stress_braid5_36", "conway_sum_2",
                 "conway_sum_3", "conway_sum_8", "hard_unknot_8"]:
        diagram = Diagram.from_json(json.loads((examples / (name + ".json")).read_text()))
        plain = compressed_khovanov_decide(diagram.pd)
        early = euler_compressed_khovanov_decide(diagram.pd, check_d_squared=True)
        if plain["status"] != early["status"]:
            raise AssertionError("Euler verdict differs from complete capped scan")
        if name == "conway_sum_8":
            limited = euler_compressed_khovanov_decide(diagram.pd, euler_max_states=1)
            if limited["status"] != plain["status"] or not limited["euler_exhausted"]:
                raise AssertionError("budget fallback failed")
        else:
            limited = None
        output[name] = dict(
            complete_work=plain["stats"].get("entries", 0) + plain["stats"].get("compositions", 0),
            euler_result=early, tiny_budget_result=limited)
        print(name, early["status"], early["method"],
              f"{early['stage']}/{early['crossings']}", early["euler_stats"], flush=True)
    return output


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--examples", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    args.output.write_text(json.dumps(record(args.examples), indent=2) + "\n")
