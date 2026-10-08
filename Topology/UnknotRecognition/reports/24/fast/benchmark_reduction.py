"""Compare recognition against a revision before the post-reduction certificate.

Only recognize.py is loaded from the baseline revision; every other module is
shared, isolating stage placement. Input validation is outside the timing.
"""
import argparse
import json
from pathlib import Path
import platform
import random
import statistics
import subprocess
from time import perf_counter
from types import ModuleType

from fastunknot import Diagram, recognize


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--baseline", default="1323898c3")
    parser.add_argument("--rounds", type=int, default=9)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if args.rounds < 1:
        parser.error("rounds must be positive")
    here = Path(__file__).resolve().parent
    revision = subprocess.check_output(
        ["git", "rev-parse", "--verify", args.baseline + "^{commit}"], cwd=here, text=True).strip()
    source = subprocess.check_output(
        ["git", "show", revision + ":Topology/UnknotRecognition/fast/fastunknot/recognize.py"],
        cwd=here, text=True)
    baseline = ModuleType("fastunknot._benchmark_baseline")
    baseline.__package__ = "fastunknot"
    exec(compile(source, f"{revision}:recognize.py", "exec"), baseline.__dict__)
    cases = [(f"padded_weaving_{2*m}", Diagram.from_braid(3, [1, -2] * m + [2, -2, -1, 1]))
             for m in (5, 50, 500)]
    for name in ("conway", "hard_unknot_8", "grid_scrambled_unknot"):
        cases.append((name, Diagram.from_json(json.loads(
            (here / "examples" / (name + ".json")).read_text()))))
    rng = random.Random(2026100710)
    rows = []
    for name, diagram in cases:
        samples = []
        for _ in range(args.rounds):
            arms = ["old", "control", "new"]
            rng.shuffle(arms)
            sample = {"execution_order": arms}
            statuses = []
            for arm in arms:
                call = recognize if arm == "new" else baseline.recognize
                start = perf_counter()
                for _ in range(5):
                    result = call(Diagram(diagram.pd))
                    statuses.append(result.status)
                sample[arm] = (perf_counter() - start) / 5
                sample[arm + "_method"] = result.method
            assert len(set(statuses)) == 1
            sample["status"] = statuses[0]
            samples.append(sample)
        row = dict(name=name, crossings=diagram.crossings, samples=samples,
                   median_speedup=statistics.median(s["old"] / s["new"] for s in samples),
                   median_aa=statistics.median(s["old"] / s["control"] for s in samples))
        rows.append(row)
        print(f'{name}: {row["median_speedup"]:.2f}x, A/A {row["median_aa"]:.3f}', flush=True)
    report = dict(baseline_revision=revision, baseline_scope="recognize.py only; shared other modules",
                  python=platform.python_version(), platform=platform.platform(), seed=2026100710,
                  rounds=args.rounds, timing_boundary="five fresh validated-Diagram recognition calls per arm",
                  speedup_definition="median paired old/new; greater than one is faster", cases=rows)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2) + "\n")


if __name__ == "__main__":
    main()

