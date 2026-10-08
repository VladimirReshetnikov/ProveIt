"""Raw twist/scanner comparison, distinct from default unknot recognition.

Input diagrams are prepared once. Timings include order selection for the
scanner and exact size preflight for the twist adapter. Every arm starts a
fresh computation; ranks and every original cube degree must agree. Most
cases have earlier recognition certificates, so gains here are homology gains.
"""
import argparse
import json
from pathlib import Path
import platform
import random
import statistics
from time import perf_counter

from fastunknot import Diagram, khovanov_rank, recognize
from fastunknot.twist import Budget
from fastunknot.twist_adapter import twist_khovanov_rank


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--rounds", type=int, default=7)
    parser.add_argument("--context-only", action="store_true",
                        help="measure the long four-strand context at 201 and 801 repeated letters")
    args = parser.parse_args()
    rng = random.Random(2026100718)
    cases = [(f"two_strand_{n}", 2, [1]*n) for n in (51, 201, 801)]
    cases += [(f"mixed_four_strand_{n}", 4, [1]*n+[2, -3, 2, 3, 1, -2]) for n in (3, 15, 51)]
    cases += [("alternating_no_compression", 3, [1, -2]*4),
              ("morton_four_strand", 4, [-3, -3, 2, -3, 2, 1, 1, 1, -2, 1, -2])]
    if args.context_only:
        cases = [(f"mixed_four_strand_{n}", 4, [1]*n+[2, -3, 2, 3, 1, -2]) for n in (201, 801)]
    rows = []
    for name, strands, word in cases:
        diagram = Diagram.from_braid(strands, word)
        samples, metrics = [], {}
        # Warm imports and verify before collecting times.
        base = khovanov_rank(diagram.pd, seconds=30)
        macro = twist_khovanov_rank(diagram, budget=Budget(seconds=30))
        assert macro["by_degree"] == base["by_degree"], name
        for _ in range(args.rounds):
            arms = ["scanner", "control", "twist"]
            rng.shuffle(arms)
            sample = {"order": arms}
            for arm in arms:
                started = perf_counter()
                if arm == "twist":
                    result = twist_khovanov_rank(diagram, budget=Budget(seconds=30))
                else:
                    result = khovanov_rank(diagram.pd, seconds=30)
                sample[arm] = perf_counter() - started
                assert result["rank"] == base["rank"] and result["by_degree"] == base["by_degree"], name
                metrics[arm] = result
            samples.append(sample)
        default = recognize(diagram)
        row = dict(name=name, strands=strands, word=word, crossings=len(word), samples=samples,
                   median_speedup=statistics.median(s["scanner"]/s["twist"] for s in samples),
                   median_aa=statistics.median(s["scanner"]/s["control"] for s in samples),
                   scanner=metrics["scanner"], twist=metrics["twist"], default_recognition_method=default.method)
        rows.append(row)
        print(name, round(row["median_speedup"], 3), round(row["median_aa"], 3),
              row["twist"]["stats"]["basis"], row["twist"]["stats"]["peak_chain_dimension"],
              default.method, flush=True)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(dict(python=platform.python_version(), seed=2026100718,
        rounds=args.rounds, context_only=args.context_only, timing_scope=__doc__, cases=rows), indent=2)+"\n")


if __name__ == "__main__":
    main()

