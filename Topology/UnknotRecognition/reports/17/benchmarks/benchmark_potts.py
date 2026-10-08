"""Paired Jones-filter kernel measurements with fixed inputs and A/A controls.

Run with --fast-dir /path/to/fast --output /path/to/results.json.
Diagram construction, validation, import, and order search are outside each
timed call.  Every call receives a fresh uncached Diagram object and the
same precomputed crossing order.  These are filter-kernel measurements,
not claims about the full recognition pipeline.
"""
import argparse
import hashlib
import json
import math
from pathlib import Path
import platform
import random
import statistics
import sys
import time


def quantile(values, fraction):
    values = sorted(values)
    position = (len(values) - 1) * fraction
    lo = int(position)
    hi = min(lo + 1, len(values) - 1)
    return values[lo] + (position - lo) * (values[hi] - values[lo])


def median_interval(values):
    ordered = sorted(values)
    n = len(ordered)
    tail = 0
    rank = 0
    for candidate in range(1, (n + 1) // 2 + 1):
        tail += math.comb(n, candidate - 1) / 2 ** n
        if tail <= 0.025:
            rank = candidate
        else:
            break
    return [ordered[rank - 1], ordered[n - rank]] if rank else [ordered[0], ordered[-1]]


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--fast-dir", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--rounds", type=int, default=15)
    args = parser.parse_args()
    if args.rounds < 7:
        parser.error("at least seven rounds are required")
    sys.path.insert(0, str(args.fast_dir.resolve()))
    from fastunknot.diagram import Diagram, DiagramError
    from fastunknot import filters
    from fastunknot.ordering import best_scan_order, order_profile
    from fastunknot.potts import POTTS_A, potts_bracket
    from fastunknot.potts_exact import potts_exact
    from fastunknot.potts_factorized import factorized_potts_bracket
    from fastunknot.potts_factorized_exact import factorized_potts_exact

    cases = []
    for path in sorted((args.fast_dir / "examples").glob("*.json")):
        source = json.loads(path.read_text())
        diagram = Diagram.from_json(source)
        order = best_scan_order(diagram.pd, tries=min(max(1, diagram.crossings), 12))
        cases.append((path.stem, "named_greedy", source, diagram, order))
    rng = random.Random(764259)
    accepted = 0
    while accepted < 12:
        word = [rng.choice((-1, 1)) * rng.randrange(1, 5) for _ in range(16)]
        try:
            diagram = Diagram.from_braid(5, word)
        except DiagramError:
            continue
        accepted += 1
        order = list(range(16))
        rng.shuffle(order)
        source = {"braid": {"strands": 5, "word": word}}
        cases.append((f"random_order_{accepted:02}", "first12_seed764259", source, diagram, order))
    for exponent in (5, 7, 11):
        source = {"braid": {"strands": 3, "word": [1, -2] * exponent}}
        diagram = Diagram.from_json(source)
        order = best_scan_order(diagram.pd, tries=min(diagram.crossings, 12))
        cases.append((f"weaving_W3_{exponent}", "q5_collision_control", source, diagram, order))

    original_a = filters.JONES_A
    diagnostics = {}
    for name, _, _, diagram, order in cases:
        result = filters.jones_obstruction(Diagram(diagram.pd), order=order,
                                           max_states=50000, max_transitions=2_000_000)
        diagnostics[name] = dict(original_generic_jones_detects=result is not None)
    filters.JONES_A = POTTS_A
    arm_names = ("matching_A1", "mod_q5", "factored_mod_q5", "exact_q5", "exact_q6",
                 "factored_exact_q6", "matching_A2")
    source_names = ("diagram.py", "filters.py", "ordering.py", "planar.py", "potts.py",
                    "potts_exact.py", "potts_factorized.py", "potts_factorized_exact.py")
    def source_hashes():
        return {name: hashlib.sha256((args.fast_dir / "fastunknot" / name).read_bytes()).hexdigest()
                for name in source_names}
    before_hashes = source_hashes()
    report = dict(schema=1, python=sys.version, platform=platform.platform(),
                  rounds=args.rounds, arm_names=arm_names,
                  measurement="supplied-order fresh-uncached-Diagram filter call; excludes validation, order selection, import",
                  comparison="matching and modular q5 arms use identical A; exact q6 is a different specialization",
                  random_control_seed=764259, source_sha256=before_hashes,
                  benchmark_script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                  cases=[])
    for number, (name, corpus, source, diagram, order) in enumerate(cases):
        def invoke(arm):
            fresh = Diagram(diagram.pd)
            options = dict(order=order, max_states=50000, max_transitions=2_000_000)
            start = time.perf_counter_ns()
            if arm.startswith("matching"):
                value = filters.jones_obstruction(fresh, **options)
            elif arm == "mod_q5":
                value = potts_bracket(fresh, **options)
            elif arm == "factored_mod_q5":
                value = factorized_potts_bracket(fresh, **options)
            elif arm == "factored_exact_q6":
                value = factorized_potts_exact(fresh, colors=6, **options)
            else:
                value = potts_exact(fresh, colors=5 if arm == "exact_q5" else 6, **options)
            elapsed = time.perf_counter_ns() - start
            return elapsed, value

        counters = {}
        for arm in arm_names:
            _, counters[arm] = invoke(arm)
        expected_modular = counters["mod_q5"]["bracket"]
        matching_value = counters["matching_A1"]
        recovered_matching = (matching_value["bracket"] if matching_value is not None
                              else counters["mod_q5"]["unknot_bracket"])
        if (recovered_matching != expected_modular
                or counters["factored_mod_q5"]["bracket"] != expected_modular):
            raise ArithmeticError("same-specialization disagreement in " + name)
        if (counters["exact_q6"]["partition_function"]
                != counters["factored_exact_q6"]["partition_function"]):
            raise ArithmeticError("exact q6 factorization disagreement in " + name)
        timings = []
        for round_number in range(args.rounds):
            shift = (number + round_number) % len(arm_names)
            sequence = arm_names[shift:] + arm_names[:shift]
            samples = {}
            for arm in sequence:
                elapsed, value = invoke(arm)
                if value != counters[arm]:
                    raise ArithmeticError("nondeterministic result in " + name + "/" + arm)
                samples[arm] = elapsed
            timings.append(dict(round=round_number, sequence=sequence, ns=samples))
        aa = [row["ns"]["matching_A1"] / row["ns"]["matching_A2"] for row in timings]
        comparisons = {}
        for arm in arm_names[1:-1]:
            ratios = [row["ns"]["matching_A1"] / row["ns"][arm] for row in timings]
            median, interval = statistics.median(ratios), median_interval(ratios)
            label = "no_clear_timing_claim"
            if interval[0] > 1 and median > quantile(aa, 0.75):
                label = "faster_on_this_input"
            elif interval[1] < 1 and median < quantile(aa, 0.25):
                label = "slower_on_this_input"
            comparisons[arm] = dict(median_matching_over_arm=median,
                                    median_ratio_interval_at_least_95pct=interval,
                                    claim=label)
        row = dict(name=name, corpus=corpus, input=source, order=order,
                   crossings=diagram.crossings, boundary_profile=order_profile(diagram.pd, order),
                   diagnostics=diagnostics[name], counters=counters, samples=timings,
                   median_ms={arm: statistics.median([r["ns"][arm] for r in timings]) / 1e6
                              for arm in arm_names},
                   aa_median=statistics.median(aa), aa_iqr=[quantile(aa, .25), quantile(aa, .75)],
                   comparisons=comparisons)
        report["cases"].append(row)
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(report, indent=2) + "\n")
        print(name, " ".join(f"{arm}={comparisons[arm]['median_matching_over_arm']:.3f}x"
                             for arm in comparisons), flush=True)
    filters.JONES_A = original_a
    after_hashes = source_hashes()
    if before_hashes != after_hashes:
        raise ArithmeticError("measured source files changed during the benchmark")
    report["source_sha256_after"] = after_hashes
    report["complete"] = True
    report["total_timed_calls"] = len(cases) * args.rounds * len(arm_names)
    args.output.write_text(json.dumps(report, indent=2) + "\n")


if __name__ == "__main__":
    main()
