"""Hot-process end-to-end recognition comparison, with native generic Jones.

Timed region: JSON parsing, Diagram conversion/validation, full default
recognition except the selected Jones backend, and JSON result encoding.
Imports, fixture file I/O, CLI argument parsing, and process startup are
excluded.  No early stages are disabled.  Each sample creates a fresh
diagram, including its checked source-braid provenance when supplied.
"""
import argparse
import csv
import hashlib
import json
from pathlib import Path
import platform
import statistics
import sys
import time

from benchmark_potts import median_interval, quantile


def has_jones(value):
    if isinstance(value, dict):
        return "jones" in value or any(has_jones(v) for v in value.values())
    if isinstance(value, list):
        return any(has_jones(v) for v in value)
    return False


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--fast-dir", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--rounds", type=int, default=7)
    args = parser.parse_args()
    if args.rounds < 7:
        parser.error("at least seven rounds are required")
    sys.path.insert(0, str(args.fast_dir.resolve()))
    from fastunknot.diagram import Diagram
    from fastunknot.filters import JONES_A
    from fastunknot.recognize import recognize
    # Import optional modules before warmup.  This explicitly measures a
    # hot process, not a claim about cold one-command startup latency.
    import fastunknot.potts_exact
    import fastunknot.potts_factorized_exact

    cases = [(path.stem, path.read_text())
             for path in sorted((args.fast_dir / "examples").glob("*.json"))]
    for exponent in (5, 7, 11):
        source = {"braid": {"strands": 3, "word": [1, -2] * exponent}}
        cases.append((f"weaving_W3_{exponent}", json.dumps(source)))
    arms = ("matching_A1", "exact_q6", "factored_exact_q6", "matching_A2")
    backend = {"matching_A1": "matching", "matching_A2": "matching",
               "exact_q6": "potts-exact", "factored_exact_q6": "potts-exact-factorized"}
    names = ("diagram.py", "recognize.py", "filters.py", "ordering.py", "planar.py",
             "potts.py", "potts_exact.py", "potts_factorized.py", "potts_factorized_exact.py")
    def hashes():
        return {name: hashlib.sha256((args.fast_dir / "fastunknot" / name).read_bytes()).hexdigest()
                for name in names}
    before = hashes()
    report = dict(schema=1, python=sys.version, platform=platform.platform(),
                  native_generic_JONES_A=JONES_A, rounds=args.rounds,
                  measurement="hot process: JSON parse + Diagram conversion/validation + default recognition + JSON encoding",
                  excluded="imports, file I/O, CLI parsing, process startup",
                  options="all pipeline stages at defaults; only Jones backend differs; exact q=6",
                  source_sha256=before,
                  benchmark_script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                  arm_names=arms, cases=[])
    summary = []
    for number, (name, source_text) in enumerate(cases):
        def invoke(arm):
            start = time.perf_counter_ns()
            diagram = Diagram.from_json(json.loads(source_text))
            result = recognize(diagram, jones_backend=backend[arm], potts_colors=6).to_json()
            encoded = json.dumps(result, indent=1)
            elapsed = time.perf_counter_ns() - start
            return elapsed, result, len(encoded)

        warm = {}
        for arm in arms:
            _, result, _ = invoke(arm)
            warm[arm] = result
        statuses = {result["status"] for result in warm.values()}
        if len(statuses) != 1 or "UNKNOWN" in statuses:
            raise ArithmeticError("incomplete or inconsistent pipeline result: " + name)
        exercised = {arm: has_jones(result["evidence"]) for arm, result in warm.items()}
        samples = []
        for round_number in range(args.rounds):
            shift = (number + round_number) % len(arms)
            sequence = arms[shift:] + arms[:shift]
            values, outcomes = {}, {}
            for arm in sequence:
                elapsed, result, encoded_length = invoke(arm)
                for field in ("status", "method", "input_crossings", "reduced_crossings"):
                    if result[field] != warm[arm][field]:
                        raise ArithmeticError("unstable pipeline method or verdict: " + name)
                if has_jones(result["evidence"]) != exercised[arm]:
                    raise ArithmeticError("unstable backend dispatch: " + name)
                values[arm] = elapsed
                outcomes[arm] = {field: result[field] for field in
                                 ("status", "method", "input_crossings", "reduced_crossings")}
                outcomes[arm]["encoded_bytes"] = encoded_length
            samples.append(dict(round=round_number, sequence=sequence, ns=values, outcomes=outcomes))
        aa = [sample["ns"]["matching_A1"] / sample["ns"]["matching_A2"] for sample in samples]
        comparisons = {}
        for arm in ("exact_q6", "factored_exact_q6"):
            ratios = [sample["ns"]["matching_A1"] / sample["ns"][arm] for sample in samples]
            median, interval = statistics.median(ratios), median_interval(ratios)
            claim = "no_clear_timing_claim"
            if not exercised[arm] and not exercised["matching_A1"]:
                claim = "backend_bypassed_no_backend_speed_claim"
            elif interval[0] > 1 and median > quantile(aa, .75):
                claim = "faster_on_this_input"
            elif interval[1] < 1 and median < quantile(aa, .25):
                claim = "slower_on_this_input"
            comparisons[arm] = dict(median_matching_over_arm=median,
                                    median_ratio_interval_at_least_95pct=interval, claim=claim)
        row = dict(name=name, input=json.loads(source_text), warmup_results=warm,
                   backend_exercised=exercised, samples=samples, comparisons=comparisons,
                   aa_median=statistics.median(aa), aa_iqr=[quantile(aa, .25), quantile(aa, .75)],
                   median_ms={arm: statistics.median([s["ns"][arm] for s in samples]) / 1e6
                              for arm in arms})
        report["cases"].append(row)
        small = dict(name=name, status=warm["matching_A1"]["status"],
                     crossings=warm["matching_A1"]["input_crossings"],
                     backend_exercised=exercised["matching_A1"],
                     matching_method=warm["matching_A1"]["method"])
        for arm, value in comparisons.items():
            small[arm + "_method"] = warm[arm]["method"]
            small[arm + "_matching_ratio"] = value["median_matching_over_arm"]
            small[arm + "_ci_low"], small[arm + "_ci_high"] = value["median_ratio_interval_at_least_95pct"]
            small[arm + "_claim"] = value["claim"]
        for arm, value in row["median_ms"].items():
            small[arm + "_median_ms"] = value
        summary.append(small)
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(report, indent=2) + "\n")
        print(name, warm["matching_A1"]["status"], warm["matching_A1"]["method"],
              "Jones=" + str(exercised["matching_A1"]),
              " ".join(f"{arm}={comparisons[arm]['median_matching_over_arm']:.3f}x"
                       for arm in comparisons), flush=True)
    after = hashes()
    if before != after:
        raise ArithmeticError("pipeline source changed during measurement")
    report.update(complete=True, source_sha256_after=after,
                  total_timed_calls=len(cases) * args.rounds * len(arms),
                  backend_exercised_cases=sum(row["backend_exercised"]["matching_A1"]
                                             for row in report["cases"]))
    args.output.write_text(json.dumps(report, indent=2) + "\n")
    with args.output.with_suffix(".csv").open("w", newline="") as stream:
        writer = csv.DictWriter(stream, fieldnames=list(summary[0]))
        writer.writeheader()
        writer.writerows(summary)


if __name__ == "__main__":
    main()
