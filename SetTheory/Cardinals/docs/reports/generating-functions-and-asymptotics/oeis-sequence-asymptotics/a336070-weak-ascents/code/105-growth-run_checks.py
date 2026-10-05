#!/usr/bin/env python3
"""Run the complete exact suite and corruption tests, normally and with -O.

From the report directory:
    python3 code/run_checks.py
    python3 code/run_checks.py --output code/exact_check_results.json
The JSON summary is printed to stdout and optionally saved. Floating-point
sanity checks are intentionally NOT called by this exact-suite runner.
"""
import argparse
import ast
import copy
import json
from pathlib import Path
import subprocess
import sys
import tempfile
from time import monotonic_ns

from exact_models import CheckFailure, require


def invoke(command):
    completed = subprocess.run(command, capture_output=True, text=True, timeout=180)
    output = completed.stdout if completed.returncode == 0 else completed.stderr
    try:
        parsed = json.loads(output)
    except (ValueError, TypeError) as error:
        raise CheckFailure("verifier did not return one JSON result: " + output[:400]) from error
    return completed, parsed


def check_sources(code):
    checked = []
    for path in sorted(code.glob("*.py")):
        tree = ast.parse(path.read_text(encoding="utf-8"), filename=str(path))
        require(not any(isinstance(node, ast.Assert) for node in ast.walk(tree)),
                "optimization-dependent check in " + path.name)
        checked.append(path.name)
    return checked


def make_fixtures(base_certificate, base_terms, directory):
    fixtures = []
    def store(name, value, error_fragment):
        path = directory / (name + ".json")
        path.write_text(json.dumps(value) + "\n", encoding="ascii")
        fixtures.append((name, path, base_terms, error_fragment))

    broken = directory / "malformed_json.json"
    broken.write_text('{"schema":', encoding="ascii")
    fixtures.append(("malformed_json", broken, base_terms, "Expecting value"))

    certificate = json.loads(base_certificate.read_text(encoding="ascii"))
    bad = copy.deepcopy(certificate)
    bad["poisson_cases"].pop()
    store("missing_case", bad, "missing or extra cases")

    bad = copy.deepcopy(certificate)
    bad["poisson_cases"][1]["c_over_q"] = "1"
    store("altered_rational_claim", bad, "value mismatch")

    bad = copy.deepcopy(certificate)
    bad["frozen_cases"].append(copy.deepcopy(bad["frozen_cases"][0]))
    store("extra_case", bad, "missing or extra cases")

    duplicate = directory / "duplicate_key.json"
    duplicate.write_text('{"schema":"duplicated",' + json.dumps(certificate)[1:] + "\n", encoding="ascii")
    fixtures.append(("duplicate_json_key", duplicate, base_terms, "duplicate JSON key"))

    bad = copy.deepcopy(certificate)
    bad["inventory"]["positive_recurrence_lengths"][0] = False
    store("wrong_json_type", bad, "wrong JSON type")

    bad_terms = directory / "altered_terms.txt"
    lines = base_terms.read_text(encoding="ascii").splitlines()
    index, value = lines[-1].split()
    lines[-1] = index + " " + str(int(value) + 1)
    bad_terms.write_text("\n".join(lines) + "\n", encoding="ascii")
    fixtures.append(("altered_stored_term", base_certificate, bad_terms, "terms.sha256: value mismatch"))
    return fixtures


def run(root):
    code = root / "code"
    verifier = code / "verify_exact.py"
    certificate = root / "data" / "exact_certificate.json"
    terms = root / "data" / "weak_ascent_terms.txt"
    summary = {"status": "passed", "scope": "Finite exact checks only; not analytic proofs.",
        "source_files_checked_for_optimization_safety": check_sources(code), "runs": []}
    with tempfile.TemporaryDirectory(prefix="report105-exact-") as temp:
        fixtures = make_fixtures(certificate, terms, Path(temp))
        for optimize in (False, True):
            prefix = [sys.executable] + (["-O"] if optimize else []) + [str(verifier)]
            start = monotonic_ns()
            completed, result = invoke(prefix)
            require(completed.returncode == 0 and result.get("status") == "passed",
                    "normal exact run failed: " + completed.stderr)
            require(result.get("python_optimization") == int(optimize), "wrong optimization mode")
            require(completed.stderr == "", "successful verifier emitted stderr")
            run_result = {"mode": "optimized" if optimize else "normal",
                "elapsed_nanoseconds": monotonic_ns() - start, "exact_checks": result,
                "corruption_checks": []}
            for name, fixture_certificate, fixture_terms, expected_error in fixtures:
                completed, result = invoke(prefix + ["--certificate", str(fixture_certificate),
                                                    "--terms", str(fixture_terms)])
                require(completed.returncode == 1 and result.get("status") == "failed",
                        "corruption was not rejected: " + name)
                require(result.get("phase") == "preflight", "corruption reached expensive checks: " + name)
                require(expected_error in result.get("error", ""), "unexpected rejection reason: " + name)
                require(completed.stdout == "", "failed verifier emitted a success-channel message")
                run_result["corruption_checks"].append({"category": name, "status": "rejected",
                    "phase": result["phase"], "reason": result["error"]})
            summary["runs"].append(run_result)
    normal = dict(summary["runs"][0]["exact_checks"])
    optimized = dict(summary["runs"][1]["exact_checks"])
    normal.pop("python_optimization")
    optimized.pop("python_optimization")
    require(normal == optimized, "normal and optimized mathematical results differ")
    summary["matching_exact_results_across_modes"] = True
    summary["full_regenerations"] = 2
    summary["rejected_corruptions"] = sum(len(run["corruption_checks"]) for run in summary["runs"])
    return summary


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    try:
        result = run(Path(__file__).resolve().parents[1])
        encoded = json.dumps(result, sort_keys=True, indent=2) + "\n"
        if args.output:
            args.output.write_text(encoded, encoding="ascii")
    except Exception as error:
        print(json.dumps({"status": "failed", "error_type": type(error).__name__, "error": str(error)}), file=sys.stderr)
        return 1
    print(encoded, end="")
    return 0


if __name__ == "__main__":
    sys.exit(main())
