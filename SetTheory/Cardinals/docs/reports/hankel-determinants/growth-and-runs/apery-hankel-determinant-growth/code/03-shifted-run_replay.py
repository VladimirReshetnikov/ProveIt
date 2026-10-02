#!/usr/bin/env python3
"""Run the recorded determinants, first correction, and exact checks.

Writes only under --output (default: generated next to this script).
Expected results are read-only. Timings are machine-dependent.
"""

import argparse
from datetime import datetime, timezone
import importlib.metadata
import json
from pathlib import Path
import platform
import subprocess
import sys
import time

import mpmath as mp

from check_shift import evaluate, logdet, sf
from evaluate_c1 import coefficient, corrected_residuals
from verify_c1_log_shift import verify as verify_log_shift
from check_first_correction_trace import verify as verify_trace
from verify_symbolic import verify


ROOT = Path(__file__).resolve().parent
CASES = (("s01", "0.1", 1024), ("s02", "0.2", 1024), ("s1", "1", 512))


def write_json(path, value):
    path.write_text(json.dumps(value, indent=2) + "\n", encoding="utf-8")


def compare(actual, expected):
    """Absolute differences in useful values, ignoring float tail diagnostics."""
    differences = {
        key: abs(actual["constants"][key] - expected["constants"][key])
        for key in ("F", "f0", "f1", "bias", "Q", "E")
    }
    with mp.workdps(40):
        for result, reference in zip(actual["checks"], expected["checks"]):
            if (result["N"], result["r"]) != (reference["N"], reference["r"]):
                raise AssertionError("Mismatched determinant sizes or shifts.")
            for key in ("logratio_minus_NF", "log_relative_error", "N_times_error"):
                differences[f"N={result['N']}:{key}"] = float(
                    abs(mp.mpf(result[key]) - mp.mpf(reference[key])))
    return differences


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=ROOT / "generated")
    parser.add_argument("--stability", action="store_true",
                        help="also double M and compare the N=80 determinant at 320/400 dps")
    args = parser.parse_args()
    args.output.mkdir(parents=True, exist_ok=True)
    started = time.perf_counter()
    report = {
        "started_utc": datetime.now(timezone.utc).isoformat(),
        "python": platform.python_version(),
        "versions": {name: importlib.metadata.version(name)
                     for name in ("mpmath", "numpy", "scipy", "sympy")},
        "status": "finite tests and numerical stability checks, not certification",
        "reference_tolerance": 1e-10,
        "runs": [],
    }
    timer = time.perf_counter()
    result = subprocess.run([sys.executable, "-m", "unittest", "discover", "-s", "tests", "-v"],
                            cwd=ROOT, text=True, capture_output=True, check=False)
    (args.output / "tests.txt").write_text(result.stdout + result.stderr, encoding="utf-8")
    report["tests"] = {"exit_code": result.returncode,
                       "seconds": time.perf_counter() - timer}
    if result.returncode:
        raise RuntimeError("Unit tests failed; see tests.txt in the output directory.")

    timer = time.perf_counter()
    symbolic = verify()
    write_json(args.output / "symbolic_results.json", symbolic)
    write_json(args.output / "first_correction_log_shift.json", verify_log_shift())
    write_json(args.output / "first_correction_trace.json", verify_trace())
    report["symbolic_seconds"] = time.perf_counter() - timer
    numerics = {}
    for suffix, slope, M in CASES:
        timer = time.perf_counter()
        actual = evaluate(slope, M)
        numerics[suffix] = actual
        write_json(args.output / f"numerics_{suffix}.json", actual)
        expected = json.loads((ROOT / "expected" / f"numerics_{suffix}.json").read_text())
        differences = compare(actual, expected)
        largest = max(differences.values())
        if largest > report["reference_tolerance"]:
            raise AssertionError(f"{suffix}: reference difference {largest} exceeds tolerance")
        run = {"case": suffix, "seconds": time.perf_counter() - timer,
               "max_reference_absolute_difference": largest,
               "reference_absolute_differences": differences}
        if args.stability:
            timer = time.perf_counter()
            doubled = sf(slope, 2*M)
            run["doubled_M"] = {"M": 2*M, "seconds": time.perf_counter() - timer,
                                "absolute_differences": {
                                    key: abs(doubled[key] - actual["constants"][key])
                                    for key in ("F", "f0", "bias", "Q", "E")}}
            timer = time.perf_counter()
            N, r = 80, int(mp.mpf(slope) * 80)
            low = logdet(N, r, 320)
            high = logdet(N, r, 400)
            with mp.workdps(420):
                run["determinant_precision"] = {
                    "N": N, "r": r, "decimal_precisions": [320, 400],
                    "absolute_logdet_difference": mp.nstr(abs(high-low), 10),
                    "seconds": time.perf_counter() - timer,
                }
        report["runs"].append(run)
        print(f"{suffix}: reference values agree within {largest:.3g}", flush=True)

    correction_results = {}
    correction_report = {"runs": []}
    for M in (256, 512):
        timer = time.perf_counter()
        value = coefficient("1", M=M)
        filename = f"c1_direct_s1_{M}.json"
        write_json(args.output / filename, value)
        correction_results[M] = value
        expected = json.loads((ROOT / "expected" / filename).read_text())
        with mp.workdps(50):
            differences = {key: float(abs(mp.mpf(value[key])-mp.mpf(expected[key])))
                           for key in ("U_prime", "U_second", "S_prime", "c_rel", "c_full")}
        largest = max(differences.values())
        if largest > report["reference_tolerance"]:
            raise AssertionError(f"first correction M={M}: reference difference {largest}")
        identity_error = abs(float(value["S_prime_identity_residual"]))
        formula_difference = abs(float(value["c_rel_formula_difference"]))
        if identity_error > 1e-12 or formula_difference > 1e-14:
            raise AssertionError("First-correction endpoint identity failed its numerical check.")
        correction_report["runs"].append({
            "nodes": M, "seconds": time.perf_counter()-timer,
            "reference_absolute_differences": differences,
            "max_reference_absolute_difference": largest,
            "absolute_S_prime_identity_residual": identity_error,
            "absolute_c_rel_formula_difference": formula_difference,
        })
        print(f"first correction M={M}: reference values agree within {largest:.3g}", flush=True)
    with mp.workdps(50):
        correction_report["grid_difference_c_rel"] = mp.nstr(abs(
            mp.mpf(correction_results[256]["c_rel"])
            - mp.mpf(correction_results[512]["c_rel"])), 10)
    residuals = corrected_residuals(numerics["s1"], correction_results[256])
    write_json(args.output / "first_correction_residuals_s1.json", residuals)
    expected = json.loads((ROOT / "expected" / "first_correction_residuals_s1.json").read_text())
    with mp.workdps(50):
        largest = max(float(abs(mp.mpf(actual["N_squared_corrected_error"])
                               - mp.mpf(reference["N_squared_corrected_error"])))
                      for actual, reference in zip(residuals["checks"], expected["checks"]))
    if largest > report["reference_tolerance"]:
        raise AssertionError("Corrected residuals failed the reference comparison.")
    correction_report["max_N_squared_residual_reference_difference"] = largest
    report["first_correction"] = correction_report
    report["total_seconds"] = time.perf_counter() - started
    report["result"] = "PASS"
    write_json(args.output / "validation_report.json", report)
    print(f"PASS: total {report['total_seconds']:.2f} seconds; details in {args.output.name}")


if __name__ == "__main__":
    main()
