#!/usr/bin/env python3
"""Reproduce the independent symbolic and numerical checks.

Usage, from any current directory:
    python /path/to/package/code/run_independent.py --quick
    python /path/to/package/code/run_independent.py

The default full run keeps the original working precisions: 90 decimal
digits for parity and audit quadrature, 100 for one-2 words, and 60 for
the four mixed rows. Numerical quadrature is not interval certification.
The separate core certificate replay is provided by replay_certificates.py.

Original verified outputs are preserved in results/independent/*/reference/.
This runner only regenerates files in results/independent/ and never changes
the article, its sections, or the core certificate code/results.
"""

from __future__ import annotations

import argparse
from collections import Counter
from dataclasses import dataclass
from datetime import datetime, timezone
from decimal import Decimal
import json
from pathlib import Path
import subprocess
import sys
import time


PACKAGE_ROOT = Path(__file__).resolve().parents[1]
SCRIPT_ROOT = PACKAGE_ROOT / "code" / "independent"
RESULT_ROOT = PACKAGE_ROOT / "results" / "independent"


def require(condition, message):
    if not condition:
        raise AssertionError(message)


def small(value, tolerance):
    number = Decimal(str(value))
    require(number.is_finite(), f"Nonfinite residual: {value}")
    require(abs(number) < Decimal(tolerance),
            f"Residual {value} does not satisfy < {tolerance}")


def parity_pairs():
    return {(weight-b, b) for weight in (6, 8) for b in range(1, weight)}


def one_two_keys():
    return {(tuple([1]*a + [2] + [1]*(n-a-2)), component)
            for n in (4, 5, 6) for a in range(n-1)
            for component in ("real", "imag")}


def validate_parity_symbolic(data):
    require(data["exact_identity_checks"] == 12, "Expected 12 exact parity identities")
    require(data["complex_real_consistency_checks"] == 100,
            "Expected 100 complex/real formula comparisons")
    require(len(data["records"]) == 12, "Expected 12 parity coefficient rows")
    require({(r["a"], r["b"]) for r in data["records"]} == parity_pairs(),
            "Parity coefficient indices differ from the required set")
    return {"parity_rows": 12, "general_formula_comparisons": 100}


def validate_one_two_symbolic(data):
    require(len(data["rows"]) == 24, "Expected all 24 one-2 component rows")
    require({(tuple(r["indices"]), r["component"]) for r in data["rows"]}
            == one_two_keys(), "One-2 coefficient rows differ from the required set")
    weights = data["assigned_weights"]
    for row in data["rows"]:
        for term in row["terms"]:
            require(isinstance(term["numerator"], int), "Noninteger numerator")
            require(isinstance(term["denominator"], int) and term["denominator"] > 0,
                    "Invalid rational denominator")
            require(sum(weights[name]*power for name, power in term["powers"].items())
                    == row["weight"], "Incorrect assigned weight in coefficient table")
    return {"one_two_component_rows": 24}


def validate_mixed_symbolic(data):
    require(data["symbolic_identity_checks"] == 4, "Expected four mixed symbolic identities")
    rows = data["symbolic_checks"]
    require(len(rows) == 4, "Expected four mixed symbolic rows")
    require({(r["tower"], r["a"], r["b"]) for r in rows}
            == {(tower, a, 1) for tower in ("Gaussian", "Eisenstein") for a in (4, 5)},
            "Mixed symbolic indices differ from the required set")
    require(all(r["exact_difference"] == "0" for r in rows),
            "A mixed symbolic difference is nonzero")
    return {"mixed_symbolic_rows": 4}


def validate_exact_audit(data):
    require(data["exact_uniform_radius_checks"] == 160,
            "Expected 160 exact rational radius checks")
    return {"exact_rational_radius_cases": 160}


def validate_parity_numeric(data):
    require(data["mpmath_dps"] >= 90, "Parity precision was lowered")
    rows = data["checks"]
    require(len(rows) == 12 and {(r["a"], r["b"]) for r in rows} == parity_pairs(),
            "Expected all 12 parity quadrature rows")
    for row in rows:
        small(row["absolute_residual"], "1e-83")
    return {"parity_quadrature_rows": 12, "working_decimal_digits": data["mpmath_dps"]}


def validate_mixed_numeric(data):
    validate_mixed_symbolic(data)
    require(data["mpmath_dps"] >= 60, "Mixed-row precision was lowered")
    rows = data["numerical_checks"]
    require(len(rows) == 4, "Expected all four mixed quadrature rows")
    require({(r["tower"], r["a"], r["b"]) for r in rows}
            == {(tower, a, 1) for tower in ("Gaussian", "Eisenstein") for a in (4, 5)},
            "Mixed numerical indices differ from the required set")
    for row in rows:
        small(row["absolute_residual"], "1e-55")
    return {"mixed_quadrature_rows": 4, "working_decimal_digits": data["mpmath_dps"]}


def validate_one_two_extended(data):
    require(data["working_decimal_digits"] >= 100, "One-2 precision was lowered")
    rows = data["records"]
    require(len(rows) == 112, "Expected all 112 one-2 logarithmic moment comparisons")
    wanted = {(point, n, a, n-a-2)
              for point in ("gaussian", "eisenstein", "disk", "negative")
              for n in range(2, 9) for a in range(n-1)}
    require({(r["point"], r["weight"], r["a"], r["b"]) for r in rows} == wanted,
            "One-2 broad-check endpoints or indices differ from the required set")
    for row in rows:
        small(row["quadrature_residual"], "1e-96")
        if "series_residual" in row:
            small(row["series_residual"], "1e-96")
    series_count = sum("series_residual" in row for row in rows)
    require(series_count == 30, "Expected 30 direct nested-series comparisons")
    require(len(data["explicit_rows"]) == 5, "Expected five separately transcribed identities")
    for row in data["explicit_rows"]:
        small(row["residual"], "1e-96")
    return {"logarithmic_moment_comparisons": 112, "direct_nested_series_comparisons": 30,
            "explicit_formula_comparisons": 5, "working_decimal_digits": 100}


def validate_one_two_coefficients(data):
    require(data["working_decimal_digits"] >= 100, "One-2 coefficient precision was lowered")
    rows = data["rows"]
    require(len(rows) == 24, "Expected all 24 exported polynomial components")
    require({(tuple(r["indices"]), r["component"]) for r in rows} == one_two_keys(),
            "The exported coefficient checks are incomplete")
    for row in rows:
        small(row["residual"], "1e-96")
    small(data["maximum_residual"], "1e-96")
    return {"independent_real_imaginary_component_checks": 24, "working_decimal_digits": 100}


def validate_audit_numeric(data):
    validate_exact_audit(data)
    require(data["precision_decimal_digits"] >= 90, "Audit precision was lowered")
    rows = data["digamma_component_checks"]
    require(len(rows) == 15, "Expected 15 digamma component checks")
    require(Counter(row["m"] for row in rows) == Counter({m: 3 for m in range(5)}),
            "Audit derivative orders are incomplete")
    for row in rows:
        small(row["residual"], "1e-80")
    mixed = data["mixed_diagonal_antisymmetry"]
    small(mixed["residual"], "1e-80")
    # Decimal subtraction uses only the printed 82-digit values; allow the
    # original audit's 80-digit threshold, unchanged.
    small(Decimal(mixed["positive_integral"])-Decimal(mixed["closed_form"]), "1e-80")
    small(data["Li33_diagonal"]["residual_modulus"], "1e-80")
    return {"digamma_component_checks": 15, "exact_rational_radius_cases": 160,
            "other_scalar_or_complex_identity_checks": 3, "working_decimal_digits": 90}


@dataclass
class Job:
    name: str
    category: str
    script: str
    arguments: list[str]
    output: Path | None = None
    validator: object = None


def build_jobs(quick):
    parity = RESULT_ROOT / "parity"
    one_two = RESULT_ROOT / "one_two"
    audit = RESULT_ROOT / "audit"
    jobs = [
        Job("weight6_ode_derivation", "parity", "derive.py", []),
        Job("weight8_ode_derivation", "parity", "extend_weight8.py", []),
        Job("parity_symbolic_comparison", "parity", "gaussian_parity.py",
            ["--output", str(parity / "gaussian_coefficients.json")],
            parity / "gaussian_coefficients.json", validate_parity_symbolic),
        Job("one_two_coefficient_derivation", "one_two", "derive_rows.py",
            ["--outdir", str(one_two)], one_two / "coefficients.json", validate_one_two_symbolic),
        Job("mixed_symbolic_derivation", "parity", "mixed_candidates.py",
            ["--symbolic-only", "--output", str(parity / "mixed_symbolic_checks.json")],
            parity / "mixed_symbolic_checks.json", validate_mixed_symbolic),
        Job("audit_exact_radius_checks", "audit", "verify_corrections.py",
            ["--exact-only", "--output", str(audit / "exact_radius_checks.json")],
            audit / "exact_radius_checks.json", validate_exact_audit),
    ]
    if not quick:
        jobs += [
            Job("parity_quadrature", "parity", "check_quadrature.py",
                ["--output", str(parity / "quadrature_checks.json")],
                parity / "quadrature_checks.json", validate_parity_numeric),
            Job("mixed_quadrature", "parity", "mixed_candidates.py",
                ["--output", str(parity / "mixed_checks.json")],
                parity / "mixed_checks.json", validate_mixed_numeric),
            Job("one_two_broad_quadrature", "one_two", "one_two_identities.py",
                ["--digits", "100", "--output", str(one_two / "verification.json")],
                one_two / "verification.json", validate_one_two_extended),
            Job("one_two_exported_coefficients", "one_two", "verify_coefficients.py",
                ["--coefficients", str(one_two / "coefficients.json"),
                 "--output", str(one_two / "coefficient_verification.json")],
                one_two / "coefficient_verification.json", validate_one_two_coefficients),
            Job("audit_numerical_checks", "audit", "verify_corrections.py",
                ["--output", str(audit / "correction_checks.json")],
                audit / "correction_checks.json", validate_audit_numeric),
        ]
    return jobs


def main():
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--quick", action="store_true",
                        help="run symbolic derivations and exact rational checks only")
    args = parser.parse_args()
    RESULT_ROOT.mkdir(parents=True, exist_ok=True)
    mode = "quick" if args.quick else "full"
    summary_path = RESULT_ROOT / f"runner_{mode}_summary.json"
    started = time.perf_counter()
    summary = {"mode": mode, "started_utc": datetime.now(timezone.utc).isoformat(),
               "status": "running", "jobs": [],
               "interpretation": "Symbolic identities and rational bounds are exact; "
                                 "quadrature residuals are independent numerical cross-checks."}
    try:
        for job in build_jobs(args.quick):
            script = SCRIPT_ROOT / job.category / job.script
            log_path = RESULT_ROOT / job.category / "logs" / f"{job.name}.log"
            log_path.parent.mkdir(parents=True, exist_ok=True)
            command = [sys.executable, "-B", str(script)] + job.arguments
            previous_mtime = (job.output.stat().st_mtime_ns
                              if job.output and job.output.exists() else None)
            print(f"Running {job.name} ...", flush=True)
            tick = time.perf_counter()
            completed = subprocess.run(command, cwd=PACKAGE_ROOT, text=True,
                                       stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                                       timeout=1800, check=False)
            elapsed = time.perf_counter() - tick
            log_path.write_text(completed.stdout, encoding="utf-8")
            record = {"name": job.name, "category": job.category,
                      "script": str(script.relative_to(PACKAGE_ROOT)),
                      "exit_code": completed.returncode, "duration_seconds": round(elapsed, 3),
                      "log": str(log_path.relative_to(PACKAGE_ROOT))}
            summary["jobs"].append(record)
            require(completed.returncode == 0,
                    f"{job.name} exited {completed.returncode}; see {log_path}")
            if job.output:
                require(job.output.exists(), f"{job.name} did not create {job.output}")
                require(previous_mtime is None or job.output.stat().st_mtime_ns != previous_mtime,
                        f"{job.name} left its output unchanged; refusing to validate a stale file")
                record["output"] = str(job.output.relative_to(PACKAGE_ROOT))
                record["validated_counts"] = job.validator(json.loads(job.output.read_text()))
            record["status"] = "passed"
            print(f"Passed {job.name} ({elapsed:.2f} s)", flush=True)
            summary_path.write_text(json.dumps(summary, indent=2) + "\n")
        summary["status"] = "passed"
    except Exception as error:
        summary["status"] = "failed"
        summary["error"] = f"{type(error).__name__}: {error}"
        print(summary["error"], file=sys.stderr, flush=True)
    finally:
        summary["duration_seconds"] = round(time.perf_counter() - started, 3)
        summary["finished_utc"] = datetime.now(timezone.utc).isoformat()
        summary_path.write_text(json.dumps(summary, indent=2) + "\n")
    print(f"{summary['status'].upper()}: {len(summary['jobs'])} jobs, "
          f"{summary['duration_seconds']:.2f} s; {summary_path}", flush=True)
    return 0 if summary["status"] == "passed" else 1


if __name__ == "__main__":
    raise SystemExit(main())
