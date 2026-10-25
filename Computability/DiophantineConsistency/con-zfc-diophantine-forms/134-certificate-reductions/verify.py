#!/usr/bin/env python3
"""Run the independent checks for all three equation families.

Usage (from any working directory):
    python3 -B /path/to/verify.py
    python3 -B -O /path/to/verify.py --rebuild
    python3 -B /path/to/verify.py --rebuild --receipt /tmp/receipt.json

The default mode is read-only.  --rebuild asks the direct and natural checkers
to regenerate their mathematical artifacts in temporary directories and compare
the results byte for byte.  Compact circuit and fixed-coefficient reconstruction
are read-only checks in both modes.  No receipt is written unless --receipt is
explicitly supplied.  Only the Python standard library is required.
"""

import argparse
from datetime import datetime, timezone
import json
from pathlib import Path
import platform
import subprocess
import sys
import time


ROOT = Path(__file__).resolve().parent


def interpreter():
    """Use this interpreter and preserve its assertion/docstring optimization."""
    command = [sys.executable, "-B"]
    if sys.flags.optimize == 1:
        command.append("-O")
    elif sys.flags.optimize >= 2:
        command.append("-OO")
    return command


def checks(rebuild):
    rebuild_args = ["--rebuild"] if rebuild else []
    result = [
        ("direct_independent", "direct/code/check.py", rebuild_args),
        ("direct_equation_text", "direct/code/print_equation.py", ["--check"]),
        ("natural_independent", "natural/verify.py", rebuild_args),
        ("natural_equation_text", "natural/render_equation.py", ["--check"]),
    ]
    result.extend([
        ("natural_arithmetic_controls", "natural/review_arithmetic_controls.py", []),
        ("natural_source_provenance", "natural/provenance/check_pins.py", []),
        ("compact_circuit_reconstruction", "compact/build.py", ["--check"]),
        ("compact_coefficient_reconstruction", "compact/rebuild_coefficients.py", []),
        ("compact_independent", "compact/verify.py", []),
    ])
    return result


def run_check(name, script, arguments):
    argv = interpreter() + [str(ROOT / script)] + arguments
    started = time.perf_counter()
    entry = {
        "name": name,
        "script": script,
        "arguments": arguments,
        "optimization": sys.flags.optimize,
    }
    try:
        completed = subprocess.run(
            argv, cwd=ROOT, text=True, encoding="utf-8", capture_output=True,
            check=False,
        )
    except OSError as exc:
        entry.update(status="FAIL", error=str(exc))
    else:
        entry["returncode"] = completed.returncode
        if completed.stderr:
            entry["stderr"] = completed.stderr
        try:
            result = json.loads(completed.stdout)
        except (json.JSONDecodeError, ValueError) as exc:
            entry.update(
                status="FAIL", error="Checker did not emit one JSON result: " + str(exc),
                stdout=completed.stdout,
            )
        else:
            entry["result"] = result
            passed = completed.returncode == 0
            # Some reconstruction scripts return arrays of verified artifacts.
            # Checkers returning an explicit status must report success as well.
            if isinstance(result, dict):
                if "status" in result and result["status"] != "PASS":
                    passed = False
                if "verified" in result and result["verified"] is not True:
                    passed = False
            entry["status"] = "PASS" if passed else "FAIL"
    entry["seconds"] = round(time.perf_counter() - started, 3)
    return entry


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--rebuild", action="store_true",
        help="regenerate direct and natural artifacts in temporary directories and compare bytes",
    )
    parser.add_argument(
        "--receipt", type=Path,
        help="explicit destination for the same JSON receipt printed to standard output",
    )
    args = parser.parse_args()
    began = time.perf_counter()
    steps = checks(args.rebuild)
    results = []
    for index, (name, script, arguments) in enumerate(steps, 1):
        print("[{}/{}] {}".format(index, len(steps), name), file=sys.stderr, flush=True)
        result = run_check(name, script, arguments)
        results.append(result)
        print(
            "  {} ({:.3f} s)".format(result["status"], result["seconds"]),
            file=sys.stderr, flush=True,
        )
    receipt = {
        "status": "PASS" if all(r["status"] == "PASS" for r in results) else "FAIL",
        "schema": "con-zfc-integration-check-v1",
        "completed_utc": datetime.now(timezone.utc).isoformat(),
        "python": platform.python_version(),
        "optimization": sys.flags.optimize,
        "rebuild": args.rebuild,
        "scope": (
            "Independent finite artifact checks, equation-text round trips, exact circuit "
            "and coefficient reconstruction, arithmetic controls, and optional direct/natural "
            "byte-identical rebuilds. These checks do not constitute a formal proof in ZFC."
        ),
        "seconds": round(time.perf_counter() - began, 3),
        "checks": results,
    }
    output = json.dumps(receipt, indent=2, sort_keys=True) + "\n"
    if args.receipt is not None:
        # The destination is relative to the caller's working directory, not
        # the artifact tree.  Missing parent directories are not created.
        try:
            args.receipt.write_text(output, encoding="utf-8")
        except OSError as exc:
            print("Could not write requested receipt: " + str(exc), file=sys.stderr)
            print(output, end="")
            return 2
    print(output, end="")
    return 0 if receipt["status"] == "PASS" else 1


if __name__ == "__main__":
    sys.exit(main())
