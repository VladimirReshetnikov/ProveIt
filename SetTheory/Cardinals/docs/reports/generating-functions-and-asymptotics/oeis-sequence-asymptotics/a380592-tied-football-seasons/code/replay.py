#!/usr/bin/env python3
"""Recompute all verification results and compare them with frozen fixtures.

Run from any working directory with Python 3.10+ and requirements.txt installed.
No network access, TeX installation, or document build is needed. Expected
fixtures are never updated. Generated JSON goes to replay_outputs/ by default;
--output-dir selects another directory without changing any source or fixture.

Integers, rational/polynomial strings, decimal strings, and JSON structure
must match exactly. Binary floating-point diagnostics use relative tolerance
5e-13 and zero absolute tolerance to accommodate platform libm differences.
"""

import argparse
import json
import math
import os
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
sys.dont_write_bytecode = True
sys.path.insert(0, str(ROOT / "code"))
from output_support import OUTPUT_ENVIRONMENT_VARIABLE, output_directory

CHECKS = (
    "leading_term_checks",
    "symbolic_identity_checks",
    "first_correction_checks",
    "cumulant_filtration_checks",
    "finite_n_gaussian_checks",
    "independent_ibp_checks",
    "residue_constants_checks",
)
FLOAT_RELATIVE_TOLERANCE = 5e-13


def compare(expected, actual, path="$", differences=None):
    """Return human-readable discrepancies; never coerce exact values."""
    if differences is None:
        differences = []
    if type(expected) is not type(actual):
        differences.append(f"{path}: type {type(actual).__name__}, expected {type(expected).__name__}")
    elif isinstance(expected, dict):
        missing = expected.keys() - actual.keys()
        extra = actual.keys() - expected.keys()
        if missing:
            differences.append(f"{path}: missing keys {sorted(missing)}")
        if extra:
            differences.append(f"{path}: unexpected keys {sorted(extra)}")
        for key in sorted(expected.keys() & actual.keys()):
            compare(expected[key], actual[key], f"{path}.{key}", differences)
    elif isinstance(expected, list):
        if len(expected) != len(actual):
            differences.append(f"{path}: length {len(actual)}, expected {len(expected)}")
        for index, (left, right) in enumerate(zip(expected, actual)):
            compare(left, right, f"{path}[{index}]", differences)
    elif isinstance(expected, float):
        if not (
            math.isfinite(expected) and math.isfinite(actual)
            and math.isclose(expected, actual, rel_tol=FLOAT_RELATIVE_TOLERANCE, abs_tol=0.0)
        ):
            differences.append(f"{path}: {actual!r}, expected {expected!r}")
    elif expected != actual:
        differences.append(f"{path}: {actual!r}, expected {expected!r}")
    return differences


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--output-dir", type=Path, default=ROOT / "replay_outputs",
        help="Directory for generated results (default: package-local replay_outputs)",
    )
    arguments = parser.parse_args(argv)
    try:
        directory = output_directory(arguments.output_dir)
        directory.mkdir(parents=True, exist_ok=True)
        directory = output_directory(directory)
    except (OSError, RuntimeError, ValueError) as error:
        print(f"FAIL: unsafe or unavailable output directory: {error}", file=sys.stderr)
        return 1
    if sys.version_info < (3, 10):
        print("FAIL: Python 3.10 or newer is required", file=sys.stderr)
        return 1
    try:
        import sympy
    except ImportError:
        print("FAIL: install dependencies with python -m pip install -r requirements.txt", file=sys.stderr)
        return 1
    print(f"Python {sys.version.split()[0]}; SymPy {sympy.__version__}", flush=True)
    if sympy.__version__ != "1.14.0":
        print("Note: fixtures were verified with the pinned SymPy 1.14.0", flush=True)
    environment = os.environ.copy()
    environment.pop("PYTHONOPTIMIZE", None)
    environment["PYTHONHASHSEED"] = "0"
    environment["PYTHONIOENCODING"] = "utf-8"
    environment[OUTPUT_ENVIRONMENT_VARIABLE] = str(directory)
    failures = []
    for name in CHECKS:
        print(f"RUN  {name}", flush=True)
        expected_path = ROOT / "expected" / f"{name}.json"
        actual_path = directory / f"{name}.json"
        try:
            expected_bytes = expected_path.read_bytes()
            expected = json.loads(expected_bytes)
        except (OSError, ValueError) as error:
            failures.append(name)
            print(f"FAIL {name}: cannot read frozen fixture: {error}", file=sys.stderr, flush=True)
            continue
        # Remove only this generated output, never a fixture, so a failed
        # subprocess cannot accidentally reuse a stale successful result.
        if actual_path.is_symlink():
            failures.append(name)
            print(f"FAIL {name}: output file is a symbolic link", file=sys.stderr)
            continue
        actual_path.unlink(missing_ok=True)
        process = subprocess.run(
            [sys.executable, "-B", str(ROOT / "code" / f"{name}.py")],
            cwd=ROOT, env=environment, capture_output=True, text=True,
            encoding="utf-8", errors="replace", check=False,
        )
        if process.returncode:
            failures.append(name)
            print(f"FAIL {name}: subprocess exit {process.returncode}", file=sys.stderr)
            print(process.stdout + process.stderr, file=sys.stderr)
            continue
        try:
            actual = json.loads(actual_path.read_text(encoding="utf-8"))
            differences = compare(expected, actual)
            if expected_path.read_bytes() != expected_bytes:
                differences.append("Frozen fixture changed during replay")
        except (OSError, ValueError) as error:
            differences = [f"Cannot read result: {error}"]
        if differences:
            failures.append(name)
            print(f"FAIL {name}", file=sys.stderr)
            for difference in differences:
                print(f"  {difference}", file=sys.stderr)
        else:
            print(f"PASS {name}", flush=True)
    if failures:
        print(f"FAILED: {len(failures)} of {len(CHECKS)} checks", file=sys.stderr)
        return 1
    print(f"PASS: all {len(CHECKS)} checks matched their frozen fixtures")
    print("Exact algebra and finite diagnostics verified; analytic bounds are established in the report.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
