#!/usr/bin/env python3
"""Regenerate all three exact verification suites and compare their evidence.

Uses only the Python standard library.  All generated JSON files go into a
temporary directory; the delivered evidence is read without modification.
JSON objects are compared by their parsed structure, ignoring whitespace and
object-key ordering.  Array ordering and value types remain significant.
The script works from any current working directory.
"""

import argparse
import json
from pathlib import Path
import subprocess
import sys
import tempfile


SUITES = (
    ("graded selection", "verify_graded_selection.py", "graded_selection_checks.json"),
    ("norm gap", "verify_norm_gap.py", "norm_gap_checks.json"),
    ("polynomial obstruction", "verify_polynomial_obstruction.py",
     "polynomial_obstruction_results.json"),
)


def first_difference(expected, actual, path="$"):
    """Return a compact explanation of the first structural difference."""
    if type(expected) is not type(actual):
        return (f"{path}: expected {type(expected).__name__}, "
                f"received {type(actual).__name__}")
    if isinstance(expected, dict):
        missing = sorted(expected.keys() - actual.keys())
        added = sorted(actual.keys() - expected.keys())
        if missing or added:
            return f"{path}: missing keys {missing!r}; additional keys {added!r}"
        for key in sorted(expected):
            difference = first_difference(expected[key], actual[key], f"{path}.{key}")
            if difference is not None:
                return difference
    elif isinstance(expected, list):
        if len(expected) != len(actual):
            return f"{path}: expected {len(expected)} entries, received {len(actual)}"
        for index, (old, new) in enumerate(zip(expected, actual)):
            difference = first_difference(old, new, f"{path}[{index}]")
            if difference is not None:
                return difference
    elif expected != actual:
        return f"{path}: expected {repr(expected)[:160]}, received {repr(actual)[:160]}"
    return None


def run_suite(label, script_name, evidence_name, directory, temporary):
    script = directory / script_name
    evidence = directory / evidence_name
    generated = temporary / evidence_name
    completed = subprocess.run(
        [sys.executable, str(script), "--output", str(generated)],
        cwd=temporary,
        capture_output=True,
        text=True,
        check=False,
    )
    if completed.returncode != 0:
        details = (completed.stderr or completed.stdout).strip()
        raise RuntimeError(
            f"{label}: verifier exited with status {completed.returncode}\n"
            f"{details[-5000:]}"
        )
    if not generated.is_file():
        raise RuntimeError(f"{label}: verifier did not write its requested JSON file")
    with evidence.open(encoding="utf-8") as stream:
        expected = json.load(stream)
    with generated.open(encoding="utf-8") as stream:
        actual = json.load(stream)
    difference = first_difference(expected, actual)
    if difference is not None:
        raise RuntimeError(f"{label}: evidence mismatch at {difference}")
    print(f"PASS {label}: regenerated JSON matches {evidence_name}", flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.parse_args()
    directory = Path(__file__).resolve().parent
    try:
        with tempfile.TemporaryDirectory(prefix="gowers-exact-verification-") as name:
            temporary = Path(name)
            for label, script, evidence in SUITES:
                run_suite(label, script, evidence, directory, temporary)
    except (OSError, ValueError, RuntimeError) as error:
        print(f"FAIL {error}", file=sys.stderr)
        return 1
    print("All three verification suites passed; delivered evidence was not modified.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
