#!/usr/bin/env python3
"""Verify literal sources, coefficients, proofs' finite interfaces and exports.

Requires only Python 3.10+ standard library. Defaults are read-only with
temporary reconstruction files. --receipt is the only persistent output.
These finite checks do not prove the unbounded consistency equivalence.
"""
from pathlib import Path
import argparse
import hashlib
import json
import os
import subprocess
import sys

ROOT = Path(__file__).resolve().parent


def run(arguments):
    command = [sys.executable, "-B"]
    if sys.flags.optimize:
        command.append("-O")
    process = subprocess.run(
        command + list(map(str, arguments)), cwd=ROOT,
        env=dict(os.environ, PYTHONDONTWRITEBYTECODE="1"),
        check=True, capture_output=True, text=True
    )
    try:
        return json.loads(process.stdout)
    except json.JSONDecodeError as error:
        raise ValueError(f"Non-JSON verification output from {arguments[0]}") from error


def manifest():
    path = ROOT / "MANIFEST.sha256"
    if not path.is_file():
        raise ValueError("Missing release manifest; use --skip-manifest only while editing")
    count = 0
    for line in path.read_text().splitlines():
        expected, relative = line.split("  ", 1)
        file = (ROOT / relative).resolve()
        if ROOT not in file.parents or not file.is_file():
            raise ValueError("Invalid manifest path: " + relative)
        if hashlib.sha256(file.read_bytes()).hexdigest() != expected:
            raise ValueError("Release checksum differs: " + relative)
        count += 1
    return {"status": "PASS", "checked_files": count}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--skip-parent", action="store_true")
    parser.add_argument("--skip-rebuild", action="store_true")
    parser.add_argument("--skip-manifest", action="store_true")
    parser.add_argument("--manifest-only", action="store_true")
    parser.add_argument("--receipt", type=Path)
    args = parser.parse_args()
    receipt = {"status": "PASS", "python_optimization": sys.flags.optimize}
    if not args.manifest_only:
        checks = [
            ("fixed_source", [ROOT / "code/check_fixed_growth_source.py"]),
            ("fixed_power_interface", [ROOT / "code/audit_power_interface.py"]),
            ("modular_interface", [ROOT / "code/audit_modular_interface.py"]),
            ("signed_J_majorant", [ROOT / "code/audit_J_majorant.py", "--check"]),
            ("final_algebra", [ROOT / "code/check_final.py"]),
            ("arithmetic_regressions", [ROOT / "code/check_math.py"]),
            ("modular_regressions", [ROOT / "code/check_modular_lemmas.py"]),
            ("two_square_regressions", [ROOT / "code/check_two_square_center.py"]),
            ("readable_exports", [ROOT / "code/report_inputs.py", "--check"]),
        ]
        for label, arguments in checks:
            receipt[label] = run(arguments)
        receipt["reproduction"] = (
            {"status": "SKIPPED"} if args.skip_rebuild
            else run([ROOT / "reproduce.py"])
        )
        receipt["retained_parent"] = (
            {"status": "SKIPPED"} if args.skip_parent
            else run([ROOT / "upstream/factorial_free/verify.py"])
        )
    receipt["manifest"] = (
        {"status": "SKIPPED"} if args.skip_manifest else manifest()
    )
    receipt["scope"] = (
        "Finite source reconstruction, interfaces, exact integral transformations, "
        "all collected coefficients, deterministic builds, arithmetic regressions "
        "and readable exports. The unbounded arithmetic and inherited logical "
        "calibration require the accompanying mathematical proofs. No fresh "
        "end-to-end Lean/Rocq certificate is claimed."
    )
    output = json.dumps(receipt, indent=2, sort_keys=True) + "\n"
    if args.receipt:
        args.receipt.parent.mkdir(parents=True, exist_ok=True)
        args.receipt.write_text(output)
    print(output, end="")


if __name__ == "__main__":
    main()
