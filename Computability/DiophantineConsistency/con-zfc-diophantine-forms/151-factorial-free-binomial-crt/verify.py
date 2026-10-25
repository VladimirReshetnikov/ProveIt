#!/usr/bin/env python3
"""Reproduce and check the released finite algebraic artifacts.

Uses the Python standard library. This is not a proof-assistant verification of
the unbounded arithmetic and logic in the accompanying mathematical report.
"""
from pathlib import Path
import argparse
import hashlib
import json
import subprocess
import sys

ROOT = Path(__file__).resolve().parent


def run_json(arguments, optimized=False):
    command = [sys.executable, "-B"]
    if optimized:
        command.append("-O")
    command.extend(map(str, arguments))
    process = subprocess.run(command, cwd=ROOT, check=True,
                             capture_output=True, text=True)
    return json.loads(process.stdout)


def check_manifest():
    manifest = ROOT / "MANIFEST.sha256"
    if not manifest.exists():
        return {"status": "NOT_PRESENT"}
    count = 0
    for line in manifest.read_text().splitlines():
        expected, name = line.split("  ", 1)
        path = (ROOT / name).resolve()
        if ROOT not in path.parents:
            raise RuntimeError("Manifest contains an escaping path")
        actual = hashlib.sha256(path.read_bytes()).hexdigest()
        if actual != expected:
            raise RuntimeError(f"Checksum mismatch: {name}")
        count += 1
    return {"status": "PASS", "checked_files": count}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--skip-parent", action="store_true",
                        help="skip rechecking the included parent source")
    parser.add_argument("--skip-manifest", action="store_true",
                        help="useful while intentionally editing the release")
    parser.add_argument("--manifest-only", action="store_true")
    parser.add_argument("--receipt", type=Path)
    args = parser.parse_args()
    receipt = {"status": "PASS"}
    if not args.manifest_only:
        direct_args = [ROOT / "direct/reproduce.py"]
        if args.skip_parent:
            direct_args.append("--skip-parent")
        receipt["direct_reproduction"] = run_json(direct_args)
        receipt["new_arithmetic_regressions"] = run_json(
            [ROOT / "code/check_new_lemmas.py"])
        optimized = run_json([ROOT / "code/check_new_lemmas.py"], optimized=True)
        if optimized != receipt["new_arithmetic_regressions"]:
            raise RuntimeError("Arithmetic regression differs under Python -O")
        receipt["new_arithmetic_optimized_matches"] = True
        receipt["report_inputs"] = run_json([ROOT / "code/report_inputs.py", "--check"])
    if not args.skip_manifest:
        receipt["manifest"] = check_manifest()
    receipt["scope"] = (
        "Exact finite reconstruction, coefficient identities, interface audit, "
        "readable exports, number-theory regressions, and release checksums. "
        "The ordinary unbounded mathematical proof is in report/main.tex."
    )
    output = json.dumps(receipt, indent=2, sort_keys=True) + "\n"
    if args.receipt:
        args.receipt.parent.mkdir(parents=True, exist_ok=True)
        args.receipt.write_text(output)
    print(output, end="")


if __name__ == "__main__":
    main()
