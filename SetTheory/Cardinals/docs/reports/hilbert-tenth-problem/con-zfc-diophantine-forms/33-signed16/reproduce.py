#!/usr/bin/env python3
"""Rebuild and check the released constructions without network access.

Python 3.10+; standard library only. Run from any working directory.
The universal mathematical proofs are in report.tex and the bundled proofs.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
STAGES = (
    ("Affine quartic and exact polynomial identities", "quartic31/build_and_verify.py"),
    ("Fixed Jones coefficient recipes and strict index bound", "code/prepare_index.py"),
    ("Sixteen-integer circuit and exact degree certificate", "code/build_signed16.py"),
    ("Independent signed16 arithmetic and source audit", "code/verify_signed16.py"),
    ("Twelve-positive-variable evaluator and independent norm audit", "positive12/build_and_verify.py"),
    ("Smaller complete coefficient tuple", "coefficients_small/build.py"),
    ("Independent coefficient reconstruction and rank examples", "coefficients_small/audit_independent.py"),
    ("Separately authored geometry and rank audit", "coefficients_small/audit_external_review.py"),
)


def check_release():
    manifest = ROOT / "RELEASE_SHA256.json"
    if not manifest.is_file():
        raise SystemExit("RELEASE_SHA256.json is missing; use the complete release archive.")
    data = json.loads(manifest.read_text())
    for relative, digest in data["files"].items():
        path = ROOT / relative
        if not path.is_file() or hashlib.sha256(path.read_bytes()).hexdigest() != digest:
            raise SystemExit("Release integrity mismatch: " + relative)
    print("PASS: " + str(len(data["files"])) + " release file hashes", flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check-release", action="store_true", help="check distributed file hashes without rebuilding")
    parser.add_argument("--verbose", action="store_true", help="also print each complete check receipt")
    args = parser.parse_args()
    if args.check_release:
        check_release()
        return
    if sys.version_info < (3, 10):
        raise SystemExit("Python 3.10 or newer is required.")
    if not __debug__:
        raise SystemExit("Run without -O: some independent audits intentionally use assertions.")
    environment = dict(os.environ)
    environment.pop("PYTHONOPTIMIZE", None)
    environment.update(PYTHONHASHSEED="0", PYTHONDONTWRITEBYTECODE="1")
    stages = []
    for number, (label, script) in enumerate(STAGES, 1):
        print(f"[{number}/{len(STAGES)}] {label}", flush=True)
        result = subprocess.run([sys.executable, "-B", str(ROOT / script)], cwd=ROOT,
                                env=environment, text=True, capture_output=True)
        if result.returncode:
            print(result.stdout, end="")
            print(result.stderr, end="", file=sys.stderr)
            raise SystemExit("FAILED: " + script)
        if args.verbose:
            print(result.stdout, end="")
        stages.append({"script": script, "status": "PASS"})
    signed = json.loads((ROOT / "verification/signed16_build.json").read_text())
    expected = {"add": 674, "sub": 29, "mul": 887}
    if signed["operation_counts"] != expected or signed["operations"] != 1590:
        raise SystemExit("Signed16 operation count differs from the paper.")
    if signed["degree_certificate"]["degree"] != 406528 * 5**32 + 10008:
        raise SystemExit("Signed16 degree differs from the paper.")
    receipt = {
        "status": "PASS", "stages": stages,
        "signed16_operations": signed["operations"],
        "signed16_operation_counts": expected,
        "signed16_exact_degree": signed["degree_certificate"]["degree"],
        "scope": "Portable generation, exact algebra and finite arithmetic audits; universal proofs and imported dependencies are described in report.tex. No ZFC consistency decision or new proof-assistant build."
    }
    (ROOT / "verification/reproduction.json").write_text(json.dumps(receipt, indent=2) + "\n")
    print("PASS: all eight stages; 16 unrestricted integers, 1590 operations.", flush=True)


if __name__ == "__main__":
    main()
