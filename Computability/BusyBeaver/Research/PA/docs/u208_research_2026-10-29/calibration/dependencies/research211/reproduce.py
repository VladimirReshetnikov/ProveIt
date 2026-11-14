#!/usr/bin/env python3
"""One-command offline reconstruction and verification of the U211 candidate."""
from pathlib import Path
import argparse
import hashlib
import os
import subprocess
import sys

ROOT = Path(__file__).resolve().parent


def run(*args):
    print("\n>>> " + " ".join(map(str, args)), flush=True)
    subprocess.run(list(map(str, args)), cwd=ROOT, check=True,
                   env={**os.environ, "PYTHONDONTWRITEBYTECODE": "1"})


def hashes():
    manifest = ROOT / "SHA256SUMS"
    if not manifest.exists():
        raise RuntimeError("Missing SHA256SUMS")
    count = 0
    for line in manifest.read_text().splitlines():
        expected, name = line.split("  ", 1)
        actual = hashlib.sha256((ROOT / name).read_bytes()).hexdigest()
        if actual != expected:
            raise RuntimeError("Hash mismatch: " + name)
        count += 1
    print(f"Frozen artifact identities: {count} files checked", flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--quick", action="store_true",
                        help="skip the unbounded symbolic primitive replay")
    parser.add_argument("--pdf", action="store_true",
                        help="also regenerate report.pdf using pdflatex")
    args = parser.parse_args()
    if not args.quick and (not __debug__ or sys.flags.optimize or os.getenv("PYTHONOPTIMIZE")):
        raise RuntimeError("Full reproduction requires ordinary Python with assertions enabled")
    hashes()
    py = sys.executable
    run(py, "code/build.py")
    run(py, "code/audit_rotation_source.py", "inputs/u212.native.tm",
        "inputs/u212.sites.json", "inputs/rotations.json",
        "machine/rotated212.native.tm", "machine/sites.json",
        "--output", "evidence/source.json")
    run(py, "code/verify_fold.py")
    run(py, "-O", "code/verify_fold.py")
    run(py, "code/audit_startup.py", "inputs/u212.native.tm",
        "machine/u211.native.tm", "machine/sites.json",
        "--output", "evidence/startup.json")
    if not args.quick:
        run(py, "code/verify_runtime.py")
    if args.pdf:
        run(py, "code/make_report_data.py")
        for _ in range(2):
            run("pdflatex", "-interaction=nonstopmode", "-halt-on-error", "report.tex")
    print("\nQUICK CHECKS PASSED; full runtime replay SKIPPED" if args.quick else
          "\nALL CONSTRUCTION, SOURCE, FOLD, STARTUP, AND RUNTIME CHECKS PASSED")
    print("Mathematical and executable evidence; no proof-assistant endpoint is claimed.")


if __name__ == "__main__":
    main()
