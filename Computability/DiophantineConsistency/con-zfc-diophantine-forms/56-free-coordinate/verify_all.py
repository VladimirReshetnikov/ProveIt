#!/usr/bin/env python3
"""Authenticate and reproduce this release without changing its components."""
from pathlib import Path
import hashlib
import json
import os
import shutil
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parent


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def run(work, script, optimized=False):
    command = [sys.executable] + (["-O"] if optimized else []) + [script]
    environment = dict(os.environ)
    environment["PYTHONDONTWRITEBYTECODE"] = "1"
    result = subprocess.run(command, cwd=work, env=environment,
                            text=True, capture_output=True)
    require(result.returncode == 0,
            f"{work.name}/{script} failed:\n{result.stdout}\n{result.stderr}")
    return result.stdout


def main():
    manifest = json.loads((ROOT / "SHA256SUMS.json").read_text())
    for name, expected in manifest.items():
        path = ROOT / name
        require(path.is_file(), "missing release file: " + name)
        actual = hashlib.sha256(path.read_bytes()).hexdigest()
        require(actual == expected, "release hash mismatch: " + name)

    with tempfile.TemporaryDirectory(prefix="proveit-free-coordinate-") as temp:
        temp_root = Path(temp)
        for name in ("nine", "short"):
            shutil.copytree(ROOT / name, temp_root / name,
                            ignore=shutil.ignore_patterns("__pycache__", "*.pyc"))

        run(temp_root / "nine", "verify.py")
        nine_receipt = json.loads(
            (temp_root / "nine/VERIFICATION.json").read_text())

        short_rebuilds = []
        for optimized in (False, True):
            run(temp_root / "short", "build_and_audit.py", optimized)
            compared = 0
            for original in sorted((ROOT / "short/generated").glob("*.json")):
                rebuilt = temp_root / "short/generated" / original.name
                require(rebuilt.read_bytes() == original.read_bytes(),
                        "short rebuild mismatch: " + original.name)
                compared += 1
            short_rebuilds.append({"optimized_python": optimized,
                                   "byte_identical_files": compared,
                                   "status": "passed"})
        short_receipt = json.loads(
            (temp_root / "short/generated/AUDIT.json").read_text())

    result = {
        "status": "passed",
        "release_files_authenticated": len(manifest),
        "outer_python_optimized": bool(sys.flags.optimize),
        "nine": nine_receipt,
        "short_rebuilds": short_rebuilds,
        "short": short_receipt,
        "scope": "Finite reproducibility and algebraic checks; universal "
                 "solvability equivalence is proved mathematically with the "
                 "identified inherited compiler and Jones theorems."
    }
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
