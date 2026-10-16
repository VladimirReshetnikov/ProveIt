#!/usr/bin/env python3
"""Verify the delivered manifest, theory data, and exact saved TM certificates.

This does not run the ideal consistency search, a Coq kernel, or the full
compiler regeneration. Python's standard library suffices; no network is used.
Run with assertions enabled: python3 -B verify_artifacts.py
"""
from __future__ import annotations

import hashlib
import json
from pathlib import Path
import subprocess
import sys
import tempfile


def main():
    if not __debug__:
        raise RuntimeError("Assertions must remain enabled; do not use -O")
    root = Path(__file__).resolve().parent
    manifest = json.loads((root / "artifact_manifest.json").read_text())
    checked = 0
    for entry in manifest["files"]:
        relative = Path(entry["path"])
        if relative.is_absolute() or ".." in relative.parts:
            raise ValueError("Unsafe manifest path")
        path = root / relative
        content = path.read_bytes()
        if len(content) != entry["bytes"]:
            raise AssertionError(f"Size mismatch: {relative}")
        if hashlib.sha256(content).hexdigest() != entry["sha256"]:
            raise AssertionError(f"Hash mismatch: {relative}")
        checked += 1
    print(f"PASS: {checked} delivered file sizes and SHA-256 hashes", flush=True)

    with tempfile.TemporaryDirectory(prefix="zfc-k12-verify-") as directory:
        result = subprocess.run(
            [sys.executable, "-B", str(root / "theory/finite_assignment_kernel.py"),
             "--out", directory],
            check=True, capture_output=True, text=True,
        )
        summary = json.loads(result.stdout)
        for name in ("finite_kernel_clauses.json", "finite_kernel_clauses.txt",
                     "finite_kernel_audit.json"):
            if (Path(directory) / name).read_bytes() != (root / "theory/data" / name).read_bytes():
                raise AssertionError(f"Regenerated theory data mismatch: {name}")
        if summary["metrics"]["clauses"] != 28 or summary["diagnostic_cases"] != 8:
            raise AssertionError("Unexpected payload or diagnostic counts")
    print("PASS: exact 28-clause payload regenerated; 8 ground diagnostics and XOR table", flush=True)

    subprocess.run([sys.executable, "-B", str(root / "engineering/verify_saved.py")], check=True)
    print("PASS: bundle checks complete. Coq kernel and ideal consistency search were not run.")


if __name__ == "__main__":
    main()
