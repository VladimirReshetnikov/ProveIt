#!/usr/bin/env python3
"""Standard-library verification for the staged-contract package."""

from __future__ import annotations

import hashlib
import json
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent


def run(cmd: list[str], cwd: Path | None = None) -> None:
    print("+", " ".join(cmd))
    subprocess.run(cmd, cwd=cwd or ROOT, check=True)


def check_json() -> None:
    for path in sorted(ROOT.rglob("*.json")):
        json.loads(path.read_text(encoding="utf-8"))
        print(f"JSON OK {path.relative_to(ROOT)}")


def check_lean_no_admissions() -> None:
    bad = re.compile(r"\b(?:axiom|sorry|admit)\b")
    failures: list[str] = []
    for path in sorted((ROOT / "lean").rglob("*.lean")):
        for line_no, line in enumerate(path.read_text(encoding="utf-8").splitlines(), 1):
            # The supplied Lean sources intentionally contain no occurrence,
            # even in comments, so a lexical scan is sufficient here.
            if bad.search(line):
                failures.append(f"{path.relative_to(ROOT)}:{line_no}: {line.strip()}")
    if failures:
        raise SystemExit("Lean admission scan failed:\n" + "\n".join(failures))
    print("LEAN LEXICAL SCAN OK")


def check_manifest() -> None:
    manifest = ROOT / "MANIFEST.sha256"
    if not manifest.exists():
        print("MANIFEST not present yet; skipping integrity check")
        return
    for raw in manifest.read_text(encoding="utf-8").splitlines():
        if not raw.strip():
            continue
        expected, rel = raw.split("  ", 1)
        path = ROOT / rel
        actual = hashlib.sha256(path.read_bytes()).hexdigest()
        if actual != expected:
            raise SystemExit(f"checksum mismatch: {rel}")
    print("MANIFEST OK")


def main() -> None:
    run([sys.executable, "test_staged_contracts.py"], ROOT / "code")
    run([sys.executable, "demo.py"], ROOT / "code")
    check_json()
    check_lean_no_admissions()
    check_manifest()
    pdf = ROOT / "paper" / "ipra_staged_contract_kernel.pdf"
    if pdf.exists() and pdf.stat().st_size > 10_000:
        print(f"PDF OK {pdf.relative_to(ROOT)} ({pdf.stat().st_size} bytes)")
    else:
        print("PDF not present yet; build.sh will create it")
    print("ALL AVAILABLE CHECKS PASSED")


if __name__ == "__main__":
    main()
