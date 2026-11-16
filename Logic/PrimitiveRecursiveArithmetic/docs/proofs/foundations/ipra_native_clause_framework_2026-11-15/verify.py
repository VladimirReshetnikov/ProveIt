#!/usr/bin/env python3
"""Offline verification helper for the delivered package."""

from __future__ import annotations

import hashlib
import json
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent


def check_json() -> None:
    for path in sorted(ROOT.rglob("*.json")):
        with path.open("r", encoding="utf-8") as handle:
            json.load(handle)
        print(f"JSON OK: {path.relative_to(ROOT)}")


def check_manifest() -> None:
    manifest = ROOT / "MANIFEST.sha256"
    if not manifest.exists():
        print("Manifest not present yet; run ./build.sh to create it.")
        return
    failures = []
    for line in manifest.read_text(encoding="utf-8").splitlines():
        if not line.strip():
            continue
        expected, rel = line.split(maxsplit=1)
        rel = rel.lstrip("*")
        path = ROOT / rel
        if not path.exists():
            failures.append(f"missing: {rel}")
            continue
        actual = hashlib.sha256(path.read_bytes()).hexdigest()
        if actual != expected:
            failures.append(f"checksum mismatch: {rel}")
    if failures:
        raise SystemExit("\n".join(failures))
    print("Manifest OK")


def run_tests() -> None:
    subprocess.run(
        [sys.executable, "-m", "unittest", "-v", "test_native_clause_framework.py"],
        cwd=ROOT / "code",
        check=True,
    )


def static_lean_audit() -> None:
    lean_root = ROOT / "lean" / "NativeClauseFramework"
    holes = 0
    axioms = 0
    bridge_holes = 0
    for path in lean_root.glob("*.lean"):
        for line in path.read_text(encoding="utf-8").splitlines():
            stripped = line.strip()
            if stripped == "sorry":
                holes += 1
                if path.name == "Bridge.lean":
                    bridge_holes += 1
            if stripped.startswith("axiom "):
                axioms += 1
    if holes != 17 or bridge_holes != 0 or axioms != 0:
        raise SystemExit(
            f"unexpected Lean static audit: holes={holes}, "
            f"bridge_holes={bridge_holes}, axioms={axioms}"
        )
    print("Lean static audit OK: 17 blueprint holes, 0 Bridge holes, 0 axioms")


def main() -> None:
    check_json()
    run_tests()
    static_lean_audit()
    check_manifest()


if __name__ == "__main__":
    main()
