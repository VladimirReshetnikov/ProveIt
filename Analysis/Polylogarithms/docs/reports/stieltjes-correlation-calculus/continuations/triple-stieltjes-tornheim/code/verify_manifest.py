#!/usr/bin/env python3
"""Check the delivered SHA-256 snapshots; does not validate mathematics."""
from __future__ import annotations

import hashlib
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]

def main() -> int:
    manifest = ROOT / "SHA256SUMS"
    if not manifest.is_file():
        print("Missing SHA256SUMS", file=sys.stderr)
        return 2
    failures: list[str] = []
    checked = 0
    for line in manifest.read_text(encoding="utf-8").splitlines():
        if not line.strip():
            continue
        expected, relative = line.split("  ", 1)
        path = (ROOT / relative).resolve()
        if not path.is_relative_to(ROOT.resolve()):
            raise ValueError(f"Unsafe path in manifest: {relative}")
        if not path.is_file():
            failures.append(f"MISSING {relative}")
            continue
        actual = hashlib.sha256(path.read_bytes()).hexdigest()
        checked += 1
        if actual != expected:
            failures.append(f"CHANGED {relative}")
    if failures:
        print("\n".join(failures), file=sys.stderr)
        return 1
    print(f"PASS: {checked} delivered file hashes agree.")
    return 0

if __name__ == "__main__":
    raise SystemExit(main())
