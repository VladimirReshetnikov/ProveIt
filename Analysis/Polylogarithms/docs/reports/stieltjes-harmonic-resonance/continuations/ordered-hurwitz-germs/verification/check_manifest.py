#!/usr/bin/env python3
"""Verify the distributed package hashes without changing files."""
from pathlib import Path
import hashlib
import sys

def main() -> int:
    root = Path(__file__).resolve().parents[1]
    manifest = root / "SHA256SUMS"
    if not manifest.is_file():
        print("Missing SHA256SUMS", file=sys.stderr)
        return 2
    failures = []
    count = 0
    for line in manifest.read_text(encoding="utf-8").splitlines():
        if not line.strip():
            continue
        expected, name = line.split("  ", 1)
        target = (root / name).resolve()
        if not target.is_relative_to(root) or not target.is_file():
            failures.append(f"Missing or unsafe path: {name}")
            continue
        actual = hashlib.sha256(target.read_bytes()).hexdigest()
        count += 1
        if actual != expected:
            failures.append(f"Hash mismatch: {name}")
    if failures:
        print("\n".join(failures), file=sys.stderr)
        return 1
    print(f"PASS: {count} packaged file hashes verified.")
    return 0

if __name__ == "__main__":
    raise SystemExit(main())
