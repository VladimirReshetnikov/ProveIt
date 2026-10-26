#!/usr/bin/env python3
"""Verify the distributed file hashes without external dependencies."""
from pathlib import Path
import hashlib
import sys
root = Path(__file__).resolve().parents[1]
failures = []
count = 0
for line in (root / "MANIFEST.sha256").read_text().splitlines():
    expected, name = line.split("  ", 1)
    path = root / name
    actual = hashlib.sha256(path.read_bytes()).hexdigest() if path.is_file() else "MISSING"
    if actual != expected:
        failures.append(name)
    count += 1
for name in failures:
    print("FAILED:", name)
print(f"Verified {count - len(failures)}/{count} packaged files")
sys.exit(bool(failures))
