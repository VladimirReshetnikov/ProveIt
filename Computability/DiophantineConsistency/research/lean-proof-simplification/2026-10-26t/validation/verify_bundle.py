#!/usr/bin/env python3
"""Verify the packaged file hashes without executing Lean or modifying files."""
from pathlib import Path
import hashlib
import sys

root = Path(__file__).resolve().parent.parent
manifest = root / "MANIFEST.sha256"
if not manifest.is_file():
    raise SystemExit("MANIFEST.sha256 is missing")
failures = []
count = 0
for line in manifest.read_text(encoding="utf-8").splitlines():
    expected, relative = line.split("  ", 1)
    source = root / relative
    if not source.resolve().is_relative_to(root):
        failures.append(f"Path outside bundle: {relative}")
        continue
    if not source.is_file():
        failures.append(f"Missing file: {relative}")
        continue
    actual = hashlib.sha256(source.read_bytes()).hexdigest()
    if actual != expected:
        failures.append(f"Hash mismatch: {relative}")
    count += 1
if failures:
    print("\n".join(failures), file=sys.stderr)
    raise SystemExit(1)
print(f"Verified {count} packaged files.")
