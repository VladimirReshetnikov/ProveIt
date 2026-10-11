#!/usr/bin/env python3
"""Verify delivered files against MANIFEST.sha256 using only Python stdlib."""
import hashlib
from pathlib import Path

root = Path(__file__).resolve().parent
count = 0
for line in (root/"MANIFEST.sha256").read_text().splitlines():
    expected, name = line.split("  ", 1)
    path = root/name
    if not path.is_file():
        raise SystemExit(f"Missing: {name}")
    actual = hashlib.sha256(path.read_bytes()).hexdigest()
    if actual != expected:
        raise SystemExit(f"Checksum mismatch: {name}")
    count += 1
print(f"Verified {count} delivered files.")
