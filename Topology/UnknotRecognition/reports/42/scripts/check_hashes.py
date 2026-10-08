#!/usr/bin/env python3
"""Verify all distributed file digests from the bundle root."""
import hashlib
from pathlib import Path
import sys
ROOT = Path(__file__).resolve().parents[1]
manifest = ROOT / "SHA256SUMS"
errors = []
count = 0
for line in manifest.read_text().splitlines():
    digest, name = line.split("  ", 1)
    path = ROOT / name
    if not path.is_file() or hashlib.sha256(path.read_bytes()).hexdigest() != digest:
        errors.append(name)
    count += 1
if errors:
    print("Digest mismatch or missing file:", *errors, sep="\n")
    sys.exit(1)
print("Verified", count, "file digests.")
