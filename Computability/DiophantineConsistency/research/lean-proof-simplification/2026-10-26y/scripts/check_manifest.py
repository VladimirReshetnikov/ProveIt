#!/usr/bin/env python3
"""Verify the files recorded in MANIFEST.sha256 without modifying them."""
from pathlib import Path
import hashlib
import sys

root = Path(__file__).resolve().parents[1]
errors = []
for line in (root / "MANIFEST.sha256").read_text().splitlines():
    expected, relative = line.split("  ", 1)
    path = root / relative
    if not path.is_file():
        errors.append("missing: " + relative)
    elif hashlib.sha256(path.read_bytes()).hexdigest() != expected:
        errors.append("changed: " + relative)
if errors:
    print("\n".join(errors))
    sys.exit(1)
print("All recorded file hashes match.")
