#!/usr/bin/env python3
"""Verify the packet manifest and reject proof placeholders in supplied Lean files."""
import hashlib
from pathlib import Path
import re
import sys

root = Path(__file__).resolve().parents[1]
failures = []
count = 0
for row in (root / "MANIFEST.sha256").read_text().splitlines():
    expected, relative = row.split("  ", 1)
    path = root / relative
    if not path.is_file() or hashlib.sha256(path.read_bytes()).hexdigest() != expected:
        failures.append(f"Hash mismatch or missing file: {relative}")
    count += 1
for directory in ("lean", "candidates"):
    for path in (root / directory).glob("*.lean"):
        # A modest source hygiene check, not a substitute for kernel checking.
        text = path.read_text()
        text = re.sub(r"/-.*?-/", "", text, flags=re.S)
        text = re.sub(r"--[^\n]*", "", text)
        if re.search(r"\b(sorry|admit)\b|(?m:^\s*(?:private\s+)?axiom\s)", text):
            failures.append(f"Proof placeholder or new axiom declaration: {path.relative_to(root)}")
if failures:
    print("\n".join(failures), file=sys.stderr)
    sys.exit(1)
print(f"PASS: {count} manifest entries; no detected proof placeholders or new axioms.")
print("This checks archive integrity only. See evidence/ for compiler receipts and scope.")
