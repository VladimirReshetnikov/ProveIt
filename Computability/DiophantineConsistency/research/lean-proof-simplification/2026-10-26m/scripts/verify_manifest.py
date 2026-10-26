#!/usr/bin/env python3
"""Verify the exact extracted files recorded in FILES_SHA256.json."""
from pathlib import Path
import hashlib
import json
import sys

root = Path(__file__).resolve().parents[1]
entries = json.loads((root / "FILES_SHA256.json").read_text())
failures = []
for entry in entries:
    path = root / entry["path"]
    if not path.is_file():
        failures.append(f"Missing: {entry['path']}")
        continue
    data = path.read_bytes()
    if len(data) != entry["bytes"] or hashlib.sha256(data).hexdigest() != entry["sha256"]:
        failures.append(f"Mismatch: {entry['path']}")
for failure in failures:
    print(failure, file=sys.stderr)
print(f"Verified {len(entries) - len(failures)} of {len(entries)} files.")
raise SystemExit(bool(failures))
