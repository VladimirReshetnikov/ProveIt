#!/usr/bin/env python3
"""Verify the immutable delivery ledger; run before rebuilding or rerunning."""
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent
ledger = json.loads((ROOT / "MANIFEST.sha256.json").read_text())
failures = []
for record in ledger["files"]:
    path = ROOT / record["path"]
    if not path.is_file():
        failures.append({"path": record["path"], "error": "missing"})
        continue
    data = path.read_bytes()
    if len(data) != record["size"] or hashlib.sha256(data).hexdigest() != record["sha256"]:
        failures.append({"path": record["path"], "error": "size or SHA-256 mismatch"})
if failures:
    raise SystemExit(json.dumps(failures, indent=2))
print(f"All {len(ledger['files'])} delivered file hashes match.")
