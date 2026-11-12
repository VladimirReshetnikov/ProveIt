#!/usr/bin/env python3
"""Verify the untouched distribution. Rebuilding generated files may change their hashes."""
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent
manifest = json.loads((ROOT / "MANIFEST.json").read_text())
bad = []
for name, expected in manifest.items():
    p = ROOT / name
    actual = hashlib.sha256(p.read_bytes()).hexdigest() if p.is_file() else None
    if actual != expected:
        bad.append(name)
if bad:
    raise SystemExit("Hash mismatch: " + ", ".join(bad))
print("Verified " + str(len(manifest)) + " files.")

