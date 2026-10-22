#!/usr/bin/env python3
"""Check all listed archive files against MANIFEST.json; no theorem is inferred."""
import hashlib
import json
from pathlib import Path

root = Path(__file__).resolve().parent
manifest = json.loads((root / "MANIFEST.json").read_text())
failures = []
for entry in manifest["files"]:
    path = (root / entry["path"]).resolve()
    if not path.is_relative_to(root):
        failures.append(f"Unsafe inventory path: {entry['path']}")
        continue
    if not path.is_file():
        failures.append(f"Missing file: {entry['path']}")
        continue
    data = path.read_bytes()
    if len(data) != entry["bytes"] or hashlib.sha256(data).hexdigest() != entry["sha256"]:
        failures.append(f"Content mismatch: {entry['path']}")
if failures:
    raise SystemExit("\n".join(failures))
print(f"PASS: {len(manifest['files'])} files match their recorded length and SHA-256.")
print("This verifies archive inventory only, not a proof-assistant result or signature.")
