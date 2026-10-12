#!/usr/bin/env python3
"""Verify distributed byte identities without modifying the package."""
import hashlib
import json
from pathlib import Path

root = Path(__file__).resolve().parents[1]
manifest = json.loads((root / "data" / "package_manifest.json").read_text())
errors = []
for entry in manifest["files"]:
    path = root / entry["path"]
    if not path.is_file():
        errors.append({"path":entry["path"], "error":"missing"})
    elif hashlib.sha256(path.read_bytes()).hexdigest() != entry["sha256"]:
        errors.append({"path":entry["path"], "error":"hash mismatch"})
print(json.dumps({"checked":len(manifest["files"]), "errors":errors}, indent=2))
raise SystemExit(bool(errors))
