#!/usr/bin/env python3
"""Check archive file hashes, without changing any file."""
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent
manifest = json.loads((ROOT / "FILE_MANIFEST.json").read_text())
for entry in manifest["files"]:
    path = ROOT / entry["path"]
    if not path.is_file():
        raise FileNotFoundError(entry["path"])
    data = path.read_bytes()
    if len(data) != entry["bytes"] or hashlib.sha256(data).hexdigest() != entry["sha256"]:
        raise ValueError("Package integrity mismatch: " + entry["path"])
print("PASS package integrity: " + str(len(manifest["files"])) + " files")
