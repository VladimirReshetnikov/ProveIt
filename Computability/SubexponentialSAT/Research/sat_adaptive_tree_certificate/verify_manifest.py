#!/usr/bin/env python3
"""Verify delivered bytes before rebuilding or regenerating result files."""
from pathlib import Path
import hashlib
import json

ROOT = Path(__file__).resolve().parent


def main():
    entries = json.loads((ROOT/"MANIFEST.sha256.json").read_text(encoding="utf-8"))["files"]
    for entry in entries:
        path = ROOT/entry["path"]
        if not path.is_file() or hashlib.sha256(path.read_bytes()).hexdigest() != entry["sha256"]:
            raise RuntimeError("Manifest mismatch: "+entry["path"])
    print(json.dumps({"status": "PASS", "verified_files": len(entries)}, indent=2))


if __name__ == "__main__":
    main()
