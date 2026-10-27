#!/usr/bin/env python3
"""Verify the shipped artifact hashes. Does not establish mathematical truth."""
from hashlib import sha256
from pathlib import Path
import json


def main():
    root = Path(__file__).resolve().parent
    manifest = json.loads((root / "MANIFEST.json").read_text())
    checked = 0
    for entry in manifest["files"]:
        relative = Path(entry["path"])
        if relative.is_absolute() or ".." in relative.parts:
            raise RuntimeError(f"Unsafe manifest entry: {relative}")
        path = root / relative
        content = path.read_bytes()
        if len(content) != entry["bytes"] or sha256(content).hexdigest() != entry["sha256"]:
            raise RuntimeError(f"File differs from shipped manifest: {relative}")
        checked += 1
    print(f"PASS: {checked} files match MANIFEST.json")


if __name__ == "__main__":
    main()
