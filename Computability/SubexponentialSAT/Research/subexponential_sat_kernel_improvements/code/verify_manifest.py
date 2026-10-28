#!/usr/bin/env python3
"""Verify the immutable release files listed in the accompanying manifest.

The manifest excludes itself, temporary build files, and Python caches.
Additional replay outputs are allowed and are not inspected.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parents[1])
    args = parser.parse_args()
    root = args.root.resolve()
    manifest = json.loads((root / "provenance/artifact_manifest.json").read_text())
    failures = []
    for item in manifest["files"]:
        relative = Path(item["path"])
        path = (root / relative).resolve()
        if relative.is_absolute() or not path.is_relative_to(root):
            failures.append(f"Unsafe manifest path: {relative}")
            continue
        if not path.is_file():
            failures.append(f"Missing: {relative}")
            continue
        data = path.read_bytes()
        if len(data) != item["size_bytes"]:
            failures.append(f"Size mismatch: {relative}")
        if hashlib.sha256(data).hexdigest() != item["sha256"]:
            failures.append(f"SHA-256 mismatch: {relative}")
    if failures:
        for failure in failures:
            print(failure)
        return 1
    print(f"Verified {len(manifest['files'])} release files; all sizes and SHA-256 hashes match.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
