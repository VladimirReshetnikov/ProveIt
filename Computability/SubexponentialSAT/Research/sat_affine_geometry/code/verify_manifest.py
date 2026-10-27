#!/usr/bin/env python3
"""Verify packaged file hashes. Newly generated extra files are ignored."""
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def main():
    data = json.loads((ROOT / "MANIFEST.json").read_text())
    failures = []
    for row in data["files"]:
        path = (ROOT / row["path"]).resolve()
        if ROOT not in path.parents:
            raise ValueError("Unsafe manifest path")
        if not path.is_file():
            failures.append(row["path"] + ": missing")
        elif hashlib.sha256(path.read_bytes()).hexdigest() != row["sha256"]:
            failures.append(row["path"] + ": SHA-256 mismatch")
    if failures:
        raise RuntimeError("\n".join(failures))
    print("PASS: " + str(len(data["files"])) + " packaged file hashes verified.")


if __name__ == "__main__":
    main()
