#!/usr/bin/env python3
"""Verify delivered bytes against MANIFEST.json, without executing proof code.

This is an integrity check, not an authenticity or formal-proof checker.
The manifest excludes itself. Run on an unmodified extracted packet.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path, PurePosixPath


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parent)
    args = parser.parse_args()
    root = args.root.resolve()
    manifest = json.loads((root / "MANIFEST.json").read_text(encoding="utf-8"))
    records = manifest["files"]
    expected: set[str] = set()
    errors: list[str] = []
    for record in records:
        name = record["path"]
        pure = PurePosixPath(name)
        if pure.is_absolute() or ".." in pure.parts or name in expected:
            errors.append(f"Unsafe or duplicate manifest path: {name}")
            continue
        expected.add(name)
        path = root.joinpath(*pure.parts)
        if path.is_symlink() or not path.is_file() or root not in path.resolve().parents:
            errors.append(f"Missing, nonregular, or out-of-root file: {name}")
            continue
        content = path.read_bytes()
        if len(content) != record["bytes"]:
            errors.append(f"Size mismatch: {name}")
        if hashlib.sha256(content).hexdigest() != record["sha256"]:
            errors.append(f"SHA-256 mismatch: {name}")
    actual = {
        p.relative_to(root).as_posix()
        for p in root.rglob("*")
        if p.is_file() or p.is_symlink()
    } - {"MANIFEST.json"}
    for name in sorted(actual - expected):
        errors.append(f"Unlisted file: {name}")
    if errors:
        raise SystemExit("FAIL\n" + "\n".join(errors))
    print(f"PASS: {len(expected)} files match the delivered manifest.")
    print("This verifies bytes only; see README.md for proof-kernel replay.")


if __name__ == "__main__":
    main()
