#!/usr/bin/env python3
"""Verify the final package's SHA-256 manifest, without changing any file."""

import hashlib
from pathlib import Path


def main() -> None:
    root = Path(__file__).resolve().parents[1]
    manifest = root / "SHA256SUMS.txt"
    count = 0
    for line in manifest.read_text(encoding="utf-8").splitlines():
        if not line:
            continue
        digest, relative = line.split("  ", 1)
        target = (root / relative).resolve()
        if not target.is_relative_to(root) or not target.is_file():
            raise ValueError("Invalid or missing manifest file: " + relative)
        actual = hashlib.sha256(target.read_bytes()).hexdigest()
        if actual != digest:
            raise ValueError("SHA-256 mismatch: " + relative)
        count += 1
    if count == 0:
        raise ValueError("Empty manifest")
    print(f"Verified {count} file fingerprints.")


if __name__ == "__main__":
    main()
