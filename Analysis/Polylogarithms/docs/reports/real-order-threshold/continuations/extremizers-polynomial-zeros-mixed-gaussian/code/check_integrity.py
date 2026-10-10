#!/usr/bin/env python3
"""Verify the exact payload recorded by MANIFEST.sha256 (standard library)."""
from hashlib import sha256
from pathlib import Path

BASE = Path(__file__).resolve().parents[1]


def main():
    rows = (BASE / "MANIFEST.sha256").read_text().splitlines()
    checked = 0
    for row in rows:
        expected, relative = row.split("  ", 1)
        path = (BASE / relative).resolve()
        if not path.is_relative_to(BASE):
            raise ValueError("Manifest path escapes the package")
        if sha256(path.read_bytes()).hexdigest() != expected:
            raise RuntimeError("Checksum mismatch: " + relative)
        checked += 1
    print(f"Integrity verified for {checked} payload files.")


if __name__ == "__main__":
    main()
