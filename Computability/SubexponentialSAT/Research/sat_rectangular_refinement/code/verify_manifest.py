#!/usr/bin/env python3
"""Check hashes of delivered files; ignore newly generated replay directories."""
from hashlib import sha256
from pathlib import Path


def main():
    root = Path(__file__).resolve().parents[1]
    count = 0
    for line in (root / "SHA256SUMS").read_text().splitlines():
        digest, relative = line.split("  ", 1)
        path = (root / relative).resolve()
        if root not in path.parents:
            raise ValueError("Unsafe manifest path: " + relative)
        if sha256(path.read_bytes()).hexdigest() != digest:
            raise ValueError("Digest mismatch: " + relative)
        count += 1
    print("PASS:", count, "delivered files match SHA256SUMS.")


if __name__ == "__main__":
    main()
