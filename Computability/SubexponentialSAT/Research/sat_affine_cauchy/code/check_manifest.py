#!/usr/bin/env python3
"""Check archived hashes before rebuilding or regenerating any file."""
import hashlib
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

def main():
    records = (ROOT / "MANIFEST.sha256").read_text().splitlines()
    for record in records:
        expected, name = record.split("  ", 1)
        path = ROOT / name
        if not path.is_file():
            raise SystemExit(f"MISSING: {name}")
        actual = hashlib.sha256(path.read_bytes()).hexdigest()
        if actual != expected:
            raise SystemExit(f"HASH MISMATCH: {name}")
    print(f"PASS: {len(records)} archived files match MANIFEST.sha256")

if __name__ == "__main__":
    main()
