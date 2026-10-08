#!/usr/bin/env python3
"""Verify the distributed files before modifying them or regenerating results."""
from __future__ import annotations
import hashlib
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def main():
    failures = []
    checked = 0
    for line in (ROOT / "SHA256SUMS").read_text(encoding="utf-8").splitlines():
        if not line:
            continue
        expected, relative = line.split("  ", 1)
        name = Path(relative)
        if name.is_absolute() or ".." in name.parts:
            raise SystemExit(f"Invalid manifest path: {relative}")
        path = ROOT / name
        actual = hashlib.sha256(path.read_bytes()).hexdigest() if path.is_file() else None
        if actual != expected:
            failures.append(relative)
        checked += 1
    if failures:
        raise SystemExit("Changed or missing files:\n" + "\n".join(failures))
    print(f"All {checked} distributed file hashes match.")


if __name__ == "__main__":
    main()
