#!/usr/bin/env python3
"""Check every delivered file against SHA256SUMS, without modifying files."""
from __future__ import annotations

import hashlib
from pathlib import Path


def main() -> None:
    root = Path(__file__).resolve().parent.parent
    seen: set[str] = set()
    errors: list[str] = []
    for line in (root / "SHA256SUMS").read_text(encoding="utf-8").splitlines():
        if not line.strip():
            continue
        expected, name = line.split("  ", 1)
        if name in seen:
            errors.append("Duplicate entry: " + name)
            continue
        seen.add(name)
        path = (root / name).resolve()
        if not path.is_relative_to(root) or not path.is_file():
            errors.append("Missing or invalid path: " + name)
            continue
        actual = hashlib.sha256(path.read_bytes()).hexdigest()
        if actual != expected:
            errors.append("Digest differs: " + name)
    if errors:
        raise SystemExit("\n".join(errors))
    print(f"All {len(seen)} delivered file digests match.")


if __name__ == "__main__":
    main()
