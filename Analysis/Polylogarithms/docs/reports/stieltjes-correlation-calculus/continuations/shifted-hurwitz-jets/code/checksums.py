#!/usr/bin/env python3
"""Create or verify SHA256SUMS for this delivered package."""
from __future__ import annotations
import argparse, hashlib
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
MANIFEST = ROOT / "SHA256SUMS"

def digest(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1024 * 1024), b""):
            h.update(block)
    return h.hexdigest()

def eligible(path: Path) -> bool:
    return (path.is_file() and path != MANIFEST
            and "__pycache__" not in path.parts and path.suffix != ".pyc")

def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--verify", action="store_true")
    args = parser.parse_args()
    if args.verify:
        if not MANIFEST.exists():
            raise SystemExit("SHA256SUMS is missing.")
        count = 0
        for line in MANIFEST.read_text().splitlines():
            expected, name = line.split("  ", 1)
            path = ROOT / name
            if not path.is_file() or digest(path) != expected:
                raise SystemExit(f"Checksum mismatch or missing file: {name}")
            count += 1
        print(f"Verified {count} checksums.")
    else:
        paths = sorted((p for p in ROOT.rglob("*") if eligible(p)),
                       key=lambda p: p.relative_to(ROOT).as_posix())
        MANIFEST.write_text("".join(f"{digest(p)}  {p.relative_to(ROOT).as_posix()}\n" for p in paths))
        print(f"Wrote {len(paths)} checksums.")

if __name__ == "__main__":
    main()
