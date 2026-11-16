#!/usr/bin/env python3
from __future__ import annotations

import hashlib
from pathlib import Path

ROOT = Path(__file__).resolve().parent
OUT = ROOT / "MANIFEST.sha256"
EXCLUDED_NAMES = {
    "MANIFEST.sha256",
    "ocipra_framework_2026-11-15.zip",
}
EXCLUDED_SUFFIXES = {".pyc"}
EXCLUDED_DIRS = {"__pycache__", "rendered_pdf", "contact_sheets"}


def included(path: Path) -> bool:
    rel = path.relative_to(ROOT)
    if any(part in EXCLUDED_DIRS for part in rel.parts):
        return False
    if path.name in EXCLUDED_NAMES or path.suffix in EXCLUDED_SUFFIXES:
        return False
    if rel.parts and rel.parts[0] == "paper" and path.suffix in {".aux", ".log", ".out", ".toc"}:
        return False
    return path.is_file()


def digest(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            h.update(block)
    return h.hexdigest()


def main() -> None:
    rows = []
    for path in sorted(p for p in ROOT.rglob("*") if included(p)):
        rows.append(f"{digest(path)}  {path.relative_to(ROOT).as_posix()}")
    OUT.write_text("\n".join(rows) + "\n", encoding="utf-8")
    print(f"wrote {OUT.name} with {len(rows)} entries")


if __name__ == "__main__":
    main()
