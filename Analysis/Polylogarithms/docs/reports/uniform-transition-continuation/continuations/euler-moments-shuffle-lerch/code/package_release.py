#!/usr/bin/env python3
"""Write the release hash manifest and a ZIP containing only deliverables."""
from __future__ import annotations

import hashlib
from pathlib import Path
import zipfile

ROOT = Path(__file__).resolve().parents[1]
EXCLUDED_SUFFIXES = {".aux", ".log", ".out", ".toc", ".fls", ".fdb_latexmk", ".synctex.gz", ".pyc"}


def release_files():
    return sorted(p for p in ROOT.rglob("*") if p.is_file()
                  and "__pycache__" not in p.parts
                  and p.suffix not in EXCLUDED_SUFFIXES
                  and not p.name.endswith(".synctex.gz")
                  and p.name != "MANIFEST.sha256")


def main():
    files = release_files()
    manifest = ROOT / "MANIFEST.sha256"
    manifest.write_text("".join(
        f"{hashlib.sha256(p.read_bytes()).hexdigest()}  {p.relative_to(ROOT).as_posix()}\n"
        for p in files
    ))
    dest = ROOT.parent / "proveit_polylogarithms_research_2026-10-10.zip"
    with zipfile.ZipFile(dest, "w", compression=zipfile.ZIP_DEFLATED, compresslevel=9) as archive:
        for p in [*files, manifest]:
            info = zipfile.ZipInfo(f"{ROOT.name}/{p.relative_to(ROOT).as_posix()}")
            info.date_time = (2026, 10, 10, 12, 0, 0)
            info.compress_type = zipfile.ZIP_DEFLATED
            info.external_attr = 0o100644 << 16
            archive.writestr(info, p.read_bytes())
    with zipfile.ZipFile(dest) as archive:
        assert archive.testzip() is None
        assert len(archive.namelist()) == len(files) + 1
    print(f"Created {dest.name}: {len(files)+1} files, {dest.stat().st_size} bytes")
    print(f"SHA256 {hashlib.sha256(dest.read_bytes()).hexdigest()}")


if __name__ == "__main__":
    main()
