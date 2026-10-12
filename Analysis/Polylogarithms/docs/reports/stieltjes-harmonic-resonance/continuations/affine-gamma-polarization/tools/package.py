#!/usr/bin/env python3
"""Create a clean source/PDF/replay ZIP with a SHA-256 manifest.

This script packages existing outputs. Build and verify them first.
"""
from __future__ import annotations
import argparse
import hashlib
from pathlib import Path
import zipfile

ROOT = Path(__file__).resolve().parents[1]
EXCLUDED_DIRS = {"build", "__pycache__", ".git"}
EXCLUDED_SUFFIXES = {".aux", ".log", ".out", ".toc", ".fls", ".fdb_latexmk", ".pyc", ".synctex.gz"}


def files() -> list[Path]:
    return sorted(p for p in ROOT.rglob("*") if p.is_file()
                  and not any(part in EXCLUDED_DIRS for part in p.relative_to(ROOT).parts)
                  and p.suffix not in EXCLUDED_SUFFIXES
                  and not p.name.endswith(".synctex.gz") and p.name != "SHA256SUMS")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path,
                        default=ROOT.parent / "ProveIt_Affine_Gamma_Polarization_2026-10-11.zip")
    args = parser.parse_args()
    output = args.output.resolve()
    if output.is_relative_to(ROOT):
        raise SystemExit("Place the ZIP outside its source directory.")
    for required in ["article.pdf", "article.tex", "standalone.tex", "data/verification_summary.json"]:
        if not (ROOT / required).is_file():
            raise SystemExit(f"Missing required artifact: {required}")
    selected = files()
    manifest = "".join(f"{hashlib.sha256(p.read_bytes()).hexdigest()}  {p.relative_to(ROOT).as_posix()}\n" for p in selected)
    (ROOT / "SHA256SUMS").write_text(manifest)
    output.parent.mkdir(parents=True, exist_ok=True)
    with zipfile.ZipFile(output, "w", compression=zipfile.ZIP_DEFLATED, compresslevel=9) as archive:
        for p in selected + [ROOT / "SHA256SUMS"]:
            archive.write(p, Path(ROOT.name) / p.relative_to(ROOT))
    with zipfile.ZipFile(output) as archive:
        if archive.testzip() is not None:
            raise SystemExit("ZIP integrity check failed.")
    print(f"Wrote {output} ({output.stat().st_size:,} bytes; {len(selected)+1} files)")


if __name__ == "__main__":
    main()
