#!/usr/bin/env python3
"""Package the report, sources, exact checks, and recorded verification.

Run only after building report.pdf and running code/verify.py.  Temporary
LaTeX files, local build directories, and Python bytecode are excluded.
"""
from __future__ import annotations

import hashlib
from pathlib import Path
import shutil
import zipfile

ROOT = Path(__file__).resolve().parents[1]
NAME = "euclidean_geometry_ipra_2026-11-22"
DIRECTORIES = ("chapters", "lean", "code", "certificates", "figures", "sources", "verification")
TOP_FILES = ("README.md", "report.tex", "report.pdf", "build_report.sh", "requirements.txt")


def files() -> list[Path]:
    result = [ROOT / name for name in TOP_FILES]
    for name in DIRECTORIES:
        for path in (ROOT / name).rglob("*"):
            relative = path.relative_to(ROOT / name)
            if not path.is_file() or any(part in ("__pycache__", "build", ".lake", "tmp") for part in relative.parts):
                continue
            if path.suffix in (".pyc", ".olean", ".ilean", ".aux", ".fdb_latexmk", ".fls"):
                continue
            result.append(path)
    for path in result:
        if not path.is_file():
            raise SystemExit(f"Missing release input: {path.relative_to(ROOT)}")
    return sorted(result, key=lambda p: p.relative_to(ROOT).as_posix())


def main() -> None:
    inputs = files()
    manifest = ROOT / "SHA256SUMS"
    manifest.write_text("".join(
        f"{hashlib.sha256(path.read_bytes()).hexdigest()}  {path.relative_to(ROOT).as_posix()}\n"
        for path in inputs
    ), encoding="utf-8")
    output = ROOT.parent / "output"
    output.mkdir(exist_ok=True)
    pdf = output / f"{NAME}.pdf"
    archive = output / f"{NAME}.zip"
    shutil.copy2(ROOT / "report.pdf", pdf)
    with zipfile.ZipFile(archive, "w", compression=zipfile.ZIP_DEFLATED, compresslevel=9) as z:
        for path in [*inputs, manifest]:
            z.write(path, f"{NAME}/{path.relative_to(ROOT).as_posix()}")
    with zipfile.ZipFile(archive) as z:
        bad = z.testzip()
        if bad is not None:
            raise SystemExit(f"Archive checksum failed: {bad}")
    print(f"Archive: {archive} ({archive.stat().st_size} bytes; {len(inputs)+1} files)")
    print(f"PDF: {pdf} ({pdf.stat().st_size} bytes)")
    print(f"SHA256: {hashlib.sha256(archive.read_bytes()).hexdigest()}")


if __name__ == "__main__":
    main()
