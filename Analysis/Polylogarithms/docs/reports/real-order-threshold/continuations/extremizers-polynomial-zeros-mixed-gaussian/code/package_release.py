#!/usr/bin/env python3
"""Create the payload manifest and review ZIP; no repository/network operations."""
from hashlib import sha256
from pathlib import Path
from zipfile import ZipFile, ZipInfo, ZIP_DEFLATED

BASE = Path(__file__).resolve().parents[1]
ZIP_NAME = "ProveIt_Polylogarithms_Extremizers_Zeros_2026-10-10.zip"
TOP = "polylogarithms_extremizers_zeros_20261010"
SUFFIXES = {".tex", ".pdf", ".png", ".py", ".json", ".md", ".txt"}
NAMES = {"Makefile", "LICENSE"}


def main():
    pdf = BASE / "article.pdf"
    if not pdf.is_file() or not pdf.read_bytes().startswith(b"%PDF-"):
        raise RuntimeError("Build article.pdf before packaging")
    files = sorted(
        f for f in BASE.rglob("*")
        if f.is_file()
        and "__pycache__" not in f.parts
        and not any(p.startswith(".") for p in f.relative_to(BASE).parts)
        and (f.suffix in SUFFIXES or f.name in NAMES)
    )
    manifest = BASE / "MANIFEST.sha256"
    manifest.write_text("".join(
        sha256(f.read_bytes()).hexdigest() + "  " +
        f.relative_to(BASE).as_posix() + "\n" for f in files))
    target = BASE.parent / ZIP_NAME
    with ZipFile(target, "w", compression=ZIP_DEFLATED, compresslevel=9) as archive:
        for f in files + [manifest]:
            entry = ZipInfo(TOP + "/" + f.relative_to(BASE).as_posix(),
                            date_time=(2026, 10, 10, 0, 0, 0))
            entry.compress_type = ZIP_DEFLATED
            entry.external_attr = 0o100644 << 16
            archive.writestr(entry, f.read_bytes(), compress_type=ZIP_DEFLATED,
                             compresslevel=9)
    print(f"Packaged {len(files) + 1} files: {target}")


if __name__ == "__main__":
    main()
