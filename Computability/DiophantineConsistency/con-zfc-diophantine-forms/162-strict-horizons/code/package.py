#!/usr/bin/env python3
"""Make the release manifest, deterministic ZIP, and standalone report PDF."""
from pathlib import Path
import hashlib
import json
import shutil
import zipfile

ROOT = Path(__file__).resolve().parents[1]
TEMP_SUFFIXES = {".aux", ".log", ".out", ".toc", ".fls", ".fdb_latexmk", ".pyc"}


def included():
    return sorted(p for p in ROOT.rglob("*") if p.is_file()
                  and "__pycache__" not in p.parts
                  and p.suffix not in TEMP_SUFFIXES)


def main():
    manifest = ROOT / "MANIFEST.sha256"
    manifest.write_text("".join(
        hashlib.sha256(p.read_bytes()).hexdigest() + "  "
        + p.relative_to(ROOT).as_posix() + "\n"
        for p in included() if p != manifest))
    target = ROOT.parent / (ROOT.name + ".zip")
    with zipfile.ZipFile(target, "w", compression=zipfile.ZIP_DEFLATED,
                         compresslevel=9) as archive:
        for path in included():
            name = ROOT.name + "/" + path.relative_to(ROOT).as_posix()
            info = zipfile.ZipInfo(name, date_time=(2026, 10, 25, 0, 0, 0))
            info.compress_type = zipfile.ZIP_DEFLATED
            info.create_system = 3
            info.external_attr = 0o100644 << 16
            archive.writestr(info, path.read_bytes(), compresslevel=9)
    with zipfile.ZipFile(target) as archive:
        bad = archive.testzip()
        if bad is not None:
            raise ValueError("ZIP integrity failure: " + bad)
        count = len(archive.infolist())
    pdf = ROOT.parent / (ROOT.name + ".pdf")
    shutil.copyfile(ROOT / "report/main.pdf", pdf)
    print(json.dumps({
        "status": "PASS", "archive": str(target),
        "archive_bytes": target.stat().st_size,
        "archive_sha256": hashlib.sha256(target.read_bytes()).hexdigest(),
        "archive_files": count, "pdf": str(pdf),
        "pdf_bytes": pdf.stat().st_size,
        "pdf_sha256": hashlib.sha256(pdf.read_bytes()).hexdigest(),
    }, indent=2))


if __name__ == "__main__":
    main()
