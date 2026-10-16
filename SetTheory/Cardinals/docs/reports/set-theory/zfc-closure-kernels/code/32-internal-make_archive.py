#!/usr/bin/env python3
"""Create the research archive after generating and checking its manifest.

The output must be outside this source directory and must not already exist.
The archive uses sorted entries, fixed timestamps and preserved source bytes.
ZIP compression may differ across zlib versions; file hashes are authoritative.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import zipfile

ROOT = Path(__file__).resolve().parent
REPORT = "zfc_small_machine_report"
BUILD_SUFFIXES = {".aux", ".fdb_latexmk", ".fls", ".log", ".toc", ".out", ".synctex.gz"}


def included(path: Path) -> bool:
    rel = path.relative_to(ROOT)
    if not path.is_file() or path.is_symlink():
        return False
    if "__pycache__" in rel.parts or path.suffix in {".pyc", ".olean", ".ilean"}:
        return False
    if path.parent == ROOT and path.name.startswith(REPORT):
        if any(path.name == REPORT + suffix for suffix in BUILD_SUFFIXES):
            return False
    return rel.as_posix() != "MANIFEST.json"


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    output = args.output.resolve()
    if output.exists():
        parser.error("output already exists")
    if output.is_relative_to(ROOT):
        parser.error("output must be outside the source directory")
    files = sorted((p for p in ROOT.rglob("*") if included(p)),
                   key=lambda p: p.relative_to(ROOT).as_posix())
    entries = []
    for path in files:
        data = path.read_bytes()
        entries.append({"path": path.relative_to(ROOT).as_posix(),
                        "bytes": len(data),
                        "sha256": hashlib.sha256(data).hexdigest()})
    manifest = {
        "format": "zfc-small-machine-research-manifest-v1",
        "audit_date": "2026-10-16",
        "proveit_pin": "4747142d5d15213eb711bdadfa3cc7e769fcb7a7",
        "public253_pin": "0d544f2a2e3c18f12278441a74b7879f31cbe856",
        "new_sub253_consistency_machine_claim": False,
        "scope": "Exact package file integrity; does not itself prove any theorem.",
        "files": entries,
    }
    mf = ROOT / "MANIFEST.json"
    mf.write_text(json.dumps(manifest, indent=2) + "\n")
    subprocess.run([sys.executable, "-I", "-B", str(ROOT / "verify_package.py")],
                   check=True)
    output.parent.mkdir(parents=True, exist_ok=True)
    with zipfile.ZipFile(output, "x", compression=zipfile.ZIP_DEFLATED,
                         compresslevel=9) as archive:
        for path in sorted(files + [mf], key=lambda p: p.relative_to(ROOT).as_posix()):
            name = ROOT.name + "/" + path.relative_to(ROOT).as_posix()
            info = zipfile.ZipInfo(name, date_time=(2026, 10, 16, 0, 0, 0))
            info.compress_type = zipfile.ZIP_DEFLATED
            info.create_system = 3
            info.external_attr = 0o100644 << 16
            archive.writestr(info, path.read_bytes(), compress_type=zipfile.ZIP_DEFLATED,
                             compresslevel=9)
    data = output.read_bytes()
    print(json.dumps({"archive": str(output), "archive_bytes": len(data),
                      "archive_sha256": hashlib.sha256(data).hexdigest(),
                      "files_in_archive": len(files) + 1,
                      "source_bytes": sum(x["bytes"] for x in entries)}, indent=2))


if __name__ == "__main__":
    main()
