#!/usr/bin/env python3
"""Create and verify a source/PDF ZIP with an internal SHA-256 manifest."""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import shutil
import zipfile

ROOT = Path(__file__).resolve().parents[1]
NAME = "ProveIt_UnknotRecognition_SymbolicCompression_2026-10-08"


def included(path):
    relative = path.relative_to(ROOT)
    if not path.is_file() or "__pycache__" in relative.parts or path.suffix == ".pyc":
        return False
    if relative.as_posix() == "MANIFEST.json":
        return False
    if relative.parts[0] == "article" and (path.suffix in {".aux", ".log", ".out", ".toc", ".new"}
                                          or path.name.startswith("build_pass_")):
        return False
    return True


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-directory", type=Path, default=ROOT.parent)
    arguments = parser.parse_args()
    arguments.output_directory.mkdir(parents=True, exist_ok=True)
    files = sorted(p for p in ROOT.rglob("*") if included(p))
    manifest = {"format_version": 1,
                "base_commit": "d54009df0ea3751b8662bb76549d3c1bb0eec19c",
                "manifest_excludes_itself": True,
                "files": [{"path": p.relative_to(ROOT).as_posix(),
                           "size_bytes": p.stat().st_size,
                           "sha256": hashlib.sha256(p.read_bytes()).hexdigest()} for p in files]}
    manifest_path = ROOT / "MANIFEST.json"
    manifest_path.write_text(json.dumps(manifest, indent=2) + "\n")
    files.append(manifest_path)
    target = arguments.output_directory / (NAME + ".zip")
    with zipfile.ZipFile(target, "w", compression=zipfile.ZIP_DEFLATED, compresslevel=9) as archive:
        for path in sorted(files):
            name = ROOT.name + "/" + path.relative_to(ROOT).as_posix()
            info = zipfile.ZipInfo(name, date_time=(2026, 10, 8, 0, 0, 0))
            info.compress_type = zipfile.ZIP_DEFLATED
            info.external_attr = 0o100644 << 16
            archive.writestr(info, path.read_bytes(), compress_type=zipfile.ZIP_DEFLATED,
                             compresslevel=9)
    with zipfile.ZipFile(target) as archive:
        bad = archive.testzip()
        if bad is not None:
            raise RuntimeError("ZIP CRC failed for " + bad)
        for record in manifest["files"]:
            data = archive.read(ROOT.name + "/" + record["path"])
            if len(data) != record["size_bytes"] or hashlib.sha256(data).hexdigest() != record["sha256"]:
                raise RuntimeError("Manifest verification failed for " + record["path"])
        if len(archive.namelist()) != len(files):
            raise RuntimeError("Unexpected archive entry count")
    pdf = arguments.output_directory / (NAME + ".pdf")
    shutil.copy2(ROOT / "article" / "unknot_symbolic_compression.pdf", pdf)
    print(json.dumps({"status": "PASS", "archive": str(target.resolve()),
                      "archive_files": len(files), "archive_bytes": target.stat().st_size,
                      "archive_sha256": hashlib.sha256(target.read_bytes()).hexdigest(),
                      "pdf": str(pdf.resolve()), "pdf_bytes": pdf.stat().st_size}, indent=2))


if __name__ == "__main__":
    main()
