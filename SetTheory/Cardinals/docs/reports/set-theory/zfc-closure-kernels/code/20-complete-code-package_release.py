#!/usr/bin/env python3
"""Package the finished report and research artifacts with a hash manifest.

Build report.pdf first. This command inventories files; it does not rerun
mathematical checks or proof assistants. The output ZIP must be outside the
source directory and must not already exist.
"""
from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path
import zipfile


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    out = args.output.resolve()
    if out.is_relative_to(root):
        raise SystemExit("ZIP output must be outside the source directory")
    if out.exists():
        raise SystemExit("Refusing to overwrite an existing release ZIP")
    if not (root / "report.pdf").is_file():
        raise SystemExit("Build report.pdf before packaging")
    excluded_suffixes = {".pyc", ".aux", ".out", ".toc", ".fls", ".fdb_latexmk", ".synctex"}
    files = [p for p in sorted(root.rglob("*")) if p.is_file()
             and "__pycache__" not in p.parts and p.suffix not in excluded_suffixes
             and p.name not in {"MANIFEST.json", "report.log", "report.synctex.gz"}]
    manifest = {"format": 1, "report_date": "2026-10-16",
                "scope": "File integrity inventory; no new formal endpoint certification",
                "self_excluded": "MANIFEST.json", "files": []}
    for path in files:
        data = path.read_bytes()
        manifest["files"].append({"path": path.relative_to(root).as_posix(),
                                  "bytes": len(data),
                                  "sha256": hashlib.sha256(data).hexdigest()})
    manifest_path = root / "MANIFEST.json"
    manifest_path.write_text(json.dumps(manifest, indent=2, ensure_ascii=False) + "\n")
    out.parent.mkdir(parents=True, exist_ok=True)
    with zipfile.ZipFile(out, "x", compression=zipfile.ZIP_DEFLATED, compresslevel=9) as archive:
        for path in sorted([*files, manifest_path]):
            name = root.name + "/" + path.relative_to(root).as_posix()
            entry = zipfile.ZipInfo(name, date_time=(2026, 10, 16, 0, 0, 0))
            entry.compress_type = zipfile.ZIP_DEFLATED
            entry.create_system = 3
            entry.external_attr = 0o100644 << 16
            archive.writestr(entry, path.read_bytes(), compress_type=zipfile.ZIP_DEFLATED, compresslevel=9)
    with zipfile.ZipFile(out) as archive:
        bad = archive.testzip()
        if bad:
            raise ValueError("ZIP integrity failure: " + bad)
        for record in manifest["files"]:
            data = archive.read(root.name + "/" + record["path"])
            if len(data) != record["bytes"] or hashlib.sha256(data).hexdigest() != record["sha256"]:
                raise ValueError("Archived bytes disagree with manifest: " + record["path"])
    print(json.dumps({"archive": str(out), "files": len(files) + 1,
                      "bytes": out.stat().st_size,
                      "sha256": hashlib.sha256(out.read_bytes()).hexdigest(),
                      "zip_crc_and_manifest": "PASS"}, indent=2))


if __name__ == "__main__":
    main()
