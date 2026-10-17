#!/usr/bin/env python3
"""Create the report archive and its exact file manifest.

Run on the finalized bundle. The output ZIP must be outside it.
This records byte identities; it does not certify mathematical claims.
"""
from pathlib import Path
import argparse
import hashlib
import json
import zipfile

ROOT = Path(__file__).resolve().parents[1]
PREFIX = "zfc_consistency_research_2026-10-17"
EXCLUDED_SUFFIXES = {".aux", ".log", ".out", ".toc", ".fls", ".fdb_latexmk", ".pyc"}


def included(path):
    relative = path.relative_to(ROOT)
    return (path.is_file() and "__pycache__" not in relative.parts
            and not any(x.startswith(".") for x in relative.parts)
            and path.suffix not in EXCLUDED_SUFFIXES
            and relative.as_posix() != "MANIFEST.json")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    target = args.output.resolve()
    if target.is_relative_to(ROOT):
        raise SystemExit("ZIP output must be outside the report bundle")
    if target.exists():
        raise SystemExit("Refusing to overwrite an existing archive")
    files = sorted(p for p in ROOT.rglob("*") if included(p))
    manifest = {
        "title": "Toward a Smaller Con(ZFC) Machine",
        "date_utc": "2026-10-17",
        "scope": "Ordinary proofs and finite diagnostics. No new calibrated "
                 "sub-253-state machine, new kernel theorem, or serialized ZFC proof.",
        "proveit_primary_pin": "3d731d8cf44941560752abc625149f7bfa109930",
        "proveit_novelty_pin": "ba00775e2bf56b184d071346867db74f2eb0c621",
        "upstream_merged_pin": "297ab8df7e5de329605c3875b4934643b371a5e3",
        "public253_head": "0d544f2a2e3c18f12278441a74b7879f31cbe856",
        "archive_root": PREFIX,
        "exclusions": "LaTeX temporary files, caches, hidden files; manifest "
                      "does not hash itself.",
        "files": [{"path": p.relative_to(ROOT).as_posix(),
                   "bytes": p.stat().st_size,
                   "sha256": hashlib.sha256(p.read_bytes()).hexdigest()}
                  for p in files]}
    manifest_path = ROOT / "MANIFEST.json"
    manifest_path.write_text(json.dumps(manifest, indent=2) + "\n")
    files.append(manifest_path)
    target.parent.mkdir(parents=True, exist_ok=True)
    with zipfile.ZipFile(target, "x", compression=zipfile.ZIP_DEFLATED,
                         compresslevel=9) as archive:
        for path in sorted(files):
            entry = zipfile.ZipInfo(PREFIX + "/" + path.relative_to(ROOT).as_posix(),
                                    date_time=(2026, 10, 17, 0, 0, 0))
            entry.create_system = 3
            entry.external_attr = 0o100644 << 16
            entry.compress_type = zipfile.ZIP_DEFLATED
            archive.writestr(entry, path.read_bytes(), compresslevel=9)
    with zipfile.ZipFile(target) as archive:
        failure = archive.testzip()
        if failure:
            raise SystemExit("ZIP CRC failure: " + failure)
        for row in manifest["files"]:
            data = archive.read(PREFIX + "/" + row["path"])
            if hashlib.sha256(data).hexdigest() != row["sha256"]:
                raise SystemExit("ZIP identity mismatch: " + row["path"])
    print(json.dumps({"archive": str(target), "files": len(files),
                      "bytes": target.stat().st_size,
                      "sha256": hashlib.sha256(target.read_bytes()).hexdigest(),
                      "status": "passed"}, indent=2))


if __name__ == "__main__":
    main()

