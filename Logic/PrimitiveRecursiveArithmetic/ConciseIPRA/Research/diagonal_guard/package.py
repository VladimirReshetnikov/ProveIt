#!/usr/bin/env python3
"""Build the deliverable ZIP and verify its integrity manifest.

Run after tests/reproduce.py and build.py when updating the package.
The archive is deterministic for fixed input files under the same zlib.
"""

from pathlib import Path
import argparse
import hashlib
import json
import zipfile


ROOT = Path(__file__).resolve().parent
STAMP = (2026, 11, 11, 0, 0, 0)
PREFIX = "ipra_diagonal_guard"


def included(path):
    relative = path.relative_to(ROOT)
    return (
        path.is_file()
        and "__pycache__" not in relative.parts
        and not any(part.startswith(".") for part in relative.parts)
        and "pending" not in path.name
        and path.suffix not in {".pyc", ".aux", ".log", ".out", ".toc", ".zip"}
        and path.name != "MANIFEST.sha256"
    )


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--output", type=Path,
        default=ROOT.parent / "output" / "ipra_diagonal_guard_2026-11-11.zip",
    )
    args = parser.parse_args()
    files = sorted(path for path in ROOT.rglob("*") if included(path))
    entries = {
        str(path.relative_to(ROOT)): hashlib.sha256(path.read_bytes()).hexdigest()
        for path in files
    }
    manifest = ROOT / "MANIFEST.sha256"
    manifest.write_text(
        "".join(f"{digest}  {name}\n" for name, digest in entries.items()),
        encoding="utf-8",
    )
    args.output.parent.mkdir(parents=True, exist_ok=True)
    with zipfile.ZipFile(args.output, "w", compression=zipfile.ZIP_DEFLATED,
                         compresslevel=9) as archive:
        for path in sorted(files + [manifest]):
            info = zipfile.ZipInfo(f"{PREFIX}/{path.relative_to(ROOT)}", STAMP)
            info.compress_type = zipfile.ZIP_DEFLATED
            info.create_system = 3
            info.external_attr = 0o100644 << 16
            archive.writestr(info, path.read_bytes(), compresslevel=9)
    with zipfile.ZipFile(args.output) as archive:
        assert archive.testzip() is None, "ZIP CRC failure"
        assert len(archive.namelist()) == len(entries) + 1
        for name, digest in entries.items():
            assert hashlib.sha256(archive.read(f"{PREFIX}/{name}")).hexdigest() == digest
        assert archive.read(f"{PREFIX}/MANIFEST.sha256") == manifest.read_bytes()
    print(json.dumps({
        "archive": str(args.output.resolve()),
        "bytes": args.output.stat().st_size,
        "sha256": hashlib.sha256(args.output.read_bytes()).hexdigest(),
        "files_including_manifest": len(entries) + 1,
        "zip_crc_and_manifest": "passed",
    }, indent=2))


if __name__ == "__main__":
    main()
