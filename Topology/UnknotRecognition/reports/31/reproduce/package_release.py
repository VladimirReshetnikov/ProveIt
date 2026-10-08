#!/usr/bin/env python3
"""Build and verify the research ZIP with a complete SHA-256 file manifest."""

import argparse
import hashlib
import json
from pathlib import Path
import zipfile


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    root = args.root.resolve()
    output = (args.output or root.with_suffix(".zip")).resolve()
    if output.is_relative_to(root):
        parser.error("Write the ZIP outside the package directory.")
    generated = {"release-manifest.json", "SHA256SUMS"}
    tex_aux = {".aux", ".blg", ".fdb_latexmk", ".fls", ".log", ".toc", ".out"}

    def included(path):
        relative = path.relative_to(root)
        return (path.is_file() and relative.as_posix() not in generated
                and not any(part in {".git", "__pycache__"} for part in relative.parts)
                and path.suffix not in {".pyc", ".pyo"}
                and not (relative.parts[0] == "article" and path.suffix in tex_aux))

    paths = sorted(path for path in root.rglob("*") if included(path))
    records = [{"path": path.relative_to(root).as_posix(),
                "bytes": path.stat().st_size, "sha256": sha256(path)} for path in paths]
    manifest = {
        "schema": "proveit.unknot-research-release.v1",
        "release_date": "2026-10-08",
        "baseline": "8a95834940cf77cdab1b39571ffc102ca8b6bede",
        "title": "Certified primitives for faster unknot recognition",
        "article_pages": 38,
        "manifested_file_count": len(records),
        "archive_file_count": len(records) + len(generated),
        "manifested_uncompressed_bytes": sum(record["bytes"] for record in records),
        "manifest_exclusions": sorted(generated),
        "archive_exclusions": "TeX auxiliary files (except .bbl), Python caches, .git",
        "files": records,
    }
    (root / "release-manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
    (root / "SHA256SUMS").write_text("".join(
        f"{record['sha256']}  {record['path']}\n" for record in records))
    archive_paths = sorted(paths + [root / name for name in generated])
    with zipfile.ZipFile(output, "w", compression=zipfile.ZIP_DEFLATED,
                         compresslevel=9) as archive:
        for path in archive_paths:
            relative = Path(root.name) / path.relative_to(root)
            info = zipfile.ZipInfo(relative.as_posix(), (2026, 10, 8, 0, 0, 0))
            info.compress_type = zipfile.ZIP_DEFLATED
            info.create_system = 3
            info.external_attr = (0o100755 if path.suffix == ".sh" else 0o100644) << 16
            archive.writestr(info, path.read_bytes(), compresslevel=9)
    with zipfile.ZipFile(output) as archive:
        bad = archive.testzip()
        if bad is not None:
            raise RuntimeError(f"ZIP CRC failure: {bad}")
        assert len(archive.namelist()) == len(archive_paths)
        for record in records:
            data = archive.read(f"{root.name}/{record['path']}")
            if len(data) != record["bytes"] or hashlib.sha256(data).hexdigest() != record["sha256"]:
                raise RuntimeError(f"Archive hash mismatch: {record['path']}")
        for name in generated:
            assert archive.read(f"{root.name}/{name}") == (root / name).read_bytes()
    digest = sha256(output)
    output.with_suffix(output.suffix + ".sha256").write_text(f"{digest}  {output.name}\n")
    print(json.dumps({"archive": str(output), "bytes": output.stat().st_size,
                      "sha256": digest, "archive_files": len(archive_paths),
                      "crc_check": "passed", "every_member_hash": "passed"}, indent=2))


if __name__ == "__main__":
    main()
