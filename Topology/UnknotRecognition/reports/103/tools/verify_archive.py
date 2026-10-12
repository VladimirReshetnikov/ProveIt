#!/usr/bin/env python3
"""Verify the package checksums and internal source-manifest consistency."""
import argparse
import hashlib
import json
from pathlib import Path


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--package", type=Path, default=Path(__file__).resolve().parents[1])
    args = parser.parse_args()
    root = args.package.resolve(strict=True)
    checked = 0
    for line in (root / "SHA256SUMS.txt").read_text().splitlines():
        wanted, relative = line.split("  ", 1)
        path = (root / relative).resolve(strict=True)
        if not path.is_relative_to(root) or not path.is_file():
            raise ValueError(f"Invalid package path: {relative}")
        if digest(path) != wanted:
            raise ValueError(f"Checksum mismatch: {relative}")
        checked += 1
    manifest = json.loads((root / "integration/manifest.json").read_text())
    if digest(root / "integration/proveit-relative-top-handles.patch") != manifest["patch_sha256"]:
        raise ValueError("Patch differs from its source manifest")
    for row in manifest["files"]:
        path = root / "integration/overlay" / row["path"]
        if path.stat().st_size != row["bytes"] or digest(path) != row["sha256"]:
            raise ValueError(f"Overlay mismatch: {row['path']}")
    print(json.dumps({"verified_package_files": checked,
                      "verified_source_files": len(manifest["files"]),
                      "base_commit": manifest["base_commit"], "success": True}, indent=2))


if __name__ == "__main__":
    main()
