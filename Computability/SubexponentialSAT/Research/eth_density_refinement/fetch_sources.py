#!/usr/bin/env python3
"""Fetch and verify the pinned upstream TeX files from source_manifest.json."""
from pathlib import Path
import argparse
import hashlib
import json
import urllib.request

ROOT = Path(__file__).resolve().parent

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--destination", type=Path, default=ROOT / "upstream")
    args = parser.parse_args()
    manifest = json.loads((ROOT / "source_manifest.json").read_text(encoding="utf-8"))
    destination = args.destination.resolve()
    destination.mkdir(parents=True, exist_ok=True)
    for record in manifest["upstream_files"]:
        relative = Path(record["local_name"])
        if relative.is_absolute() or ".." in relative.parts:
            raise ValueError("Manifest contains an unsafe relative path")
        target = destination / relative
        if target.exists():
            raise FileExistsError(f"Refusing to overwrite {target}")
        with urllib.request.urlopen(record["raw_url"], timeout=60) as response:
            data = response.read()
        header = b"blob " + str(len(data)).encode("ascii") + b"\0"
        assert hashlib.sha1(header + data).hexdigest() == record["git_blob_sha1"]
        assert hashlib.sha256(data).hexdigest() == record["sha256"]
        assert len(data) == record["size_bytes"]
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(data)
        print("Verified", relative)
    print("All pinned source files verified.")

if __name__ == "__main__":
    main()

