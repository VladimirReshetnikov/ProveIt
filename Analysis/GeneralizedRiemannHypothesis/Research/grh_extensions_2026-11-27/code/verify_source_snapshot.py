#!/usr/bin/env python3
"""Verify the paper's inspected source-file hashes against a local ProveIt tree."""

from pathlib import Path
import argparse
import hashlib
import json
import sys


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("checkout", type=Path, help="Root of a local ProveIt checkout")
    args = parser.parse_args()
    manifest_path = Path(__file__).resolve().parents[1] / "provenance/source_snapshot.json"
    manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    failures = []
    for item in manifest["files"]:
        path = args.checkout / item["path"]
        if not path.is_file():
            failures.append((item["path"], "missing"))
            continue
        data = path.read_bytes()
        digest = hashlib.sha1(b"blob " + str(len(data)).encode("ascii") + b"\0" + data).hexdigest()
        if digest != item["git_blob_sha1"]:
            failures.append((item["path"], "content differs"))
    if failures:
        for path, status in failures:
            print(f"FAIL {status}: {path}")
        return 1
    print(f"PASS {len(manifest['files'])} source files match commit {manifest['commit']}")
    print("This is a content-hash check, not a Lean build or proof replay.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
