#!/usr/bin/env python3
"""Verify the byte identity of the upstream source files used in the report."""
import argparse
import hashlib
import json
from pathlib import Path
from urllib.request import urlopen

COMMIT = "72fead102f663d5c7a407964a13dc0cf9d977207"
BASE_URL = f"https://raw.githubusercontent.com/lsernau/grh-lean/{COMMIT}/"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--checkout", type=Path,
                        help="read local checkout bytes (default: fetch the pinned GitHub files)")
    args = parser.parse_args()
    paths = json.loads(Path(__file__).with_name("upstream_blobs.json").read_text())
    for path, expected in paths.items():
        if args.checkout is None:
            with urlopen(BASE_URL + path, timeout=60) as response:
                data = response.read()
        else:
            data = (args.checkout / path).read_bytes()
        header = f"blob {len(data)}".encode("ascii") + b"\0"
        actual = hashlib.sha1(header + data).hexdigest()
        if actual != expected:
            raise SystemExit(f"Mismatch for {path}: expected {expected}, found {actual}")
        print(actual, path)
    print(f"Verified {len(paths)} source blobs at {COMMIT}.")


if __name__ == "__main__":
    main()
