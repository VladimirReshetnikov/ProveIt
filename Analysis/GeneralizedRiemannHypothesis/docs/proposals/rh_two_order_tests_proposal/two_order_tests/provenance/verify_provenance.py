#!/usr/bin/env python3
"""Verify archived source/proposal provenance against a local ProveIt checkout.

Usage: python3 verify_provenance.py /path/to/ProveIt
Uses only the Python standard library and does not invoke Lean.
"""
from __future__ import annotations
import argparse
import csv
import hashlib
from pathlib import Path

COMMIT = "89d12dd40424f1217fd818d84877b3da52396a3b"


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("checkout", type=Path)
    parser.add_argument("--manifest-dir", type=Path, default=Path(__file__).resolve().parent)
    args = parser.parse_args()
    seen = {}
    rows_count = 0
    directories = set()
    for name, separator in [("source_anchors.tsv", "\t"), ("proposal_inventory.csv", ",")]:
        with (args.manifest_dir / name).open(newline="") as stream:
            rows = list(csv.DictReader(stream, delimiter=separator))
        for row in rows:
            rows_count += 1
            assert row["commit"] == COMMIT, (name, "unexpected commit")
            relative = Path(row["path"])
            assert not relative.is_absolute() and ".." not in relative.parts
            data = (args.checkout / relative).read_bytes()
            digest = hashlib.sha256(data).hexdigest()
            assert digest == row["sha256"], (str(relative), "SHA-256 mismatch")
            blob = hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()
            assert blob == row["git_blob_sha1"], (str(relative), "Git blob mismatch")
            if "line" in row:
                assert 1 <= int(row["line"]) <= len(data.splitlines())
            if "directory" in row:
                directories.add(row["directory"])
            if str(relative) in seen:
                assert seen[str(relative)] == digest
            seen[str(relative)] = digest
    assert len(directories) == 5
    print(f"Verified {rows_count} provenance records, {len(seen)} distinct source files, and all five proposal directories.")
    print("Every recorded SHA-256 and Git blob SHA-1 matches. No Lean compilation was attempted.")


if __name__ == "__main__":
    main()
