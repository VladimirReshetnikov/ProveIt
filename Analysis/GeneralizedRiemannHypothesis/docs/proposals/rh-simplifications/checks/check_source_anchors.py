#!/usr/bin/env python3
"""Check Lean source anchors offline against a readable grh package, using Python 3.

Usage:
    python3 check_source_anchors.py /path/to/grh-lean/grh

Keep source-anchors.tsv alongside this program. The pinned source is available at
https://github.com/lsernau/grh-lean/tree/72fead102f663d5c7a407964a13dc0cf9d977207/grh
with the equivalent ProveIt URLs in the table. This verifies bytes and declaration
locations. Formal proof checking requires the project's pinned Lean toolchain.
"""
import argparse
import csv
import hashlib
import json
import re
from pathlib import Path

COMMIT = "d8415e76ad850651f8c0083afe689dd9f4a45a10"
BASE_URL = (
    "https://github.com/VladimirReshetnikov/ProveIt/blob/"
    + COMMIT
    + "/Analysis/GeneralizedRiemannHypothesis/vendor/grh-lean/grh"
)
MATHLIB = "56a005855ea17e0b0958f73ec801ae140b0a1679"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("package", type=Path, help="grh directory containing src/")
    args = parser.parse_args()
    table = Path(__file__).with_name("source-anchors.tsv")
    cached = {}
    n = 0
    try:
        with table.open(encoding="utf-8", newline="") as stream:
            for row in csv.DictReader(stream, delimiter="\t"):
                path = row["path"]
                if path not in cached:
                    data = (args.package / path).read_bytes()
                    header = b"blob " + str(len(data)).encode("ascii") + b"\0"
                    cached[path] = (
                        hashlib.sha1(header + data).hexdigest(),
                        data.decode("utf-8").splitlines(),
                    )
                sha, lines = cached[path]
                line = int(row["line"])
                if sha != row["git_blob_sha1"]:
                    raise ValueError(f"{path}: Git blob differs")
                if row["permalink"] != f"{BASE_URL}/{path}#L{line}":
                    raise ValueError(f"{path}:{line}: permalink differs")
                name = re.escape(row["declaration"])
                decl = rf"^\s*(?:(?:protected|private|noncomputable)\s+)*(?:def|theorem|lemma|structure|abbrev)\s+{name}(?=\s|:|\{{)"
                if not 1 <= line <= len(lines) or not re.match(decl, lines[line - 1]):
                    raise ValueError(f"{path}:{line}: declaration {row['declaration']} missing")
                n += 1
        if not n:
            raise ValueError("source map has no entries")
        toolchain = (args.package / "lean-toolchain").read_text().strip()
        packages = json.loads((args.package / "lake-manifest.json").read_text())["packages"]
        revisions = [p["rev"] for p in packages if p["name"] == "mathlib"]
        if toolchain != "leanprover/lean4:v4.35.0" or revisions != [MATHLIB]:
            raise ValueError("Lean or Mathlib version differs")
    except (OSError, KeyError, ValueError) as error:
        parser.exit(1, f"Source verification failed: {error}\n")
    print(f"Verified {n} declaration anchors in {len(cached)} Git blobs.")
    print(f"Package pins {toolchain} and Mathlib {MATHLIB}.")


if __name__ == "__main__":
    main()
