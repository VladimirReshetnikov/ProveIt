#!/usr/bin/env python3
"""Check the pinned source-map files and declaration anchors in a local grh checkout."""
import argparse
import csv
import hashlib
import re
from pathlib import Path


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("grh", type=Path, help="directory containing src/Main.lean")
    args = parser.parse_args()
    index = Path(__file__).resolve().with_name("source-map.tsv")
    files = {}
    count = 0
    with index.open(encoding="utf-8", newline="") as stream:
        for row in csv.DictReader(stream, delimiter="\t"):
            path = args.grh / row["path_from_grh"]
            if path not in files:
                data = path.read_bytes()
                header = b"blob " + str(len(data)).encode("ascii") + b"\0"
                files[path] = (hashlib.sha1(header + data).hexdigest(),
                               data.decode("utf-8").splitlines())
            digest, lines = files[path]
            if digest != row["git_blob_sha1"]:
                raise SystemExit(f"Git blob mismatch for {path}")
            line = int(row["line"])
            name = row["declaration_as_written"]
            pattern = r"\b(?:lemma|def|theorem|abbrev|structure|class)\s+(?:_root_\.)?" + re.escape(name) + r"(?=\s|:|\{|\(|$)"
            if line < 1 or line > len(lines) or not re.search(pattern, lines[line - 1]):
                raise SystemExit(f"Declaration {name} missing from {path}:{line}")
            count += 1
    print(f"Matched {count} declaration anchors and {len(files)} Git blobs.")


if __name__ == "__main__":
    main()
