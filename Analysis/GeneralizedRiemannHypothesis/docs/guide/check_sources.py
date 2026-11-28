#!/usr/bin/env python3
"""Check source-map.tsv against the Lean source directory containing src/Main.lean.

Run: python3 check_sources.py /path/to/Analysis/GeneralizedRiemannHypothesis/Lean/grh
Requires only Python 3. Checks source identity and declaration anchors, without elaborating Lean.
"""
import argparse
import csv
import hashlib
import re
from pathlib import Path
from urllib.parse import quote

COMMIT = "7a5bb1e051e4bad127bafe90abbea19764778e32"
BASE = ("https://github.com/VladimirReshetnikov/ProveIt/blob/" + COMMIT +
        "/Analysis/GeneralizedRiemannHypothesis/Lean/grh/")
FIELDS = ("topic", "mathematical_role", "declaration_as_written", "path_from_grh",
          "line", "git_blob_sha1", "permalink")
DECLARATION = r"\b(?:theorem|lemma|def|abbrev|structure|class|inductive)\s+(?:_root_\.)?"


def matches(line, name):
    pattern = DECLARATION + re.escape(name) + r"(?=\s|:|\{|\(|$)"
    return re.search(pattern, line) is not None


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("grh", type=Path, help="root of the readable Lean package")
    args = parser.parse_args()
    index = Path(__file__).resolve().with_name("source-map.tsv")
    sources = {}
    declarations = set()
    topics = set()
    count = 0
    with index.open(encoding="utf-8", newline="") as stream:
        reader = csv.DictReader(stream, delimiter="\t")
        if tuple(reader.fieldnames or ()) != FIELDS:
            raise SystemExit("Unexpected source-map header")
        for row in reader:
            if not all(row.get(k) for k in FIELDS):
                raise SystemExit(f"Missing column in TSV row {reader.line_num}")
            relative = row["path_from_grh"]
            if not relative.startswith("src/") or ".." in Path(relative).parts:
                raise SystemExit(f"Unexpected source path {relative!r}")
            if relative not in sources:
                data = (args.grh / relative).read_bytes()
                header = b"blob " + str(len(data)).encode("ascii") + b"\0"
                sources[relative] = (hashlib.sha1(header + data).hexdigest(),
                                     data.decode("utf-8").splitlines())
            digest, lines = sources[relative]
            if digest != row["git_blob_sha1"]:
                raise SystemExit(f"Git blob mismatch for {relative}: expected {row['git_blob_sha1']}, found {digest}")
            line, name = int(row["line"]), row["declaration_as_written"]
            if not 1 <= line <= len(lines) or not matches(lines[line - 1], name):
                raise SystemExit(f"Declaration {name} missing from {relative}:{line}")
            if row["permalink"] != f"{BASE}{quote(relative)}#L{line}":
                raise SystemExit(f"Incorrect pinned permalink for {relative}:{line}")
            if (relative, line) in declarations:
                raise SystemExit(f"Duplicate declaration in {relative}:{line}")
            declarations.add((relative, line))
            topics.add(row["topic"])
            count += 1
    if not count:
        raise SystemExit("Empty source map")
    print(f"Matched {count} declarations in {len(sources)} Git blobs across {len(topics)} topics.")
    print(f"All declaration links are pinned to ProveIt {COMMIT}.")


if __name__ == "__main__":
    main()
