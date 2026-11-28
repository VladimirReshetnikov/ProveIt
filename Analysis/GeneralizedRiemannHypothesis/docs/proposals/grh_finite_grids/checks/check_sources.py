#!/usr/bin/env python3
"""Check the pinned source blobs, anchors, proposal directories and TeX counts."""
import csv
import hashlib
import sys
from pathlib import Path

evidence = Path(__file__).resolve().parents[1] / "evidence"
repo = Path(sys.argv[1]).resolve()
with (evidence / "sources.tsv").open() as stream:
    anchors = list(csv.DictReader(stream, delimiter="\t"))
for row in anchors:
    path = repo / row["path_from_repo_root"]
    data = path.read_bytes()
    header = f"blob {len(data)}\0".encode()
    assert hashlib.sha1(header + data).hexdigest() == row["blob_sha1"], path
    assert row["symbol"] in data.decode().splitlines()[int(row["line"]) - 1], row

with (evidence / "proposal-catalog.tsv").open() as stream:
    catalog = list(csv.DictReader(stream, delimiter="\t"))
directory = repo / "Analysis/GeneralizedRiemannHypothesis/docs/proposals"
expected = {r["directory"]: int(r["tex_files"]) for r in catalog}
actual = {d.name: len(list(d.rglob("*.tex"))) for d in directory.iterdir() if d.is_dir()}
assert expected == actual, "Proposal inventory differs from the recorded revision"
print(f"Verified {len(anchors)} source anchors and their Git blobs.")
print(f"Verified {len(catalog)} proposal directories containing {sum(actual.values())} TeX files.")
