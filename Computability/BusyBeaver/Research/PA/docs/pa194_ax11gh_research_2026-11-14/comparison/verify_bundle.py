#!/usr/bin/env python3
"""Replay the bundled 110-class comparison, without the original repository.

By default verify manifest integrity, every historical representative, graph
classes, all broad structural equivalences, and both newly supplied candidates.
--repository PATH additionally rechecks all 10,495 original Git payloads. It
uses only locally available Git objects and never requests a missing object.
The arithmetic calibration of a machine is outside this graph checker's scope.
"""
import argparse
import csv
import gzip
import hashlib
import json
import subprocess
from pathlib import Path

import audit

ROOT = Path(__file__).resolve().parent
PIN = "1e1a41f799d4658b829cdd0eabae3775a0c8c4a0"


def read(name):
    return json.loads((ROOT / name).read_text())


def sha(data):
    return hashlib.sha256(data).hexdigest()


def git_sha(data):
    return hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()


def graph(data):
    rows, states, start, declared = audit.parse(data)
    ordinary = audit.canonical(rows, states)
    assert ordinary is not None, "No spanning control"
    broad = min(audit.canonical(rows, states, mirror=m, flip=f, loose=True)
                for m in (False, True) for f in (False, True))
    return {
        "ordinary": ordinary,
        "broad": broad,
        "ordinary_sha256": sha(audit.encode(ordinary)),
        "broad_sha256": sha(audit.encode(broad)),
        "states": len(states),
        "rows": len(rows),
        "start": start,
        "declared_start": declared,
        "start_reachable": audit.rooted(rows, set(states), start)[1]
            if start is not None else None,
        "bisimulation_controls": audit.bisimulation_count(rows, states),
    }


def check_original_sources(repository, manifest):
    # Listing available objects prevents a promisor Git repository from making
    # an implicit network request for a source object not actually present.
    listed = subprocess.check_output(
        ["git", "cat-file", "--batch-all-objects", "--batch-check=%(objectname)"],
        cwd=repository, text=True)
    available = set(listed.splitlines())
    absent = [x for x in manifest["files"] if x["git_blob_sha1"] not in available]
    assert not absent, "Original source blobs unavailable locally: " + str(absent[:5])
    process = subprocess.Popen(["git", "cat-file", "--batch"], cwd=repository,
                               stdin=subprocess.PIPE, stdout=subprocess.PIPE)
    checked = 0
    try:
        for item in manifest["files"]:
            oid = item["git_blob_sha1"]
            process.stdin.write((oid + "\n").encode())
            process.stdin.flush()
            header = process.stdout.readline().decode().split()
            assert len(header) == 3 and header[1] == "blob", (item, header)
            data = process.stdout.read(int(header[2]))
            assert process.stdout.read(1) == b"\n"
            assert git_sha(data) == oid, item
            checked += 1
    finally:
        process.stdin.close()
        process.wait()
    assert process.returncode == 0
    return checked


def main():
    assert __debug__, "Run with assertions enabled; do not use python -O."
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repository", type=Path)
    parser.add_argument("--receipt", type=Path)
    args = parser.parse_args()

    retained = read("bundle_manifest.json")
    for item in retained["files"]:
        p = ROOT / item["path"]
        assert p.is_file(), item
        data = p.read_bytes()
        assert len(data) == item["bytes"] and sha(data) == item["sha256"], item

    manifest = json.loads(gzip.decompress((ROOT / "source_manifest.json.gz").read_bytes()))
    assert manifest["commit"] == PIN
    assert manifest["count"] == len(manifest["files"]) == 10495
    assert len({x["path"] for x in manifest["files"]}) == 10495
    original_ids = {x["path"]: x["git_blob_sha1"] for x in manifest["files"]}
    bindings = {x["canonical_class"]: x for x in read("source_bindings.json")}
    designs = read("designs194.json")
    packets = read("packets86.json")
    assert len(designs) == len(bindings) == 110
    assert len(packets) == 86
    assert sum(x["filed_or_incoming"] == "filed" for x in packets) == 82
    assert sum(x["filed_or_incoming"] == "incoming" for x in packets) == 4
    ordinary_seen = set()
    broad_seen = set()
    historical = []
    for i, row in enumerate(designs):
        data = (ROOT / row["representative_file"]).read_bytes()
        b = bindings[row["canonical_class"]]
        assert b["representative_file"] == row["representative_file"]
        assert b["raw_source_sha256"] == row["representative_sha256"] == sha(data)
        assert b["source_file_bytes"] == len(data)
        assert original_ids[b["top_level_path"]] == b["top_level_git_blob_sha1"]
        if not b["archive_members"]:
            assert git_sha(data) == b["top_level_git_blob_sha1"]
            assert sha(data) == b["top_level_sha256"]
        g = graph(data)
        assert g["states"] == 194 and g["rows"] == 388
        assert g["ordinary_sha256"] == row["canonical_class"]
        assert g["broad_sha256"] == row["strong_class"]
        assert g["bisimulation_controls"] == row["ordinary_bisimulation_controls"] == 194
        # These are exact tuple comparisons, not just digest comparisons.
        assert g["ordinary"] not in ordinary_seen
        assert g["broad"] not in broad_seen
        ordinary_seen.add(g["ordinary"])
        broad_seen.add(g["broad"])
        historical.append((row["name"], g))
        if (i + 1) % 20 == 0:
            print("Historical graphs checked:", i + 1, flush=True)

    candidate_graphs = []
    result = {"snapshot": PIN, "status": "PASS", "historical_194_classes": 110,
              "filed_deliveries": 82, "incoming_deliveries": 4,
              "exact_tuple_comparison": True, "candidates": {},
              "full_original_sources_rechecked": bool(args.repository),
              "arithmetic_calibration_checked": False}
    for name in ("PA194AX11GH", "PA194AX11GHS"):
        data = (ROOT / "candidates" / (name + ".tm")).read_bytes()
        expected = read("candidates/" + name + "_novelty.json")
        g = graph(data)
        assert sha(data) == expected["sha256"]
        assert g["ordinary_sha256"] == expected["canonical_class"]
        assert g["broad_sha256"] == expected["strong_class"]
        assert g["states"] == 194 and g["rows"] == 388
        assert g["start"] == 0 and g["start_reachable"] == 194
        assert g["bisimulation_controls"] == 194
        ordinary_matches = [n for n, h in historical if g["ordinary"] == h["ordinary"]]
        broad_matches = [n for n, h in historical if g["broad"] == h["broad"]]
        assert ordinary_matches == broad_matches == []
        assert g["broad"] not in candidate_graphs
        candidate_graphs.append(g["broad"])
        result["candidates"][name] = {"sha256": sha(data), "states": 194,
            "rows": 388, "start": 0, "reachable": 194,
            "ordinary_matches": ordinary_matches, "broad_matches": broad_matches}
    result["candidates_pairwise_distinct"] = True
    if args.repository:
        result["original_source_payloads_checked"] = check_original_sources(args.repository, manifest)
    if args.receipt:
        args.receipt.parent.mkdir(parents=True, exist_ok=True)
        args.receipt.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
