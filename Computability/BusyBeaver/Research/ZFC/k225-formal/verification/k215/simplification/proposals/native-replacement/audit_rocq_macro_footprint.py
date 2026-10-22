#!/usr/bin/env python3
"""Read-only lexical/graph audit of four pinned Rocq source files.

No Rocq source is executed, compiled, imported, or interpreted. This script
parses literal node declarations only. It is an independently written source
audit, not a formal certificate of the proposed transfer theorem.

Usage:
  python audit_rocq_macro_footprint.py --sources PATH --output result.json

Supply exact files fetched at PIN, with names ProgLibPerm.v, ProgLib219.v,
DagPerm.v and Dag219.v. Paths and expected Git blob IDs are included below.
"""
import argparse
import hashlib
import json
import re
from pathlib import Path

PIN = "6d9800d1ca67c52db0eb6e1c65df7b5cab9cdb95"
REPO = "VladimirReshetnikov/ProveIt"
PREFIX = "Computability/BusyBeaver/Research/ZFC/k225-formal/rocq/rocq-extension/coq/"
PATHS = {
    "ProgLibPerm.v": PREFIX + "215/ProgLibPerm.v",
    "DagPerm.v": PREFIX + "215/DagPerm.v",
    "ProgLib219.v": PREFIX + "218/ProgLib219.v",
    "Dag219.v": PREFIX + "218/Dag219.v",
}
# GitHub connector metadata for these files at PIN, independently matched
# against the hash of each fetched byte string before recording this audit.
EXPECTED_BLOBS = {"ProgLibPerm.v":"c9e20ad6fe3e54aa9360a69be34bc6eaf0cb5e1c","DagPerm.v":"74a1715ff35e2b1abbf0cb5f58efdf2aafb1ef6b","ProgLib219.v":"df5349f0d236c0f0ae82df0b2f332ec66bf5d5d8","Dag219.v":"63d54d60f2f5c21a28f330dd7d548dfb0db359bf"}
MARKER = "(** ** Determinism of the big-step semantics (generic in the program). *)"
EDGE = r"(?:ENode [0-9]+|EInc [0-9]+|EDecnz [0-9]+|EBreak [0-9]+|EContinue [0-9]+|EHalt)"
ROW = re.compile(r"^  \| ([0-9]+) => \((" + EDGE + r"), (" + EDGE + r")\)$", re.M)

def parse_dag(text):
    declarations = ROW.findall(text)
    rows = {int(n): (a, b) for n, a, b in declarations}
    assert len(rows) == len(declarations), "Duplicate numbered row"
    # Fail if a row uses an unsupported shape rather than silently skipping it.
    all_numbered = re.findall(r"^\s*\|\s*([0-9]+)\s*=>", text, re.M)
    assert len(all_numbered) == len(rows), "Unparsed numbered row"
    bound = int(re.search(r"mkProg dag_nodes 0 ([0-9]+)\.", text).group(1))
    assert set(rows) == set(range(bound)), "Rows do not cover exact node range"
    assert "  | _ => (EHalt, EHalt)\n  end." in text, "Unexpected default row"
    return rows, bound

def successor_nodes(row):
    return [int(edge[6:]) for edge in row if edge.startswith("ENode ")]

def closure(roots, rows):
    todo = list(roots)
    seen = set()
    while todo:
        n = todo.pop()
        if n not in seen:
            assert n in rows, "Footprint reaches missing/default row"
            seen.add(n)
            todo.extend(successor_nodes(rows[n]))
    return seen

def equal_closed(roots, footprint, p, q):
    return (roots <= footprint
            and all(n in p and n in q and p[n] == q[n] for n in footprint)
            and all(c in footprint for n in footprint
                    for c in successor_nodes(p[n])))

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--sources", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    contents = {}
    source_info = {}
    for name, path in PATHS.items():
        raw = (args.sources / name).read_bytes()
        blob = hashlib.sha1(b"blob " + str(len(raw)).encode() + b"\0" + raw).hexdigest()
        if EXPECTED_BLOBS:
            assert blob == EXPECTED_BLOBS[name], "Source differs from pinned bytes"
        contents[name] = raw.decode("utf-8")
        source_info[name] = {
            "path": path,
            "url": "https://github.com/" + REPO + "/blob/" + PIN + "/" + path,
            "git_blob_sha1": blob,
            "sha256": hashlib.sha256(raw).hexdigest(),
            "bytes": len(raw),
            "newline_count": raw.count(b"\n"),
            "ends_in_newline": raw.endswith(b"\n"),
        }
    perm = contents["ProgLibPerm.v"]
    old = contents["ProgLib219.v"]
    pstart, ostart = perm.index(MARKER), old.index(MARKER)
    psuffix, osuffix = perm[pstart:], old[ostart:]
    identical = psuffix.replace("dagPerm", "dag219") == osuffix
    assert identical, "Libraries are not the reported exact renamed suffix"
    # These are literal semantic entry mentions, not all numbers in source.
    roots = set(map(int, re.findall(r"sem\s*\(\s*ENode\s+(\d+)\s*\)", perm)))
    prow, pbound = parse_dag(contents["DagPerm.v"])
    orow, obound = parse_dag(contents["Dag219.v"])
    pfoot = closure(roots, prow)
    ofoot = closure(roots, orow)
    assert pfoot == ofoot
    assert equal_closed(roots, pfoot, prow, orow)
    changed_reachable = dict(prow)
    assert changed_reachable[115][0] == "EDecnz 8"
    changed_reachable[115] = ("EDecnz 7", changed_reachable[115][1])
    negative_controls = {
        "reject_changed_reachable_primitive_row":
            not equal_closed(roots, pfoot, changed_reachable, orow),
        "reject_omitted_successor_154_of_row_115":
            not equal_closed(roots - {154}, pfoot - {154}, prow, orow),
        "reject_omitted_entry_115":
            not equal_closed(roots, pfoot - {115}, prow, orow),
    }
    assert all(negative_controls.values()), "A negative control failed"
    changed = sorted(n for n in orow if prow.get(n) != orow[n])
    assert pfoot.isdisjoint(changed)
    result = {
        "kind": "source-only audit; NOT a compiled proof or kernel certificate",
        "repository": REPO,
        "pin": PIN,
        "sources": source_info,
        "identical_suffix": {
            "normalization": "replace dagPerm by dag219 in Perm suffix only",
            "marker": MARKER,
            "perm_start_line": perm[:pstart].count("\n") + 1,
            "old_start_line": old[:ostart].count("\n") + 1,
            "newline_count": psuffix.count("\n"),
            "characters": len(psuffix),
            "bytes": len(psuffix.encode()),
            "identical_after_normalization": identical,
        },
        "literal_sem_entry_count": len(roots),
        "literal_sem_entries": sorted(roots),
        "footprint_count": len(pfoot),
        "footprint": sorted(pfoot),
        "all_rows_equal_and_both_children_closed": True,
        "negative_controls": negative_controls,
        "dagPerm_node_count": pbound,
        "dag219_node_count": obound,
        "changed_old_rows": {
            str(n): {"old": orow[n], "new": prow[n]} for n in changed
        },
        "added_rows": sorted(set(prow) - set(orow)),
        "claim_boundary": "Macro-edge big-step contracts only, not whole-root equivalence.",
    }
    args.output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({
        "matching_suffix_lines": result["identical_suffix"]["newline_count"],
        "literal_entries": len(roots),
        "closed_equal_rows": len(pfoot),
        "changed_old_rows": changed,
        "output": str(args.output),
    }))

if __name__ == "__main__":
    main()
