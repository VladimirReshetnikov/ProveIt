#!/usr/bin/env python3
"""Compare a numeric binary table with the frozen pinned-corpus graph census.

Usage from the package root:
    python3 comparison/verify_novelty.py path/to/machine.tm

This checks novelty against the supplied census manifest. To rebuild that
manifest's source data, use census.py and graph_census.py with the pinned repo.
No downloaded program is executed while scanning the source corpus.
"""
from pathlib import Path
import argparse
import hashlib
import json

from census import parse_table, canonical_root
from graph_census import canonical


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("table", type=Path)
    ap.add_argument("--start", type=int, default=0)
    ap.add_argument("--manifest", type=Path,
                    default=Path(__file__).with_name("graph_classes.json"))
    ap.add_argument("--output", type=Path)
    args = ap.parse_args()
    raw = args.table.read_bytes()
    metadata, rows = parse_table(raw)
    if not metadata["complete"] or len(metadata["terminal_labels"]) != 1:
        raise ValueError("Expected a total binary working-state table with one terminal halt")
    corpus = json.loads(args.manifest.read_text())
    hashes = {x["root_free_graph_sha256"] for x in corpus["classes"]}
    symmetries = []
    for mirror, complement in ((False, False), (True, False),
                               (False, True), (True, True)):
        transformed = {
            (q, b ^ complement):
            (w ^ complement, ("L" if d == "R" else "R") if mirror else d, n)
            for (q, b), (w, d, n) in rows.items()
        }
        graph_hash, root = canonical(transformed)
        symmetries.append({"mirror": mirror, "complement_bits": complement,
                           "canonical_hash": graph_hash,
                           "canonicalizing_root": root,
                           "matches_corpus": graph_hash in hashes})
    result = {
        "source_commit": corpus["commit"],
        "table_sha256": hashlib.sha256(raw).hexdigest(),
        "working_states": metadata["working_states"],
        "rows": len(rows),
        "complete": metadata["complete"],
        "rooted": canonical_root(rows, args.start),
        "compared_classes": len(hashes),
        "symmetry_checks": symmetries,
        "new_up_to_relabeling_mirroring_and_complement":
            not any(x["matches_corpus"] for x in symmetries),
        "scope": "Finite graph comparison; not a consistency or nonhalting proof.",
    }
    encoded = json.dumps(result, indent=2) + "\n"
    if args.output:
        args.output.write_text(encoded)
    print(encoded, end="")


if __name__ == "__main__":
    main()
