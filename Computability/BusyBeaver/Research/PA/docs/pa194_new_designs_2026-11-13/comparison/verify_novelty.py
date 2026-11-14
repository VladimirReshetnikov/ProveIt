#!/usr/bin/env python3
"""Compare a literal table with an explicitly scoped action-graph census.

This checks finite graph novelty only.  It is not a proof of consistency,
nonhalting, minimality, or machine refinement.  The input census uses
read-0-first BFS, minimizing over all spanning roots, with compact JSON.
"""
import argparse
import hashlib
import json
from collections import Counter
from pathlib import Path


def parse(data):
    rows = {}
    for line in data.decode("utf8").splitlines():
        line = line.strip()
        if not line or line.startswith(("#", "//", ";")):
            continue
        p = line.split()
        if len(p) != 5 or p[1] not in ("0", "1") or p[2] not in ("0", "1") or p[3] not in ("L", "R"):
            raise ValueError("Not a numeric five-column binary L/R table")
        q, b, w, d, t = p
        key = int(q), int(b)
        if key in rows:
            raise ValueError("Repeated transition")
        rows[key] = int(w), d, int(t)
    states = {q for q, _ in rows}
    if not states or set(rows) != {(q, b) for q in states for b in (0, 1)}:
        raise ValueError("Not a complete binary table")
    halts = {t for _, _, t in rows.values()} - states
    if len(halts) != 1:
        raise ValueError("Require exactly one terminal label")
    return rows, states, next(iter(halts))


def canonical(rows, states, halt, root):
    labels, todo, out = {root: 0}, [root], []
    for q in todo:
        rr = []
        for b in (0, 1):
            w, d, t = rows[q, b]
            if t == halt:
                k = -1
            else:
                if t not in labels:
                    labels[t] = len(todo)
                    todo.append(t)
                k = labels[t]
            rr.append([w, d, k])
        out.append(rr)
    if len(todo) != len(states):
        return None
    return json.dumps(out, separators=(",", ":")).encode()


def check(table, census):
    data = table.read_bytes()
    rows, states, halt = parse(data)
    known = [r for r in census["raw_tables"] if r["states"] == len(states)]
    known_hashes = {r["root_free_sha256"] for r in known}
    transformations = []
    for reflect, complement in ((False, False), (True, False), (False, True), (True, True)):
        transformed = {(q, b ^ complement): (w ^ complement, ("R" if d == "L" else "L") if reflect else d, t)
                       for (q, b), (w, d, t) in rows.items()}
        words = [c for q in sorted(states) if (c := canonical(transformed, states, halt, q)) is not None]
        if not words:
            raise ValueError("Candidate has no spanning root; this canonicalizer is inapplicable")
        digest = hashlib.sha256(min(words)).hexdigest()
        transformations.append({"reflect": reflect, "complement": complement,
                                "root_free_sha256": digest,
                                "spanning_roots": len(words),
                                "matches": [r for r in known if r["root_free_sha256"] == digest]})
    actions = Counter((w, d) for w, d, _ in rows.values())
    return {"census_commit": census["summary"]["commit"],
            "candidate_file": table.name,
            "candidate_sha256": hashlib.sha256(data).hexdigest(),
            "states": len(states), "transitions": len(rows), "halt": halt,
            "action_counts": {f"{w}{d}": actions[w, d] for w in (0, 1) for d in ("L", "R")},
            "same_size_census_byte_forms": len(known),
            "same_size_census_root_free_graph_classes": len(known_hashes - {None}),
            "transformations": transformations,
            "absent_under_all_four_transformations": not any(t["matches"] for t in transformations),
            "scope": "Finite action-graph novelty within the supplied literal-table census; no semantic or minimality claim."}


def main():
    p = argparse.ArgumentParser()
    p.add_argument("table", type=Path)
    p.add_argument("--census", type=Path, required=True)
    p.add_argument("--output", type=Path)
    a = p.parse_args()
    result = check(a.table, json.loads(a.census.read_text()))
    encoded = json.dumps(result, indent=2) + "\n"
    if a.output:
        a.output.write_text(encoded)
    print(encoded, end="")
    if not result["absent_under_all_four_transformations"]:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
