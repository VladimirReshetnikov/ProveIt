#!/usr/bin/env python3
"""Independently parse and bind K215's dense table to its Lean/Rocq literals.

This checks finite data and a bounded bootstrap only. It does not compile a
proof assistant and does not establish the unbounded halting equivalence.
"""
from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path
import re

PIN = "cdd582bec13f908df3711fa9e05d1ddac368a5db"
TM_SHA256 = "fdbcef0825886035c3091c8537a69535bc96f9e265f0ae45863543d40ae70090"
TM_REL = "Computability/BusyBeaver/Research/ZFC/candidate-k215/k215.tm"
LEAN_REL = "Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KDense215.lean"
ROCQ_REL = "Computability/BusyBeaver/Research/ZFC/k225-formal/rocq/rocq-extension/coq/215/Table215.v"


def require(condition, message):
    if not condition:
        raise ValueError(message)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def parse_tm(data):
    """Return sorted (state,read,write,move,next) integer rows; move +/-1."""
    require(sha(data) == TM_SHA256, "The exact K215 table hash does not match")
    lines = data.decode("ascii").splitlines()
    require(lines[0] == "#! start 0", "Unexpected starting-state declaration")
    actions = {}
    for n, line in enumerate(lines[1:], start=2):
        m = re.fullmatch(r"(\d+) ([01]) ([01]) ([LR]) (\d+)", line)
        require(m is not None, f"Invalid transition line {n}")
        q, r, w, d, target = m.groups()
        q, r, w, target = map(int, (q, r, w, target))
        require(0 <= q < 215 and 0 <= target <= 215, f"Out-of-range line {n}")
        require((q, r) not in actions, f"Duplicate action {q},{r}")
        actions[q, r] = (q, r, w, 1 if d == "R" else -1, target)
    require(set(actions) == {(q, r) for q in range(215) for r in (0, 1)},
            "The table is not total on the 215 working states")
    return [actions[q, r] for q in range(215) for r in (0, 1)]


def parse_lean(data):
    text = data.decode("utf-8")
    body = text.split("def rows215 :", 1)[1].split(":= [", 1)[1].split("]", 1)[0]
    pattern = r"\(\((true|false), (true|false), (\d+)\), \((true|false), (true|false), (\d+)\)\)"
    literals = re.findall(pattern, body)
    remainder = re.sub(pattern, "", body)
    require(not remainder.replace(",", "").strip(), "Unparsed Lean literal text")
    require(len(literals) == 215, "Lean row count differs")
    rows = []
    for q, row in enumerate(literals):
        for r in (0, 1):
            w, direction, target = row[3*r:3*r+3]
            rows.append((q, r, int(w == "true"), 1 if direction == "true" else -1, int(target)))
    return rows


def parse_rocq(data):
    text = data.decode("utf-8")
    body = text.split("Definition table215 :", 1)[1].split(":= [", 1)[1].split("]", 1)[0]
    pattern = r"\((true|false), ([LR]), (\d+), (true|false), ([LR]), (\d+)\)"
    literals = re.findall(pattern, body)
    remainder = re.sub(pattern, "", body)
    require(not remainder.replace(";", "").strip(), "Unparsed Rocq literal text")
    require(len(literals) == 215, "Rocq row count differs")
    rows = []
    for q, row in enumerate(literals):
        for r in (0, 1):
            w, direction, target = row[3*r:3*r+3]
            rows.append((q, r, int(w == "true"), 1 if direction == "R" else -1, int(target)))
    return rows


def bootstrap(rows):
    actions = {(q, r): (w, d, n) for q, r, w, d, n in rows}
    ones = set()
    q = head = 0
    for _ in range(95714):
        require(q != 215, "Unexpected halt during the recorded bootstrap")
        w, d, q = actions[q, int(head in ones)]
        if w:
            ones.add(head)
        else:
            ones.discard(head)
        head += d
    require((q, head, len(ones)) == (83, -8, 95), "Bootstrap summary mismatch")
    payload = json.dumps(sorted(ones), separators=(",", ":")).encode("ascii")
    return {"steps": 95714, "state": q, "head": head, "one_cells": len(ones),
            "one_positions_sha256": sha(payload),
            "scope": "bounded bootstrap check, not an unbounded correctness proof"}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    files = {key: (args.repo / rel).read_bytes() for key, rel in
             (("tm", TM_REL), ("lean", LEAN_REL), ("rocq", ROCQ_REL))}
    rows = parse_tm(files["tm"])
    require(parse_lean(files["lean"]) == rows, "Lean literals differ from the transition table")
    require(parse_rocq(files["rocq"]) == rows, "Rocq literals differ from the transition table")
    result = {
        "schema": "proveit-k215-independent-transition-export-v1",
        "repository_commit": PIN,
        "convention": {"start": 0, "halt": 215, "blank": 0, "head": 0,
                       "tape": "two-way infinite", "move_encoding": {"L": -1, "R": 1}},
        "source_sha256": {key: sha(data) for key, data in files.items()},
        "source_paths": {"tm": TM_REL, "lean": LEAN_REL, "rocq": ROCQ_REL},
        "working_states": 215,
        "transition_count": 430,
        "direction_counts": {"L": sum(row[3] == -1 for row in rows),
                             "R": sum(row[3] == 1 for row in rows)},
        "terminal_transitions": [row for row in rows if row[4] == 215],
        "lean_literal_match": True,
        "rocq_literal_match": True,
        "bootstrap": bootstrap(rows),
        "transition_fields": ["state", "read", "write", "move", "next"],
        "transitions": rows,
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({key: value for key, value in result.items() if key != "transitions"}, indent=2))


if __name__ == "__main__":
    main()
