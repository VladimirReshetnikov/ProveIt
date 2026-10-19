#!/usr/bin/env python3
"""Certify the 240 -> 239 context split and fold, using only Python's stdlib.

Usage:
  python certify_239_fold.py boundary240_old.tm candidate239_old.tm --output proof.json
  python certify_239_fold.py boundary240_old.tm --build candidate239_old.tm --output proof.json

This checks exact table edits, every incoming port, and six whole-tape local
block identities.  Reads outside the two explicitly represented cells are
rejected.  The mathematical composition argument is in fold239.tex.
"""
import argparse
import hashlib
import json
from pathlib import Path

START = 95
HALT = 254
EXPECTED_REFERENCE_SHA256 = "19cd7f7863a681828fd026adbf8ce91c21e3ac7604439bc9d4603ba58661853e"
EXPECTED_CANDIDATE_SHA256 = "d061770f487937f9da652919c9bc9bb79bc9bf137ca41dd7a08eb5ecda8e7719"


def require(condition, message):
    if not condition:
        raise ValueError(message)


def read_table(path):
    rows = {}
    for number, line in enumerate(path.read_text().splitlines(), 1):
        if not line or line.startswith("#"):
            continue
        fields = line.split()
        require(len(fields) == 5, f"line {number}: expected five fields")
        q, b, w, d, t = fields
        q, b, w, t = map(int, (q, b, w, t))
        require(q >= 0 and t >= 0 and b in (0, 1) and w in (0, 1)
                and d in ("L", "R"), f"line {number}: invalid transition")
        require((q, b) not in rows, f"line {number}: repeated row")
        rows[q, b] = (w, d, t)
    states = {q for q, b in rows}
    require(len(rows) == 2 * len(states), "each working state needs two rows")
    require(START in states and HALT not in states, "wrong start/halt convention")
    require(all(t in states or t == HALT for w, d, t in rows.values()),
            "undefined target other than the designated halt")
    return rows


def incoming(table, state):
    return sorted((q, b, w, d) for (q, b), (w, d, t) in table.items() if t == state)


def construct(old):
    new = {}
    for (q, b), (w, d, t) in old.items():
        if q == 218:
            continue
        if t == 218:
            require(d == "R", "every old218 caller must move right")
            t = 223 if w == 0 else 179
        new[q, b] = (w, d, t)
    new[179, 1] = (1, "L", 215)
    new[223, 0] = (0, "R", 23)
    new[223, 1] = (1, "R", 70)
    return new


def serialize(table):
    return "".join(f"{q} {b} {w} {d} {t}\n"
                   for (q, b), (w, d, t) in sorted(table.items()))


def block(table, q, tag, read, length):
    tape = {-1: tag, 0: read}
    head = 0
    trace = []
    for tick in range(length):
        require(head in tape, "local certificate tried to read an unspecified cell")
        bit = tape[head]
        require((q, bit) in table, "block reached an undefined transition")
        write, direction, target = table[q, bit]
        trace.append({"step": tick + 1, "state": q, "head": head,
                      "read": bit, "write": write, "move": direction, "next": target})
        tape[head] = write
        head += 1 if direction == "R" else -1
        q = target
    return (q, head, tape), trace


def verify(old, new):
    old_states = {q for q, b in old}
    new_states = {q for q, b in new}
    require(len(old_states) == 240 and len(new_states) == 239,
            "expected240 old states and239 new states")
    require(new_states == old_states - {218}, "only state218 is deleted")
    require(new == construct(old), "candidate is not exactly the certified edit set")
    require(START not in (179, 218, 223), "special roles cannot be initial")

    ports179 = incoming(old, 179)
    ports218 = incoming(old, 218)
    ports223 = incoming(old, 223)
    require(ports179 == [(161, 0, 0, "R"), (236, 0, 0, "R"), (239, 0, 0, "R")],
            "unexpected incoming ports for179")
    require(ports218 == [(187, 1, 1, "R"), (220, 1, 1, "R"), (237, 0, 0, "R")],
            "unexpected incoming ports for218")
    require(ports223 == [(218, 0, 0, "L")], "old223 must be internal to218/0")
    require(all(w == 0 and d == "R" for q, b, w, d in ports179),
            "old179's preceding bit must always be0")
    for q, b, w, d in ports218:
        require(new[q, b] == (w, d, 223 if w == 0 else 179),
                "218 caller does not route according to its written tag")

    # (old state, left tag, scanned bit, new state, old steps, new steps, endpoint)
    obligations = [
        (179, 0, 0, 179, 1, 1, 105),
        (179, 0, 1, 179, 1, 5, 105),
        (218, 0, 0, 223, 3, 1, 23),
        (218, 0, 1, 223, 1, 1, 70),
        (218, 1, 0, 179, 3, 1, 105),
        (218, 1, 1, 179, 1, 3, 70),
    ]
    checked = []
    for q, tag, read, mapped, old_steps, new_steps, endpoint in obligations:
        old_end, old_trace = block(old, q, tag, read, old_steps)
        new_end, new_trace = block(new, mapped, tag, read, new_steps)
        expected = (endpoint, 1, {-1: tag, 0: read})
        require(old_end == new_end == expected, f"block obligation failed: {(q, tag, read)}")
        require(old_steps > 0 and new_steps > 0, "both block lengths must be positive")
        checked.append({"old_state": q, "left_tag": tag, "read": read,
                        "new_state": mapped, "old_steps": old_steps, "new_steps": new_steps,
                        "endpoint_state": endpoint, "endpoint_head": 1,
                        "whole_tape_unchanged": True, "old_trace": old_trace,
                        "new_trace": new_trace})

    # Every other checkpoint uses the identical write and move.  Any target
    # changed by construct is exactly one of the three certified incoming ports.
    for (q, b), (w, d, t) in old.items():
        if q in (179, 218, 223):
            continue
        if t == 218:
            require(new[q, b] == (w, d, 223 if w == 0 else 179), "bad port transition")
        else:
            require(t != 223, "old helper223 has an uncovered incoming transition")
            require(new[q, b] == old[q, b], "an ordinary transition changed")

    edits = []
    for key in sorted(set(old) | set(new)):
        if old.get(key) != new.get(key):
            edits.append({"state": key[0], "read": key[1],
                          "old": old.get(key), "new": new.get(key)})
    return {
        "status": "PASS",
        "claim": "Whole-tape positive-block simulation between the supplied240 and239 tables",
        "initial_tapes": "Every binary tape at start95, including blank",
        "start": START, "halt": HALT,
        "old_working_states": len(old_states), "new_working_states": len(new_states),
        "checkpoint_mapping": {
            "old179,left0": 179, "old218,left0": 223, "old218,left1": 179,
            "old223": "Internal to the three-step old218/0 block; not a checkpoint",
            "other_states": "Identity",
        },
        "incoming_ports": {"179": ports179, "218": ports218, "223": ports223},
        "explicit_tape_cells": [-1, 0],
        "outside_tape": "Arbitrary and never read or written by the six checked blocks",
        "block_obligations": checked,
        "table_edits": edits,
        "proof_scope": "Finite certificate with the mathematical composition argument in fold239.tex; not a proof-assistant kernel certificate",
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("reference", type=Path)
    parser.add_argument("candidate", type=Path, nargs="?")
    parser.add_argument("--build", type=Path, help="write the constructed candidate to a new path")
    parser.add_argument("--output", type=Path, help="write the full JSON certificate")
    args = parser.parse_args()
    require((args.candidate is None) != (args.build is None),
            "supply either a candidate path or --build, but not both")
    old = read_table(args.reference)
    path = args.candidate if args.candidate is not None else args.build
    if args.build is not None:
        require(not path.exists(), "--build destination already exists")
        proposed = construct(old)
        verify(old, proposed)
        path.write_text(serialize(proposed))
    new = read_table(path)
    result = verify(old, new)
    result["reference_sha256"] = hashlib.sha256(args.reference.read_bytes()).hexdigest()
    result["candidate_sha256"] = hashlib.sha256(path.read_bytes()).hexdigest()
    result["reference_matches_reported_digest"] = result["reference_sha256"] == EXPECTED_REFERENCE_SHA256
    result["candidate_matches_reported_digest"] = result["candidate_sha256"] == EXPECTED_CANDIDATE_SHA256
    result["checker_sha256"] = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    rendered = json.dumps(result, indent=2) + "\n"
    if args.output:
        args.output.write_text(rendered)
    print(json.dumps({"status": result["status"], "old_states": 240, "new_states": 239,
                      "blocks_checked": len(result["block_obligations"]),
                      "reference_sha256": result["reference_sha256"],
                      "candidate_sha256": result["candidate_sha256"]}, indent=2))


if __name__ == "__main__":
    main()
