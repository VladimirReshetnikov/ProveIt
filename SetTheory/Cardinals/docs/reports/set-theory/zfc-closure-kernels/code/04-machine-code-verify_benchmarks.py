#!/usr/bin/env python3
"""Independently audit the two literal benchmark tables and the 253 boot.

No upstream Python modules are imported. This finite computation is diagnostic
evidence, not a proof of nonhalting or an internal ZFC theorem.
"""
from __future__ import annotations
import argparse
from collections import deque
import hashlib
import json
from pathlib import Path
import sys

if sys.flags.optimize:
    raise RuntimeError("Run with assertions enabled.")

BASE_SHA = "d655ce2cf8cccebd21caa21a49f0f9f010960a44b95c17aae6cc425c518954eb"
NEW_SHA = "84a21f714017c1d491008d86e9bd19c43cc6c5c9ae99a538b4f2314387827d95"
DELTA = {(3, 0): (0, "L", 48), (5, 0): (1, "R", 97),
         (5, 1): (1, "R", 64), (49, 1): (0, "R", 5)}

def table(path: Path, expected_states: int, expected_hash: str):
    raw = path.read_bytes()
    assert hashlib.sha256(raw).hexdigest() == expected_hash
    rows = {}
    start = None
    for line in raw.decode("ascii").splitlines():
        if line.startswith("#! start "):
            assert start is None
            start = int(line.split()[-1])
        elif line and not line.startswith("#"):
            q, b, w, d, r = line.split()
            q, b, w, r = int(q), int(b), int(w), int(r)
            assert (q, b) not in rows
            assert b in (0, 1) and w in (0, 1) and d in ("L", "R")
            assert 0 <= r <= expected_states
            rows[q, b] = w, d, r
    assert start == 0
    assert set(rows) == {(q, b) for q in range(expected_states) for b in (0, 1)}
    return rows

def infer_bijection(old, new):
    """Infer the unique graph correspondence from the two designated starts."""
    patched = {k: DELTA.get(k, v) for k, v in old.items() if k[0] != 8}
    assert all(old[k] != v for k, v in DELTA.items())
    assert all(r != 8 for w, d, r in patched.values())
    mapping, inverse, todo = {5: 0}, {0: 5}, deque([5])
    while todo:
        q = todo.popleft()
        v = mapping[q]
        if q == 254:
            assert v == 253
            continue
        assert q != 8 and v < 253
        for b in (0, 1):
            w, d, r = patched[q, b]
            w2, d2, r2 = new[v, b]
            assert (w, d) == (w2, d2)
            if r in mapping:
                assert mapping[r] == r2
            else:
                assert r2 not in inverse
                mapping[r], inverse[r2] = r2, r
                todo.append(r)
    assert set(mapping) == set(range(255)) - {8}
    assert set(inverse) == set(range(254))
    assert mapping[96] == 33 and mapping[254] == 253
    return mapping

def simulate(rows, steps):
    state, head, ones = 0, 0, set()
    for k in range(steps):
        b = int(head in ones)
        assert (state, b) in rows, ("early halt", k, state)
        w, d, state = rows[state, b]
        if w:
            ones.add(head)
        else:
            ones.discard(head)
        head += 1 if d == "R" else -1
    return state, head, ones

def boot_expected():
    head = -17
    physical = [0, 2, 0, 0, 0, 0, 5, 0, 0]
    spare = [0] * 158
    spare[2] = spare[8] = 1
    ones = {head - 1}
    p = head + 40
    ones.add(p)  # Header after the 40-cell zero gap.
    p += 1
    for value in physical + spare:
        p += 1  # Zero separator.
        ones.update(range(p, p + value + 1))
        p += value + 1
    return 33, head, ones, physical, spare

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    root = Path(__file__).resolve().parents[1]
    ap.add_argument("--baseline", type=Path, default=root/"machines"/"zfc_254.tm")
    ap.add_argument("--candidate", type=Path, default=root/"machines"/"zfc_253.tm")
    ap.add_argument("--out", type=Path)
    args = ap.parse_args()
    old = table(args.baseline, 254, BASE_SHA)
    new = table(args.candidate, 253, NEW_SHA)
    mapping = infer_bijection(old, new)
    state, head, ones = simulate(new, 312975)
    es, eh, eo, physical, spare = boot_expected()
    assert (state, head, ones) == (es, eh, eo)
    tape_json = json.dumps(sorted(ones), separators=(",", ":")).encode()
    result = {
        "status": "passed",
        "baseline_sha256": BASE_SHA,
        "candidate_sha256": NEW_SHA,
        "working_states": [254, 253],
        "transition_counts": [508, 506],
        "changed_old_rows": [
            {"state": q, "read": b, "before": list(old[q,b]), "after": list(v)}
            for (q,b), v in sorted(DELTA.items())
        ],
        "deleted_old_state": 8,
        "inferred_old_to_compact_bijection": {str(k): v for k,v in sorted(mapping.items())},
        "literal_boot": {
            "steps": 312975, "state": state, "head": head,
            "head_to_header_gap": 40,
            "physical_registers": physical,
            "source_order_registers": [5,0,0,0,2,0,0,0,0],
            "spare_blocks": len(spare),
            "nonzero_spares": {str(k): v for k,v in enumerate(spare) if v},
            "one_cells": len(ones),
            "first_one": min(ones), "last_one": max(ones),
            "sorted_one_positions_json_sha256": hashlib.sha256(tape_json).hexdigest(),
            "entire_finite_tape_matched": True
        },
        "scope": "Finite table/renumbering/boot checks only; not a nonhalting proof, RM-prefix proof, or ZFC internalization."
    }
    out = json.dumps(result, indent=2) + "\n"
    if args.out:
        args.out.parent.mkdir(parents=True, exist_ok=True)
        args.out.write_text(out)
    print(out)

if __name__ == "__main__":
    main()
