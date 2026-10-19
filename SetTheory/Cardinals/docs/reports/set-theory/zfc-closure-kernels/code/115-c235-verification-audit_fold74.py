#!/usr/bin/env python3
"""Small independent proof checker for the specific 193-to-74 fold.

The only context facts are proved from ALL literal incoming transitions:
old 74 always has a zero immediately left; old 193 always has a one.
No shared abstract interpreter, compiler, or discovery code is imported.
"""
from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path


def parse(raw):
    table, start = {}, None
    for line in raw.decode().splitlines():
        if line.startswith("#! start "):
            start = int(line.split()[-1])
        elif line and not line.startswith("#"):
            state, symbol, write, direction, target = line.split()
            state, symbol, write, target = map(int, (state, symbol, write, target))
            assert symbol in (0, 1) and write in (0, 1) and direction in ("L", "R")
            assert (state, symbol) not in table
            table[state, symbol] = write, -1 if direction == "L" else 1, target
    states = {q for q, b in table}
    assert set(table) == {(q, b) for q in states for b in (0, 1)}
    assert {z for w, d, z in table.values()} - states == {254}
    assert start == 95 and start not in (74, 193)
    return table


def verify(old, new):
    phi = lambda q: 74 if q == 193 else q
    assert len(old) == 472 and len(new) == 470
    assert {q for q, b in new} == {q for q, b in old} - {193}
    arrivals = {}
    for q, tag in ((74, 0), (193, 1)):
        incoming = [(state, read, write, direction) for (state, read), (write, direction, target) in old.items() if target == q]
        assert incoming
        assert all(write == tag and direction == 1 for state, read, write, direction in incoming)
        arrivals[q] = incoming
    unchanged = 0
    for (q, b), (w, d, z) in old.items():
        if q in (74, 193):
            continue
        assert new[q, b] == (w, d, phi(z))
        unchanged += 1
    macros = []
    for old_q, tag in ((74, 0), (193, 1)):
        for value in (0, 1):
            cells = {-1: tag, 0: value}
            before = cells.copy()
            head, state = 0, 74
            trace = []
            for _ in range(3):
                assert head in cells, "proof would read an arbitrary unrepresented cell"
                read = cells[head]
                write, direction, target = new[state, read]
                trace.append([state, head, read, write, direction, target])
                cells[head] = write
                head += direction
                state = target
                assert state != 254, "interior halt"
            ow, od, oz = old[old_q, value]
            assert (ow, od) == (value, 1)
            assert state == phi(oz) and head == 1 and cells == before
            macros.append({"old_row": [old_q, value], "left_tag": tag, "new_steps": 3, "trace": trace,
                           "entire_tape_preserved": True, "old_endpoint": [oz, 1]})
    return {"all_incoming_rows": arrivals, "ordinary_rows_checked": unchanged,
            "special_rows_checked": 4, "special_macros": macros,
            "ordinary_block_length": 1, "special_block_length": 3,
            "initial_configurations_identical": True,
            "scope": "Halting equivalence for every binary tape from state 95 at any integer head position"}


def main():
    p = argparse.ArgumentParser()
    p.add_argument("old", type=Path)
    p.add_argument("new", type=Path)
    p.add_argument("--output", type=Path, required=True)
    a = p.parse_args()
    old_bytes, new_bytes = a.old.read_bytes(), a.new.read_bytes()
    receipt = {"status": "INDEPENDENT_LITERAL_FOLD_PROOF_PASS", **verify(parse(old_bytes), parse(new_bytes)),
               "old_sha256": hashlib.sha256(old_bytes).hexdigest(),
               "new_sha256": hashlib.sha256(new_bytes).hexdigest(),
               "checker_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    a.output.write_text(json.dumps(receipt, indent=2) + "\n")
    print(json.dumps({k: v for k, v in receipt.items() if k != "special_macros"}, indent=2))


if __name__ == "__main__":
    main()
