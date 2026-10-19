#!/usr/bin/env python3
"""Check the finite premises of the independent 223 -> 182 fold proof.

This deliberately does not import the search or generic fold checker.  The
unbounded simulation argument is in sections/fold236.tex.  No sampled
run length is used here: all ordinary rows and all four exceptional cases
are checked literally, together with the complete incoming-row guards.
"""
from pathlib import Path
import argparse
import hashlib
import json
import sys

if not __debug__ or sys.flags.optimize:
    raise RuntimeError("Run this premise checker without Python optimization; its assertions are proof checks")


def read_table(data):
    rows = {}
    start = None
    for line in data.decode("utf-8").splitlines():
        if line.startswith("#! start "):
            assert start is None, "Repeated initial-state declaration"
            start = int(line.removeprefix("#! start "))
        elif line and not line.startswith("#"):
            state, bit, write, direction, target = line.split()
            state, bit, write, target = map(int, (state, bit, write, target))
            assert bit in (0, 1) and write in (0, 1)
            assert direction in ("L", "R")
            assert (state, bit) not in rows
            rows[state, bit] = (write, 1 if direction == "R" else -1, target)
    states = {q for q, _ in rows}
    assert set(rows) == {(q, b) for q in states for b in (0, 1)}
    assert 254 not in states and start in states
    assert {z for _, _, z in rows.values()} - states == {254}
    return rows, states, start


def main():
    here = Path(__file__).resolve().parent
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--old", type=Path,
                        default=here.parent / "machines/zfc_rotated237_old.tm")
    parser.add_argument("--new", type=Path,
                        default=here.parent / "machines/zfc236_old.tm")
    parser.add_argument("--output", type=Path,
                        default=here.parent / "evidence/fold236_independent.json")
    args = parser.parse_args()
    old_bytes, new_bytes = args.old.read_bytes(), args.new.read_bytes()
    old, old_states, old_start = read_table(old_bytes)
    new, new_states, new_start = read_table(new_bytes)
    assert old_start == new_start == 95
    assert len(old_states) == 237 and len(new_states) == 236
    assert new_states == old_states - {223}
    phi = lambda q: 182 if q == 223 else q

    # The only arrival writes the tag immediately to the left of the head.
    guards = {}
    for q, tag, predecessor in ((182, 1, (76, 1)), (223, 0, (237, 0))):
        incoming = [(state, bit, *edge) for (state, bit), edge in old.items()
                    if edge[2] == q]
        assert incoming == [(*predecessor, tag, 1, q)], (q, incoming)
        assert old_start != q
        guards[q] = {"left_bit": tag, "complete_incoming_rows": incoming}

    ordinary = 0
    for (q, b), (w, d, z) in old.items():
        if q not in (182, 223):
            assert new[phi(q), b] == (w, d, phi(z)), (q, b)
            ordinary += 1
    assert ordinary == 470

    expected = {(182, 0): (198, 136, 187),
                (182, 1): (210, 177, 212),
                (223, 0): (198, 206, 23),
                (223, 1): (210, 114, 70)}
    exceptional = []
    for (q, bit), expected_states in expected.items():
        # Every read in the three-step block is at one of these two cells.
        # Every write preserves the read value, proving whole-tape equality.
        tape = {-1: guards[q]["left_bit"], 0: bit}
        state, head, trace = phi(q), 0, []
        for step in range(3):
            assert state != 254 and head in tape
            read = tape[head]
            write, move, target = new[state, read]
            assert write == read
            trace.append([state, head, read, write, move, target])
            head += move
            state = target
            assert state == expected_states[step]
        assert head == 1
        assert old[q, bit] == (bit, 1, state)
        exceptional.append({"old_state": q, "read_bit": bit,
                            "left_bit": guards[q]["left_bit"],
                            "new_trace": trace, "steps": 3,
                            "entire_tape_preserved": True,
                            "old_target": state, "head_change": head})

    result = {
        "status": "PASS_LITERAL_PREMISES_OF_FOUR_CASE_PROOF",
        "old_sha256": hashlib.sha256(old_bytes).hexdigest(),
        "new_sha256": hashlib.sha256(new_bytes).hexdigest(),
        "old_states": 237, "new_states": 236,
        "start": 95, "halt": 254, "state_map": {"223": 182},
        "head_and_tape_map": "identity", "guards": guards,
        "ordinary_rows": ordinary, "exceptional_rows": exceptional,
        "conclusion": "Ordinary mathematical positive-block proof: all common initial tapes and head positions have identical halting behavior; even terminal head and tape agree.",
        "formalization_status": "Not a proof-assistant proof of this Python program or an internal PA endpoint."
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({k: v for k, v in result.items()
                      if k not in ("guards", "exceptional_rows")}, indent=2))


if __name__ == "__main__":
    main()
