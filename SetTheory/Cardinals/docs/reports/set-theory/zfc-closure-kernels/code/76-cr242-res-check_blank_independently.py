#!/usr/bin/env python3
"""Execute the old and new blank prefixes and compare their complete tapes."""
import argparse
import hashlib
import json
from pathlib import Path

from verify_reuse_independently import table, OLD_SHA, NEW_SHA, START, HALT


def run(rows, steps):
    state, head, ones, pulses = START, 0, set(), 0
    for tick in range(steps):
        assert state != HALT, ("unexpected halt", tick)
        bit = int(head in ones)
        if (state, bit) == (11, 0) and head + 1 not in ones:
            pulses += 1
        write, move, state = rows[state, bit]
        if write:
            ones.add(head)
        else:
            ones.discard(head)
        head += 1 if move == "R" else -1
    return state, head, ones, pulses


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("old_table", type=Path)
    ap.add_argument("new_table", type=Path)
    ap.add_argument("--output", type=Path)
    args = ap.parse_args()
    if not __debug__:
        raise RuntimeError("Assertions must remain enabled.")
    assert hashlib.sha256(args.old_table.read_bytes()).hexdigest() == OLD_SHA
    assert hashlib.sha256(args.new_table.read_bytes()).hexdigest() == NEW_SHA
    old, _ = table(args.old_table)
    new, _ = table(args.new_table)
    before = run(old, 407967)
    new_duration = 407967 + 2 * before[3]
    after = run(new, new_duration)
    assert before[:3] == after[:3]
    assert (after[0], after[1], len(after[2])) == (96, -5, 351)
    assert before[3] == 6 and new_duration == 407979
    tape_text = "\n".join(map(str, sorted(after[2]))) + "\n"
    result = dict(status="PASS_LITERAL_WHOLE_TAPE_COMPARISON",
                  old_sha256=OLD_SHA, new_sha256=NEW_SHA,
                  old_steps=407967, new_steps=new_duration,
                  old_inserted_pulse_count=before[3],
                  final_state=after[0], final_head=after[1],
                  final_ones=len(after[2]), min_one=min(after[2]), max_one=max(after[2]),
                  complete_tape_equal=True,
                  sorted_one_coordinates_sha256=hashlib.sha256(tape_text.encode("ascii")).hexdigest(),
                  scope="Actual finite execution; halting equivalence comes from the separate local proof.")
    if args.output:
        args.output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
