#!/usr/bin/env python3
"""Independent finite checks for the 250-state retimed prefix-carry table.

This uses only Python's standard library. It verifies the exact final table,
the two local three-transition identities, the structural first-entry invariant,
and the complete blank bootstrap with two independent tape representations.
It does not replace the unbounded register-operation proofs or kernel-check
the mathematical calibration with ZFC. Those belong to the companion notes.
"""
from __future__ import annotations

import argparse
from collections import Counter
from hashlib import sha256
from itertools import product
import json
from pathlib import Path

EXPECTED_FINAL_SHA256 = "fd455304bad82a6da7ab83149352d0b1db27557582c4cc6312de003c96ff4e43"
BOOT_STEPS = 585431
PHYSICAL_OF_LOGICAL = (6, 2, 0, 4, 3, 7, 8, 5, 1)
OLD_ROWS = {
    (75, 0): (0, "R", 255),
    (255, 0): (1, "L", 112),
    (255, 1): (1, "L", 97),
    (97, 0): (0, "L", 112),
    (97, 1): (1, "R", 97),
}
NEW_ROWS = {
    (75, 0): (1, "R", 255),
    (255, 0): (1, "L", 97),
    (255, 1): (1, "L", 131),
    (97, 0): (1, "R", 83),
    (97, 1): (1, "L", 131),
}


def parse(raw: bytes):
    table = {}
    start = None
    for line in raw.decode("ascii").splitlines():
        if line.startswith("#! start "):
            start = int(line.split()[-1])
        if not line.strip() or line.startswith("#"):
            continue
        q, b, w, d, t = line.split()
        q, b, w, t = map(int, (q, b, w, t))
        assert b in (0, 1) and w in (0, 1) and d in ("L", "R")
        assert (q, b) not in table
        table[q, b] = w, d, t
    states = {q for q, _ in table}
    assert len(states) == 250 and len(table) == 500
    assert states == (set(range(254)) - {5, 8, 43, 59, 85}) | {255}
    assert set(table) == {(q, b) for q in states for b in (0, 1)}
    assert {t for _, _, t in table.values()} - states == {254}
    assert start == 97
    return table, start


def step(table, q, h, ones):
    w, d, target = table[q, int(h in ones)]
    if w:
        ones.add(h)
    else:
        ones.discard(h)
    return target, h + (1 if d == "R" else -1)


def sparse_run(table, q, h, ones, count):
    ones = set(ones)
    visits = Counter()
    for _ in range(count):
        assert q != 254, "unexpected early halt"
        visits[q, int(h in ones)] += 1
        q, h = step(table, q, h, ones)
    return q, h, ones, visits


def dense_blank_run(table, start, count):
    # A separate representation and loop, without calling step/sparse_run.
    # The head cannot leave [-count, count] in count binary transitions.
    offset = count + 1
    tape = bytearray(2 * count + 3)
    index, state = offset, start
    for _ in range(count):
        assert state != 254
        value, direction, successor = table[state, tape[index]]
        tape[index] = value
        index += 1 if direction == "R" else -1
        state = successor
    return state, index - offset, {i - offset for i, b in enumerate(tape) if b}


def expected_boot_ones():
    primary = {-4, 225, 227, 229, 230, 231, 233, 235, 236, 237,
               238, 239, 241, 243, 245, 246, 248, 250}
    return primary | {252 + 3 * j + b for j in range(210) for b in (0, 1)}


def parse_complete_frame(q, head, ones):
    assert q == 96 and head == -3 and min(ones) == head - 1
    header = min(x for x in ones if x >= head)
    assert header - head == 228
    cursor, values = header + 1, []
    while cursor <= max(ones):
        assert cursor not in ones
        cursor += 1
        begin = cursor
        while cursor in ones:
            cursor += 1
        assert cursor > begin
        values.append(cursor - begin - 1)
    assert values[:9] == [0, 2, 0, 4, 0, 0, 1, 0, 0]
    assert values[9:] == [1] * 210
    assert cursor == 881
    logical = [values[i] for i in PHYSICAL_OF_LOGICAL]
    assert logical == [1, 0, 0, 0, 4, 0, 0, 0, 2]
    return dict(state=q, head=head, marker=head - 1, header=header,
                gap=header - head, primary_physical=values[:9],
                primary_logical=logical, spare_count=210, spare_value=1,
                one_count=len(ones), last_one=max(ones), all_exterior_blank=True)


def verify(path: Path):
    raw = path.read_bytes()
    digest = sha256(raw).hexdigest()
    assert digest == EXPECTED_FINAL_SHA256
    new, start = parse(raw)
    assert all(new[k] == value for k, value in NEW_ROWS.items())
    old = dict(new)
    old.update(OLD_ROWS)
    assert new[131, 1] == old[131, 1] == (0, "L", 112)
    assert new[112, 0] == old[112, 0] == (1, "L", 131)

    # The finite local identity reads/writes only coordinates 0 and 1.
    # Additional contexts test that all surrounding cells stay unchanged.
    local_cases = 0
    for left, right in product((0, 1), repeat=2):
        for exterior in product((0, 1), repeat=5):
            tape = {i for i, v in zip((-3, -2, -1, 2, 3), exterior) if v}
            if left:
                tape.add(0)
            if right:
                tape.add(1)
            length = 1 if left else 3
            a = sparse_run(old, 75, 0, tape, length)[:3]
            b = sparse_run(new, 75, 0, tape, length)[:3]
            assert a == b
            if not left:
                assert a[:2] == ((131 if not right else 112), -1)
                assert a[2] - {0, 1} == tape - {0, 1}
                assert (0 in a[2]) == (right == 0) and 1 in a[2]
            local_cases += 1

    # This is the finite graph premise of the inductive invariant:
    # every later 97 entry is 75/0 -> 255/0 -> 97, reading the 1 just written
    # at the first step. Therefore 97/read0 occurs only at the blank start.
    incoming255 = [(q, b) for (q, b), (_, _, t) in new.items() if t == 255]
    incoming97 = [(q, b) for (q, b), (_, _, t) in new.items() if t == 97]
    assert incoming255 == [(75, 0)] and incoming97 == [(255, 0)]
    assert new[75, 0] == (1, "R", 255)
    assert new[255, 0] == (1, "L", 97)
    first_q, first_h, first_ones, _ = sparse_run(new, start, 0, set(), 1)
    assert (first_q, first_h, first_ones) == (83, 1, {0})

    q, h, ones, visits = sparse_run(new, start, 0, set(), BOOT_STEPS)
    assert (q, h) == (96, -3)
    assert ones == expected_boot_ones()
    assert visits[97, 0] == 1
    assert dense_blank_run(new, start, BOOT_STEPS) == (q, h, ones)
    # Reconstruct the pre-retiming runtime and reproduce the seed trajectory.
    assert sparse_run(old, 83, 1, {0}, BOOT_STEPS - 1)[:3] == (q, h, ones)
    frame = parse_complete_frame(q, h, ones)
    return dict(status="PASS", table_sha256=digest, working_states=250,
                transition_rows=500, start=97, halt=254,
                local_cases=local_cases, local_identity_steps={"read0": 3, "read1": 1},
                incoming255=incoming255, incoming97=incoming97,
                blank_first_step=dict(state=83, head=1, one_positions=[0]),
                first_step_normalized=dict(state=83, head=0, one_positions=[-1]),
                bootstrap_steps=BOOT_STEPS, normalized_seed_steps=BOOT_STEPS - 1,
                bootstrap_97_read0_visits=visits[97, 0],
                sparse_dense_complete_tape_agreement=True,
                pre_retiming_seed_endpoint_agreement=True, boot_frame=frame,
                finite_verification_scope=__doc__.strip())


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--table", type=Path,
                    default=Path(__file__).resolve().parents[1]/"machine/zfc_prefix250_old.tm")
    ap.add_argument("--output", type=Path)
    args = ap.parse_args()
    if not __debug__:
        ap.error("Assertions are required; do not run with -O.")
    result = verify(args.table)
    data = json.dumps(result, indent=2) + "\n"
    if args.output:
        args.output.write_text(data, encoding="utf-8")
    print(data, end="")


if __name__ == "__main__":
    main()
