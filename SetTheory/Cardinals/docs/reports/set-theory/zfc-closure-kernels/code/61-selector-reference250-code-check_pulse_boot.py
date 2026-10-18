#!/usr/bin/env python3
"""Independent pulse identity, incoming-edge invariant, and exact blank bootstrap.

The finite bootstrap is checked with two different tape representations.
Its exact complete tape, including the nonempty spare suffix, is compared
against a separately specified finite set of positions. No long-run sample
is used as a nonhalting proof.
"""
from __future__ import annotations
from collections import Counter
from itertools import product
import json
from rebuild_machines import ROOT, build, PHYSICAL, OLD_FINAL_SHA256

BOOT_STEPS = 585431

def sparse(table, state, head, ones, steps):
    ones = set(ones)
    visits = Counter()
    for _ in range(steps):
        assert state != 254, "unexpected halt in the certified finite prefix"
        read = int(head in ones)
        visits[state, read] += 1
        write, direction, state = table[state, read]
        if write:
            ones.add(head)
        else:
            ones.discard(head)
        head += 1 if direction == "R" else -1
    return state, head, ones, visits

def dense(table, steps):
    # Independent execution loop: no calls to sparse and no set-based tape.
    table_array = [[None, None] for _ in range(256)]
    for (q, b), (w, d, t) in table.items():
        table_array[q][b] = w, (1 if d == "R" else -1), t
    offset = steps + 1
    tape = bytearray(2*steps + 3)
    head = offset
    state = 97
    for _ in range(steps):
        assert state != 254
        transition = table_array[state][tape[head]]
        tape[head] = transition[0]
        head += transition[1]
        state = transition[2]
    return state, head - offset, {i - offset for i, b in enumerate(tape) if b}

def main():
    if not __debug__:
        raise SystemExit("Assertions are required; do not use -O.")
    new = build()
    old = dict(new)
    old.update({(75, 0): (0, "R", 255), (255, 0): (1, "L", 112),
        (255, 1): (1, "L", 97), (97, 0): (0, "L", 112), (97, 1): (1, "R", 97)})
    cases = 0
    for first, second in product((0, 1), repeat=2):
        for exterior in product((0, 1), repeat=5):
            tape = {i for i, b in zip((-3, -2, -1, 2, 3), exterior) if b}
            if first:
                tape.add(0)
            if second:
                tape.add(1)
            length = 1 if first else 3
            a = sparse(old, 75, 0, tape, length)[:3]
            b = sparse(new, 75, 0, tape, length)[:3]
            assert a == b
            assert a[2] - {0, 1} == tape - {0, 1}
            if first == 0:
                assert a[:2] == (131 if second == 0 else 112, -1)
                assert (0 in a[2]) == (second == 0) and 1 in a[2]
            cases += 1
    incoming255 = sorted(key for key, row in new.items() if row[2] == 255)
    incoming97 = sorted(key for key, row in new.items() if row[2] == 97)
    assert incoming255 == [(75, 0)] and incoming97 == [(255, 0)]
    assert new[75, 0] == (1, "R", 255) and new[255, 0] == (1, "L", 97)
    # These two finite graph premises prove the unbounded invariant: any 97
    # entry after startup reads the one written two steps earlier at 75/0.
    assert sparse(new, 97, 0, set(), 1)[:3] == (83, 1, {0})
    state, head, ones, visits = sparse(new, 97, 0, set(), BOOT_STEPS)
    expected = {-4, 225, 227, 229, 230, 231, 233, 235, 236,
        237, 238, 239, 241, 243, 245, 246, 248, 250}
    expected |= {252 + 3*j + bit for j in range(210) for bit in (0, 1)}
    assert (state, head) == (96, -3) and ones == expected and len(ones) == 438
    assert dense(new, BOOT_STEPS) == (state, head, ones)
    assert visits[97, 0] == 1
    assert sparse(old, 83, 1, {0}, BOOT_STEPS-1)[:3] == (state, head, ones)
    assert min(ones) == head - 1
    header = min(p for p in ones if p >= head)
    assert header == 225 and header - head == 228
    values = []
    cursor = header + 1
    while cursor <= max(ones):
        assert cursor not in ones
        cursor += 1
        start = cursor
        while cursor in ones:
            cursor += 1
        assert cursor > start
        values.append(cursor - start - 1)
    assert values[:9] == [0, 2, 0, 4, 0, 0, 1, 0, 0]
    assert values[9:] == [1]*210 and cursor == 881
    logical = [values[r] for r in PHYSICAL]
    assert logical == [1, 0, 0, 0, 4, 0, 0, 0, 2]
    # Safety is formula data: top=cache=stack=0. Numeric control fields are free.
    assert logical[1] == logical[2] == logical[5] == 0
    out = dict(status="PASS", exact_table_sha256=OLD_FINAL_SHA256,
        pulse_local_context_cases=cases,
        pulse_invariant_premises=dict(incoming255=incoming255, incoming97=incoming97),
        bootstrap_steps=BOOT_STEPS, dual_sparse_dense_agreement=True,
        state=state, head=head, marker=head-1, header=header, gap=228, extra_gap=188, pc="",
        physical_primary=values[:9], logical_primary=logical,
        spare_count=210, spare_value=1, one_count=438, last_one=880,
        all_one_positions=sorted(ones), all_other_cells_zero=True,
        initializer_read_zero_visits=visits[97, 0], safe_top_cache_stack=[0, 0, 0],
        scope="Exact finite bootstrap plus structural proof premises; not a nonhalting test.")
    (ROOT / "results/pulse-bootstrap.json").write_text(json.dumps(out, indent=2)+"\n", encoding="ascii")
    print(json.dumps({k:v for k,v in out.items() if k != "all_one_positions"}, indent=2))

if __name__ == "__main__":
    main()
