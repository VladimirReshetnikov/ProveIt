#!/usr/bin/env python3
"""Independent audit of the five-row pulse retiming in prefix250.

No imported project checker is executed.  The finite local truth table is
universal because the checker records every read location and verifies that
both gadget runs inspect only the two explicitly enumerated cells.  Equality
on all uninspected cells follows from their absence from the write sets.
The companion note supplies the induction from gadget to complete runs.
"""
from __future__ import annotations

import argparse
from collections import Counter
from hashlib import sha256
import json
from pathlib import Path


EXPECTED_HASH = "fd455304bad82a6da7ab83149352d0b1db27557582c4cc6312de003c96ff4e43"
EXPECTED_STEPS = 585431
INTERNAL = {97, 255}
PHYSICAL_OF_LOGICAL = (6, 2, 0, 4, 3, 7, 8, 5, 1)
CORE_ROWS = {
    (75, 0): (0, 1, 255),
    (255, 0): (1, -1, 112),
    (255, 1): (1, -1, 97),
    (97, 0): (0, -1, 112),
    (97, 1): (1, 1, 97),
}
PULSE_ROWS = {
    (75, 0): (1, 1, 255),
    (255, 0): (1, -1, 97),
    (255, 1): (1, -1, 131),
    (97, 0): (1, 1, 83),
    (97, 1): (1, -1, 131),
}


def load_table(path):
    data = path.read_bytes()
    assert sha256(data).hexdigest() == EXPECTED_HASH
    table, start = {}, None
    for line in data.decode("ascii").splitlines():
        if line.startswith("#! start "):
            start = int(line.split()[-1])
        if line.startswith("#") or not line.strip():
            continue
        q, b, w, d, n = line.split()
        q, b, w, n = map(int, (q, b, w, n))
        assert (q, b) not in table
        assert b in (0, 1) and w in (0, 1) and d in ("L", "R")
        table[q, b] = (w, 1 if d == "R" else -1, n)
    states = {q for q, _ in table}
    assert start == 97 and len(states) == 250 and len(table) == 500
    assert set(table) == {(q, b) for q in states for b in (0, 1)}
    assert {n for w, d, n in table.values()} - states == {254}
    assert sum(n == 254 for w, d, n in table.values()) == 1
    assert all(table[k] == value for k, value in PULSE_ROWS.items())
    core = dict(table)
    core.update(CORE_ROWS)
    assert {k for k in table if table[k] != core[k]} == set(PULSE_ROWS)
    return table, core


def partial_tape_run(table, first, second, length):
    # Cells outside 0,1 are deliberately undefined.  Reading one would be an
    # error, instead of silently assuming blank.  Thus the proof covers every
    # exterior tape, including tapes of infinite support.
    bits = {0: first, 1: second}
    q, h = 75, 0
    reads, writes, trace = [], [], []
    for _ in range(length):
        assert h in bits, ("unaccounted-for exterior read", q, h)
        reads.append(h)
        value = bits[h]
        w, d, following = table[q, value]
        trace.append([q, h, value, w, d, following])
        bits[h] = w
        writes.append(h)
        q, h = following, h + d
    return (q, h, bits), reads, writes, trace


def check_universal_local_cases(pulse, core):
    branches = []
    for first, second in ((0, 0), (0, 1), (1, 0), (1, 1)):
        length = 3 if first == 0 else 1
        new, nr, nw, nt = partial_tape_run(pulse, first, second, length)
        old, cr, cw, ct = partial_tape_run(core, first, second, length)
        assert new == old
        assert set(nr + nw + cr + cw) <= {0, 1}
        expected = ((131, -1, {0: 1, 1: 1}) if second == 0 else
                    (112, -1, {0: 0, 1: 1})) if first == 0 else (
                    63, -1, {0: 1, 1: second})
        assert new == expected
        branches.append(dict(input=[first, second], steps=length,
                             output_state=new[0], relative_head=new[1],
                             output_cells=[new[2][0], new[2][1]],
                             pulse_trace=nt, core_trace=ct))
    return branches


def incoming(table, target):
    return sorted([list(k) for k, (_, _, n) in table.items() if n == target])


def check_graph_premises(pulse, core):
    assert incoming(pulse, 255) == [[75, 0]]
    assert incoming(core, 255) == [[75, 0]]
    assert incoming(pulse, 97) == [[255, 0]]
    assert incoming(core, 97) == [[97, 1], [255, 1]]
    for table in (pulse, core):
        for (q, b), (_, _, n) in table.items():
            if q not in INTERNAL | {75}:
                assert n not in INTERNAL
    # Both exits of each local case lie outside INTERNAL.  Neither internal
    # state is the halt label, and all other rows are literally identical.
    assert {63, 112, 131, 254}.isdisjoint(INTERNAL)
    return dict(pulse_incoming97=incoming(pulse, 97),
                pulse_incoming255=incoming(pulse, 255),
                core_incoming97=incoming(core, 97),
                core_incoming255=incoming(core, 255),
                unchanged_outside_rows=len(pulse) - len(PULSE_ROWS),
                internal_states=sorted(INTERNAL),
                macro_entry=75, macro_exits=[63, 112, 131])


def check_coupled_bootstrap(pulse, core):
    # Independently coded tape representations: a set for the pulse machine,
    # a dictionary for the core.  They are compared at each gadget boundary.
    pulse_ones = set()
    q, h = 97, 0
    w, d, n = pulse[q, 0]
    if w:
        pulse_ones.add(h)
    q, h = n, h + d
    assert (q, h, pulse_ones) == (83, 1, {0})
    cq, ch, core_bits = q, h, {0: 1}
    visits = Counter({(97, 0): 1})
    block_counts = Counter()
    ticks, cutpoints = 1, 0
    while ticks < EXPECTED_STEPS:
        assert q not in INTERNAL and q != 254
        length = 3 if q == 75 and h not in pulse_ones else 1
        assert ticks + length <= EXPECTED_STEPS
        block_counts[length] += 1
        for _ in range(length):
            old_state, value = q, int(h in pulse_ones)
            visits[old_state, value] += 1
            w, d, q = pulse[old_state, value]
            if w:
                pulse_ones.add(h)
            else:
                pulse_ones.discard(h)
            h += d
            # The core interpreter does not call the pulse interpreter.
            symbol = core_bits.get(ch, 0)
            write, displacement, successor = core[cq, symbol]
            if write == 0:
                core_bits.pop(ch, None)
            else:
                core_bits[ch] = 1
            ch = ch + displacement
            cq = successor
        ticks += length
        cutpoints += 1
        assert (q, h) == (cq, ch)
        assert pulse_ones == core_bits.keys()
    assert (q, h) == (96, -3)
    assert visits[97, 0] == 1
    assert min(pulse_ones) == -4
    assert len(pulse_ones) == 438
    expected_primary = {-4, 225, 227, 229, 230, 231, 233, 235, 236,
                        237, 238, 239, 241, 243, 245, 246, 248, 250}
    expected = expected_primary | {252 + 3 * j + b
                                   for j in range(210) for b in (0, 1)}
    assert pulse_ones == expected
    header = min(i for i in pulse_ones if i >= h)
    assert header == 225 and header - h == 228
    cursor, values = header + 1, []
    while cursor <= max(pulse_ones):
        assert cursor not in pulse_ones and cursor + 1 in pulse_ones
        cursor += 1
        start = cursor
        while cursor in pulse_ones:
            cursor += 1
        values.append(cursor - start - 1)
    assert values[:9] == [0, 2, 0, 4, 0, 0, 1, 0, 0]
    assert values[9:] == [1] * 210
    logical = [values[i] for i in PHYSICAL_OF_LOGICAL]
    assert logical == [1, 0, 0, 0, 4, 0, 0, 0, 2]
    return dict(actual_blank_steps=ticks, postinitial_core_steps=ticks - 1,
                compared_cutpoints=cutpoints,
                one_step_blocks=block_counts[1], three_step_blocks=block_counts[3],
                initializer_row_uses=visits[97, 0], runtime97_read1_uses=visits[97, 1],
                endpoint_state=q, endpoint_head=h, marker=min(pulse_ones),
                header=header, gap=header - h, physical=values[:9], logical=logical,
                spare_count=len(values) - 9, spare_value=1,
                exact_one_count=len(pulse_ones), last_one=max(pulse_ones),
                all_other_cells_blank=True, complete_tapes_equal_at_every_cutpoint=True)


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--table", type=Path, required=True)
    ap.add_argument("--output", type=Path)
    args = ap.parse_args()
    if not __debug__:
        ap.error("Assertions must be enabled.")
    pulse, core = load_table(args.table)
    result = dict(status="PASS", table_sha256=EXPECTED_HASH,
                  working_states=250, transition_rows=500,
                  local_cases=check_universal_local_cases(pulse, core),
                  graph_premises=check_graph_premises(pulse, core),
                  bootstrap=check_coupled_bootstrap(pulse, core),
                  interpretation="Universal local finite case split plus graph premises; "
                  "the companion note proves the unbounded cutpoint induction. "
                  "No proof assistant or logical-calibration check is claimed.")
    output = json.dumps(result, indent=2) + "\n"
    if args.output:
        args.output.write_text(output, encoding="utf-8")
    print(output, end="")


if __name__ == "__main__":
    main()
