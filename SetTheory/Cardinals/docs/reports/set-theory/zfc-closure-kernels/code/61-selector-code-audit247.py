#!/usr/bin/env python3
"""Freeze and independently replay the 247-state prefix-carry construction.

Run from any directory. The optional --source selects the original-label
prefix250 table. The default locates the bundled reference250 table.
Only standard Python modules are required; use without -O.

This is an exact finite bootstrap certificate, not a proof of nonhalting or
of the universal clean-frame simulation. Those proof obligations are separate.
"""
from __future__ import annotations

import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import time

SOURCE_SHA256 = "fd455304bad82a6da7ab83149352d0b1db27557582c4cc6312de003c96ff4e43"
BOOT_STEPS = 741241
PHYSICAL = (6, 2, 0, 4, 3, 7, 8, 5, 1)


def parse(raw):
    table = {}
    initial = None
    for line in raw.decode("ascii").splitlines():
        if line.startswith("#! start "):
            initial = int(line.split()[-1])
        if not line or line.startswith("#"):
            continue
        q, b, w, d, t = line.split()
        q, b, w, t = map(int, (q, b, w, t))
        assert b in (0, 1) and w in (0, 1) and d in ("L", "R")
        assert (q, b) not in table
        table[q, b] = w, d, t
    states = {q for q, b in table}
    assert initial in states
    assert set(table) == {(q, b) for q in states for b in (0, 1)}
    return table, initial


def encode(table, initial):
    return (f"#! start {initial}\n" + "".join(
        f"{q} {b} {w} {d} {t}\n" for (q, b), (w, d, t) in sorted(table.items())
    )).encode("ascii")


def construct(source):
    raw = source.read_bytes()
    assert hashlib.sha256(raw).hexdigest() == SOURCE_SHA256
    prefix250, initial = parse(raw)
    assert initial == 97 and len(prefix250) == 500
    # The only deleted-state entry in the remaining table is 60/read0 -> 0.
    external_entries = sorted((q, b, t) for (q, b), (w, d, t) in prefix250.items()
                              if q not in (0, 1, 3) and t in (0, 1, 3))
    assert external_entries == [(60, 0, 0)]
    assert prefix250[0, 1] == prefix250[20, 1] == (0, "L", 2)
    assert prefix250[20, 0] == (1, "L", 2)
    table = {key: row for key, row in prefix250.items() if key[0] not in (0, 1, 3)}
    assert table[60, 0] == (0, "R", 0)
    table[60, 0] = (0, "R", 20)
    states = {q for q, b in table}
    assert states == (set(range(254)) - {0, 1, 3, 5, 8, 43, 59, 85}) | {255}
    assert len(states) == 247 and len(table) == 494
    assert {t for w, d, t in table.values()} - states == {254}
    # Equivalent intermediate machine: retarget 0/read0 to 2, remove 1,3,
    # then identify the now exactly equal states 0 and 20.
    intermediate = {key: row for key, row in prefix250.items() if key[0] not in (1, 3)}
    intermediate[0, 0] = (1, "L", 2)
    assert all(intermediate[0, b] == intermediate[20, b] for b in (0, 1))
    def quotient(q):
        return 20 if q == 0 else q
    for (q, b), (w, d, t) in intermediate.items():
        assert table[quotient(q), b] == (w, d, quotient(t))
    order = [initial] + sorted(states - {initial})
    mapping = {q: i for i, q in enumerate(order)}
    canonical = {(mapping[q], b): (w, d, 247 if t == 254 else mapping[t])
                 for (q, b), (w, d, t) in table.items()}
    return table, canonical, mapping


def sparse(table, initial, steps):
    state, head, ones = initial, 0, set()
    visits = Counter()
    for _ in range(steps):
        assert state != 254, "unexpected early halt"
        read = int(head in ones)
        visits[state, read] += 1
        write, direction, state = table[state, read]
        if write:
            ones.add(head)
        else:
            ones.discard(head)
        head += 1 if direction == "R" else -1
    return state, head, ones, visits


def dense_canonical(table, steps):
    # Independent loop, direct canonical array, dense bytearray tape.
    rows = [[None, None] for _ in range(247)]
    for (q, b), (w, d, t) in table.items():
        rows[q][b] = w, 1 if d == "R" else -1, t
    offset = steps + 1
    tape = bytearray(2 * steps + 3)
    position = offset
    state = 0
    for _ in range(steps):
        assert state != 247, "unexpected early halt"
        write, movement, next_state = rows[state][tape[position]]
        tape[position] = write
        position += movement
        state = next_state
    ones = {i - offset for i, value in enumerate(tape) if value}
    return state, position - offset, ones


def decode_root(state, head, ones):
    assert state == 96 and head == -5 and min(ones) == -6
    header = min(i for i in ones if i >= head)
    assert header == 245 and header - head == 250
    values = []
    cursor = header + 1
    rightmost = max(ones)
    while cursor <= rightmost:
        assert cursor not in ones and cursor + 1 in ones
        cursor += 1
        first = cursor
        while cursor in ones:
            cursor += 1
        values.append(cursor - first - 1)
    assert values[:9] == [0, 0, 0, 3, 0, 0, 3, 0, 0]
    assert values[9:] == [1] * 235
    assert len(values) == 244 and cursor == 975 and rightmost == 974
    logical = [values[i] for i in PHYSICAL]
    assert logical == [3, 0, 0, 0, 3, 0, 0, 0, 0]
    # Entire tape comparison is stronger than only matching the first blocks.
    expected = {-6, 245, 247, 249, 251, 253, 254, 255, 256,
                258, 260, 262, 263, 264, 265, 267, 269}
    expected |= {271 + 3*j + bit for j in range(235) for bit in (0, 1)}
    assert ones == expected and len(ones) == 487
    return dict(marker=-6, header=header, gap=250, extra_gap=210, pc="",
                physical_primary=values[:9], logical_primary=logical,
                spare_count=235, spare_values=values[9:],
                all_one_positions=sorted(ones), all_other_cells_zero=True,
                one_count=487, rightmost_one=974)


def main():
    if not __debug__:
        raise SystemExit("Do not use -O: assertions are required.")
    parser = argparse.ArgumentParser()
    here = Path(__file__).resolve().parent
    parser.add_argument("--source", type=Path,
        default=here.parent / "reference250/machine/zfc_prefix250_old.tm")
    parser.add_argument("--output", type=Path, default=here)
    args = parser.parse_args()
    started = time.monotonic()
    table, canonical, mapping = construct(args.source)
    old_bytes = encode(table, 97)
    canonical_bytes = encode(canonical, 0)
    state, head, ones, visits = sparse(table, 97, BOOT_STEPS)
    assert dense_canonical(canonical, BOOT_STEPS) == (mapping[state], head, ones)
    result = decode_root(state, head, ones)
    assert visits[97, 0] == 1
    incoming255 = sorted(key for key, row in table.items() if row[2] == 255)
    incoming97 = sorted(key for key, row in table.items() if row[2] == 97)
    assert incoming255 == [(75, 0)] and incoming97 == [(255, 0)]
    graph_seen = set()
    pending = [0]
    while pending:
        q = pending.pop()
        if q == 247 or q in graph_seen:
            continue
        graph_seen.add(q)
        pending.extend(canonical[q, b][2] for b in (0, 1))
    assert len(graph_seen) == 247
    result.update(status="PASS", bootstrap_steps=BOOT_STEPS,
        source_sha256=SOURCE_SHA256,
        old_sha256=hashlib.sha256(old_bytes).hexdigest(),
        canonical_sha256=hashlib.sha256(canonical_bytes).hexdigest(),
        working_states=247, rows=494, old_start=97, canonical_start=0,
        old_halt=254, canonical_halt=247, old_state=state,
        canonical_state=mapping[state], head=head,
        graph_reachable_working_states=len(graph_seen),
        dual_sparse_dense_canonical_agreement=True,
        initializer_zero_visits=visits[97, 0],
        incoming255=incoming255, incoming97=incoming97,
        removed_from_prefix250=[0, 1, 3],
        modified_surviving_rows=[dict(state=60, read=0,
            before=[0, "R", 0], after=[0, "R", 20])],
        scope="Exact finite bootstrap and table identity; universal runtime transport is a separate proof.",
        elapsed_seconds=time.monotonic() - started)
    args.output.mkdir(parents=True, exist_ok=True)
    (args.output / "zfc_prefix247_old.tm").write_bytes(old_bytes)
    (args.output / "zfc_prefix247.tm").write_bytes(canonical_bytes)
    (args.output / "renumbering247.json").write_text(json.dumps(dict(
        old_to_canonical=mapping, canonical_to_old={v: k for k, v in mapping.items()},
        old_sha256=result["old_sha256"], canonical_sha256=result["canonical_sha256"]
    ), indent=2) + "\n")
    (args.output / "bootstrap247.json").write_text(json.dumps(result, indent=2) + "\n")
    (args.output / "bootstrap247-row-visits.json").write_text(json.dumps(
        [{"state": q, "read": b, "count": n} for (q, b), n in sorted(visits.items())],
        indent=2) + "\n")
    print(json.dumps({k: v for k, v in result.items()
                      if k not in ("all_one_positions", "spare_values")}, indent=2))


if __name__ == "__main__":
    main()
