#!/usr/bin/env python3
"""Strict, independent table audit, dense renumbering, and blank replay.

This finite check proves the concrete blank prefix. Universal source and tape
simulation obligations are deliberately separate and must also be checked.
"""
from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path


def read_table(path):
    table = {}
    start = None
    for line in path.read_text().splitlines():
        if line.startswith('#! start '):
            assert start is None
            start = int(line.split()[-1])
        elif line and not line.startswith('#'):
            q, b, w, direction, target = line.split()
            q, b, w, target = map(int, (q, b, w, target))
            assert b in (0, 1) and w in (0, 1) and direction in ('L', 'R')
            assert (q, b) not in table
            table[q, b] = (w, -1 if direction == 'L' else 1, target)
    working = {q for q, b in table}
    terminal = {t for w, d, t in table.values()} - working
    assert start in working and len(terminal) == 1
    assert set(table) == {(q, b) for q in working for b in (0, 1)}
    return table, start, working, terminal.pop()


def sparse(table, start, steps):
    q, x, ones = start, 0, set()
    for _ in range(steps):
        w, dx, q = table[q, int(x in ones)]
        if w:
            ones.add(x)
        else:
            ones.discard(x)
        x += dx
    return q, x, sorted(ones)


def dense(table, start, steps):
    # Independent state lookup and tape representation; the allocation covers
    # every cell reachable in the requested number of unit head moves.
    transitions = [None] * (2 * (1 + max(q for q, _ in table)))
    for (q, b), row in table.items():
        transitions[2*q+b] = row
    origin = steps + 1
    tape = bytearray(2*steps + 3)
    q, position = start, origin
    for _ in range(steps):
        w, dx, target = transitions[2*q + tape[position]]
        tape[position] = w
        position += dx
        q = target
    return q, position-origin, [i-origin for i, b in enumerate(tape) if b]


def expected_frame():
    ones = {-6, 176}
    pos = 177
    values = [0, 0, 0, 3, 0, 0, 3, 0, 0] + [1]*167
    for value in values:
        assert pos not in ones
        ones.update(range(pos+1, pos+value+2))
        pos += value+2
    return sorted(ones)


def main():
    if not __debug__:
        raise RuntimeError('Assertions are required; do not use Python -O.')
    ap = argparse.ArgumentParser()
    ap.add_argument('--table', type=Path, required=True)
    ap.add_argument('--baseline', type=Path, required=True)
    ap.add_argument('--output', type=Path, required=True)
    args = ap.parse_args()
    assert __debug__, 'Assertions must be enabled.'
    args.output.mkdir(parents=True, exist_ok=True)
    table, start, working, halt = read_table(args.table)
    old, oldstart, oldworking, oldhalt = read_table(args.baseline)
    assert (len(working), len(table), start, halt) == (244, 488, 95, 254)
    assert oldworking - working == {26} and not working - oldworking
    assert (oldstart, oldhalt) == (start, halt)
    edits = [(q, b, old[q, b], table[q, b]) for q, b in sorted(table) if old[q, b] != table[q, b]]
    assert edits == [(12, 0, (0, 1, 17), (0, 1, 18)), (12, 1, (1, 1, 18), (1, 1, 17)), (17, 1, (1, 1, 26), (0, -1, 20))]
    order = [start] + sorted(working - {start})
    renumber = {q: i for i, q in enumerate(order)}
    renumber[halt] = len(working)
    canonical = {(renumber[q], b):(w, dx, renumber[t]) for (q,b),(w,dx,t) in table.items()}
    lines = ['#! start 0'] + [f'{q} {b} {w} {"L" if dx < 0 else "R"} {t}'
        for (q,b),(w,dx,t) in sorted(canonical.items())]
    data = ('\n'.join(lines)+'\n').encode()
    assert data == args.table.with_name('machine.tm').read_bytes(), 'Supplied canonical table differs from independently computed dense renumbering.'
    assert hashlib.sha256(args.baseline.read_bytes()).hexdigest() == 'f8dbeacdad5fd89c57e3f240781324b09110be8e0ccdb838a9c710fb28d2a267'
    (args.output/'zfc244.tm').write_bytes(data)
    (args.output/'zfc244_old.tm').write_bytes(args.table.read_bytes())
    (args.output/'renumbering.json').write_text(json.dumps(renumber, indent=2)+'\n')
    steps = 407931
    expected = (96, -5, expected_frame())
    assert sparse(table, start, steps) == expected
    assert dense(table, start, steps) == expected
    assert sparse(canonical, 0, steps) == (renumber[96], *expected[1:])
    assert dense(canonical, 0, steps) == (renumber[96], *expected[1:])
    record = dict(status='PASS_INDEPENDENT_244_TABLE_AND_BLANK_PREFIX',
        working_states=244, transitions=488, start=0, halt=244,
        dispatcher=renumber[96], old_start=95, old_halt=254, old_dispatcher=96,
        table_sha256=hashlib.sha256(data).hexdigest(),
        old_table_sha256=hashlib.sha256(args.table.read_bytes()).hexdigest(),
        baseline_sha256=hashlib.sha256(args.baseline.read_bytes()).hexdigest(),
        deleted_state=26, transition_changes=edits,
        blank_steps=steps, head=-5, marker=-6, header=176, header_distance=181,
        physical_registers=[0,0,0,3,0,0,3,0,0],
        logical_registers=[3,0,0,0,3,0,0,0,0],
        spare_count=167, spare_values=[1]*167,
        all_one_positions=expected[2], one_count=len(expected[2]),
        sparse_dense_exact_agreement_both_numberings=True,
        all_other_cells_zero=True,
        scope='Exact finite blank prefix; source equivalence and universal machine simulation checked separately.')
    (args.output/'independent-blank.json').write_text(json.dumps(record, indent=2)+'\n')
    print(json.dumps({k:v for k,v in record.items() if k not in ('all_one_positions','spare_values')}, indent=2))


if __name__ == '__main__':
    main()
