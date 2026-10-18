#!/usr/bin/env python3
"""Construct and universally check a two-row, one-state reduction of Combined243.

The local Boolean enumeration checks an inductive invariant for arbitrary tapes.
The two finite blocks read only their represented cells, so their equalities are
universal in the untouched tape context. No simulation prefix proves nonhalting.
Python 3.10+, standard library only; assertions must be enabled.
"""
from __future__ import annotations
import argparse
import hashlib
import itertools
import json
from pathlib import Path

BASE_SHA = '4207fc3d1bb16f3c64c3cff0980eaa1486160c3f467aee7685740a39e3df7300'

def read_table(path):
    table, start = {}, None
    for line in path.read_text().splitlines():
        if line.startswith('#! start '):
            assert start is None
            start = int(line.split()[-1])
        elif line and not line.startswith('#'):
            q, b, w, d, t = line.split()
            q, b, w, t = map(int, (q, b, w, t))
            assert b in (0, 1) and w in (0, 1) and d in ('L', 'R')
            assert (q, b) not in table
            table[q, b] = (w, 1 if d == 'R' else -1, t)
    states = {q for q, b in table}
    assert set(table) == {(q, b) for q in states for b in (0, 1)}
    halts = {t for w, d, t in table.values()} - states
    assert len(halts) == 1 and start in states
    return table, start, states, halts.pop()

def encode(table, start):
    rows = [f'#! start {start}']
    rows += [f'{q} {b} {w} {"R" if d == 1 else "L"} {t}'
             for (q, b), (w, d, t) in sorted(table.items())]
    return ('\n'.join(rows) + '\n').encode()

def invariant(q, h, tape):
    return ((q not in (18, 47, 65) or tape[h-1] == 0)
            and (q != 27 or tape[h] == 0))

def block(table, state, tape, steps):
    tape, h, trace = dict(tape), 0, []
    for _ in range(steps):
        # Reading outside the represented window would invalidate a universal
        # finite-context certificate; do not silently supply a zero there.
        assert h in tape, (state, h, tape)
        b = tape[h]
        w, d, target = table[state, b]
        trace.append([state, h, b, w, d, target])
        tape[h], h, state = w, h+d, target
    return (state, h, tape), trace

def main():
    if not __debug__:
        raise RuntimeError('Do not run with Python -O: assertions are required.')
    ap = argparse.ArgumentParser()
    ap.add_argument('baseline', type=Path)
    ap.add_argument('--output', type=Path, required=True)
    args = ap.parse_args()
    args.output.mkdir(parents=True, exist_ok=True)
    assert hashlib.sha256(args.baseline.read_bytes()).hexdigest() == BASE_SHA
    old, start, states, halt = read_table(args.baseline)
    assert (start, len(states), halt) == (95, 243, 254)
    assert old[15, 0] == (0, 1, 21) and old[15, 1] == (1, 1, 22)
    assert old[11, 0] == (0, 1, 15) and old[27, 1] == (1, 1, 39)
    new = {k: v for k, v in old.items() if k[0] != 15}
    new[11, 0] = (0, 1, 27)
    new[27, 1] = (1, 1, 22)
    assert len(new) == 484 and all(t != 15 for w, d, t in new.values())
    edits = [[q, b, list(old[q, b]), list(new[q, b])]
             for q, b in sorted(new) if old[q, b] != new[q, b]]
    assert [x[:2] for x in edits] == [[11, 0], [27, 1]]

    # Complete predecessor inventories, checked against the literal input table.
    incoming = {target: [[q, b, w, d] for (q, b), (w, d, t) in sorted(old.items())
                         if t == target] for target in (15, 18, 27, 47, 65)}
    assert incoming == {
        15: [[11, 0, 0, 1]],
        18: [[12, 0, 0, 1], [148, 0, 0, 1]],
        27: [[18, 0, 0, -1], [47, 0, 0, -1], [65, 0, 0, -1]],
        47: [[33, 0, 0, 1], [144, 0, 0, 1], [167, 0, 0, 1]],
        65: [[51, 0, 0, 1], [81, 0, 0, 1]],
    }

    # This is an exhaustive finite truth-table proof of one-step inductiveness.
    # The ±2 window contains every read appearing in I(q,0,T) or I(q',d,T').
    invariant_cases = 0
    for bits in itertools.product((0, 1), repeat=5):
        tape = dict(zip(range(-2, 3), bits))
        assert invariant(start, 0, tape)
        for q in states:
            if not invariant(q, 0, tape):
                continue
            w, d, target = old[q, tape[0]]
            after = dict(tape)
            after[0] = w
            assert invariant(target, d, after), (q, tape, target, after)
            invariant_cases += 1

    # Every paired endpoint excludes deleted state15. The only feasible changed
    # outgoing row is11/0. Row27/1 is impossible in the ORIGINAL invariant.
    ordinary_rows = []
    for q, b in sorted(new):
        if (q, b) in ((11, 0), (27, 1)):
            continue
        assert old[q, b] == new[q, b]
        assert old[q, b][2] != 15
        ordinary_rows.append([q, b])
    assert len(ordinary_rows) == 482
    assert all(not invariant(27, 0, {0: 1, -1: b}) for b in (0, 1))

    blocks = []
    for b in (0, 1):
        tape = {0: 0, 1: b}
        old_endpoint, old_trace = block(old, 11, tape, 2)
        new_steps = 4 if b == 0 else 2
        new_endpoint, new_trace = block(new, 11, tape, new_steps)
        assert old_endpoint == new_endpoint == (21 if b == 0 else 22, 2, tape)
        assert all(r[0] != halt for r in old_trace + new_trace)
        blocks.append(dict(next_bit=b, old_steps=2, new_steps=new_steps,
                           old_trace=old_trace, new_trace=new_trace,
                           endpoint_state=old_endpoint[0], endpoint_head=2,
                           tape_unchanged=True, reads_within=[0, 1]))

    old_data = encode(new, start)
    retained = states - {15}
    renumber = {q: i for i, q in enumerate([start] + sorted(retained - {start}))}
    renumber[halt] = len(retained)
    canonical = {(renumber[q], b): (w, d, renumber[t])
                 for (q, b), (w, d, t) in new.items()}
    canonical_data = encode(canonical, 0)
    (args.output/'zfc_zero_reuse242_old.tm').write_bytes(old_data)
    (args.output/'zfc_zero_reuse242.tm').write_bytes(canonical_data)
    (args.output/'renumbering.json').write_text(json.dumps({
        'old_to_canonical': renumber,
        'canonical_to_old': {v: k for k, v in renumber.items()},
    }, indent=2) + '\n')
    record = dict(status='PASS_UNIVERSAL_LOCAL_TRANSFER',
        baseline_sha256=BASE_SHA,
        old_table_sha256=hashlib.sha256(old_data).hexdigest(),
        canonical_sha256=hashlib.sha256(canonical_data).hexdigest(),
        states=242, rows=484, old_start=95, old_halt=254,
        canonical_start=0, canonical_halt=242, canonical_dispatcher=renumber[96],
        deleted_states=[15], edits=edits, incoming=incoming,
        invariant='q in {18,47,65} implies T(h-1)=0; q=27 implies T(h)=0',
        invariant_boolean_cases=invariant_cases,
        invariant_window=[-2, -1, 0, 1, 2],
        ordinary_row_count=len(ordinary_rows), blocks=blocks,
        old_clock_bounds=[1, 2], new_clock_bounds=[1, 4],
        theorem='For every head h and arbitrary binary tape T, old and new '
                'have the same halting outcome from (95,h,T).',
        scope='Universal finite-premise checker for the accompanying ordinary '
              'proof; not a proof-assistant kernel and not a consistency proof.')
    (args.output/'zero-reuse242-proof.json').write_text(json.dumps(record, indent=2)+'\n')
    print(json.dumps({k: v for k, v in record.items() if k not in ('incoming', 'blocks')}, indent=2))

if __name__ == '__main__':
    main()
