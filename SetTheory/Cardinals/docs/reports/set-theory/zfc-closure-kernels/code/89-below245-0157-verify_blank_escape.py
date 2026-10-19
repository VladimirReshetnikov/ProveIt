#!/usr/bin/env python3
"""Replay a finite proof that every start of the spare-zero table is trivial.

The infinite continuation is a single blank-ray self-loop. Its proof is the
induction stated in the accompanying note, not extrapolation from a run bound.
"""
import argparse
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def read_table(path):
    table = {}
    for line in path.read_text().splitlines():
        if not line or line.startswith('#'):
            continue
        q, bit, write, move, successor = line.split()
        key = int(q), int(bit)
        assert key not in table
        assert bit in ('0', '1') and write in ('0', '1') and move in ('L', 'R')
        table[key] = int(write), 1 if move == 'R' else -1, int(successor)
    states = {q for q, _ in table}
    assert len(states) == 245 and len(table) == 490
    assert set(table) == {(q, b) for q in states for b in (0, 1)}
    assert {t for w, d, t in table.values()} - states == {254}
    return table, sorted(states)


def dense_replay(table, start, steps):
    """Independent array tape, exact fixed time, complete one-cell comparison."""
    origin = steps + 1
    tape = bytearray(2 * steps + 3)
    position, state = origin, start
    rows = [None] * 512
    for (q, b), row in table.items():
        rows[2 * q + b] = row
    for _ in range(steps):
        write, motion, state = rows[2 * state + tape[position]]
        tape[position] = write
        position += motion
    return state, position - origin, [i - origin for i, bit in enumerate(tape) if bit]


def classify(table, start):
    state, head, ones = start, 0, set()
    for step in range(6001):
        if state == 254:
            record = dict(start=start, kind='HALT', steps=step, state=state,
                          head=head, ones=sorted(ones))
            break
        write, motion, successor = table[state, int(head in ones)]
        outward_blank = (not ones or
                         (head > max(ones) if motion == 1 else head < min(ones)))
        if head not in ones and successor == state and outward_blank:
            record = dict(start=start, kind='BLANK_RAY_ESCAPE', steps=step,
                          state=state, head=head, ones=sorted(ones),
                          self_loop=[write, motion, successor],
                          continuation='state unchanged; head advances by motion each step; '
                                       'all newly encountered cells are zero')
            break
        if write:
            ones.add(head)
        else:
            ones.discard(head)
        head += motion
        state = successor
    else:
        raise AssertionError(('No complete certificate within verifier cap', start))
    assert dense_replay(table, start, record['steps']) == (
        record['state'], record['head'], record['ones'])
    return record


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--table', type=Path, default=ROOT/'inputs/spare0_245_old.tm')
    parser.add_argument('--output', type=Path, default=ROOT/'results/spare0_blank_certificate.json')
    args = parser.parse_args()
    assert __debug__, 'Assertions must remain enabled.'
    table, states = read_table(args.table)
    assert table[255, 0] == (0, -1, 255)
    records = [classify(table, start) for start in states]
    main_start = next(r for r in records if r['start'] == 95)
    assert {k: main_start[k] for k in ('steps', 'state', 'head', 'ones')} == dict(
        steps=78, state=42, head=4, ones=[-3, -2, 2])
    assert table[42, 0] == (1, 1, 42)
    halts = [r for r in records if r['kind'] == 'HALT']
    escapes = [r for r in records if r['kind'] == 'BLANK_RAY_ESCAPE']
    assert [(r['start'], r['steps']) for r in halts] == [(73, 5380), (83, 5379)]
    assert len(escapes) == 243
    result = dict(status='PASS_FINITE_PREFIXES_AND_INDUCTIVE_ESCAPE',
                  table_sha256=hashlib.sha256(args.table.read_bytes()).hexdigest(),
                  working_states=len(states), halting_starts=len(halts),
                  provable_escape_starts=len(escapes), unresolved_starts=0,
                  maximum_prefix_steps=max(r['steps'] for r in records),
                  independent_sparse_dense_agreement=True, records=records,
                  scope='Complete classification of blank starts for this one modified table. '
                        'It is not a lower bound for consistency machines.')
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps({k: v for k, v in result.items() if k != 'records'}, indent=2))


if __name__ == '__main__':
    main()
