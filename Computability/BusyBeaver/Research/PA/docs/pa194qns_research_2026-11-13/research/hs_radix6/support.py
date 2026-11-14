#!/usr/bin/env python3
"""Inherited finite helper functions from the primary PA194 builder.

Python 3.10+, standard library only; run without -O. No search, network,
repository checkout, or proof assistant is required. The symbolic executor
uses the unchanged arithmetic-block lemmas in reference/M6/Runtime.lean.
The separate independent physical audit in the release checks those blocks
from literal rows. These executable certificates are not a new Lean proof.
"""
from pathlib import Path
import argparse
import hashlib
import json

import compiler as c

HERE = Path(__file__).resolve().parent
START, HALT = 74, 254
ORIGINAL_PHYSICAL = [6, 2, 0, 4, 3, 7, 8, 5, 1]
ORIGINAL_MACHINE, ORIGINAL_NODES = c.machine, c.raw_nodes
EXPECTED_NATIVE = 'e0a7397cf2134e8e7f58a8b1de2f7ff90b74ededd54c912f6ba5b7db48dabe54'
EXPECTED_DENSE = '4bfea62b17aad7d8c8c5e682fe8942e0a86b93e4351f8e675e32705bdaae007f'


def table_text(rows):
    return ''.join(f'{q} {b} {w} {"R" if d else "L"} {n}\n'
                   for (q, b), (w, d, n) in sorted(rows.items()))


def read_table(path):
    result = {}
    for line in path.read_text().strip().splitlines():
        q, b, w, d, n = line.split()
        q, b, w, n = map(int, (q, b, w, n))
        assert (q, b) not in result
        assert b in (0, 1) and w in (0, 1) and d in ('L', 'R')
        result[q, b] = w, d == 'R', n
    return result


def expanded(t):
    inc = ('leaf', 'inc', 1)
    if t == 'node60':
        return inc, inc
    if t == 'node61':
        return (inc, inc), (inc, inc)
    return tuple(map(expanded, t)) if c.isnode(t) else t


def word(t):
    return word(t[0]) + word(t[1]) if c.isnode(t) else [t]


def apply_folds(rows, folds):
    aliases = {a: b for a, b, actions in folds}
    actions = {b: acts for a, b, acts in folds}
    assert len(aliases) == len(folds)
    assert len({q for a, b, acts in folds for q in (a, b)}) == 2 * len(folds)
    out = {}
    for (q, bit), act in rows.items():
        if q in aliases:
            continue
        w, d, target = actions[q][bit] if q in actions else act
        out[q, bit] = w, bool(d), aliases.get(target, target)
    return out, aliases


def check_local_folds(raw, folded, aliases, folds):
    """Exhaust all four contexts per pair on the final simultaneous table."""
    incoming = {}
    for (q, bit), (w, d, target) in raw.items():
        incoming.setdefault(target, []).append([q, bit, w, d, target])
    cases = []
    for a, b, acts in folds:
        assert START not in (a, b)
        assert {(row[2], row[3]) for row in incoming[a]} == {(0, True)}
        assert {(row[2], row[3]) for row in incoming[b]} == {(1, True)}
        for old, history in ((a, 0), (b, 1)):
            for bit in (0, 1):
                w, d, target = raw[old, bit]
                expected = (aliases.get(target, target), 1 if d else -1,
                            {-1: history, 0: w})
                now, pos, tape = b, 0, {-1: history, 0: bit}
                trace = [[now, pos, tape[-1], tape[0]]]
                for steps in range(1, 21):
                    assert pos in (-1, 0)
                    wr, dr, now = folded[now, tape[pos]]
                    tape[pos] = wr
                    pos += 1 if dr else -1
                    trace.append([now, pos, tape[-1], tape[0]])
                    if (now, pos, tape) == expected:
                        break
                else:
                    raise AssertionError(('local simulation did not close', old, bit))
                cases.append({'old_state': old, 'history_bit': history,
                              'current_bit': bit, 'duration': steps, 'trace': trace})
    affected = {q for a, b, acts in folds for q in (a, b)}
    return {'cases': cases, 'incoming_rows': [row for q in sorted(affected)
                                            for row in incoming[q]]}


def dense_table(rows, count=194):
    controls = {q for q, bit in rows}
    assert len(controls) == count and len(rows) == 2 * count and HALT not in controls
    assert all((q, bit) in rows for q in controls for bit in (0, 1))
    assert {n for w, d, n in rows.values()} - controls == {HALT}
    order, index = [START], {START: 0}
    for q in order:
        for bit in (0, 1):
            target = rows[q, bit][2]
            if target != HALT and target not in index:
                index[target] = len(order)
                order.append(target)
    assert len(order) == count
    dense = {(index[q], bit): (w, d, count if n == HALT else index[n])
             for (q, bit), (w, d, n) in rows.items()}
    return dense, order + [HALT]


def startup(rows, path):
    """Check the complete finite-support tape, head, and clean source frame."""
    expected_head = -2
    physical = [0, 0, 0, 0, 0, 0, 2, 0, 0] + [1] * 26
    expected = {expected_head - 1, expected_head + 48}
    expected.update(expected_head + i for i, bit in enumerate(path) if bit)
    pos = expected_head + 49
    for value in physical:
        pos += 1
        expected.update(range(pos, pos + value + 1))
        pos += value + 1
    state, head, ones = START, 0, set()
    for step in range(1, 100001):
        w, d, state = rows[state, int(head in ones)]
        (ones.add if w else ones.discard)(head)
        head += 1 if d else -1
        assert state != HALT, ('blank halt during startup', step)
        if (state, head, ones) == (84, expected_head, expected):
            return {'steps': step, 'state': state, 'head': head,
                    'physical_file': physical, 'complete_tape_equality': True,
                    'one_cells': sorted(ones)}
    raise AssertionError('Exact clean frame not reached')


