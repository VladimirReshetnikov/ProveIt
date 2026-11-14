#!/usr/bin/env python3
"""Verify a companion PA194 with the physical A/D tape blocks exchanged.

Run Python 3 without -O. The primary build and its source proof remain in
build194.py. This optional companion changes three instruction-router rows.
"""
from pathlib import Path
import argparse
import hashlib
import json
import time
import build194 as primary
import compiler as c

HERE = Path(__file__).resolve().parent
PHYSICAL = [6, 2, 0, 3, 4, 7, 8, 5, 1]
EDITS = {(17, 1): (0, True, 48),
         (144, 1): (0, True, 32),
         (161, 1): (0, True, 48)}


def table_text(rows):
    return ''.join(f'{q} {b} {w} {"R" if d else "L"} {n}\n'
                   for (q, b), (w, d, n) in sorted(rows.items()))


def dense_table(rows):
    controls = {q for q, b in rows}
    assert len(controls) == 194 and len(rows) == 388
    assert all((q, b) in rows for q in controls for b in (0, 1))
    assert {n for w, d, n in rows.values()} - controls == {254}
    order, index = [74], {74: 0}
    for q in order:
        for bit in (0, 1):
            target = rows[q, bit][2]
            if target != 254 and target not in index:
                index[target] = len(order)
                order.append(target)
    assert len(order) == 194
    dense = {(index[q], b): (w, d, 194 if n == 254 else index[n])
             for (q, b), (w, d, n) in rows.items()}
    return dense, order + [254]


def check_local_folds(raw, folded, folds):
    aliases = {a: b for a, b, actions in folds}
    incoming = {}
    for (q, bit), (w, d, target) in raw.items():
        incoming.setdefault(target, set()).add((w, d))
    for a, b, acts in folds:
        assert incoming[a] == {(0, True)} and incoming[b] == {(1, True)}
        for q, history in ((a, 0), (b, 1)):
            for bit in (0, 1):
                w, d, n = raw[q, bit]
                expected = aliases.get(n, n), 1 if d else -1, {-1: history, 0: w}
                now, pos, tape = b, 0, {-1: history, 0: bit}
                for steps in range(1, 21):
                    assert pos in tape
                    wr, dr, now = folded[now, tape[pos]]
                    tape[pos] = wr
                    pos += 1 if dr else -1
                    if (now, pos, tape) == expected:
                        break
                else:
                    raise AssertionError(('remapped fold did not close', a, b, bit, history))


def startup(rows, path):
    expected_head = -2
    physical = [0] * 9 + [1] * 26
    physical[PHYSICAL[0]] = 2
    expected = {expected_head - 1, expected_head + 48}
    expected.update(expected_head + i for i, bit in enumerate(path) if bit)
    pos = expected_head + 49
    for value in physical:
        pos += 1
        expected.update(range(pos, pos + value + 1))
        pos += value + 1
    state, head, ones = 74, 0, set()
    for step in range(1, 100001):
        w, d, state = rows[state, int(head in ones)]
        (ones.add if w else ones.discard)(head)
        head += 1 if d else -1
        assert state != 254
        if (state, head, ones) == (84, expected_head, expected):
            return {'steps': step, 'state': state, 'head': head,
                    'physical_file': physical, 'one_cells': len(ones),
                    'complete_tape_equality': True}
    raise AssertionError('No exact clean startup frame')


def build(write=False):
    if not __debug__:
        raise SystemExit('Run without Python -O; assertions implement checks.')
    started = time.monotonic()
    c.PHYSICAL[:] = [6, 2, 0, 4, 3, 7, 8, 5, 1]
    parent, parent_sites, parent_instructions, parent_receipt = primary.build(full=False)
    rows = dict(parent)
    rows.update(EDITS)
    assert all(q not in c.BOXSTATES for q, b in EDITS)
    assert all(rows[q, b] == parent[q, b]
               for q in c.BOXSTATES for b in (0, 1))
    grammar = c.read_grammar(HERE / 'source/pa194.grammar.json')
    raw, index, shape = c.build(grammar)
    raw.update(EDITS)
    folds = json.loads((HERE / 'source/pa194.folds.json').read_text())
    check_local_folds(raw, rows, folds)
    c.PHYSICAL[:] = PHYSICAL
    sites, instructions, contracts = c.source(grammar)
    assert sites == parent_sites and instructions == parent_instructions
    assert len(sites) == 3673 and len(contracts) == 4780
    runtime = c.validate(rows, contracts)
    assert runtime['ok'] and runtime['contracts'] == 4780, runtime
    blank = startup(rows, sites[25][0])
    assert blank['steps'] == 58122
    dense, labels = dense_table(rows)
    files = {'pa194_AD.native.tm': table_text(rows),
             'pa194_AD.tm': table_text(dense),
             'pa194_AD.labels.json': json.dumps(labels) + '\n'}
    for name, text in files.items():
        path = HERE / 'tables' / name
        if write:
            path.write_text(text)
        assert path.read_text() == text, ('delivered bytes disagree', name)
    receipt = {
        'family': 'PA194_AD', 'working_states': 194, 'transition_rows': 388,
        'native_start': 74, 'native_halt': 254, 'dense_start': 0, 'dense_halt': 194,
        'graph_reachable_working_controls': 194, 'raw_readers': len(shape),
        'simultaneous_folds': len(folds), 'source_sites': 3673,
        'source_instructions_and_paths_unchanged': True,
        'physical_register_map': PHYSICAL,
        'arithmetic_box_rows_unchanged': True, 'final_local_folds_checked': True,
        'changes': [{'state': q, 'read': b, 'parent': parent[q, b], 'new': act}
                    for (q, b), act in sorted(EDITS.items())],
        'symbolic_validation': runtime, 'blank_startup': blank,
        'sha256': {name: hashlib.sha256(text.encode()).hexdigest()
                   for name, text in files.items()},
        'proof_scope': 'Physical store-conjugacy transport; no new Lean or Rocq endpoint',
        'seconds': round(time.monotonic() - started, 6),
    }
    (HERE / 'evidence/pa194_AD.verification.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps(receipt, indent=2))
    return rows, sites, instructions, receipt


if __name__ == '__main__':
    if not __debug__:
        raise SystemExit('Run without Python -O; assertions implement checks.')
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--write', action='store_true', help='Rebuild delivered companion tables')
    args = parser.parse_args()
    build(args.write)
