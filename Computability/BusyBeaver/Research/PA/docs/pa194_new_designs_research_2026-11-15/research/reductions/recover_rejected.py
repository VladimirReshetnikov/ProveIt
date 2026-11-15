#!/usr/bin/env python3
"""Rebuild and literally certify an invalid 193-state reduction.

This is a diagnostic counterexample, not a PA-consistency construction.
Only the Python standard library is needed. Run this file, then replay_cycles.py.
"""
from pathlib import Path
import hashlib
import json

ROOT = Path(__file__).resolve().parent
BASE_SHA = 'e0a7397cf2134e8e7f58a8b1de2f7ff90b74ededd54c912f6ba5b7db48dabe54'
CHILD_SHA = 'cb53ad33e8812dc2ebfb6a1a1b452962eeba0cf6b851d398d403a192ea0e6b80'

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def read_table(path):
    table = {}
    for line in path.read_text().splitlines():
        q, bit, write, direction, nxt = line.split()
        key = int(q), int(bit)
        assert key not in table
        assert direction in ('L', 'R')
        table[key] = int(write), direction, int(nxt)
    return table

def build_child(base):
    child = {}
    for (q, bit), old_row in base.items():
        if q == 16:
            continue
        write, direction, nxt = base[16, bit] if q == 38 else old_row
        child[q, bit] = write, direction, 38 if nxt == 16 else nxt
    assert len(child) == 386
    states = {q for q, bit in child}
    assert len(states) == 193 and 254 not in states
    assert set(child) == {(q, bit) for q in states for bit in (0, 1)}
    assert {row[2] for row in child.values()} - states == {254}
    return child

def write_table(table, path):
    path.write_text(''.join(f'{q} {b} {w} {d} {n}\n'
                            for (q, b), (w, d, n) in sorted(table.items())))

def frame(path, physical, spares, gap=0):
    ones = {-1, 48 + gap}
    ones.update(i for i, b in enumerate(path) if b == '1')
    position = 49 + gap
    for value in physical + spares:
        position += 1
        ones.update(range(position, position + value + 1))
        position += value + 1
    return ones

def config(q, head, ones):
    return {'state': q, 'head': head, 'ones': sorted(ones)}

def find_cycle(table, q, head, ones, limit=100000):
    initial = config(q, head, ones)
    seen, trace = {}, []
    for time in range(limit + 1):
        key = q, head, tuple(sorted(ones))
        if key in seen:
            preperiod = seen[key]
            return {
                'initial_configuration': initial,
                'preperiod': preperiod,
                'period': time - preperiod,
                'cycle_configuration': config(q, head, ones),
                'prefix_rows': trace[:preperiod],
                'cycle_rows': trace[preperiod:],
            }
        assert q != 254, f'Unexpected halt at time {time}'
        seen[key] = time
        bit = int(head in ones)
        write, direction, nxt = table[q, bit]
        trace.append([q, bit, write, direction, nxt])
        if write:
            ones.add(head)
        else:
            ones.discard(head)
        head += 1 if direction == 'R' else -1
        q = nxt
    raise AssertionError('Cycle search exceeded stated bound')

def main():
    base_path = ROOT / 'inputs/pa194.native.tm'
    assert sha(base_path) == BASE_SHA
    base = read_table(base_path)
    child = build_child(base)
    output = ROOT / 'rejected193'
    output.mkdir(exist_ok=True)
    child_path = output / 'REJECTED_16_to_38.native.tm'
    write_table(child, child_path)
    assert sha(child_path) == CHILD_SHA
    sites = json.loads((ROOT / 'inputs/pa194.sites.json').read_text())
    assert sites[3661] == ['101100', 'dec', 1]
    witnesses = {
        'blank': find_cycle(child, 74, 0, set()),
        'site3661_positive': find_cycle(
            child, 84, 0, frame('101100', [0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 1])),
    }
    assert (witnesses['blank']['preperiod'], witnesses['blank']['period']) == (28217, 52)
    assert (witnesses['site3661_positive']['preperiod'], witnesses['site3661_positive']['period']) == (0, 52)
    receipt = {
        'status': 'REJECTED: exact complete-configuration cycles',
        'evidence_status': 'Freshly regenerated from surviving exact primary table after tmpfs loss',
        'base_sha256': BASE_SHA,
        'rejected_native_sha256': CHILD_SHA,
        'nonhalting_controls': 193,
        'rows': 386,
        'start_state': 74,
        'halting_state': 254,
        'construction': 'Delete16; redirect every target16 to38; use both old16 rows at38.',
        'tape_semantics': 'Bi-infinite binary tape; listed positions are1 and every other position is0.',
        'witnesses': {},
    }
    for name, witness in witnesses.items():
        witness['machine_sha256'] = CHILD_SHA
        witness['case'] = name
        witness['evidence_status'] = receipt['evidence_status']
        path = output / f'{name}_cycle.json'
        path.write_text(json.dumps(witness, indent=2) + '\n')
        receipt['witnesses'][name] = {
            'file': path.name, 'sha256': sha(path),
            'preperiod': witness['preperiod'], 'period': witness['period'],
            'cycle_state': witness['cycle_configuration']['state'],
            'cycle_head': witness['cycle_configuration']['head'],
            'cycle_ones': len(witness['cycle_configuration']['ones']),
        }
    (output / 'recovery_receipt.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps(receipt, indent=2))

if __name__ == '__main__':
    main()
