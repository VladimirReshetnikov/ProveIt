#!/usr/bin/env python3
"""Independent literal audit of the attributed ProveIt 252-state baseline.

This checks finite transition data and the complete blank bootstrap only.
It does not prove unbounded simulation or any consistency assertion.
"""
from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path

PACKAGE = Path(__file__).resolve().parents[1]


def parse_table(path):
    rows = {}
    start = None
    for line_no, line in enumerate(path.read_text().splitlines(), 1):
        if line.startswith('#! start '):
            start = int(line.split()[-1])
        elif line and not line.startswith('#'):
            fields = line.split()
            if len(fields) != 5:
                raise ValueError(f'Invalid row {line_no}')
            q, b, w = map(int, fields[:3])
            d, t = fields[3], int(fields[4])
            if b not in (0, 1) or w not in (0, 1) or d not in ('L', 'R'):
                raise ValueError(f'Invalid action {line_no}')
            if (q, b) in rows:
                raise ValueError(f'Duplicate row {line_no}')
            rows[q, b] = (w, -1 if d == 'L' else 1, t)
    if start is None:
        raise ValueError('No explicit start state')
    return start, rows


def simulate(start, rows, steps):
    q, head, ones = start, 0, set()
    left = right = 0
    for step in range(steps):
        if (q, int(head in ones)) not in rows:
            raise ValueError(f'Halt or undefined action at step {step}')
        write, move, q = rows[q, int(head in ones)]
        if write:
            ones.add(head)
        else:
            ones.discard(head)
        head += move
        left, right = min(left, head), max(right, head)
    return q, head, ones, (left, right)


def decode_frame(head, ones):
    if not ones or min(ones) != head - 1:
        raise ValueError('Unexpected exterior or left marker')
    header = min(x for x in ones if x >= head)
    values, position = [], header + 1
    maximum = max(ones)
    while position <= maximum:
        if position in ones:
            raise ValueError('Missing block separator')
        position += 1
        size = 0
        while position in ones:
            size += 1
            position += 1
        if size == 0:
            raise ValueError('Empty unary block')
        values.append(size - 1)
    return header - head, values


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--table', type=Path,
                        default=PACKAGE/'baseline/zfc_permutation252.tm')
    parser.add_argument('--manifest', type=Path,
                        default=PACKAGE/'baseline/renumbering.json')
    parser.add_argument('--output', type=Path,
                        default=PACKAGE/'results/baseline_audit.json')
    args = parser.parse_args()
    manifest = json.loads(args.manifest.read_text())
    start, rows = parse_table(args.table)
    states = {q for q, _ in rows}
    if states != set(range(252)) or set(rows) != {(q, b) for q in states for b in (0, 1)}:
        raise ValueError('Not a total 252-state binary table')
    if start != 0 or any(t not in states | {252} for _, _, t in rows.values()):
        raise ValueError('Invalid start or target label')
    digest = hashlib.sha256(args.table.read_bytes()).hexdigest()
    if digest != manifest['canonical_sha256']:
        raise ValueError('Table differs from the pinned artifact')
    claimed = manifest['blank_prefix']
    q, head, ones, visited = simulate(start, rows, claimed['steps'])
    gap, values = decode_frame(head, ones)
    comparisons = {
        'state': q == claimed['state_canonical'],
        'head': head == claimed['head'],
        'complete_tape': sorted(ones) == claimed['all_one_positions'],
        'gap': gap == claimed['gap'],
        'primary': values[:9] == claimed['primary'],
        'spares': values[9:] == claimed['spares'],
    }
    if not all(comparisons.values()):
        raise ValueError(f'Bootstrap disagreement: {comparisons}')
    reached, queue = {start}, [start]
    while queue:
        q0 = queue.pop()
        for bit in (0, 1):
            t = rows[q0, bit][2]
            if t in states and t not in reached:
                reached.add(t)
                queue.append(t)
    result = {
        'scope': 'Independent finite literal bootstrap and table audit; no unbounded or logical theorem.',
        'source_commit': 'fab89c5d26b81cd2ccab2ee5d213ff23725c7726',
        'working_states': len(states), 'transitions': len(rows),
        'halting_rows': sum(t == 252 for _, _, t in rows.values()),
        'graph_reachable_states': len(reached), 'sha256': digest,
        'blank_steps': claimed['steps'], 'state': q, 'head': head,
        'gap': gap, 'one_cells': len(ones), 'blocks': len(values),
        'primary': values[:9], 'spares': values[9:],
        'one_positions': sorted(ones), 'all_other_cells_zero': True,
        'visited_head_interval': list(visited), 'comparisons': comparisons,
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2)+'\n')
    print(f'PASS: {len(states)} states; {claimed["steps"]} blank steps; exact complete frame.')


if __name__ == '__main__':
    main()
