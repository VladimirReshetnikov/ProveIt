#!/usr/bin/env python3
"""Literal finite blank-tape simulator; a bounded run does not prove nonhalting."""
from pathlib import Path
import argparse
import hashlib
import json


def read_table(path):
    table = {}
    for number, line in enumerate(path.read_text().splitlines(), 1):
        if not line.strip() or line.lstrip().startswith('#'):
            continue
        q, b, w, d, target = line.split()
        q, b, w, target = map(int, (q, b, w, target))
        if b not in (0, 1) or w not in (0, 1) or d not in ('L', 'R'):
            raise ValueError(f'Invalid transition at line {number}')
        if (q, b) in table:
            raise ValueError(f'Duplicate row at line {number}')
        table[q, b] = w, 1 if d == 'R' else -1, target
    states = {q for q, b in table}
    if any((q, b) not in table for q in states for b in (0, 1)):
        raise ValueError('Missing transition')
    return table, states


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('table', type=Path)
    parser.add_argument('--steps', type=int, default=100000)
    parser.add_argument('--start', type=int, default=0)
    parser.add_argument('--halt', type=int, default=194)
    parser.add_argument('--full-tape', action='store_true')
    args = parser.parse_args()
    if args.steps < 0:
        parser.error('--steps must be nonnegative')
    table, states = read_table(args.table)
    if args.start not in states or args.halt in states:
        parser.error('Start must be working; halt must not be working')
    if any(target not in states | {args.halt} for w, d, target in table.values()):
        parser.error('A transition targets an unknown state')
    state, head, steps = args.start, 0, 0
    ones = set()
    while steps < args.steps and state != args.halt:
        write, direction, state = table[state, int(head in ones)]
        (ones.add if write else ones.discard)(head)
        head += direction
        steps += 1
    result = {'table': str(args.table),
              'sha256': hashlib.sha256(args.table.read_bytes()).hexdigest(),
              'working_states': len(states), 'transition_rows': len(table),
              'start': args.start, 'halt': args.halt, 'steps': steps,
              'halted': state == args.halt, 'state': state, 'head': head,
              'one_cell_count': len(ones),
              'one_cell_extent': [min(ones), max(ones)] if ones else None,
              'scope': 'Finite literal run only; no nonhalting conclusion.'}
    if args.full_tape:
        result['one_cells'] = sorted(ones)
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
