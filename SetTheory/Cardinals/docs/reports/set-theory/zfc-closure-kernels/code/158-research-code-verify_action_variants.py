#!/usr/bin/env python3
"""Independent finite-cylinder verification of individual one-row rewrites.

The result is a proof for arbitrary tapes, not a sample of blank executions.
Every 7-cell cylinder consistent with the changed row's read symbol is checked.
The replacement run must stay inside that cylinder and match the original
one-step state, head, and complete window in a positive number of steps.
Unvisited exterior cells are arbitrary and unchanged. Each rewrite is proved
individually; simultaneous composition requires a separate argument.
"""
from pathlib import Path
import argparse
import hashlib
import itertools
import json


def parse(path):
    table = {}
    for line in path.read_text().splitlines():
        if line and not line.startswith('#'):
            q, b, w, d, z = line.split()
            key = (int(q), int(b))
            assert key not in table
            table[key] = (int(w), 1 if d == 'R' else -1, int(z))
    return table


def verify(table, row, replacement, bound):
    write, move, target = table[row]
    assert replacement != table[row]
    max_steps = 0
    contexts = 0
    for window in itertools.product((0, 1), repeat=7):
        if window[3] != row[1]:
            continue
        wanted = list(window)
        wanted[3] = write
        actual = list(window)
        state, head = row[0], 3
        for steps in range(bound + 1):
            if steps and (state, head, actual) == (target, 3 + move, wanted):
                max_steps = max(max_steps, steps)
                contexts += 1
                break
            assert steps < bound, (row, replacement, window, 'bound')
            assert 0 <= head < 7, (row, replacement, window, 'exterior')
            key = state, actual[head]
            action = replacement if key == row else table[key]
            actual[head], delta, state = action
            head += delta
        else:
            raise AssertionError('unmatched cylinder')
    assert contexts == 64
    return max_steps


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('table', type=Path)
    p.add_argument('variants', type=Path)
    p.add_argument('--output', type=Path)
    args = p.parse_args()
    table = parse(args.table)
    variants = []
    for line in args.variants.read_text().splitlines():
        q, b, w, d, z, steps = line.split()
        row = int(q), int(b)
        action = int(w), 1 if d == 'R' else -1, int(z)
        maximum = verify(table, row, action, int(steps))
        assert maximum == int(steps)
        variants.append({'row': row, 'action': action, 'maximum_steps': maximum})
    assert len(variants) == 62
    # Negative control: a corrupt unchanged write cannot match its old endpoint.
    rejected = False
    try:
        verify(table, (0, 0), (0, 1, 94), 3)
    except AssertionError:
        rejected = True
    assert rejected
    receipt = {
        'status': 'ALL_INDIVIDUAL_REWRITES_PROVED',
        'variants': len(variants), 'cylinders': len(variants) * 64,
        'radius': 3, 'old_steps': 1, 'maximum_new_steps': 3,
        'negative_control_rejected': rejected,
        'table_sha256': hashlib.sha256(args.table.read_bytes()).hexdigest(),
        'variants_sha256': hashlib.sha256(args.variants.read_bytes()).hexdigest(),
        'scope': 'Each rewrite separately, all initial configurations and tapes; '
                 'positive exact whole-tape step refinement; no state saving.',
        'proofs': variants,
    }
    if args.output:
        args.output.write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps({k: v for k, v in receipt.items() if k != 'proofs'}, indent=2))


if __name__ == '__main__':
    main()
