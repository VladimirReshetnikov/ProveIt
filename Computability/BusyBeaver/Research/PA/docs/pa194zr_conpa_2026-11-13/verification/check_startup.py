#!/usr/bin/env python3
"""Independent literal-row check of PA194ZR's exact finite blank startup.

No compiler or inherited simulator imports. A finite set represents all
one-cells, so equality checks the entire otherwise-zero bi-infinite tape.
The physical file values are those specified by the inherited source entry
convention; this script does not prove that convention's logical meaning.
"""
import argparse
import hashlib
import json
from pathlib import Path


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--table', type=Path, required=True)
    p.add_argument('--sites', type=Path, required=True)
    p.add_argument('--output', type=Path, required=True)
    a = p.parse_args()
    rows = {}
    for line in a.table.read_text().splitlines():
        state, bit, written, direction, target = line.split()
        key = int(state), int(bit)
        if key in rows or direction not in ('L', 'R'):
            raise ValueError('Invalid or repeated transition')
        rows[key] = int(written), (-1 if direction == 'L' else 1), int(target)
    path = json.loads(a.sites.read_text())[25][0]
    if any(b not in '01' for b in path) or len(path) > 48:
        raise ValueError('Invalid source address')
    physical = [0, 0, 0, 0, 0, 0, 2, 0, 0] + [1] * 26
    # At head -2: a marker one at -1 relative to head, the address padded
    # with zeros to 48 cells, then one and the file 01^(r+1) per register.
    relative = {-1, 48} | {i for i, bit in enumerate(path) if bit == '1'}
    next_cell = 49
    for value in physical:
        relative.update(range(next_cell + 1, next_cell + value + 2))
        next_cell += value + 2
    expected_ones = {i - 2 for i in relative}
    state, head, ones = 74, 0, set()
    first_match = None
    for step in range(1, 59817):
        if state == 254:
            raise ValueError(f'Premature halt at {step-1}')
        written, delta, target = rows[state, int(head in ones)]
        if written == 1:
            ones.add(head)
        elif written == 0:
            ones.discard(head)
        else:
            raise ValueError('Invalid output bit')
        head += delta
        state = target
        if (state, head, ones) == (84, -2, expected_ones):
            if first_match is None:
                first_match = step
    if first_match != 59816:
        raise ValueError(f'Expected first exact clean frame at59816, got{first_match}')
    result = {
        'ok': True,
        'table_sha256': hashlib.sha256(a.table.read_bytes()).hexdigest(),
        'start_state': 74,
        'initial_head': 0,
        'blank_symbol': 0,
        'first_exact_clean_frame': first_match,
        'source_site': 25,
        'source_path': path,
        'final_state': state,
        'final_head': head,
        'physical_register_file': physical,
        'complete_tape_one_cells': sorted(ones),
        'scope': 'Exact finite startup only; no claim about later halting.',
    }
    a.output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({k: result[k] for k in (
        'ok', 'table_sha256', 'first_exact_clean_frame', 'final_state', 'final_head'
    )}, indent=2))


if __name__ == '__main__':
    main()
