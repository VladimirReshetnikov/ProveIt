#!/usr/bin/env python3
"""Exact whole-tape blank bootstrap, using sparse and dense independent loops.

The expected frame is constructed from the logical seed, not copied from a
trajectory. No source or runtime module is imported. Python standard library.
"""
from pathlib import Path
import argparse
import hashlib
import json
import sys


def read_sparse(path):
    rows = {}
    start = None
    for line in path.read_text().splitlines():
        if line.startswith('#! start '):
            start = int(line.split()[-1])
        elif line and not line.startswith('#'):
            q, b, w, d, n = line.split()
            q, b, w, n = map(int, (q, b, w, n))
            assert (q, b) not in rows and b in (0, 1) and w in (0, 1)
            assert d in ('L', 'R')
            rows[q, b] = (w, 1 if d == 'R' else -1, n)
    assert start is not None
    return start, rows


def expected_frame():
    logical = [3, 0, 0, 0, 3, 0, 0, 0, 0]
    permutation = (6, 2, 0, 4, 3, 7, 8, 5, 1)
    physical = [0] * 9
    for i, j in enumerate(permutation):
        physical[j] = logical[i]
    assert physical == [0, 0, 0, 3, 0, 0, 3, 0, 0]
    ones = {-6, 176}
    p = 177
    for value in physical + [1] * 167:
        p += 1
        for offset in range(value + 1):
            ones.add(p + offset)
        p += value + 1
    return logical, physical, ones


def verify(canonical, inherited, ceiling=1000000):
    if not __debug__ or sys.flags.optimize:
        raise RuntimeError('Assertions must be enabled')
    logical, physical, expected = expected_frame()
    start, rows = read_sparse(canonical)
    assert start == 0 and len(rows) == 476
    assert {q for q, _ in rows} == set(range(238))
    q, h, ones, count = start, 0, set(), 0
    for count in range(ceiling + 1):
        if q == 84 and h == -5 and ones == expected:
            break
        assert q != 238, ('premature halt', count)
        assert count < ceiling, 'Bootstrap bound exhausted'
        w, d, q = rows[q, int(h in ones)]
        if w:
            ones.add(h)
        else:
            ones.discard(h)
        h += d
    # Independently parse the inherited table into flat dense arrays. This loop
    # deliberately does not reuse read_sparse, its transition map, or its tape.
    writes, moves, targets = [None]*512, [None]*512, [None]*512
    for line in inherited.read_text().splitlines():
        if not line or line.startswith('#'):
            continue
        values = line.split()
        index = 2 * int(values[0]) + int(values[1])
        assert writes[index] is None
        writes[index] = int(values[2])
        moves[index] = {'L': -1, 'R': 1}[values[3]]
        targets[index] = int(values[4])
    radius = count + 2
    tape = bytearray(2 * radius + 1)
    position, control = radius, 95
    for _ in range(count):
        index = 2 * control + tape[position]
        assert writes[index] is not None
        tape[position] = writes[index]
        position += moves[index]
        control = targets[index]
        assert 0 <= position < len(tape)
    dense_ones = {i - radius for i, value in enumerate(tape) if value}
    assert (control, position-radius, dense_ones) == (96, -5, expected)
    assert len(expected) == 351
    assert count == 409835
    return {
        'status': 'EXACT_WHOLE_TAPE_SPARSE_DENSE_BOOTSTRAP_PASS',
        'steps': count, 'canonical_state': q, 'inherited_state': control,
        'head': h, 'marker': -6, 'header': 176, 'header_distance': 181,
        'additional_gap': 117, 'pc': '', 'logical_registers': logical,
        'physical_registers': physical, 'spare_values': [1]*167,
        'one_cells': sorted(expected), 'one_cell_count': len(expected),
        'all_other_cells_zero': True,
        'canonical_sha256': hashlib.sha256(canonical.read_bytes()).hexdigest(),
        'inherited_sha256': hashlib.sha256(inherited.read_bytes()).hexdigest(),
        'checker_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        'scope': 'Exact finite blank prefix on an infinite zero tape, checked by two different tape representations and state labelings; not a full-run nonhalting claim.'}


if __name__ == '__main__':
    root = Path(__file__).resolve().parent
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--canonical', type=Path, default=root/'zfc_composed238.tm')
    ap.add_argument('--inherited', type=Path, default=root/'zfc_composed238_old.tm')
    ap.add_argument('--output', type=Path, required=True)
    args = ap.parse_args()
    result = verify(args.canonical, args.inherited)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k not in ('one_cells','spare_values')}, indent=2))
