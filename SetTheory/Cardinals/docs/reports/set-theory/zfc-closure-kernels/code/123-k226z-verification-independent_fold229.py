#!/usr/bin/env python3
"""Independent K230-label audit of the delayed-erasure fold.

The local theorem is conditional on q=140, read=1 => right=1.
This checker proves the predecessor invariant, all positive blocks, every
ordinary row, the canonical renaming, and the complete blank initialization.
The arbitrary-register runtime proof of the right-neighbor guard is separate.
Only Python's standard library is used.
"""
import argparse
from collections import Counter
import hashlib
from itertools import product
import json
from pathlib import Path


def require(p, message):
    if not p:
        raise ValueError(message)


def read(path):
    table = {}
    start = None
    for line in path.read_text().splitlines():
        if line.startswith('#! start '):
            start = int(line.split()[-1])
        if not line or line.startswith('#'):
            continue
        q, b, w, direction, z = line.split()
        q, b, w, z = map(int, (q, b, w, z))
        require(direction in ('L', 'R') and b in (0, 1) and w in (0, 1), 'Bad row')
        require((q, b) not in table, 'Duplicate row')
        table[q, b] = (w, 1 if direction == 'R' else -1, z)
    require(start == 0, 'Wrong initial state')
    return table


P = {58: {-1: 0}, 71: {-2: 0, -1: 1},
     80: {-3: 0, -2: 1, -1: 1}, 140: {-1: 0}}
LENGTH = {(71, 0): 5, (140, 0): 3, (140, 1): 5, (80, 1): 9}


def phi(q):
    return 71 if q == 140 else q


def sparse_step(table, q, h, ones):
    w, d, target = table[q, int(h in ones)]
    if w:
        ones.add(h)
    else:
        ones.discard(h)
    return target, h + d


def expected_boot_tape():
    # Exact literals in pinned Boot230.v, interpreted independently as positions.
    ones = {-6, 176}
    p = 177
    registers = [0, 0, 0, 3, 0, 0, 3, 0, 0] + [1] * 167
    for value in registers:
        ones.update(range(p + 1, p + value + 2))
        p += value + 2
    return ones


def audit(old, new, canonical):
    require(set(old) == set(product(range(230), (0, 1))), 'Wrong old state census')
    require(set(new) == set(old) - {(140, 0), (140, 1)}, 'Wrong deletion')
    require(set(canonical) == set(product(range(229), (0, 1))), 'Wrong new state census')
    expected = {(q, b): (w, d, phi(z)) for (q, b), (w, d, z) in old.items() if q != 140}
    expected[71, 0] = (0, -1, 91)
    expected[80, 1] = (1, -1, 138)
    require(new == expected, 'Unexpected retained-row change')
    renumber = {q: q - int(q > 140) for q in range(231) if q != 140}
    require(canonical == {(renumber[q], b): (w, d, renumber[z])
                          for (q, b), (w, d, z) in new.items()}, 'Renaming differs')

    # Prove inductive closure by symbolic implication, not sampled execution.
    # Every requested post-cell is either the cell just written, or a cell
    # whose value is forced by the predecessor's invariant and scanned bit.
    incoming = {}
    for target, needs in P.items():
        incoming[target] = []
        for (q, b), (w, d, z) in old.items():
            if z != target:
                continue
            assumptions = dict(P.get(q, {}))
            require(0 not in assumptions or assumptions[0] == b, 'Incompatible premise')
            assumptions[0] = b
            for offset, value in needs.items():
                before = d + offset
                known = w if before == 0 else assumptions.get(before)
                require(known == value, f'Invariant implication fails at {(q, b)}')
            incoming[target].append([q, b, w, d])
    require(0 not in P, 'Initial invariant is not vacuous')

    blocks = []
    for (q, b), length in LENGTH.items():
        assignments = 0
        for bits in product((0, 1), repeat=5):
            tape = dict(zip(range(-3, 2), bits))
            if tape[0] != b or any(tape[k] != v for k, v in P[q].items()):
                continue
            if q == 140 and b == 1 and tape[1] != 1:
                continue
            old_tape = dict(tape)
            w, d, target = old[q, b]
            old_tape[0] = w
            h, control = 0, phi(q)
            trace = []
            for tick in range(length):
                require(h in tape, 'Block reads unspecified exterior')
                bit = tape[h]
                require(control != 230, 'Internal halt')
                write, move, next_control = new[control, bit]
                trace.append([control, h, bit, write, move, next_control])
                tape[h] = write
                h += move
                control = next_control
            require((control, h, tape) == (phi(target), d, old_tape), 'Block identity fails')
            assignments += 1
        require(assignments > 0, 'Vacuous local proof')
        blocks.append({'old_row': [q, b], 'new_steps': length,
                       'admitted_assignments': assignments, 'example_trace': trace})
    ordinary = 0
    for (q, b), (w, d, z) in old.items():
        if (q, b) in LENGTH:
            continue
        require(new[phi(q), b] == (w, d, phi(z)), 'Ordinary row fails to commute')
        ordinary += 1
    require(ordinary == 456, 'Incomplete old-row coverage')

    # Exhaustive finite initialization, checking each old/new full-tape checkpoint.
    oq, nq, oh, nh = 0, 0, 0, 0
    otape, ntape = set(), set()
    new_ticks = 0
    visits = Counter()
    guard_visits = Counter()
    for tick in range(408419):
        require((nq, nh, ntape) == (phi(oq), oh, otape), 'Checkpoint mismatch')
        for k, value in P.get(oq, {}).items():
            require(int(oh + k in otape) == value, 'Startup predecessor invariant')
        b = int(oh in otape)
        if oq == 140:
            guard_visits[b] += 1
            require(not b or oh + 1 in otape, 'Startup right-neighbor guard')
        row = oq, b
        visits[row] += 1
        duration = LENGTH.get(row, 1)
        oq, oh = sparse_step(old, oq, oh, otape)
        for _ in range(duration):
            nq, nh = sparse_step(new, nq, nh, ntape)
        new_ticks += duration
    require((oq, oh, otape) == (84, -5, expected_boot_tape()), 'Old complete startup frame')
    require((nq, nh, ntape) == (oq, oh, otape), 'New complete startup frame')
    require(new_ticks == 408563, 'Unexpected new initialization clock')
    require(len(otape) == 351, 'Incorrect whole-tape support')
    return {'status': 'INDEPENDENT_LOCAL_BLOCK_AND_BOOT_PASS',
            'logical_scope': 'Positive-block equivalence conditional on the old-run right-neighbor guard; the guard is proved here on the complete initialization only.',
            'old_working_states': 230, 'new_working_states': 229,
            'incoming_invariant_implications': incoming, 'blocks': blocks,
            'ordinary_rows': ordinary, 'special_rows': 4,
            'all_old_rows_covered': True, 'canonical_bijection_checked': True,
            'bootstrap_old_steps': 408419, 'bootstrap_new_steps': new_ticks,
            'bootstrap_all_checkpoints_compared': 408420,
            'bootstrap_guard_visits': dict(guard_visits),
            'bootstrap_special_row_counts': {f'{q}/{b}': visits[q, b] for q, b in LENGTH},
            'bootstrap_all_one_positions': sorted(otape),
            'all_other_tape_cells_zero': True}


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--old', type=Path, required=True)
    p.add_argument('--new', type=Path, required=True)
    p.add_argument('--canonical', type=Path, required=True)
    p.add_argument('--output', type=Path, required=True)
    a = p.parse_args()
    receipt = audit(read(a.old), read(a.new), read(a.canonical))
    receipt['sha256'] = {name: hashlib.sha256(path.read_bytes()).hexdigest()
                         for name, path in [('old', a.old), ('new', a.new),
                                            ('canonical', a.canonical), ('checker', Path(__file__))]}
    a.output.parent.mkdir(parents=True, exist_ok=True)
    a.output.write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps({k: v for k, v in receipt.items()
                      if k not in ('bootstrap_all_one_positions', 'blocks', 'incoming_invariant_implications')}, indent=2))


if __name__ == '__main__':
    main()
