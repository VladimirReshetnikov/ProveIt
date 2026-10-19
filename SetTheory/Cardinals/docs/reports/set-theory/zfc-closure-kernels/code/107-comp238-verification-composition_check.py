#!/usr/bin/env python3
"""Independent, exact local and blank-prefix checks for Boundary239 -> M238.

This proves finite premises of the positive-block theorem. The extra global
169/read-1 right-neighbor guard is supplied by the separate unbounded checker.
No long simulation is treated as a proof of nonhalting. Standard library only.
"""
from pathlib import Path
from collections import Counter
import argparse
import hashlib
import itertools
import json
import re
import sys

OLD_SHA = 'd061770f487937f9da652919c9bc9bb79bc9bf137ca41dd7a08eb5ecda8e7719'
NEW_SHA = '069942be27db9736875ea042320e51ac3b1eac7116cbe01cdce520fa6056f78c'
CANONICAL_SHA = '909f29c493e0ccc5d6a481fd7a20a9a82eb934ab2aa7df17b5ec3789255a8c08'
OLD_BOOT_STEPS = 409691

def require(value, message):
    if not value:
        raise AssertionError(message)

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def parse(path, default_start=None):
    table = {}
    start = default_start
    seen_start = False
    for line in path.read_text(encoding='ascii').splitlines():
        if line.startswith('#! start '):
            require(not seen_start, 'Duplicate initial-state directive')
            start = int(line[9:])
            seen_start = True
        elif line and not line.startswith('#'):
            m = re.fullmatch(r'(\d+) ([01]) ([01]) ([LR]) (\d+)', line)
            require(m is not None, ('Malformed transition', line))
            q, b, w, d, z = m.groups()
            key = int(q), int(b)
            require(key not in table, ('Duplicate transition', key))
            table[key] = int(w), 1 if d == 'R' else -1, int(z)
    states = {q for q, b in table}
    require(start in states, 'Missing initial state')
    require(set(table) == {(q, b) for q in states for b in (0, 1)}, 'Partial table')
    exits = {z for w, d, z in table.values()} - states
    require(len(exits) == 1, ('Wrong halt set', exits))
    return table, start, exits.pop()

def phi(q):
    return 80 if q == 169 else q

def invariant(q, h, tape):
    return ((q != 67 or tape[h-1] == 0)
            and (q != 80 or (tape[h-1] == 1 and tape[h-2] == 0))
            and (q != 91 or (tape[h-1] == 1 and tape[h-2] == 1 and tape[h-3] == 0))
            and (q != 169 or tape[h-1] == 0))

def finite_block(table, q, tape, length):
    tape = dict(tape)
    h = 0
    trace = []
    for _ in range(length):
        require(h in tape, ('Read beyond represented footprint', q, h))
        require((q, tape[h]) in table, ('Interior halt', q))
        b = tape[h]
        w, d, z = table[q, b]
        trace.append([q, h, b, w, d, z])
        tape[h] = w
        q, h = z, h+d
    return (q, h, tape), trace

def sparse_step(table, q, h, ones):
    w, d, z = table[q, int(h in ones)]
    if w:
        ones.add(h)
    else:
        ones.discard(h)
    return z, h+d

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--old', type=Path, required=True)
    ap.add_argument('--new', type=Path, required=True)
    ap.add_argument('--canonical', type=Path, required=True)
    ap.add_argument('--output', type=Path, required=True)
    a = ap.parse_args()
    require(__debug__ and not sys.flags.optimize, 'Run with assertions enabled')
    for path, wanted in [(a.old, OLD_SHA), (a.new, NEW_SHA), (a.canonical, CANONICAL_SHA)]:
        require(digest(path) == wanted, ('Wrong exact file', path))
    old, os, oh = parse(a.old, 95)
    new, ns, nh = parse(a.new, 95)
    canonical, cs, ch = parse(a.canonical)
    require((len(old), len(new), os, ns, oh, nh) == (478, 476, 95, 95, 254, 254), 'Convention mismatch')
    expected = {(q, b): (w, d, phi(z)) for (q, b), (w, d, z) in old.items() if q != 169}
    expected[80, 0] = 0, -1, 106
    expected[91, 1] = 1, -1, 167
    require(new == expected, 'Unexpected table mutation')
    changed = [key for key in sorted(new) if old[key] != new[key]]
    require(changed == [(80, 0), (91, 1), (147, 0)], 'Wrong edit set')
    new_states = {q for q, b in new}
    order = [95] + sorted(new_states - {95})
    rename = {q: i for i, q in enumerate(order)} | {254: 238}
    require(canonical == {(rename[q], b): (w, d, rename[z]) for (q, b), (w, d, z) in new.items()}, 'Renumbering mismatch')
    require((cs, ch, len(canonical)) == (0, 238, 476), 'Wrong canonical convention')
    reached = {cs}
    frontier = [cs]
    while frontier:
        q = frontier.pop()
        for b in (0, 1):
            z = canonical[q, b][2]
            if z != ch and z not in reached:
                reached.add(z)
                frontier.append(z)
    require(reached == set(range(238)), 'Some listed working state is graph-unreachable')

    incoming = {q: [[p, b, w, d] for (p, b), (w, d, z) in sorted(old.items()) if z == q]
                for q in (67, 80, 91, 169)}
    require(incoming == {67: [[52, 0, 0, 1], [124, 0, 0, 1]],
                         80: [[67, 1, 1, 1]], 91: [[80, 1, 1, 1]],
                         169: [[147, 0, 0, 1]]}, 'Incoming ports changed')
    inv_cases = 0
    for values in itertools.product((0, 1), repeat=9):
        tape = dict(zip(range(-4, 5), values))
        require(invariant(os, 0, tape), 'Initial invariant failed')
        for q in {q for q, b in old}:
            if invariant(q, 0, tape):
                w, d, z = old[q, tape[0]]
                after = dict(tape)
                after[0] = w
                require(invariant(z, d, after), ('Invariant is not inductive', q, tape))
                inv_cases += 1

    specs = [
        (80, 0, {-1: 1}, 5, [80, 106, 92, 107, 125, 25]),
        (169, 0, {-1: 0}, 3, [80, 106, 93, 57]),
        (169, 1, {-1: 0, 1: 1}, 5, [80, 91, 167, 151, 173, 56]),
        (91, 1, {-3: 0, -2: 1, -1: 1}, 9,
         [91, 167, 151, 24, 36, 54, 71, 82, 94, 50]),
    ]
    blocks = []
    for q, b, guard, length, path in specs:
        count = 0
        samples = []
        for values in itertools.product((0, 1), repeat=5):
            tape = dict(zip(range(-3, 2), values))
            if tape[0] != b or any(tape[x] != v for x, v in guard.items()):
                continue
            goal, old_trace = finite_block(old, q, tape, 1)
            actual, new_trace = finite_block(new, phi(q), tape, length)
            require(actual == (phi(goal[0]), goal[1], goal[2]), ('Local block fails', q, b, tape))
            require([event[0] for event in new_trace] + [actual[0]] == path, 'Unexpected block path')
            samples.append({'input': tape, 'old': old_trace, 'new': new_trace})
            count += 1
        require(count > 0, 'Vacuous block guard')
        blocks.append({'old_row': [q, b], 'guard': guard, 'new_steps': length,
                       'path': path, 'assignments': count, 'traces': samples})
    exceptional = {(q, b) for q, b, guard, length, path in specs}
    ordinary = 0
    for (q, b), (w, d, z) in old.items():
        if (q, b) not in exceptional:
            require(new[phi(q), b] == (w, d, phi(z)), ('Noncommuting ordinary row', q, b))
            ordinary += 1
    require(ordinary == 474, 'Wrong ordinary-row count')

    # A finite positive-block coupling checks every old checkpoint, all cells.
    oq = nq = 95
    ox = nx = 0
    ot, nt = set(), set()
    costs = {(q, b): length for q, b, guard, length, path in specs}
    visits = Counter()
    new_ticks = 0
    head_min = head_max = 0
    for tick in range(OLD_BOOT_STEPS):
        require((phi(oq), ox, ot) == (nq, nx, nt), ('Checkpoint mismatch', tick))
        key = oq, int(ox in ot)
        if key == (169, 1):
            require(ox+1 in ot, ('Blank guard failure', tick))
        length = costs.get(key, 1)
        visits[key] += 1
        oq, ox = sparse_step(old, oq, ox, ot)
        for _ in range(length):
            nq, nx = sparse_step(new, nq, nx, nt)
            new_ticks += 1
            head_min, head_max = min(head_min, nx), max(head_max, nx)
        require((phi(oq), ox, ot) == (nq, nx, nt), ('After-block mismatch', tick))
    require((oq, ox, len(ot)) == (96, -5, 351), 'Wrong startup frame')
    require(new_ticks == OLD_BOOT_STEPS + sum((costs[k]-1)*visits[k] for k in costs), 'Clock formula failed')
    require(new_ticks == 409835, 'Unexpected startup duration')

    # A separate fixed dense tape stores 200001 cells and checks its boundary
    # on every step; thus no unrepresented exterior can affect this finite run.
    center = 100000
    tape = bytearray(200001)
    position, state = center, 0
    for tick in range(new_ticks):
        require(0 <= position < len(tape), ('Dense tape boundary', tick))
        w, d, state = canonical[state, tape[position]]
        tape[position] = w
        position += d
    dense_ones = {i-center for i, value in enumerate(tape) if value}
    require((state, position-center, dense_ones) == (84, -5, nt), 'Independent dense/canonical startup mismatch')
    physical = []
    cursor = 177
    for _ in range(9+167):
        require(cursor not in nt, ('Expected block separator', cursor))
        cursor += 1
        count = 0
        while cursor in nt:
            count += 1
            cursor += 1
        require(count >= 1, 'Empty unary block')
        physical.append(count-1)
    require(physical[:9] == [0, 0, 0, 3, 0, 0, 3, 0, 0], 'Physical seed mismatch')
    require(physical[9:] == [1]*167, 'Spare blocks mismatch')
    require(nt == {-6, 176} | {i for i in nt if 177 <= i < cursor}, 'Unexpected external one')
    result = {
        'status': 'PASS_EXACT_COMPOSITION_LOCAL_AND_BLANK',
        'old_sha256': OLD_SHA, 'new_old_labels_sha256': NEW_SHA,
        'canonical_sha256': CANONICAL_SHA, 'working_states': 238,
        'binary_rows': 476, 'canonical_start': 0, 'canonical_halt': 238,
        'canonical_dispatcher': 84, 'graph_reachable_working_states': len(reached),
        'changed_retained_rows': changed, 'unchanged_retained_rows': 473,
        'deleted_state': 169, 'incoming_ports': incoming,
        'invariant_boolean_assignments': inv_cases, 'ordinary_commuting_rows': ordinary,
        'local_blocks': blocks, 'local_assignments': sum(b['assignments'] for b in blocks),
        'runtime_guard_required': 'In old Boundary239, state169/read1 has a 1 immediately to its right.',
        'runtime_guard_proved_here': False,
        'blank': {'old_steps': OLD_BOOT_STEPS, 'new_steps': new_ticks,
                  'all_checkpoints_compared': OLD_BOOT_STEPS+1,
                  'exceptional_visits': {f'{q}/{b}': visits[q, b] for q, b in sorted(costs)},
                  'head': nx, 'head_range': [head_min, head_max], 'marker': -6,
                  'header': 176, 'gap_parameter': 117,
                  'logical_seed': [3, 0, 0, 0, 3, 0, 0, 0, 0],
                  'physical_seed': physical[:9], 'spare_count': 167, 'spare_value': 1,
                  'all_one_positions': sorted(nt), 'one_count': len(nt),
                  'all_other_cells_zero': True, 'independent_dense_canonical_match': True},
        'scope': 'Exact finite local premises and complete finite startup; combined with the unbounded guard and inherited source calibration in the report.'
    }
    a.output.parent.mkdir(parents=True, exist_ok=True)
    a.output.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps({k: v for k, v in result.items() if k not in ('local_blocks', 'blank')}, indent=2))
    print(json.dumps({k: v for k, v in result['blank'].items() if k != 'all_one_positions'}, indent=2))

if __name__ == '__main__':
    main()
