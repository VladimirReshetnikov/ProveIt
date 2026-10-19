#!/usr/bin/env python3
"""Independent symbolic-open-tape proof of the Boundary239 -> 238 edit.

Only guard-forced cells are represented. Reading any unrepresented cell is
an error. Thus a successful trace does not enumerate or restrict the exterior
tape. The whole-tape identity follows because every written cell is represented.
"""
import argparse, hashlib, json, sys
from pathlib import Path


def table(path):
    result = {}
    for line in path.read_text().splitlines():
        if not line or line.startswith('#'):
            continue
        state, bit, written, direction, target = line.split()
        key = int(state), int(bit)
        assert key not in result
        assert bit in ('0', '1') and written in ('0', '1') and direction in ('L', 'R')
        result[key] = int(written), (-1 if direction == 'L' else 1), int(target)
    states = {state for state, bit in result}
    assert set(result) == {(state, bit) for state in states for bit in (0, 1)}
    assert {row[2] for row in result.values()} - states == {254}
    assert 95 in states and 96 in states
    return result


def state_map(q):
    return 80 if q == 169 else q


def execute(machine, entry, cells, steps):
    cells = dict(cells)
    head = 0
    state = entry
    trace = []
    for _ in range(steps):
        assert state != 254, 'An interior halt invalidates positive block simulation.'
        assert head in cells, ('Read of an unconstrained cell', state, head)
        read = cells[head]
        written, motion, target = machine[state, read]
        trace.append([state, head, read, written, motion, target])
        cells[head] = written
        head += motion
        state = target
    return (state, head, cells), trace


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--old', required=True, type=Path)
    parser.add_argument('--new', required=True, type=Path)
    parser.add_argument('--output', required=True, type=Path)
    args = parser.parse_args()
    if not __debug__ or sys.flags.optimize:
        raise RuntimeError('Run without Python optimization.')
    old, new = table(args.old), table(args.new)
    assert len(old) == 478 and len(new) == 476
    assert {q for q, b in new} == {q for q, b in old} - {169}
    expected = {(q, b): (w, d, state_map(t)) for (q, b), (w, d, t) in old.items() if q != 169}
    expected[80, 0] = 0, -1, 106
    expected[91, 1] = 1, -1, 167
    assert new == expected

    # Predecessor completeness makes the four bit implications inductive.
    predecessors = {q: sorted((p, b, w, d) for (p, b), (w, d, t) in old.items() if t == q)
                    for q in (67, 80, 91, 169)}
    assert predecessors == {67: [(52, 0, 0, 1), (124, 0, 0, 1)],
                            80: [(67, 1, 1, 1)],
                            91: [(80, 1, 1, 1)],
                            169: [(147, 0, 0, 1)]}
    guards = {67: {-1: 0}, 80: {-2: 0, -1: 1}, 91: {-3: 0, -2: 1, -1: 1}, 169: {-1: 0}}
    assert 95 not in guards
    for target, incoming in predecessors.items():
        for source, read, written, motion in incoming:
            forced = dict(guards.get(source, {}))
            forced[0] = read
            forced[0] = written
            assert all(forced.get(offset + motion) == bit for offset, bit in guards[target].items())

    specs = [(80, 0, {-1: 1}, 5),
             (169, 0, {-1: 0}, 3),
             (169, 1, {-1: 0, 1: 1}, 5),
             (91, 1, {-3: 0, -2: 1, -1: 1}, 9)]
    exceptional = {(q, b) for q, b, guard, steps in specs}
    records = []
    for q, bit, guard, steps in specs:
        initial = dict(guard)
        initial[0] = bit
        before, old_trace = execute(old, q, initial, 1)
        after, new_trace = execute(new, state_map(q), initial, steps)
        assert after == (state_map(before[0]), before[1], before[2])
        records.append({'old_row': [q, bit], 'guard': guard, 'new_steps': steps,
                        'old_trace': old_trace, 'new_trace': new_trace,
                        'final_state': after[0], 'final_head': after[1],
                        'read_footprint': sorted({step[1] for step in new_trace})})

    ordinary = 0
    for (state, bit), (written, motion, target) in old.items():
        if (state, bit) in exceptional:
            continue
        assert new[state_map(state), bit] == (written, motion, state_map(target))
        ordinary += 1
    assert ordinary == 474
    result = {'status': 'PASS_SYMBOLIC_OPEN_TAPE_POSITIVE_BLOCKS',
              'old_sha256': hashlib.sha256(args.old.read_bytes()).hexdigest(),
              'new_sha256': hashlib.sha256(args.new.read_bytes()).hexdigest(),
              'inductive_predecessor_guards': guards, 'predecessors': predecessors,
              'blocks': records, 'ordinary_rows': ordinary,
              'unresolved_local_premise': 'The old 169/read-1 state has a one immediately to the right; certified by the separate unbounded guard proof.',
              'scope': 'All exterior tapes are unrestricted; only cells forced by the stated guards are inspected. No startup or unbounded instruction proof is claimed by this local checker.'}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({key: value for key, value in result.items() if key not in ('blocks', 'predecessors')}, indent=2))


if __name__ == '__main__':
    main()
