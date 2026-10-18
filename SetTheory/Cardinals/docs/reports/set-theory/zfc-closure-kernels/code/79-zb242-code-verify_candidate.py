#!/usr/bin/env python3
"""Independent, finite source fixtures and blank replay for a 242-state table.

This checker imports no compiler, simulation checker or package code.  Its
source-level frame convention is the documented combined243 convention.
Finite tests corroborate the separate universal comparison proof; they do not
prove consistency or indefinite nonhalting.
"""
from __future__ import annotations

import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import time

SOURCE_SHA = '3ee984818f0bdfd2c4daae72aeb14340572e34d73f5cdb5616b6d29d78fcd7f4'
BASELINE_SHA = '4207fc3d1bb16f3c64c3cff0980eaa1486160c3f467aee7685740a39e3df7300'
PHYSICAL = (6, 2, 0, 4, 3, 7, 8, 5, 1)


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def read_table(path):
    table, start = {}, None
    for line in path.read_text(encoding='ascii').splitlines():
        if line.startswith('#! start '):
            assert start is None
            start = int(line.split()[-1])
        elif line and not line.startswith('#'):
            q, bit, write, direction, target = line.split()
            q, bit, write, target = map(int, (q, bit, write, target))
            assert bit in (0, 1) and write in (0, 1)
            assert direction in ('L', 'R') and (q, bit) not in table
            table[q, bit] = (write, -1 if direction == 'L' else 1, target)
    working = {q for q, _ in table}
    terminal = {target for _, _, target in table.values()} - working
    assert set(table) == {(q, bit) for q in working for bit in (0, 1)}
    assert start in working and len(terminal) == 1
    return table, start, working, terminal.pop()


def frame(head, bits, span, logical, spare):
    assert 0 <= len(bits) <= span and len(logical) == 9
    positions = {head - 1, head + span}
    positions.update(head + i for i, b in enumerate(bits) if b == '1')
    registers = [None] * 9
    for i, physical in enumerate(PHYSICAL):
        registers[physical] = logical[i]
    position = head + span + 1
    for value in registers + spare:
        assert type(value) is int and value >= 0
        positions.update(range(position + 1, position + value + 2))
        position += value + 2
    return positions


def increment(bits):
    width = len(bits)
    number = (int(bits, 2) if bits else 0) + 1
    overflow = number == 1 << width
    return (format(number % (1 << width), f'0{width}b') if width else ''), overflow


def drop_through(bits, wanted, count):
    position = len(bits)
    while count and position:
        position -= 1
        if bits[position] == wanted:
            count -= 1
    return bits[:position]


def literal_fixtures(table, sites, limit):
    rows = Counter()
    records = []
    total = 0
    started = time.monotonic()
    for index, (path, operation, register) in enumerate(sites):
        outcomes = (True, False) if operation == 'CD' else (None,)
        for zero in outcomes:
            serial = len(records)
            # Same broad fixture domain as the inherited independent regression,
            # generated locally without importing that checker.
            logical = [(17*serial + 11*j + 3*index + 7) % 23 for j in range(9)]
            if operation == 'CD':
                logical[register] = 0 if zero else 1 + (13*serial + 7*register) % 23
            spare = [(serial + 2*j + 3) % 13 for j in range(1 + serial % 5)]
            span = 64 + 17*(serial % 3)
            tape = frame(0, path, span, logical, spare)
            output, tail = logical.copy(), spare.copy()
            extra, overflow = 0, False
            if operation == 'CI':
                output[register] += 1
                tail.append(1)
                successor, overflow = increment(path)
            elif operation == 'CD' and not zero:
                output[register] -= 1
                extra = 1
                successor, overflow = increment(path)
            elif operation == 'CD':
                successor, overflow = increment(drop_through(path, '0', 1))
            elif operation == 'CB':
                successor, overflow = increment(drop_through(path, '0', register))
            elif operation == 'CC':
                successor = drop_through(path, '1', register)
            else:
                assert operation == 'CH'
                successor = ''
            endhead = -int(overflow)
            expected = None if operation == 'CH' else frame(
                endhead, successor, span + extra + int(overflow), output, tail)
            state, head = 96, 0
            for steps in range(1, limit + 1):
                key = state, int(head in tape)
                assert key in table, ('unexpected halt', serial, key)
                write, move, state = table[key]
                rows[key] += 1
                if write:
                    tape.add(head)
                else:
                    tape.discard(head)
                head += move
                if operation == 'CH' and state == 254:
                    break
                if operation != 'CH' and state == 96 and head == endhead and tape == expected:
                    break
            else:
                raise AssertionError(('fixture step limit', serial, path, operation, register,
                                      zero, state, head, sorted(tape ^ expected) if expected else None))
            total += steps
            records.append(dict(index=index, path=path, operation=operation,
                                register=register, zero=zero, steps=steps))
        if index % 1000 == 0:
            print('source sites', index, 'guard cases', len(records), flush=True)
    assert len(sites) == 6459 and len(records) == 8390
    return dict(status='PASS_FINITE_SOURCE_FIXTURES', source_leaves=len(sites),
                guarded_cases=len(records), total_transitions=total,
                maximum_case_steps=max(record['steps'] for record in records),
                minimum_case_steps=min(record['steps'] for record in records),
                covered_rows=len(rows), unused_rows=[list(key) for key in sorted(set(table)-set(rows))],
                row_counts=[[q, bit, n] for (q, bit), n in sorted(rows.items())],
                whole_tape_endpoints=True,
                arbitrary_non_guard_register_fixtures=True,
                selected_gaps=[64, 81, 98], selected_spare_lengths=[1, 2, 3, 4, 5],
                seconds=time.monotonic()-started,
                scope='Finite literal tests of every source/guard case; not an unbounded runtime proof.')


def discover_blank(table, start, expected, limit):
    tape, state, head = set(), start, 0
    for steps in range(1, limit + 1):
        write, move, state = table[state, int(head in tape)]
        if write:
            tape.add(head)
        else:
            tape.discard(head)
        head += move
        if state == 96 and head == -5 and tape == expected:
            return steps
    raise AssertionError('Complete root frame not reached within the discovery bound')


def sparse_replay(table, start, steps):
    tape, state, head = set(), start, 0
    for _ in range(steps):
        write, move, state = table[state, int(head in tape)]
        if write:
            tape.add(head)
        else:
            tape.discard(head)
        head += move
    return state, head, sorted(tape)


def dense_replay(table, start, steps):
    # A second representation and lookup path: dense byte tape and flat rows.
    rows = [None] * (2*(max(q for q, _ in table)+1))
    for (q, bit), row in table.items():
        rows[2*q+bit] = row
    offset = steps + 1
    tape = bytearray(2*steps+3)
    state, position = start, offset
    for _ in range(steps):
        write, move, target = rows[2*state+tape[position]]
        tape[position] = write
        position += move
        state = target
    return state, position-offset, [i-offset for i, bit in enumerate(tape) if bit]


def main():
    if not __debug__:
        raise RuntimeError('Run with assertions enabled.')
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--table', type=Path, required=True)
    parser.add_argument('--canonical', type=Path, required=True)
    parser.add_argument('--baseline', type=Path, required=True)
    parser.add_argument('--sites', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--step-limit', type=int, default=20000)
    parser.add_argument('--boot-limit', type=int, default=3000000)
    args = parser.parse_args()
    bindings = {str(p.resolve()):digest(p) for p in [args.table, args.canonical, args.baseline, args.sites]}
    assert digest(args.sites) == SOURCE_SHA and digest(args.baseline) == BASELINE_SHA
    table, start, states, halt = read_table(args.table)
    baseline, oldstart, oldstates, oldhalt = read_table(args.baseline)
    canonical, cstart, cstates, chalt = read_table(args.canonical)
    assert (len(states), len(table), start, halt) == (242, 484, 95, 254)
    assert (len(oldstates), len(baseline), oldstart, oldhalt) == (243, 486, 95, 254)
    assert oldstates-states == {15} and not states-oldstates
    edits = [(q, bit, baseline[q, bit], table[q, bit]) for q, bit in sorted(table)
             if table[q, bit] != baseline[q, bit]]
    assert edits == [(11, 0, (0, 1, 15), (0, 1, 27)), (27, 1, (1, 1, 39), (1, 1, 22))]
    order = [start] + sorted(states-{start})
    permutation = {q:i for i, q in enumerate(order)}
    permutation[halt] = len(states)
    expected_canonical = {(permutation[q], bit):(write, move, permutation[target])
                          for (q, bit), (write, move, target) in table.items()}
    assert (cstart, cstates, chalt) == (0, set(range(242)), 242)
    assert canonical == expected_canonical
    source = json.loads(args.sites.read_text())
    literal = literal_fixtures(table, source, args.step_limit)
    logical = [3, 0, 0, 0, 3, 0, 0, 0, 0]
    expected = frame(-5, '', 181, logical, [1]*167)
    assert len(expected) == 351
    bootsteps = discover_blank(table, start, expected, args.boot_limit)
    oldsteps = discover_blank(baseline, oldstart, expected, args.boot_limit)
    assert oldsteps == 407967
    endpoint = (96, -5, sorted(expected))
    assert sparse_replay(table, start, bootsteps) == endpoint
    assert dense_replay(table, start, bootsteps) == endpoint
    assert sparse_replay(baseline, oldstart, oldsteps) == endpoint
    assert dense_replay(baseline, oldstart, oldsteps) == endpoint
    cendpoint = (permutation[96], -5, sorted(expected))
    assert sparse_replay(canonical, cstart, bootsteps) == cendpoint
    assert dense_replay(canonical, cstart, bootsteps) == cendpoint
    blank = dict(status='PASS_EXACT_BLANK_PREFIX', baseline_steps=oldsteps,
                 candidate_steps=bootsteps, step_difference=bootsteps-oldsteps,
                 old_dispatcher=96, canonical_dispatcher=permutation[96],
                 head=-5, marker=-6, header=176, span=181,
                 logical_registers=logical, physical_registers=[0, 0, 0, 3, 0, 0, 3, 0, 0],
                 spare_count=167, spare_values=[1]*167,
                 one_cells=len(expected), all_one_positions=sorted(expected),
                 sparse_dense_agreement=True, canonical_inherited_agreement=True,
                 all_other_cells_zero=True,
                 scope='Exact finite prefix and identical complete root frame.')
    assert bindings == {p:digest(p) for p in bindings}
    result = dict(status='PASS', working_states=len(states), binary_rows=len(table),
                  source_sha256=SOURCE_SHA, input_bindings=bindings,
                  independently_checked_canonical_renumbering=True,
                  input_bindings_unchanged=True, literal_fixtures=literal, blank=blank)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps({k:v for k,v in literal.items() if k != 'row_counts'}, indent=2))
    print(json.dumps({k:v for k,v in blank.items() if k not in ('all_one_positions','spare_values')}, indent=2))
    print(args.output)


if __name__ == '__main__':
    main()
