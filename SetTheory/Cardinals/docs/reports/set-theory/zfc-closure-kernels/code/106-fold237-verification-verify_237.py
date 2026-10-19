#!/usr/bin/env python3
"""Exact ordinary mathematical premises for the composed238 -> 237 reduction.

Checks the literal tables, an inductive syntactic invariant, three open-tape
symbolic block equalities, and all checkpoints of the specified blank startup.
All local guards follow from the syntactic invariant from state95 on ANY tape;
this reduction requires no additional runtime-frame premise.
"""
import argparse
import hashlib
import itertools
import json
import re
from collections import Counter
from pathlib import Path


def need(test, reason):
    if not test:
        raise AssertionError(reason)


def read_table(path, external_start=None):
    raw = path.read_bytes()
    rows = {}
    starts = []
    for line in raw.decode('ascii').splitlines():
        if line.startswith('#! start '):
            starts.append(int(line[9:]))
        elif line.startswith('#') or not line.strip():
            continue
        else:
            match = re.fullmatch(r'(\d+) ([01]) ([01]) ([LR]) (\d+)', line)
            need(match is not None, ['malformed row', line])
            q, b, w, d, z = match.groups()
            key = int(q), int(b)
            need(key not in rows, ['duplicate row', key])
            rows[key] = int(w), (1 if d == 'R' else -1), int(z)
    states = {q for q, b in rows}
    if not starts and external_start is not None:
        starts = [external_start]
    need(len(starts) == 1 and starts[0] in states, 'start declaration')
    need(set(rows) == {(q, b) for q in states for b in (0, 1)}, 'total binary table')
    need({z for w, d, z in rows.values()} - states == {254}, 'halt convention')
    return rows, starts[0], hashlib.sha256(raw).hexdigest()


def mapped(q):
    return 98 if q == 235 else q


def invariant(q, h, tape):
    constraints = {98: {-1: 0}, 139: {-1: 1}, 156: {-1: 1},
                   235: {-2: 1, -1: 1}, 240: {-1: 0}}
    return all(tape[h + offset] == b for offset, b in constraints.get(q, {}).items())


def symbolic_block(table, q, guard, steps):
    # Every unbound cell is an independent arbitrary Boolean. No branch may
    # inspect one: if it did, this deliberately simple proof would reject.
    initial = lambda p: guard.get(p, f'x[{p}]')
    changed = {}
    head = 0
    trace = []
    for _ in range(steps):
        b = changed.get(head, initial(head))
        need(type(b) is int and b in (0, 1), ['unresolved branch', q, head, b])
        w, d, z = table[q, b]
        trace.append([q, head, b, w, d, z])
        if w == initial(head):
            changed.pop(head, None)
        else:
            changed[head] = w
        q, head = z, head + d
    return q, head, changed, trace


def sparse_step(table, state, head, support):
    w, d, z = table[state, int(head in support)]
    if w:
        support.add(head)
    else:
        support.discard(head)
    return z, head + d


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--old', type=Path, required=True)
    parser.add_argument('--new', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    old, oldstart, oldhash = read_table(args.old)
    new, newstart, newhash = read_table(args.new)
    need(oldhash == '069942be27db9736875ea042320e51ac3b1eac7116cbe01cdce520fa6056f78c', 'pinned old238 table')
    need(newhash == 'a3c4407f30e2e2139af87c6a91948c518134855841a28eb85b1d81bcfd026c9a', 'pinned new237 table')
    need((len(old), len(new), oldstart, newstart) == (476, 474, 95, 95), 'size/start')
    expected = {(q, b): (w, d, mapped(z)) for (q, b), (w, d, z) in old.items() if q != 235}
    expected[98, 0] = 0, -1, 240
    expected[240, 1] = 1, -1, 87
    need(expected == new, 'exact four-row coordinated construction')
    modified = sorted(key for key in new if old[key] != new[key])
    need(modified == [(98, 0), (139, 1), (156, 1), (240, 1)], ['unexpected edits', modified])

    closure_cases = 0
    for bits in itertools.product((0, 1), repeat=9):
        tape = dict(zip(range(-4, 5), bits))
        need(invariant(95, 0, tape), 'initial invariant')
        for q in {q for q, b in old}:
            if invariant(q, 0, tape):
                w, d, z = old[q, tape[0]]
                after = dict(tape)
                after[0] = w
                need(invariant(z, d, after), ['invariant is not inductive', q, tape])
                closure_cases += 1

    specifications = [(98, 0, {-1: 0}, 3),
                      (235, 0, {-2: 1, -1: 1}, 5),
                      (240, 1, {-1: 0}, 3)]
    exceptional = {(q, b) for q, b, g, n in specifications}
    blocks = []
    for q, b, guard, steps in specifications:
        entry_guard = {**guard, 0: b}
        oq, oh, ot, oldtrace = symbolic_block(old, q, entry_guard, 1)
        nq, nh, nt, newtrace = symbolic_block(new, mapped(q), entry_guard, steps)
        need((mapped(oq), oh, ot) == (nq, nh, nt), ['open-tape block mismatch', q, b])
        blocks.append({'old_row': [q, b], 'guard': guard, 'new_steps': steps,
                       'old_trace': oldtrace, 'new_trace': newtrace,
                       'result': [nq, nh, nt], 'arbitrary_exterior': True})
    ordinary = 0
    for (q, b), (w, d, z) in old.items():
        if (q, b) not in exceptional:
            need(new[mapped(q), b] == (w, d, mapped(z)), ['ordinary mismatch', q, b])
            ordinary += 1
    need(ordinary == 473, 'ordinary transition census')

    durations = {(q, b): n for q, b, guard, n in specifications}
    qo = qn = 95
    ho = hn = 0
    so = set()
    sn = set()
    costs = Counter()
    newsteps = 0
    for tick in range(409835):
        need((mapped(qo), ho, so) == (qn, hn, sn), ['startup checkpoint', tick])
        edge = qo, int(ho in so)
        n = durations.get(edge, 1)
        if edge in exceptional:
            costs[edge] += 1
        qo, ho = sparse_step(old, qo, ho, so)
        for _ in range(n):
            qn, hn = sparse_step(new, qn, hn, sn)
        newsteps += n
        need((mapped(qo), ho, so) == (qn, hn, sn), ['startup post-block checkpoint', tick])
    need((qo, ho, len(so)) == (96, -5, 351), ['startup endpoint', qo, ho, len(so)])
    need(newsteps == 409835 + 2 * costs[98, 0] + 4 * costs[235, 0] + 2 * costs[240, 1],
         'startup exact block-clock formula')

    # A separate dense representation independently checks the complete final
    # tape. Its bounds are checked at every literal step, so all outside cells
    # are certified untouched zeros.
    size = 16384
    origin = 8192
    dense = bytearray(size)
    dq = 95
    dh = origin
    low = high = origin
    for _ in range(newsteps):
        need(0 <= dh < size, 'dense tape bound exceeded')
        w, d, z = new[dq, dense[dh]]
        dense[dh] = w
        dq, dh = z, dh + d
        low, high = min(low, dh), max(high, dh)
    dense_support = {i - origin for i, b in enumerate(dense) if b}
    need((dq, dh - origin, dense_support) == (qn, hn, sn), 'sparse/dense whole-tape agreement')
    marker = hn - 1
    header = min(p for p in sn if p > hn + 51)
    need(header == 176 and {p for p in sn if p < header} == {marker},
         'clean zero pointer, marker, and zero left exterior')
    cursor = header + 1
    values = []
    while cursor <= max(sn):
        need(cursor not in sn, ['unary separator', cursor])
        cursor += 1
        length = 0
        while cursor in sn:
            cursor += 1
            length += 1
        need(length >= 1, 'empty unary block')
        values.append(length - 1)
    need(len(values) == 176, ['block count', len(values)])
    physical = values[:9]
    logical_to_physical = [6, 2, 0, 4, 3, 7, 8, 5, 1]
    logical = [physical[j] for j in logical_to_physical]
    need(logical == [3, 0, 0, 0, 3, 0, 0, 0, 0], ['logical seed', logical])
    need(values[9:] == [1] * 167, 'spare bank')
    record = {'status': 'PASS_237_UNCONDITIONAL_LOCAL_SIMULATION_AND_EXACT_BOOT',
              'old_sha256': oldhash, 'new_sha256': newhash,
              'old_working_states': 238, 'new_working_states': 237,
              'modified_retained_rows': modified, 'unchanged_retained_rows': 470,
              'deleted_state': 235, 'retained_state': 98,
              'inductive_boolean_window_cases': closure_cases,
              'ordinary_commuting_old_rows': ordinary, 'symbolic_open_tape_blocks': blocks,
              'blank_startup': {'old_steps': 409835, 'new_steps': newsteps,
                                'compared_checkpoints': 409836,
                                'exceptional_visits': {f'{q}/{b}': n for (q, b), n in sorted(costs.items())},
                                'head': hn, 'state': qn, 'marker': marker, 'header': header,
                                'logical_registers': logical, 'spare_bank': {'count': 167, 'value': 1},
                                'one_cells': sorted(sn), 'one_count': len(sn),
                                'dense_access_interval': [low - origin, high - origin],
                                'all_other_tape_cells_zero': True,
                                'sparse_dense_full_tape_agreement': True},
              'remaining_guard_premise': None,
              'local_simulation': {'arbitrary_initial_tape': True, 'start': 95,
                                   'minimum_block_steps': 1, 'maximum_block_steps': 5,
                                   'halting_state_preserved': 254},
              'scope': 'Universal finite-footprint block identities and all-tape syntactic invariant establish halting equivalence with the pinned238 table from state95 on every tape. The finite startup is independently reproduced. This script does not supply the inherited source-calibration theorem or a proof-assistant kernel endpoint.'}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(record, indent=2) + '\n')
    print(json.dumps({k: v for k, v in record.items() if k not in ('symbolic_open_tape_blocks', 'blank_startup')}, indent=2))
    print(json.dumps({k: v for k, v in record['blank_startup'].items() if k != 'one_cells'}, indent=2))


if __name__ == '__main__':
    main()
