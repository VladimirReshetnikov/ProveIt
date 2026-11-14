#!/usr/bin/env python3
"""Independent all-tape inductive-invariant and block-simulation audit.

No proposal code is imported. All checks use explicit exceptions, including
under python -O. Unspecified tape cells are opaque and may not be read in
the special macros. The proof is relative to the exact pinned Joint U209
native table, and applies to every initial tape in common start state 0.
"""
from collections import deque
from itertools import product
from pathlib import Path
import argparse
import hashlib
import json


BASELINE_SHA256 = 'd0a155d3c683789f3bf5327c0cfb2a0cfd78076af8f1654d4ca426ccbb604d16'
START, HALT = 0, 254
SPECIAL = {116, 172, 217, 163, 211}


def need(condition, message):
    if not condition:
        raise ValueError(message)


def read_table(path):
    table = {}
    for line in path.read_text().splitlines():
        if not line.strip() or line.startswith('#'):
            continue
        q, b, w, direction, r = line.split()
        q, b, w, r = map(int, (q, b, w, r))
        need((q, b) not in table, 'Duplicate row')
        need(direction in ('L', 'R'), 'Direction')
        table[q, b] = (w, -1 if direction == 'L' else 1, r)
    return table


def rho(q):
    return 211 if q == 172 else q


def candidate(old):
    new = {(q, b): (w, d, rho(r))
           for (q, b), (w, d, r) in old.items() if q != 172}
    new[211, 0] = 0, -1, 217
    return new


def guard(state, tape, head=0):
    if state == 116:
        return tape[head - 1] == 1
    if state == 172:
        return tape[head - 2] == 1 and tape[head - 1] == 0
    if state == 217:
        return tape[head - 1] == 1
    if state == 163:
        return tape[head - 1] == 1 or tape[head - 2] == 1
    if state == 211:
        return tape[head] == 1 or tape[head - 1] == 1
    return True


def check_invariant(old):
    # These are the COMPLETE target inventories in the actual old table.
    expected_incoming = {
        116: [(215, 1, 1, 1, 116)],
        172: [(116, 0, 0, 1, 172)],
        217: [(216, 1, 1, 1, 217)],
        163: [(132, 1, 1, 1, 163), (199, 1, 1, 1, 163), (217, 0, 0, 1, 163)],
        211: [(163, 0, 0, -1, 211), (163, 1, 1, 1, 211)],
    }
    inventories = {}
    for target in sorted(SPECIAL):
        actual = sorted((q, b, w, d, r) for (q, b), (w, d, r) in old.items()
                        if r == target)
        need(actual == expected_incoming[target], 'Unexpected incoming edge')
        inventories[target] = actual

    # Any source and destination clause is contained in this fixed window:
    # a move is +-1 and the furthest clause looks two cells left.
    positions = list(range(-3, 2))
    checked, vacuous = 0, 0
    for (q, bit), (write, move, target) in old.items():
        if target not in SPECIAL:
            continue
        for values in product((0, 1), repeat=len(positions)):
            tape = dict(zip(positions, values))
            if tape[0] != bit or not guard(q, tape):
                vacuous += 1
                continue
            tape[0] = write
            need(guard(target, tape, move), 'Invariant not inductive')
            checked += 1
    need(START not in SPECIAL, 'Initial guard not vacuous')
    return {'incoming': inventories, 'window': positions,
            'old_transition_rows': len(old),
            'guarded_target_rows': sum(len(x) for x in inventories.values()),
            'trivial_target_rows': len(old) - sum(len(x) for x in inventories.values()),
            'local_boolean_valuations': checked + vacuous,
            'satisfying_local_valuations_checked': checked,
            'inapplicable_local_valuations': vacuous,
            'initial_guard_vacuous': True}


def special_case(old, new, state, bit, initial, steps):
    initial = dict(initial)
    need(initial[0] == bit, 'Input bit')
    tape, head, q = dict(initial), 0, rho(state)
    trace = []
    for _ in range(steps):
        need(q != HALT, 'Internal halt')
        need(head in tape, 'Read outside specified local cells')
        read = tape[head]
        write, direction, target = new[q, read]
        trace.append([q, head, read, write, direction, target])
        tape[head] = write
        q, head = target, head + direction
    write, direction, target = old[state, bit]
    expected = dict(initial)
    expected[0] = write
    need(q == rho(target), 'Wrong control endpoint')
    need(head == direction, 'Wrong head endpoint')
    need(tape == expected, 'Whole-tape endpoint differs')
    return {'old_state': state, 'read': bit,
            'local_initial_cells': initial, 'steps': steps,
            'trace': trace, 'end_state': q, 'end_head': head,
            'opaque_exterior_unread': True, 'full_tape_matches': True}


def audit(old, new):
    old_states = {q for q, _ in old}
    states = {q for q, _ in new}
    need(len(old_states) == 209, 'Wrong old state count')
    need(states == old_states - {172} and len(states) == 208, 'Wrong new state set')
    need(set(new) == {(q, b) for q in states for b in (0, 1)}, 'Non-total table')
    need(all(w in (0, 1) and d in (-1, 1) and r in states | {HALT}
             for w, d, r in new.values()), 'Invalid or dangling transition')
    invariant = check_invariant(old)
    ordinary = 0
    for (q, b), (w, d, r) in old.items():
        if q in (172, 211):
            continue
        need(new[rho(q), b] == (w, d, rho(r)), 'Ordinary row fails quotient')
        ordinary += 1
    cases = [
        special_case(old, new, 172, 0, {-2: 1, -1: 0, 0: 0}, 7),
        special_case(old, new, 172, 1, {-2: 1, -1: 0, 0: 1}, 1),
        special_case(old, new, 211, 0, {-1: 1, 0: 0}, 3),
        special_case(old, new, 211, 1, {0: 1}, 1),
    ]
    reached, queue = {START}, deque([START])
    while queue:
        q = queue.popleft()
        if q == HALT:
            continue
        for bit in (0, 1):
            target = new[q, bit][2]
            if target not in reached:
                reached.add(target)
                queue.append(target)
    need(reached == states | {HALT}, 'State reachability differs')
    return {'status': 'ALL_TAPE_LOCAL_SIMULATION_PASS',
            'working_states': len(states), 'rows': len(new),
            'ordinary_old_rows': ordinary, 'invariant': invariant, 'cases': cases,
            'min_block_steps': 1, 'max_block_steps': 7,
            'graph_reachable_working': len(reached - {HALT}),
            'scope': 'Every initial tape in common state0, head0; old reachable configurations.',
            'clock_relation': 'T_new = T_old + 6*N_old(172,0) + 2*N_old(211,0)'}


def negative_controls(old, new):
    controls = []

    def reject(name, fn):
        try:
            fn()
        except (ValueError, KeyError):
            controls.append(name)
            return
        raise ValueError('Negative control unexpectedly accepted: ' + name)

    bad = dict(new)
    bad[116, 0] = old[116, 0]
    reject('missing_incoming_redirect', lambda: audit(old, bad))
    bad = dict(new)
    bad[211, 0] = 0, -1, 215
    reject('wrong_backward_helper', lambda: audit(old, bad))
    bad = dict(new)
    bad[215, 0] = 0, 1, 148
    reject('corrupt_reused_215_zero', lambda: audit(old, bad))
    bad = dict(new)
    bad[211, 0] = old[211, 0]
    reject('restore_old211_zero', lambda: audit(old, bad))
    bad = dict(new)
    bad[211, 0] = 1, -1, 217
    reject('corrupt_written_zero', lambda: audit(old, bad))
    bad = dict(new)
    bad[211, 0] = 0, 1, 217
    reject('wrong_selector_direction', lambda: audit(old, bad))
    bad = dict(new)
    bad[211, 1] = 1, 1, 157
    reject('wrong_shared_one_branch', lambda: audit(old, bad))
    bad = dict(new)
    bad[217, 0] = 0, 1, 215
    reject('corrupt_helper_zero_branch', lambda: audit(old, bad))
    bad = dict(new)
    bad[217, 1] = 1, 1, 163
    reject('corrupt_helper_one_branch', lambda: audit(old, bad))
    bad = dict(new)
    bad[157, 0] = 0, 1, 67
    reject('wrong_seven_step_endpoint_direction', lambda: audit(old, bad))
    reject('drop_second_predecessor_guard',
           lambda: special_case(old, new, 172, 0, {-2: 0, -1: 0, 0: 0}, 7))
    reject('drop_old211_zero_guard',
           lambda: special_case(old, new, 211, 0, {-2: 1, -1: 0, 0: 0}, 3))
    return controls


def encode(table):
    return ('#! start 0\n' + ''.join(
        f'{q} {b} {w} {"L" if d == -1 else "R"} {r}\n'
        for (q, b), (w, d, r) in sorted(table.items()))).encode('ascii')


def dense_relabel(table):
    states = sorted({q for q, _ in table})
    mapping = {q: i for i, q in enumerate(states)}
    mapping[HALT] = len(states)
    dense = {(mapping[q], b): (w, d, mapping[r])
             for (q, b), (w, d, r) in table.items()}
    need(mapping[START] == 0 and mapping[HALT] == 208, 'Dense boundaries')
    need(set(q for q, _ in dense) == set(range(208)), 'Dense working states')
    need(len(dense) == 416 and len(set(mapping.values())) == 209, 'Dense bijection')
    inverse = {r: q for q, r in mapping.items()}
    for (q, b), (w, d, r) in dense.items():
        need(table[inverse[q], b] == (w, d, inverse[r]), 'Dense row not conjugate')
    return dense, mapping


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--baseline', type=Path,
                        default=Path(__file__).with_name('joint209.native.tm'))
    parser.add_argument('--output', type=Path,
                        default=Path(__file__).with_name('audit208.json'))
    parser.add_argument('--candidate-native', type=Path,
                        help='Optionally require exact bytes of a delivered native table')
    parser.add_argument('--candidate-dense', type=Path,
                        help='Optionally require exact bytes of a delivered dense table')
    args = parser.parse_args()
    need(hashlib.sha256(args.baseline.read_bytes()).hexdigest() == BASELINE_SHA256,
         'Wrong pinned U209 table')
    old = read_table(args.baseline)
    new = candidate(old)
    result = audit(old, new)
    result['negative_controls_rejected'] = negative_controls(old, new)
    raw = encode(new)
    dense, mapping = dense_relabel(new)
    dense_raw = encode(dense)
    if args.candidate_native:
        need(args.candidate_native.read_bytes() == raw, 'Delivered native table differs')
    if args.candidate_dense:
        need(args.candidate_dense.read_bytes() == dense_raw, 'Delivered dense table differs')
    result['baseline_sha256'] = BASELINE_SHA256
    result['native208_sha256'] = hashlib.sha256(raw).hexdigest()
    result['dense208_sha256'] = hashlib.sha256(dense_raw).hexdigest()
    result['dense_relabel'] = {'working_labels': [0, 207], 'halt_label': 208,
                             'row_conjugacies_checked': len(dense),
                             'native_to_dense': mapping}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    args.output.with_name('independent208.native.tm').write_bytes(raw)
    args.output.with_name('independent208.tm').write_bytes(dense_raw)
    print(result['status'], '208 states, 416 rows, 4 exhaustive special macros,',
          result['invariant']['satisfying_local_valuations_checked'],
          'inductive guard cases,', len(result['negative_controls_rejected']),
          'negative controls rejected.')


if __name__ == '__main__':
    main()
