#!/usr/bin/env python3
"""Independent, standard-library verifier for boundary239 -> composed238.

This proves six exact positive-block identities on arbitrary exterior tapes.
It separately checks the inductive structural invariant and exact table edits.
The sole extra premise is the source/runtime selector guard at old state169:
if its scanned bit is1 then the bit immediately to the right is1.  That guard
is established by the independent universal runtime/guard audit, not by this
local certificate. No finite blank trace is used here.
"""
import argparse
import hashlib
import json
from pathlib import Path


def require(ok, description):
    if not ok:
        raise ValueError(description)


def read(path):
    rows = {}
    for line in path.read_text().splitlines():
        if not line or line.startswith('#'):
            continue
        q, b, w, d, n = line.split()
        q, b, w, n = map(int, (q, b, w, n))
        require(b in (0, 1) and w in (0, 1) and d in ('L', 'R'), 'Invalid row')
        require((q, b) not in rows, 'Duplicate row')
        rows[q, b] = (w, 1 if d == 'R' else -1, n)
    states = {q for q, _ in rows}
    require(set(rows) == {(q, b) for q in states for b in (0, 1)}, 'Incomplete table')
    require(95 in states and 254 not in states, 'Wrong start/halt convention')
    require({n for _, _, n in rows.values()} - states == {254}, 'Wrong exit states')
    return rows


def phi(q):
    return 80 if q == 169 else q


def run(rows, initial_state, constraints, length):
    """Outside the finite domain, each tape value is a distinct free variable.

    Every actually scanned cell must be fixed by the constraints or earlier
    writes. Rejecting any unbound read makes each checked equality universal
    for all assignments to all exterior tape cells.
    """
    state, head, tape, trace = initial_state, 0, dict(constraints), []
    for k in range(length):
        require(head in tape, f'Unspecified exterior bit read at {state}, {head}')
        require(state != 254, 'Intermediate halt')
        bit = tape[head]
        write, move, target = rows[state, bit]
        trace.append([state, head, bit, write, move, target])
        tape[head] = write
        state, head = target, head + move
    require(state != 254, 'Exceptional block endpoint must not be halt')
    return (state, head, tape), trace


def verify(old, new):
    old_states, new_states = {q for q, _ in old}, {q for q, _ in new}
    require(len(old_states) == 239 and len(new_states) == 238, 'Wrong state counts')
    require(new_states == old_states - {169}, 'Wrong removed state')
    expected = {(q, b): (w, d, phi(n)) for (q, b), (w, d, n) in old.items() if q != 169}
    expected[80, 0] = (0, -1, 106)
    expected[91, 1] = (1, -1, 167)
    require(expected == new, 'Candidate differs from the three-edit construction')
    require(old[147, 0] == (0, 1, 169), 'Wrong169 predecessor')
    require([(q, b) for (q, b), (_, _, n) in old.items() if n == 169] == [(147, 0)], 'Additional169 predecessor')

    inv = {67: {-1: 0}, 80: {-2: 0, -1: 1}, 91: {-3: 0, -2: 1, -1: 1}, 169: {-1: 0}}
    require(95 not in inv, 'Initial invariant must hold on arbitrary tapes')
    preservation = []
    for (q, b), (w, d, n) in sorted(old.items()):
        if n not in inv:
            continue
        assumptions = dict(inv.get(q, {}))
        require(0 not in assumptions or assumptions[0] == b, 'Unexpected inconsistent row')
        assumptions[0] = w
        obligations = [[i, v, d + i, assumptions.get(d + i)] for i, v in inv[n].items()]
        require(all(got == needed for _, needed, _, got in obligations), f'Invariant not inductive at {q}/{b}')
        preservation.append({'row': [q, b], 'target': n, 'obligations': obligations})

    specs = [
        (80, {-1: 1, 0: 0}, 1, 5, False),
        (80, {0: 1}, 1, 1, False),
        (169, {-1: 0, 0: 0}, 1, 3, False),
        (169, {-1: 0, 0: 1, 1: 1}, 1, 5, True),
        (91, {0: 0}, 1, 1, False),
        (91, {-3: 0, -2: 1, -1: 1, 0: 1}, 3, 11, False),
    ]
    cases, old_dependencies, new_dependencies = [], set(), set()
    for state, assumptions, old_length, new_length, guard in specs:
        before, old_trace = run(old, state, assumptions, old_length)
        after, new_trace = run(new, phi(state), assumptions, new_length)
        qo, ho, to = before
        qn, hn, tn = after
        require(phi(qo) == qn and ho == hn, 'Unequal control/head endpoints')
        for cell in to.keys() | tn.keys():
            initial_variable = ('unconstrained_original_bit', cell)
            require(to.get(cell, initial_variable) == tn.get(cell, initial_variable), 'Unequal whole tapes')
        require(old_length > 0 and new_length > 0, 'Nonpositive block length')
        old_dependencies.update((row[0], row[2]) for row in old_trace)
        new_dependencies.update((row[0], row[2]) for row in new_trace)
        cases.append({'old_state': state, 'new_state': phi(state), 'assumptions': assumptions,
                      'requires_semantic_guard': guard, 'old_steps': old_length,
                      'new_steps': new_length, 'endpoint': [qn, hn],
                      'whole_tape_equality': True, 'old_trace': old_trace, 'new_trace': new_trace})
    ordinary_count = 0
    for (q, b), (w, d, n) in old.items():
        if q not in {80, 91, 169}:
            require(new[phi(q), b] == (w, d, phi(n)), 'Uncovered ordinary row')
            ordinary_count += 1
    changed = [{'row': list(k), 'old': old.get(k), 'new': new.get(k)}
               for k in sorted(old.keys() | new.keys()) if old.get(k) != new.get(k)]
    return {'status': 'PASS', 'working_states': [239, 238], 'transition_rows': [478, 476],
            'start': 95, 'halt': 254, 'state_map': '169 -> 80; every other state fixed',
            'scope': 'Exact finite positive-block simulation under the stated selector guard; arbitrary exterior tapes',
            'guard': 'Every reached OLD q169/read1 configuration has tape[h+1]=1',
            'guard_proved_here': False, 'structural_invariant': inv,
            'structural_preservation': preservation, 'cases': cases,
            'ordinary_rows': ordinary_count, 'changed_rows': changed,
            'old_block_dependencies': sorted(map(list, old_dependencies)),
            'new_block_dependencies': sorted(map(list, new_dependencies)),
            'max_old_steps': 3, 'max_new_steps': 11,
            'proof_argument': 'Starting at95, induct on successive old checkpoints. The structural predicate is inductive. At80,91,169 use the six exact whole-tape blocks and the selector guard; elsewhere use the identical one-step row under phi. Each block has positive length and no intermediate halt. Hence an infinite old run yields an infinite new run, and a finite old halting run yields a finite new halting run. Determinism yields equivalence.'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--old', type=Path, required=True)
    parser.add_argument('--new', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    result = verify(read(args.old), read(args.new))
    result['old_sha256'] = hashlib.sha256(args.old.read_bytes()).hexdigest()
    result['new_sha256'] = hashlib.sha256(args.new.read_bytes()).hexdigest()
    result['verifier_sha256'] = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({k: result[k] for k in ('status', 'working_states', 'transition_rows', 'old_sha256', 'new_sha256', 'ordinary_rows', 'guard_proved_here')}, indent=2))


if __name__ == '__main__':
    main()
