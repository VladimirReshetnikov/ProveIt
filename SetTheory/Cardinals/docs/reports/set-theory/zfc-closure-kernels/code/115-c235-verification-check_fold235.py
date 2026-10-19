#!/usr/bin/env python3
"""Independent four-case open-tape proof of the 74/193 three-step fold.

This checker does not import the search code or the generic symbolic checker.
It establishes the local halting equivalence on every initial binary tape;
source reassociation and logical calibration have separate proof obligations.
"""
import argparse
import hashlib
import json
from pathlib import Path

BASIS_SHA256 = '014133f39c409277c239fa327db17800b4e886a5c7a5a73034ed87e4978820aa'
CANDIDATE_SHA256 = 'd017abe46023a4154085a2fe2c04c8d66bbbec53b81d193d520ad697d171cbd4'


def require(ok, message):
    if not ok:
        raise ValueError(message)


def parse(path):
    data = path.read_bytes()
    start = None
    table = {}
    for line in data.decode('utf-8').splitlines():
        if line.startswith('#! start '):
            require(start is None, 'Duplicate start header')
            start = int(line[9:])
        elif line and not line.startswith('#'):
            state, read, write, direction, target = line.split()
            state, read, write, target = map(int, (state, read, write, target))
            require(read in (0, 1) and write in (0, 1) and direction in ('L', 'R'), 'Malformed transition')
            require((state, read) not in table, 'Duplicate transition')
            table[state, read] = write, -1 if direction == 'L' else 1, target
    states = {q for q, b in table}
    require(set(table) == {(q, b) for q in states for b in (0, 1)}, 'Incomplete machine')
    require(start in states, 'Invalid start state')
    require({z for w, d, z in table.values()} - states == {254}, 'Wrong halting outcome')
    return table, start, hashlib.sha256(data).hexdigest()


def verify(basis_path, candidate_path):
    old, old_start, old_hash = parse(basis_path)
    new, new_start, new_hash = parse(candidate_path)
    require(old_hash == BASIS_SHA256, 'Unexpected basis bytes')
    require(new_hash == CANDIDATE_SHA256, 'Unexpected candidate bytes')
    require(old_start == new_start == 95, 'Unexpected initial state')
    old_states = {q for q, b in old}
    new_states = {q for q, b in new}
    require(len(old_states) == 236 and len(new_states) == 235, 'Unexpected state counts')
    require(new_states == old_states - {193}, 'Wrong deleted state')
    phi = lambda q: 74 if q == 193 else q

    incoming = {}
    for target, tag in ((74, 0), (193, 1)):
        incoming[target] = [[q, b, w, d] for (q, b), (w, d, z) in sorted(old.items()) if z == target]
        require(incoming[target], 'Unreachable special state')
        require(all(w == tag and d == 1 for q, b, w, d in incoming[target]), 'Incoming transition violates tag invariant')
        require(target != old_start, 'Initial tape would be constrained')
    require(incoming == {74: [[140, 0, 0, 1]], 193: [[163, 1, 1, 1], [229, 1, 1, 1]]}, 'Incoming inventory changed')
    # These checks establish I initially and after every old transition: all
    # entries into each constrained state write its tag immediately left.

    expected_old = {(74, 0): (0, 1, 114), (74, 1): (1, 1, 233),
                    (193, 0): (0, 1, 190), (193, 1): (1, 1, 213)}
    require(all(old[row] == transition for row, transition in expected_old.items()), 'Special old row changed')
    require(new[74, 0] == (0, -1, 138) and new[74, 1] == (1, -1, 116), 'Retained rows changed')
    commuting = 0
    for (q, b), (w, d, z) in old.items():
        if (q, b) in expected_old:
            continue
        require(new[phi(q), b] == (w, d, phi(z)), 'An ordinary row does not commute')
        commuting += 1
    require(commuting == 468, 'Incorrect ordinary-row count')

    cases = []
    expected_paths = {(74, 0): [74, 138, 210, 114], (74, 1): [74, 116, 246, 233],
                      (193, 0): [74, 138, 211, 190], (193, 1): [74, 116, 134, 213]}
    for (q, b), (w, d, z) in sorted(expected_old.items()):
        tag = 0 if q == 74 else 1
        initial = {-1: tag, 0: b}
        tape = dict(initial)
        state, head = phi(q), 0
        trace = []
        for step in range(3):
            require(state != 254, 'Interior halt')
            require(head in tape, 'An unbound exterior cell was read')
            read = tape[head]
            write, move, target = new[state, read]
            require(write == read, 'Block changes a tape cell')
            trace.append([state, head, read, write, move, target])
            tape[head] = write
            head += move
            state = target
        require((state, head, tape) == (phi(z), 1, initial), 'Wrong synchronization endpoint')
        path = [entry[0] for entry in trace] + [state]
        require(path == expected_paths[q, b], 'Expected path changed')
        cases.append({'old_row': [q, b], 'guard': {'left': tag, 'read': b},
                      'old_steps': 1, 'new_steps': 3, 'trace': trace,
                      'final_state': state, 'final_head': head,
                      'footprint': [-1, 0], 'whole_tape_preserved': True})
    return {'status': 'PASS_INDEPENDENT_ALL_TAPE_FOUR_CASE_PROOF',
            'old_sha256': old_hash, 'new_sha256': new_hash,
            'start_old': old_start, 'start_new': new_start, 'halt': 254,
            'old_states': 236, 'new_states': 235, 'old_rows': 472, 'new_rows': 470,
            'keep': 74, 'drop': 193, 'incoming': incoming,
            'invariant': {'74': {'left': 0}, '193': {'left': 1}},
            'ordinary_rows': commuting, 'exceptional_rows': 4,
            'block_length_histogram': {'1': commuting, '3': 4}, 'cases': cases,
            'scope': 'All initial binary tapes and all integer initial head positions. The old tape invariant is inductive. Every old step is simulated by a positive block with no interior halt and exactly the mapped final state, head and whole tape.',
            'proof_boundary': 'Local basis236/candidate235 halting equivalence. Source reassociation and ZFC calibration are separate.'}


def main():
    directory = Path(__file__).resolve().parent
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--basis', type=Path, default=directory / 'basis236_seven_rotations74.tm')
    parser.add_argument('--candidate', type=Path, default=directory / 'candidate235_seven_rotations74.tm')
    parser.add_argument('--output', type=Path, default=directory / 'fold235_independent.json')
    args = parser.parse_args()
    result = verify(args.basis, args.candidate)
    result['checker_sha256'] = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({key: value for key, value in result.items() if key != 'cases'}, indent=2))


if __name__ == '__main__':
    main()
