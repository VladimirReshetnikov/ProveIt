#!/usr/bin/env python3
"""Independently verify two exact guarded state folds, using only Python stdlib.

Usage:
  python3 verify_guarded_folds.py repaired220.tm tagged219.tm final218.tm receipt.json

The first fold uses predecessor tags to combine states 182 and 507. The
second deletes state 200 because every entry into it scans zero. This file
checks the literal tables and local finite proofs. It does not assert the
source/theory correspondence or replace complete primitive verification.
"""
from pathlib import Path
import argparse, copy, hashlib, json


def need(condition, message):
    if not condition:
        raise ValueError(message)


def read_table(path):
    table = {}
    starts = []
    for line in path.read_text(encoding='ascii').splitlines():
        if line.startswith('#! start '):
            starts.append(int(line[9:]))
        if not line or line.startswith('#'):
            continue
        fields = line.split()
        need(len(fields) == 5, 'Expected five transition fields')
        q, bit, write, direction, target = fields
        q, bit, write, target = map(int, (q, bit, write, target))
        need((q, bit) not in table, 'Duplicate transition')
        need(bit in (0, 1) and write in (0, 1), 'Nonbinary symbol')
        need(direction in ('L', 'R'), 'Nonmoving transition')
        table[q, bit] = write, (-1 if direction == 'L' else 1), target
    need(starts == [0], 'Expected exactly one start declaration, state 0')
    return table


def validate(table, count):
    states = {q for q, bit in table}
    need(len(states) == count, 'Incorrect working-state count')
    need(set(table) == {(q, bit) for q in states for bit in (0, 1)},
         'Partial transition table')
    need(0 in states and 254 not in states, 'Invalid start/halt')
    need({target for write, direction, target in table.values()} - states == {254},
         'Unexpected undefined target')
    need(all(write in (0, 1) and direction in (-1, 1)
             for write, direction, target in table.values()), 'Invalid action')
    reached = {0}
    todo = [0]
    for q in todo:
        for bit in (0, 1):
            target = table[q, bit][2]
            if target in states and target not in reached:
                reached.add(target)
                todo.append(target)
    need(reached == states, 'Unreachable counted working state')


def incoming(table, target):
    return sorted((key, action) for key, action in table.items() if action[2] == target)


def first_transform(table):
    result = {(q, bit): (write, direction, 182 if target == 507 else target)
              for (q, bit), (write, direction, target) in table.items() if q != 507}
    result[182, 0] = 0, -1, 209
    return result


def second_transform(table):
    return {(q, bit): (write, direction, 209 if target == 200 else target)
            for (q, bit), (write, direction, target) in table.items() if q != 200}


def local_case(parent, candidate, old_state, tag, bit):
    # The dictionary's two cells are the complete known window. Reaching any
    # other cell before the desired endpoint is rejected, so all exterior
    # tape contents remain universally quantified and unchanged.
    tape = {-1: tag, 0: bit}
    expected = dict(tape)
    write, expected_head, expected_state = parent[old_state, bit]
    expected[0] = write
    q, head = 182, 0
    trace = []
    for tick in range(20):
        if tick and (q, head, tape) == (expected_state, expected_head, expected):
            return {'old_state': old_state, 'predecessor_bit': tag,
                    'read_bit': bit, 'candidate_steps': tick, 'parent_steps': 1,
                    'endpoint_state': q, 'endpoint_head': head,
                    'whole_tape_equal': True, 'trace': trace}
        need(head in tape, 'Local proof read the unknown exterior')
        need(q != 254, 'Local proof halted internally')
        read = tape[head]
        need((q, read) in candidate, 'Undefined local transition')
        write, direction, target = candidate[q, read]
        trace.append({'state': q, 'head': head, 'read': read,
                      'write': write, 'direction': direction, 'target': target})
        tape[head] = write
        q, head = target, head + direction
    raise ValueError('Local proof failed to reach the exact parent endpoint')


def verify(parent, intermediate, final):
    validate(parent, 220)
    validate(intermediate, 219)
    validate(final, 218)
    need(intermediate == first_transform(parent), 'First fold has extra/missing changes')
    need(final == second_transform(intermediate), 'Second fold has extra/missing changes')
    need(incoming(parent, 182) == [((173, 1), (1, 1, 182))],
         'Old 182 entries do not guarantee predecessor tag 1')
    need(incoming(parent, 507) == [((18, 0), (0, 1, 507)),
                                    ((134, 0), (0, 1, 507)),
                                    ((188, 0), (0, 1, 507))],
         'Clone 507 entries do not guarantee predecessor tag 0')
    need(parent[182, 1] == parent[507, 1] == (1, 1, 61),
         'Merged read-1 actions differ')
    need(parent[182, 0] == (0, 1, 76) and parent[507, 0] == (0, 1, 90),
         'Unexpected parent read-0 actions')
    need(incoming(intermediate, 200) == [((112, 1), (1, 1, 200))],
         'Discarded state 200 has an uncertified entrance')
    need(incoming(intermediate, 112) == [((172, 0), (0, -1, 112))],
         'State 112 has an entrance that does not establish the zero guard')
    need(intermediate[200, 0] == intermediate[209, 0],
         'Second-fold read-0 actions differ')
    cases = [local_case(parent, intermediate, old_state, tag, bit)
             for old_state, tag in ((182, 1), (507, 0)) for bit in (0, 1)]
    need([case['candidate_steps'] for case in cases] == [3, 1, 5, 1],
         'Unexpected guarded local durations')
    return {
        'status': 'GUARDED_FOLDS_VERIFIED',
        'working_states': [220, 219, 218],
        'transition_rows': [440, 438, 436],
        'first_fold': {
            'drop': 507, 'keep': 182, 'selector': 209,
            'incoming_old': incoming(parent, 182),
            'incoming_clone': incoming(parent, 507),
            'cases': cases,
            'argument': 'The old entrances establish predecessor tag 1 for 182 and '
                        'tag 0 for 507. Start state 0 is neither state. The four '
                        'checked local computations replace one parent step by '
                        '1, 3, or 5 steps, with identical full tape and head at '
                        'their endpoints and no internal halt. Induction on finite '
                        'runs and positive-progress reflection transport halting '
                        'in both directions, for every initial tape at state 0.'},
        'second_fold': {
            'drop': 200, 'keep': 209,
            'incoming_200': incoming(intermediate, 200),
            'incoming_112': incoming(intermediate, 112),
            'matching_read_zero': intermediate[200, 0],
            'argument': 'Every entrance into 112 follows 172/read0, which writes '
                        'zero and moves left. The only entrance into 200 follows '
                        '112/read1, which moves right back to the written zero. '
                        'Start 0 is neither 112 nor 200. Therefore every reachable '
                        '200 configuration scans zero, where 200 and 209 agree. '
                        'State projection preserves every reachable literal step.'},
        'scope': 'Exact finite local mathematical certificates and structural '
                 'invariants. No new proof-assistant kernel certificate. Source, '
                 'theory calibration, complete primitive simulation, and actual '
                 'blank initialization remain separate obligations.'}


def mutation_controls(parent, intermediate, final):
    tests = []

    def reject(name, p, m, f):
        try:
            verify(p, m, f)
        except ValueError as error:
            tests.append({'name': name, 'status': 'REJECTED', 'reason': str(error)})
            return
        raise ValueError('Mutation control was accepted: ' + name)

    p = dict(parent)
    p[173, 1] = 0, 1, 182
    m = first_transform(p)
    reject('wrong_old_predecessor_tag', p, m, second_transform(m))
    p = dict(parent)
    p[18, 0] = 1, 1, 507
    m = first_transform(p)
    reject('wrong_clone_predecessor_tag', p, m, second_transform(m))
    m = dict(intermediate)
    m[182, 0] = 0, -1, 133
    reject('wrong_selector_action', parent, m, second_transform(m))
    p = dict(parent)
    write, direction, target = p[0, 1]
    p[0, 1] = write, direction, 200
    m = first_transform(p)
    reject('extra_unguarded_200_entry', p, m, second_transform(m))
    return tests


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('parent', type=Path)
    parser.add_argument('intermediate', type=Path)
    parser.add_argument('final', type=Path)
    parser.add_argument('receipt', type=Path)
    args = parser.parse_args()
    parent, intermediate, final = map(read_table, (args.parent, args.intermediate, args.final))
    result = verify(parent, intermediate, final)
    result['mutation_controls'] = mutation_controls(parent, intermediate, final)
    result['input_sha256'] = {name: hashlib.sha256(path.read_bytes()).hexdigest()
                              for name, path in [('parent', args.parent),
                                                 ('intermediate', args.intermediate),
                                                 ('final', args.final)]}
    args.receipt.parent.mkdir(parents=True, exist_ok=True)
    args.receipt.write_text(json.dumps(result, indent=2) + '\n', encoding='utf-8')
    print(json.dumps({'status': result['status'], 'working_states': result['working_states'],
                      'local_cases': len(result['first_fold']['cases']),
                      'mutation_controls_rejected': len(result['mutation_controls']),
                      'input_sha256': result['input_sha256']}, indent=2))


if __name__ == '__main__':
    main()
