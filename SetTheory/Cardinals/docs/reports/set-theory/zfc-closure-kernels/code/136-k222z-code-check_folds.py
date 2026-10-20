#!/usr/bin/env python3
"""Independent, standard-library checker for the two conditional-G222 folds.

Acceptance proves a positive-block simulation from a shared start state on
EVERY initial binary tape. No sampled execution, source compiler, or search
module is imported. All unmentioned tape cells are arbitrary and untouched.
"""
from pathlib import Path
import argparse
import hashlib
import json


def require(condition, message):
    if not condition:
        raise ValueError(message)


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def read_table(path):
    rows = {}
    start = None
    for line in Path(path).read_text().splitlines():
        if not line:
            continue
        if line.startswith('#! start '):
            require(start is None, 'duplicate start declaration')
            start = int(line.split()[-1])
            continue
        if line.startswith('#'):
            continue
        q, b, w, d, z = line.split()
        q, b, w, z = map(int, (q, b, w, z))
        require((q, b) not in rows, 'duplicate row')
        require(b in (0, 1) and w in (0, 1) and d in ('L', 'R'), 'nonbinary row')
        rows[q, b] = (w, -1 if d == 'L' else 1, z)
    require(start == 0, 'expected start state 0')
    check_table(rows)
    return rows


def check_table(rows):
    states = {q for q, b in rows}
    require(0 in states and 254 not in states, 'incorrect start/halt states')
    require(set(rows) == {(q, b) for q in states for b in (0, 1)}, 'incomplete table')
    require(all(z in states or z == 254 for w, d, z in rows.values()), 'missing target')
    return states


def check_inductive_invariant(rows, supplied):
    """Check initiation and every literal row, including unreachable rows.

    A fact F[q][k]=b states that the cell k steps to the right of the head
    contains b whenever old control state q is entered. The only exception
    used is an old branch whose read bit contradicts F[q][0].
    """
    states = check_table(rows)
    facts = {q: {} for q in states}
    for q, values in supplied.items():
        q = int(q)
        require(q in states, 'invariant refers to missing state')
        facts[q] = {int(k): int(b) for k, b in values.items()}
        require(all(b in (0, 1) for b in facts[q].values()), 'nonbinary invariant')
    require(not facts[0], 'initial tape must be arbitrary')
    checked = 0
    excluded = []
    for (q, b), (w, d, z) in rows.items():
        if 0 in facts[q] and facts[q][0] != b:
            excluded.append([q, b])
            continue
        antecedent = dict(facts[q])
        antecedent[0] = b
        for k, value in facts.get(z, {}).items():
            # New relative k is old relative k+d; old relative 0 was written.
            actual = w if k + d == 0 else antecedent.get(k + d)
            require(actual == value, f'noninductive fact {z}/{k} via {q}/{b}')
        checked += 1
    return facts, {'checked_rows': checked, 'excluded_rows': excluded,
                   'nonempty_facts': supplied}


def transformed(old, fold):
    keep, drop = fold['keep'], fold['delete']
    require(keep != drop and keep not in (0, 254) and drop not in (0, 254), 'bad fold')
    require((keep, 0) in old and (drop, 0) in old, 'missing fold state')
    phi = lambda q: keep if q == drop else q
    new = {(q, b): (w, d, phi(z)) for (q, b), (w, d, z) in old.items() if q != drop}
    for b in (0, 1):
        w, d, z = fold[f'a{b}']
        require(w in (0, 1) and d in (-1, 1), 'bad replacement action')
        new[keep, b] = (w, d, phi(z))
    check_table(new)
    require(len(new) == len(old) - 2, 'fold must remove exactly one state')
    return new, phi


def local_block(new, entry, initial, target, maximum):
    """Execute on a finite fixed patch, rejecting every unknown read.

    Passing therefore covers all binary assignments to its infinite exterior.
    The step limit only limits which certificates can pass; it never permits
    an unfinished or unknown path to be accepted.
    """
    q, h = entry, 0
    tape = dict(initial)
    z, expected_h, expected_tape = target
    trace = []
    for tick in range(1, maximum + 1):
        require(q != 254 and h in tape, 'interior halt or unknown tape read')
        b = tape[h]
        w, d, nxt = new[q, b]
        trace.append([q, h, b, w, d, nxt])
        tape[h] = w
        h += d
        q = nxt
        if q == z and h == expected_h and tape == expected_tape:
            return {'steps': tick, 'trace': trace, 'target_state': z,
                    'target_head': h, 'target_patch': tape}
    raise ValueError('block did not reach the exact whole-tape endpoint')


def check_chain(parent, candidate, specification):
    spec = json.loads(Path(specification).read_text())
    require(digest(parent) == spec['parent_sha256'], 'parent file hash mismatch')
    require(digest(candidate) == spec['candidate_sha256'], 'candidate file hash mismatch')
    old = read_table(parent)
    require(len(old) == 448, 'expected 224 parent working states')
    results = []
    for i, fold in enumerate(spec['folds'], 1):
        facts, invariant = check_inductive_invariant(old, fold['invariant'])
        new, phi = transformed(old, fold)
        keep, drop = fold['keep'], fold['delete']
        blocks, skipped = [], []
        for q in (keep, drop):
            for b in (0, 1):
                if 0 in facts[q] and facts[q][0] != b:
                    skipped.append([q, b])
                    continue
                initial = dict(facts[q])
                initial[0] = b
                w, d, z = old[q, b]
                expected = dict(initial)
                expected[0] = w
                block = local_block(new, keep, initial, (phi(z), d, expected), 16)
                blocks.append({'old_state': q, 'read_bit': b,
                               'initial_patch': initial, **block})
        # All other old states literally implement one mapped old step.
        for (q, b), (w, d, z) in old.items():
            if q not in (keep, drop):
                require(new[phi(q), b] == (w, d, phi(z)), 'ordinary row changed')
        results.append({'fold': i, 'keep': keep, 'delete': drop,
                        'old_states': len(old) // 2, 'new_states': len(new) // 2,
                        'ordinary_old_rows': len(old) - 4,
                        'invariant': invariant, 'impossible_fold_branches': skipped,
                        'positive_blocks': blocks})
        old = new
    require(old == read_table(candidate), 'fold chain does not yield delivered candidate')
    require(len(old) == 444, 'expected 222 candidate working states')
    reachable, todo = {0}, [0]
    for q in todo:
        for b in (0, 1):
            z = old[q, b][2]
            if z != 254 and z not in reachable:
                reachable.add(z)
                todo.append(z)
    require(reachable == check_table(old), 'unreachable declared working states')
    return {'status': 'ALL_TAPE_POSITIVE_BLOCK_FOLD_CHAIN_PASS',
            'working_states': 222, 'transition_rows': 444,
            'parent_sha256': digest(parent), 'candidate_sha256': digest(candidate),
            'source_premise': 'No source premise is needed for this equivalence result.',
            'scope': 'Same start state 0, every initial binary tape, and every head position. '
                     'The two deterministic machines halt together; every simulated old step '
                     'advances the new machine positively and preserves the whole tape at '
                     'the mapped boundary. This certificate alone does not identify the '
                     'parent machine with a proof-search program.',
            'folds': results}


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    here = Path(__file__).resolve().parent
    parser.add_argument('--parent', type=Path, default=here.parent / 'machine/parent224.k.tm')
    parser.add_argument('--candidate', type=Path, default=here.parent / 'machine/candidate222.k.tm')
    parser.add_argument('--specification', type=Path, default=here.parent / 'inputs/folds.json')
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    receipt = check_chain(args.parent, args.candidate, args.specification)
    output = json.dumps(receipt, indent=2) + '\n'
    if args.output:
        args.output.write_text(output)
    print(output)
