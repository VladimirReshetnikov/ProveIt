#!/usr/bin/env python3
"""Verify a PA196 three-category cleanup and its combination with zero-transfer."""
from __future__ import annotations
import argparse
import hashlib
import importlib.util
import json
from collections import deque
from pathlib import Path

HERE = Path(__file__).resolve().parent
PARENT_FIRST = tuple(map(int, '1010101110'))
PARENT_SECOND = tuple(map(int, '00011'))


def require(value, message):
    if not value:
        raise ValueError(message)


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    m = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(m)
    return m


def successors(row, category):
    """Track register 6 as 0, 1, or ≥2; other decrement branches are both possible."""
    op = row[0]
    if op == 'halt':
        return ()
    if op == 'jump':
        return ((row[1], category),)
    if op == 'inc':
        return ((row[2], min(2, category + 1) if row[1] == 6 else category),)
    if op == 'dec':
        if row[1] != 6:
            return ((row[2], category), (row[3], category))
        if category == 0:
            return ((row[2], 0),)
        if category == 1:
            return ((row[3], 0),)
        return ((row[3], 1), (row[3], 2))
    raise ValueError(f'unknown instruction: {row}')


def invariant(graph):
    initial = (25, 0)
    seen = {initial}
    todo = deque([initial])
    while todo:
        pc, category = todo.popleft()
        for state in successors(graph[pc], category):
            require(state[0] is not None, 'unexpected source exit')
            if state not in seen:
                seen.add(state)
                todo.append(state)
    require(initial in seen, 'missing initial state')
    for pc, category in seen:
        require(all(s in seen for s in successors(graph[pc], category)),
                f'closure failure at {(pc, category)}')
    return seen


def patch(module, root, path, test_op, old_ordinals):
    node = root
    for bit in path:
        require(module.isnode(node), 'patch path descends into leaf')
        node = module.store[node][1 + bit]
    require(module.isnode(node), 'patch parent is not a node')
    _, left, right = module.store[node]
    require(module.isnode(left), 'patch parent has no compound left child')
    _, test, _ = module.store[left]
    require(module.store[test] == test_op, 'wrong decrement at patch location')
    leaves = list(module.leaf_occurrences(root))
    actual = [i for i, (p, _) in enumerate(leaves) if p[:len(path)+1] == path + (0,)]
    # Ordinals may shift after the other disjoint patch.
    require(actual == old_ordinals, f'wrong patch interval: {actual}')
    return module.rewrite_occurrence(root, path, right)


def project_graph(original, modified, deleted, zero_targets):
    kept = [i for i in range(len(original)) if i not in deleted]
    rank = {old: new for new, old in enumerate(kept)}
    require(len(kept) == len(modified), 'wrong projected graph size')
    for test, target in zero_targets.items():
        require(test in deleted and target in rank, 'skipped test or retained zero target invalid')
        require(original[test][0] == 'dec' and original[test][2] == target,
                'skipped test does not take the specified zero edge')
    def project(target):
        if target is None:
            return None
        if target in zero_targets:
            return rank[zero_targets[target]]
        require(target in rank, f'edge targets deleted positive-loop body {target}')
        return rank[target]
    for old in kept:
        row = original[old]
        op = row[0]
        if op == 'inc':
            result = (op, row[1], project(row[2]))
        elif op == 'dec':
            result = (op, row[1], project(row[2]), project(row[3]))
        elif op == 'jump':
            result = (op, project(row[1]))
        else:
            result = row
        require(result == modified[rank[old]], f'projected CFG differs at old site {old}')
    return rank


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output', type=Path)
    args = ap.parse_args()
    m = load('pa196_rotations', HERE / 'scan_rotations.py')
    zero = load('pa196_zero', HERE / 'verify_zero_transfer.py')
    for rel, expected in zero.PINS.items():
        actual = hashlib.sha256((zero.UPSTREAM / rel).read_bytes()).hexdigest()
        require(actual == expected, f'changed seed source {rel}: {actual}')
    source = m.root
    original, _ = zero.interval_graph(m, source)
    require(original == m.graph(source), 'original source resolvers disagree')
    require(len(original) == 3812 and all(None not in row for row in original),
            'source has unexpected size or normal exit')
    require(original[7:10] == [('dec', 6, 9, 8), ('jump', 5), ('jump', 11)],
            'unexpected second cleanup source rows')
    require(original[3773:3776] == [('dec', 1, 3776, 3774), ('inc', 6, 3775), ('jump', 3773)],
            'unexpected first cleanup source rows')
    reach6 = invariant(original)
    require({c for i, c in reach6 if i == 7} == {0}, 'site 7 is not forced zero')
    require(not any(i == 8 for i, _ in reach6), 'site 8 is not unreachable')
    reach1 = zero.invariant(original, 1, 0)
    require({c for i, c in reach1 if i == 3773} == {0}, 'site 3773 is not forced zero')
    require(not any(i in (3774, 3775) for i, _ in reach1), 'first loop body is reachable')
    second = patch(m, source, PARENT_SECOND, ('dec', 6), [7, 8])
    second_graph, _ = zero.interval_graph(m, second)
    require(second_graph == m.graph(second), 'second-only resolvers disagree')
    rank_second = project_graph(original, second_graph, {7, 8}, {7: 9})
    first = patch(m, source, PARENT_FIRST, ('dec', 1), [3773, 3774, 3775])
    both = patch(m, first, PARENT_SECOND, ('dec', 6), [7, 8])
    reverse_order = patch(m, second, PARENT_FIRST, ('dec', 1), [3771, 3772, 3773])
    require(reverse_order == both, 'disjoint patch orders yield different source trees')
    both_graph, _ = zero.interval_graph(m, both)
    require(both_graph == m.graph(both), 'combined resolvers disagree')
    rank_both = project_graph(original, both_graph, {7, 8, 3773, 3774, 3775},
                              {7: 9, 3773: 3776})
    require((len(second_graph), m.metric(second)) == (3810, 161), 'second patch size changed')
    require((len(both_graph), m.metric(both)) == (3807, 162), 'combined patch size changed')
    require(rank_second[25] == 23 and rank_both[25] == 23, 'clean start projection changed')
    digest6 = hashlib.sha256(json.dumps(sorted(reach6), separators=(',', ':')).encode()).hexdigest()
    digest1 = hashlib.sha256(json.dumps(sorted(reach1), separators=(',', ':')).encode()).hexdigest()
    selected = {str(i): sorted(c for j, c in reach6 if j == i)
                for i in (0, 1, 3, 4, 5, 6, 7, 8, 9, 10, 25)}
    result = {'program_sha256': hashlib.sha256((HERE / 'Program.lean').read_bytes()).hexdigest(),
              'seed_file_sha256': zero.PINS, 'seed_site': 25,
              'initial_register_vector': [2,0,0,0,0,0,0,0,0],
              'register6_invariant_pairs': len(reach6), 'register6_invariant_sha256': digest6,
              'register6_categories_at_selected_sites': selected,
              'register1_invariant_pairs': len(reach1), 'register1_invariant_sha256': digest1,
              'single_second_patch': {'path': '00011', 'replace': 'parent with right child',
                'old_deleted_sites': [7,8], 'old_zero_successor': 9, 'sites': len(second_graph),
                'distinct_internal_nodes': m.metric(second), 'new_seed_site': rank_second[25],
                'all_retained_rows_checked': True, 'independent_resolvers_agree': True},
              'combined_patch': {'paths': ['1010101110','00011'], 'replace': 'each parent with right child',
                'old_deleted_sites': [7,8,3773,3774,3775], 'sites': len(both_graph),
                'distinct_internal_nodes': m.metric(both), 'new_seed_site': rank_both[25],
                'all_retained_rows_checked': True, 'independent_resolvers_agree': True}}
    out = json.dumps(result, indent=2, sort_keys=True) + '\n'
    print(out, end='')
    if args.output:
        args.output.write_text(out)


if __name__ == '__main__':
    main()
