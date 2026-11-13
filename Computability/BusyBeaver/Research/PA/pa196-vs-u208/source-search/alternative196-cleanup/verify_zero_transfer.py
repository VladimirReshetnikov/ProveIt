#!/usr/bin/env python3
"""Verify the PA196 site-3773 zero-transfer specialization; see ZERO-TRANSFER.md."""
from __future__ import annotations
import argparse
import hashlib
import importlib.util
import json
from collections import defaultdict, deque
from pathlib import Path

HERE = Path(__file__).resolve().parent
UPSTREAM = HERE.parents[2] / 'jamesyc-upstream/pa196'
PINS = {
    'PA196/Source/Nonhalting.lean': '0fcab6b180e8445b1874335257bd8eaaaae9cf84ad97ef21e887555337f4756b',
    'PA196/Source/CommandRegisters.lean': '45a22b537f91a820875be23b953b1896de7258a46dae0daad50dab0c418eb0a1',
    'PA196/Logic/CommandSoundness.lean': 'b749769a36c84fb000828748776c5d7729348ebd03d888898c807292872beb4c',
}
PATCH_PATH = tuple(map(int, '1010101110'))
DELETED = (3773, 3774, 3775)
INITIAL = 25


def require(condition, message):
    if not condition:
        raise ValueError(message)


def load_tree_module():
    path = HERE / 'scan_rotations.py'
    spec = importlib.util.spec_from_file_location('pa196_scan_rotations', path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def interval_graph(module, root):
    """Ordinal resolver by ancestor intervals, independent of binary successor."""
    leaves = list(module.leaf_occurrences(root))
    intervals = {}
    for i, (path, _) in enumerate(leaves):
        for n in range(len(path) + 1):
            prefix = path[:n]
            if prefix not in intervals:
                intervals[prefix] = [i, i]
            else:
                intervals[prefix][1] = i
    def after_interval(path, bit, depth):
        if depth == 0:
            return None  # caller handles depth zero as ordinary successor
        hits = [i for i, b in enumerate(path) if b == bit]
        require(len(hits) >= depth, f'unresolved cut at {path} depth {depth}')
        return path[:hits[-depth]]
    def next_after(prefix):
        j = intervals[prefix][1] + 1
        return j if j < len(leaves) else None
    rows = []
    for i, (path, op_id) in enumerate(leaves):
        op, reg = module.store[op_id]
        next_ordinal = i + 1 if i + 1 < len(leaves) else None
        if op == 'inc':
            rows.append(('inc', reg, next_ordinal))
        elif op == 'dec':
            rows.append(('dec', reg, next_after(after_interval(path, 0, 1)), next_ordinal))
        elif op == 'breakTo':
            rows.append(('jump', next_ordinal if reg == 0 else next_after(after_interval(path, 0, reg))))
        elif op == 'continueTo':
            rows.append(('jump', i if reg == 0 else intervals[after_interval(path, 1, reg)][0]))
        elif op == 'halt':
            rows.append(('halt',))
        else:
            raise ValueError(f'unknown operation {op}')
    return rows, leaves


def abstract_successors(row, category, register):
    """Overapproximate a single register by zero/positive; 1 means positive."""
    op = row[0]
    if op == 'halt':
        return ()
    if op == 'jump':
        return ((row[1], category),)
    if op == 'inc':
        return ((row[2], 1 if row[1] == register else category),)
    if op == 'dec':
        if row[1] != register:
            return ((row[2], category), (row[3], category))
        if category == 0:
            return ((row[2], 0),)
        return ((row[3], 0), (row[3], 1))
    raise ValueError(f'unknown resolved operation {op}')


def invariant(graph, register, initial_category):
    initial = (INITIAL, initial_category)
    seen = {initial}
    work = deque([initial])
    while work:
        i, category = work.popleft()
        for step in abstract_successors(graph[i], category, register):
            require(step[0] is not None, 'unexpected source exit')
            if step not in seen:
                seen.add(step)
                work.append(step)
    # Separate full closure audit: not just the queue traversal's claim.
    require(initial in seen, 'initial abstract state missing')
    for i, category in seen:
        require(all(step in seen for step in abstract_successors(graph[i], category, register)),
                f'abstract successor escapes invariant at {(i, category)}')
    return seen


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output', type=Path)
    args = ap.parse_args()
    for rel, expected in PINS.items():
        got = hashlib.sha256((UPSTREAM / rel).read_bytes()).hexdigest()
        require(got == expected, f'changed upstream seed source: {rel}: {got}')
    m = load_tree_module()  # also verifies Program.lean hash and its declared root
    source = m.root
    original, leaves = interval_graph(m, source)
    require(len(original) == 3812 and m.metric(source) == 159, 'unexpected original size')
    require(original == m.graph(source), 'independent original resolvers disagree')
    require(all(None not in row for row in original), 'normal root exit requires additional argument')
    require(original[3773:3777] == [('dec', 1, 3776, 3774), ('inc', 6, 3775),
                                    ('jump', 3773), ('dec', 2, 3779, 3777)],
            'unexpected source pattern')
    all_invariants = {}
    for reg in range(9):
        # commandConfig 25 2 0 0 zeroStore: register 0 is 2, others are 0.
        all_invariants[reg] = invariant(original, reg, 1 if reg == 0 else 0)
    reach = all_invariants[1]
    require((3773, 0) in reach and (3773, 1) not in reach, 'target test not forced zero')
    require(not any((i, c) in reach for i in (3774, 3775) for c in (0, 1)),
            'target loop body not abstractly unreachable')
    # Remove the left child of the identified parent; retain its right child.
    parent = source
    for bit in PATCH_PATH:
        require(m.isnode(parent), 'patch path descends through a leaf')
        parent = m.store[parent][1 + bit]
    require(m.isnode(parent), 'patch target is not a parent node')
    _, left, right = m.store[parent]
    require(m.isnode(left), 'patch left child is not a loop')
    _, test, body = m.store[left]
    require(m.store[test] == ('dec', 1) and m.isnode(body), 'wrong loop test')
    require([i for i, (p, _) in enumerate(leaves) if p[:len(PATCH_PATH)+1] == PATCH_PATH + (0,)]
            == list(DELETED), 'patch does not delete precisely the specified interval')
    optimized = m.rewrite_occurrence(source, PATCH_PATH, right)
    reduced, new_leaves = interval_graph(m, optimized)
    require(reduced == m.graph(optimized), 'independent optimized resolvers disagree')
    require(len(reduced) == 3809 and m.metric(optimized) == 160, 'unexpected optimized size')
    require(all(None not in row for row in reduced), 'optimized source exits root')
    kept = [i for i in range(len(original)) if i not in set(DELETED)]
    rank = {i: j for j, i in enumerate(kept)}
    zero_exit = original[3773][2]
    require(zero_exit in rank, 'zero exit was deleted')
    def project(target):
        if target is None:
            return None
        if target == 3773:
            return rank[zero_exit]
        require(target in rank, f'retained instruction targets unreachable body {target}')
        return rank[target]
    for i in kept:
        row = original[i]
        op = row[0]
        if op == 'inc':
            translated = (op, row[1], project(row[2]))
        elif op == 'dec':
            translated = (op, row[1], project(row[2]), project(row[3]))
        elif op == 'jump':
            translated = (op, project(row[1]))
        else:
            translated = row
        require(translated == reduced[rank[i]], f'CFG mismatch at original site {i}')
    require(rank[INITIAL] == INITIAL, 'clean initial site changed')
    categories = {str(i): sorted(c for j, c in reach if j == i)
                  for i in (3760, 3763, 3767, 3773, 3774, 3775, 3776)}
    forced = {str(reg): [i for i, row in enumerate(original)
                          if row[0] == 'dec' and row[1] == reg and (i, 0) in all_invariants[reg]
                          and (i, 1) not in all_invariants[reg]] for reg in range(9)}
    require(forced['1'] == [3773] and all(not forced[str(i)] for i in range(9) if i != 1),
            'forced-zero inventory changed')
    canonical = json.dumps(sorted(reach), separators=(',', ':')).encode()
    result = {'program_sha256': hashlib.sha256((HERE / 'Program.lean').read_bytes()).hexdigest(),
              'seed_file_sha256': PINS, 'seed_site': INITIAL,
              'initial_register_vector': [2, 0, 0, 0, 0, 0, 0, 0, 0],
              'zero_positive_invariant_pairs': len(reach),
              'zero_positive_invariant_sha256': hashlib.sha256(canonical).hexdigest(),
              'register1_categories_at_selected_sites': categories,
              'forced_zero_decrement_sites_by_register': forced,
              'all_register_invariant_pair_counts': {str(i): len(all_invariants[i]) for i in range(9)},
              'patch_parent_path': ''.join(map(str, PATCH_PATH)), 'patch': 'replace parent with right child',
              'deleted_old_sites': list(DELETED), 'removed_zero_exit_old_site': zero_exit,
              'original_sites': len(original), 'optimized_sites': len(reduced),
              'original_unique_internal_nodes': m.metric(source),
              'optimized_unique_internal_nodes': m.metric(optimized),
              'retained_ordinal_rows_compared': len(kept),
              'independent_source_resolvers_agree': True}
    out = json.dumps(result, indent=2, sort_keys=True) + '\n'
    print(out, end='')
    if args.output:
        args.output.write_text(out)


if __name__ == '__main__':
    main()
