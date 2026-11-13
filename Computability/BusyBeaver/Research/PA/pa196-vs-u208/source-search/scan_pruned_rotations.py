#!/usr/bin/env python3
"""Screen directional rotations of the zero-transfer-pruned PA196 source."""
from __future__ import annotations
import argparse
import importlib.util
import json
import subprocess
import sys
import time
from collections import Counter
from pathlib import Path

HERE = Path(__file__).resolve().parent


def require(condition, message):
    if not condition:
        raise ValueError(message)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    start = time.monotonic()
    # Recheck the actual semantic precondition and exact path before scanning.
    check = subprocess.run([sys.executable, '-B', str(HERE / 'verify_zero_transfer.py')],
                           check=True, capture_output=True, text=True)
    specialization = json.loads(check.stdout)
    expected = json.loads((HERE / 'zero-transfer-receipt.json').read_text())
    require(specialization == expected, 'zero-transfer certificate differs from receipt')
    spec = importlib.util.spec_from_file_location('pa196_rotations', HERE / 'scan_rotations.py')
    m = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(m)
    original = m.root
    parent = original
    path = tuple(map(int, specialization['patch_parent_path']))
    for bit in path:
        require(m.isnode(parent), 'patch descends through a leaf')
        parent = m.store[parent][1 + bit]
    require(m.isnode(parent), 'patch parent is a leaf')
    root = m.rewrite_occurrence(original, path, m.store[parent][2])
    require(m.metric(root) == 160, 'pruned root has unexpected DAG size')
    graph = m.graph(root)
    require(len(graph) == 3809, 'pruned root has unexpected site count')
    # Control: an invalid root rotation must change its last jump.
    _, left, right = m.store[root]
    require(m.isnode(left), 'control rotation has no left child')
    _, a, b = m.store[left]
    require(m.bound(a)[0] != 0 or m.bound(right)[1] != 0,
            'control rotation unexpectedly satisfies closure')
    invalid = m.graph(m.node(a, m.node(b, right)))
    require(graph[-1] == ('jump', 0) and invalid[-1] == ('jump', 11),
            'invalid rotation did not alter the known control edge')
    single, directions = Counter(), Counter()
    for path, node in m.node_occurrences(root):
        for direction, new in m.transforms(node):
            directions[direction] += 1
            single[m.metric(m.rewrite_occurrence(root, path, new))] += 1
    first, global_costs = {}, Counter()
    checked = 0
    for tree, descriptor in m.allrot(root):
        cost = m.metric(tree)
        global_costs[cost] += 1
        require(m.graph(tree) == graph, 'eligible global rotation changed the source CFG')
        checked += 1
        if cost <= 161:
            first.setdefault(tree, descriptor)
    second_costs, improvements = Counter(), []
    examined = 0
    for tree, d1 in first.items():
        for changed, d2 in m.allrot(tree):
            examined += 1
            cost = m.metric(changed)
            second_costs[cost] += 1
            if cost < 160:
                require(m.graph(changed) == graph, 'improving variant changed the source CFG')
                improvements.append({'nodes': cost, 'first': d1, 'second': d2})
    result = {'zero_transfer_receipt_rechecked': True,
              'baseline_unique_internal_nodes': 160, 'baseline_sites': len(graph),
              'single_occurrence_direction_counts': dict(directions),
              'single_occurrence_cost_counts': dict(single),
              'global_single_cost_counts': dict(global_costs),
              'single_global_full_graphs_checked': checked,
              'unique_first_with_at_most_161_nodes': len(first),
              'two_global_rotation_pairs': examined, 'two_step_cost_counts': dict(second_costs),
              'two_step_improvements_below_160': improvements,
              'elapsed_seconds': round(time.monotonic() - start, 3)}
    out = json.dumps(result, indent=2, sort_keys=True) + '\n'
    print(out, end='')
    if args.output:
        args.output.write_text(out)


if __name__ == '__main__':
    main()
