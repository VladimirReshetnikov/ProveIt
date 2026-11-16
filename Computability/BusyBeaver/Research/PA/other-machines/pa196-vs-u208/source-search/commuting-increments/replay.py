#!/usr/bin/env python3
"""Check all adjacent-increment swaps and export disjoint global candidates."""
import argparse
from collections import Counter, defaultdict
from itertools import combinations
import hashlib
import importlib.util
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
SOURCE = HERE.parent

def need(test, reason):
    if not test:
        raise ValueError(reason)

def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module

def targets(row):
    if row[0] == 'jump':
        return (row[1],)
    if row[0] == 'inc':
        return (row[2],)
    if row[0] == 'dec':
        return row[2:4]
    return ()

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    parser.add_argument('--write-sources', type=Path)
    args = parser.parse_args()
    m = load('commute_tree', SOURCE / 'scan_rotations.py')
    z = load('commute_interval', SOURCE / 'verify_zero_transfer.py')
    for path, digest in z.PINS.items():
        need(hashlib.sha256((z.UPSTREAM / path).read_bytes()).hexdigest() == digest,
             'changed source seed: ' + path)
    graph = m.graph(m.root)
    interval, leaves = z.interval_graph(m, m.root)
    need(graph == interval and len(leaves) == 3812 and m.metric(m.root) == 159,
         'original graph, size or source DAG changed')
    predecessors = defaultdict(set)
    for pc, row in enumerate(graph):
        for target in targets(row):
            need(target is not None, 'source exits the root')
            predecessors[target].add(pc)
    groups = defaultdict(list)
    for pc in range(len(graph) - 1):
        left, right = graph[pc:pc + 2]
        if (left[0] == right[0] == 'inc' and left[1] != right[1]
                and left[2] == pc + 1 and predecessors[pc + 1] == {pc}):
            groups[left[1], right[1]].append(pc)
    need({key: len(value) for key, value in groups.items()}
         == {(8, 6): 1, (7, 6): 139, (1, 6): 67},
         'adjacent-increment inventory changed')
    positions = sorted(pc for values in groups.values() for pc in values)
    need(all(b > a + 1 for a, b in zip(positions, positions[1:])), 'overlapping swaps')
    need(25 not in {i + 1 for i in positions}, 'seed enters a block in its middle')
    single_cost = Counter()
    for i in positions:
        path1, leaf1 = leaves[i]
        path2, leaf2 = leaves[i + 1]
        edited = m.rewrite_occurrence(m.rewrite_occurrence(m.root, path1, leaf2), path2, leaf1)
        single_cost[m.metric(edited)] += 1
    need(sum(single_cost.values()) == 207, 'single-occurrence census mismatch')
    opnames = {'inc':'CI', 'dec':'CD', 'breakTo':'CB', 'continueTo':'CC', 'halt':'CH'}
    candidates = []
    keys = tuple(groups)
    for count in range(1, len(keys) + 1):
        for selected in combinations(keys, count):
            selected_sites = sorted(pc for key in selected for pc in groups[key])
            edited = m.root
            for i in selected_sites:
                path1, leaf1 = leaves[i]
                path2, leaf2 = leaves[i + 1]
                edited = m.rewrite_occurrence(m.rewrite_occurrence(edited, path1, leaf2), path2, leaf1)
            edited_graph = m.graph(edited)
            other_graph, edited_leaves = z.interval_graph(m, edited)
            need(edited_graph == other_graph, 'candidate graph resolvers disagree')
            expected = list(graph)
            for i in selected_sites:
                expected[i] = ('inc', graph[i + 1][1], i + 1)
                expected[i + 1] = ('inc', graph[i][1], graph[i + 1][2])
            need(edited_graph == expected, 'candidate graph differs outside the selected swaps')
            rows = [[''.join(map(str, path)), opnames[m.store[leaf][0]],
                     None if m.store[leaf][0] == 'halt' else m.store[leaf][1]]
                    for path, leaf in edited_leaves]
            data = (json.dumps(rows, separators=(',', ':')) + '\n').encode()
            name = 'swap-' + '-'.join(f'{a}-{b}' for a, b in selected) + '.json'
            if args.write_sources:
                args.write_sources.mkdir(parents=True, exist_ok=True)
                (args.write_sources / name).write_bytes(data)
            rotation_costs = Counter(m.metric(rotated) for rotated, _ in m.allrot(edited))
            candidates.append({'groups': [list(k) for k in selected],
                               'source_name': name, 'source_sha256': hashlib.sha256(data).hexdigest(),
                               'swapped_blocks': len(selected_sites),
                               'internal_nodes': m.metric(edited),
                               'one_global_rotation_costs': dict(sorted(rotation_costs.items())),
                               'independent_graphs_agree': True})
    receipt = {'program_sha256': hashlib.sha256((z.UPSTREAM / 'PA196/Program.lean').read_bytes()).hexdigest(),
               'source_seed_sha256': z.PINS, 'source_seed_site': 25,
               'original_sites': len(graph), 'original_internal_nodes': m.metric(m.root),
               'safe_increment_pair_counts': {f'{a},{b}': len(sites) for (a, b), sites in groups.items()},
               'single_swap_internal_node_costs': dict(sorted(single_cost.items())),
               'all_selected_blocks_disjoint': True, 'candidate_full_graph_checks': 7,
               'global_candidates': candidates,
               'scope': 'Only adjacent unequal increment pairs with unique predecessor at the second site; no physical allocation or PA theorem.'}
    data = json.dumps(receipt, indent=2, sort_keys=True) + '\n'
    print(data, end='')
    if args.output:
        args.output.write_text(data)

if __name__ == '__main__':
    main()
