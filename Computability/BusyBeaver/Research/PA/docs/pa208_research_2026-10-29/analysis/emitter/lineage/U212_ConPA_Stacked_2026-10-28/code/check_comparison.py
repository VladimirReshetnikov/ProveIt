#!/usr/bin/env python3
"""Recompute the literal-table and source comparison from all eight inputs."""
import hashlib
import json
from pathlib import Path
from build import need, digest

ROOT = Path(__file__).resolve().parents[1]

def read_table(path):
    result = {}
    for line in path.read_text().splitlines():
        if not line or line.startswith('#'):
            continue
        q, bit, write, direction, target = line.split()
        key = int(q), int(bit)
        need(key not in result and direction in ('L', 'R'), 'table row')
        result[key] = int(write), direction, int(target)
    return result

def source_info(rows):
    leaves = {p: (op, arg) for p, op, arg in rows}
    need(len(leaves) == len(rows), 'duplicate source path')
    seen = set()
    def rec(prefix):
        node = leaves[prefix] if prefix in leaves else (rec(prefix + '0'), rec(prefix + '1'))
        seen.add(node)
        return node
    tree = rec('')
    metrics = {'primitive_occurrences': len(rows),
               'distinct_subtrees_including_leaves': len(seen),
               'maximum_depth': max(len(p) for p, _, _ in rows),
               'maximum_zero_run': max(len(z) for p, _, _ in rows for z in p.split('1')),
               'guarded_cases': len(rows) + sum(op == 'CD' for _, op, _ in rows)}
    bounds = {}
    for i, (p, _, _) in enumerate(rows):
        for j in range(len(p) + 1):
            prefix = p[:j]
            if prefix not in bounds:
                bounds[prefix] = [i, i + 1]
            else:
                bounds[prefix][1] = i + 1
    graph = []
    for i, (p, op, arg) in enumerate(rows):
        if op == 'CI':
            targets = [i + 1]
        elif op == 'CH':
            targets = []
        else:
            char = '1' if op == 'CC' else '0'
            offset = 1 if op == 'CD' else arg
            positions = [j for j, b in enumerate(p) if b == char]
            need(len(positions) >= offset, 'source branch escapes')
            target = bounds[p[:positions[-offset]]][0 if op == 'CC' else 1]
            targets = [target, i + 1] if op == 'CD' else [target]
        graph.append([op, arg, targets])
    return tree, metrics, graph

def run():
    catalog = json.loads((ROOT / 'comparison/catalog.json').read_text())
    base_path = ROOT / 'comparison/inputs/u214.native.tm'
    source_path = ROOT / 'comparison/inputs/u214_sites.json'
    need(digest(base_path.read_bytes()) == catalog['baseline_table_sha256'], 'U214 table')
    need(digest(source_path.read_bytes()) == catalog['baseline_source_sha256'], 'U214 source')
    base = read_table(base_path)
    base_rows = json.loads(source_path.read_text())
    _, _, base_graph = source_info(base_rows)
    base_states = {q for q, _ in base}
    hashes, summary = set(), []
    for item in catalog['entries']:
        table_path, sites_path = ROOT / item['table'], ROOT / item['source']
        need(digest(table_path.read_bytes()) == item['native_table_sha256'], 'native identity')
        need(digest(sites_path.read_bytes()) == item['source_byte_sha256'], 'source identity')
        hashes.add(item['native_table_sha256'])
        table = read_table(table_path)
        states = {q for q, _ in table}
        need(len(states) == 213 and set(table) == {(q, b) for q in states for b in (0, 1)},
             '213-state table census')
        need({z for _, _, z in table.values()} - states == {254}, 'native halt')
        seen, todo = {0}, [0]
        for q in todo:
            for bit in (0, 1):
                target = table[q, bit][2]
                if target != 254 and target not in seen:
                    seen.add(target)
                    todo.append(target)
        need(len(seen) == item['graph_reachable_states'] == 213, 'graph census')
        rows = json.loads(sites_path.read_text())
        tree, metrics, graph = source_info(rows)
        need(metrics == item['metrics'], 'source metrics')
        need(digest(json.dumps(tree, separators=(',', ':')).encode()) == item['source_tree_sha256'],
             'source tree fingerprint')
        need(digest(json.dumps(graph, separators=(',', ':')).encode()) == item['source_cfg_sha256'],
             'source graph fingerprint')
        changed = [[*key, *base[key], *table[key]] for key in sorted(base.keys() & table.keys())
                   if base[key] != table[key]]
        need(changed == item['changed_rows'], 'literal delta')
        need(len(changed) == item['changed_retained_rows_relative_to_U214'], 'delta census')
        need(sorted(base_states - states) == item['deleted_native_states_relative_to_U214'],
             'removed states')
        need(sorted(states - base_states) == item['added_native_states_relative_to_U214'],
             'added states')
        need(([r[1:] for r in rows] == [r[1:] for r in base_rows]) ==
             item['primitive_word_identical_to_U214'], 'primitive word')
        need((graph == base_graph) == item['ordinal_CFG_identical_to_U214'], 'guarded CFG')
        need((rows == base_rows) == item['source_addresses_identical_to_U214'], 'source addresses')
        helpers = [q for q in sorted(states)
                   if table[q, 0] == (0, 'R', 218) and table[q, 1] == (1, 'R', 184)]
        need(helpers == item['old167_exact_representatives'], 'translated helper role')
        summary.append({'id': item['id'], 'metrics': metrics, 'helper_roles': helpers})
    need(len(hashes) == len(summary) == 8, 'eight distinct proposals')
    return {'status': 'EIGHT_PROPOSAL_COMPARISON_PASS', 'entries': summary,
            'scope': 'Exact literal/source comparison; method descriptions retain source attribution.'}

if __name__ == '__main__':
    print(json.dumps(run(), indent=2))
