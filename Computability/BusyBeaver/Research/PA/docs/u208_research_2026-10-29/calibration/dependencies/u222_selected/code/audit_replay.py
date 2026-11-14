#!/usr/bin/env python3
"""Audit the fixed U222 reconstruction in ordinary and optimized Python.

This is a finite artifact/relabeling audit, independent of runtime and logic
proofs. No search, optimizer, network connection, or third-party module is used.
"""
from __future__ import annotations
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import subprocess
import sys
from tempfile import TemporaryDirectory


def require(ok, message):
    if not ok:
        raise ValueError(message)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def table(path):
    rows = {}
    for line in path.read_text().splitlines():
        if line and not line.startswith('#'):
            q, b, w, d, t = line.split()
            key = int(q), int(b)
            require(key not in rows, 'Duplicate table row')
            rows[key] = int(w), d, int(t)
    return rows


def source_metrics(path):
    rows = json.loads(path.read_text())
    nodes = {p: (op, arg) for p, op, arg in rows}
    require(len(nodes) == len(rows), 'Duplicate source site')
    prefixes = {p[:i] for p, _, _ in rows for i in range(len(p))}
    require(not (set(nodes) & prefixes), 'Leaf is also an internal node')
    for p in sorted(prefixes, key=lambda p: -len(p)):
        require(p+'0' in nodes and p+'1' in nodes, 'Incomplete binary source')
        nodes[p] = nodes[p+'0'], nodes[p+'1']
    require('' in nodes, 'Missing source root')
    return {
        'dag_nodes': len(set(nodes.values())),
        'leaf_occurrences': len(rows),
        'maximum_depth': max(len(p) for p, _, _ in rows),
        'maximum_zero_run': max(len(s) for p, _, _ in rows for s in p.split('1')),
    }, dict(sorted(Counter(op for _, op, _ in rows).items()))


def exact_bisimulation(rows, halt):
    """Strong state equivalence preserving read/write/move at every step."""
    states = sorted({q for q, _ in rows})
    classes = {q: 0 for q in states}
    rounds = 0
    while True:
        signatures = {}
        updated = {}
        for q in states:
            actions = []
            for b in (0, 1):
                w, d, t = rows[q, b]
                actions.append((w, d, -1 if t == halt else classes[t]))
            signature = classes[q], tuple(actions)
            updated[q] = signatures.setdefault(signature, len(signatures))
        rounds += 1
        if updated == classes:
            break
        classes = updated
    groups = {}
    for q, c in classes.items():
        groups.setdefault(c, []).append(q)
    return rounds, [g for g in groups.values() if len(g) > 1]


def main():
    here = Path(__file__).resolve().parent
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--baseline-source', type=Path, default=here.parent/'inputs/k215_sites.json')
    parser.add_argument('--baseline-table', type=Path, default=here.parent/'inputs/k215.native.tm')
    parser.add_argument('--source-recipe', type=Path, default=here.parent/'inputs/source_recipe.json')
    parser.add_argument('--table-recipe', type=Path, default=here.parent/'inputs/table_recipe.json')
    args = parser.parse_args()
    source_recipe = args.source_recipe
    table_recipe = args.table_recipe
    sr = json.loads(source_recipe.read_text())
    tr = json.loads(table_recipe.read_text())
    baseline_source = args.baseline_source
    baseline_table = args.baseline_table
    with TemporaryDirectory(prefix='u222-replay-') as temporary:
        root = Path(temporary)
        for name, options in [('normal', []), ('optimized', ['-O'])]:
            target = root/name
            target.mkdir()
            for script, arguments in [
                ('build_source.py', ['--baseline', str(baseline_source),
                                     '--recipe', str(source_recipe),
                                     '--output', str(target/'sites.json')]),
                ('build_table.py', ['--baseline', str(baseline_table),
                                    '--recipe', str(table_recipe),
                                    '--output', str(target)]),
            ]:
                subprocess.run([sys.executable, *options, str(here/script),
                                *arguments], check=True, capture_output=True, text=True)
        expected_files = ('sites.json', 'u.native.tm', 'u.tm',
                          'state_map.json', 'machine_summary.json')
        for filename in expected_files:
            require((root/'normal'/filename).read_bytes() ==
                    (root/'optimized'/filename).read_bytes(),
                    'Python -O changes '+filename)
        out = root/'normal'
        metrics, primitives = source_metrics(out/'sites.json')
        require(metrics == sr['expected_metrics'], 'Independent metric mismatch')
        require(sha(out/'sites.json') == sr['expected_source_sha256'] ==
                tr['source_sha256'], 'Source identity mismatch')
        native, dense, baseline = (table(p) for p in
            (out/'u.native.tm', out/'u.tm', baseline_table))
        mapping = {int(k): v for k, v in tr['native_to_dense'].items()}
        require(len(native) == len(dense) == 444, 'Transition count mismatch')
        require({(mapping[q], b): (w, d, mapping[t])
                 for (q, b), (w, d, t) in native.items()} == dense,
                'Native/dense row mismatch')
        native_states = {q for q, _ in native}
        old_states = {q for q, _ in baseline}
        require(native_states-old_states == set(range(500, 508)), 'Added states mismatch')
        require(old_states-native_states == {204}, 'Removed states mismatch')
        changed = [[q, b, w, 1 if d == 'R' else -1, t]
                   for (q, b), (w, d, t) in sorted(native.items())
                   if baseline.get((q, b)) != (w, d, t)]
        require(changed == tr['changed_rows'], 'Patch delta not exact')
        rounds, merges = exact_bisimulation(dense, 222)
        report = {
            'status': 'U222_FINITE_RECONSTRUCTION_AUDIT_PASS',
            'scope': 'Exact replay and finite source/table checks; runtime and logic proof are separate.',
            'python_modes': ['normal', '-O'],
            'source_sha256': sha(out/'sites.json'),
            'native_sha256': sha(out/'u.native.tm'),
            'dense_sha256': sha(out/'u.tm'),
            'source_metrics': metrics,
            'primitive_counts': primitives,
            'working_states': len(native_states),
            'transitions': len(native),
            'baseline_states': len(old_states),
            'changed_or_added_rows': len(changed),
            'modified_existing_rows': sum((r[0], r[1]) in baseline for r in changed),
            'added_states': sorted(native_states-old_states),
            'removed_states': sorted(old_states-native_states),
            'row_bijection': 'all 444 rows checked',
            'strong_bisimulation_refinement_rounds': rounds,
            'nontrivial_strong_bisimulation_classes': merges,
            'optimality_claim': False,
        }
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
