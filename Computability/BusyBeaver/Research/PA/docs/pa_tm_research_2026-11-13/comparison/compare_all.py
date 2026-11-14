#!/usr/bin/env python3
"""Reproduce the exact table/source comparison using only bundled data.

Python 3 standard library. No supplied program or Lean source is executed.
The source parser accepts only the finite Tree definitions actually used by
the two pinned snapshots. All checks survive Python's optimized mode.
"""
from pathlib import Path
from collections import Counter
import argparse
import ast
import hashlib
import json
import re

ROOT = Path(__file__).resolve().parent


def need(condition, message):
    if not condition:
        raise ValueError(message)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def read_table(path):
    rows = {}
    for line in path.read_text().splitlines():
        if not line.strip() or line.startswith('#'):
            continue
        q, b, w, direction, target = line.split()
        q, b, w, target = map(int, (q, b, w, target))
        need(b in (0, 1) and w in (0, 1) and direction in ('L', 'R'), 'Malformed row')
        need((q, b) not in rows, 'Duplicate row')
        rows[q, b] = (w, direction, target)
    states = {q for q, b in rows}
    need(set(rows) == {(q, b) for q in states for b in (0, 1)}, 'Incomplete table')
    halts = {t for w, d, t in rows.values()} - states
    need(len(halts) == 1, 'Expected exactly one halt label')
    return rows, states, halts.pop()


def canonical(rows, states, halt, start):
    mapping = {start: 0}
    queue = [start]
    result = []
    for q in queue:
        for b in (0, 1):
            w, d, t = rows[q, b]
            if t == halt:
                target = 'H'
            else:
                if t not in mapping:
                    mapping[t] = len(mapping)
                    queue.append(t)
                target = mapping[t]
            result.append([mapping[q], b, w, d, target])
    need(set(mapping) == states, 'A working state is graph-unreachable')
    return result, mapping


def parse_lean_tree(path):
    env = {}

    def expression(tokens):
        token = tokens.pop(0)
        if token == '(':
            value = expression(tokens)
            need(tokens.pop(0) == ')', 'Unbalanced Tree expression')
            return value
        if token == '.node':
            return expression(tokens), expression(tokens)
        if token == '.leaf':
            return expression(tokens)
        opcodes = {'.inc': 'CI', '.dec': 'CD', '.breakTo': 'CB', '.continueTo': 'CC'}
        if token in opcodes:
            return opcodes[token], int(tokens.pop(0))
        if token == '.halt':
            return 'CH', None
        need(token in env, 'Unknown Tree name')
        return env[token]

    for line in path.read_text().splitlines():
        match = re.fullmatch(r'def (\w+) : Tree := (.*)', line)
        if match:
            tokens = re.findall(r'\(|\)|\.\w+|\w+', match[2])
            env[match[1]] = expression(tokens)
            need(not tokens, 'Unconsumed Tree expression')
    result = []

    def flatten(node, prefix=''):
        if isinstance(node[0], str):
            result.append([prefix, *node])
        else:
            flatten(node[0], prefix + '0')
            flatten(node[1], prefix + '1')

    flatten(env['trie'])
    return result


def source_info(sites):
    leaves = {p: i for i, (p, op, a) in enumerate(sites)}
    need(len(leaves) == len(sites), 'Repeated source path')
    intervals = {}
    subtrees = set()

    def visit(prefix):
        if prefix in leaves:
            i = leaves[prefix]
            node = tuple(sites[i][1:])
            interval = (i, i + 1)
        else:
            need(any(p.startswith(prefix) for p in leaves), 'Incomplete source tree')
            left, (a, b) = visit(prefix + '0')
            right, (c, d) = visit(prefix + '1')
            need(b == c, 'Noncanonical source order')
            node = left, right
            interval = a, d
        subtrees.add(node)
        intervals[prefix] = interval
        return node, interval

    visit('')

    def unwind(path, bit, count):
        while path:
            last, path = path[-1], path[:-1]
            if last == bit:
                count -= 1
                if count == 0:
                    return (intervals[path][1] % len(sites)) if bit == '0' else intervals[path][0]
        return 0

    graph = []
    for i, (p, op, a) in enumerate(sites):
        after = (i + 1) % len(sites)
        if op == 'CI':
            effect, targets = ('increment', a), [after]
        elif op == 'CD':
            effect, targets = ('decrement', a), [unwind(p, '0', 1), after]
        elif op == 'CB':
            effect, targets = ('identity',), [unwind(p, '0', a)]
        elif op == 'CC':
            effect, targets = ('identity',), [unwind(p, '1', a)]
        else:
            need(op == 'CH', 'Unknown source instruction')
            effect, targets = ('halt',), []
        graph.append([effect, targets])
    return {
        'occurrences': len(sites), 'opcodes': dict(Counter(op for p, op, a in sites)),
        'nonhalting_edges': sum(len(x[1]) for x in graph),
        'branch_contracts': sum(2 if op == 'CD' else 1 for p, op, a in sites),
        'dag_nodes_including_leaves': len(subtrees),
        'internal_nodes': sum(not isinstance(n[0], str) for n in subtrees),
        'maximum_path_length': max(len(p) for p, op, a in sites),
        'maximum_zero_run': max(len(z) for p, op, a in sites for z in p.split('1')),
    }, graph


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    manifest = json.loads((ROOT / 'input_manifest.json').read_text())
    for name, expected in manifest['data_files'].items():
        need(sha((ROOT / name).read_bytes()) == expected, 'Input hash mismatch: ' + name)
    tables = []
    classes = {}
    for item in manifest['tables']:
        rows, states, halt = read_table(ROOT / item['file'])
        need(len(states) == item['expected_states'], 'Working state count')
        normal, mapping = canonical(rows, states, halt, item['start'])
        digest = sha(json.dumps(normal, separators=(',', ':')).encode())
        classes.setdefault(digest, []).append(item['file'])
        tables.append({**item, 'states': len(states), 'rows': len(rows), 'halt': halt,
                       'canonical_sha256': digest, 'canonical_map': mapping})
    u208_classes = {}
    for item in tables:
        if item['states'] == 208:
            u208_classes.setdefault(item['canonical_sha256'], []).append(item['file'])
    need(sorted(map(len, u208_classes.values())) == [4, 5], 'Unexpected U208 classes')
    sources = {}
    graphs = {}
    words = {}
    for name in ('u208_A', 'u208_B', 'pa196', 'pa209'):
        sites = json.loads((ROOT / 'inputs' / (name + '.sites.json')).read_text())
        sources[name], graphs[name] = source_info(sites)
        words[name] = [row[1:] for row in sites]
        if name.startswith('pa'):
            parsed = parse_lean_tree(ROOT / 'inputs' / (name + '_Program.lean'))
            need(parsed == sites, 'Flattened Lean source mismatch: ' + name)
    need(words['u208_A'] == words['u208_B'], 'U208 instruction words differ')
    need(graphs['u208_A'] == graphs['u208_B'], 'U208 source control graphs differ')
    native = {}
    for name in ('pa196', 'pa209'):
        rows, states, halt = read_table(ROOT / 'inputs' / (name + '.tm'))
        text = (ROOT / 'inputs' / (name + '_Conjugacy.lean')).read_text()
        match = re.search(r'def labels : List Nat := (\[[^\n]*\])', text)
        need(match is not None, 'Missing upstream label map')
        labels = ast.literal_eval(match[1])
        renamed = {(labels[q], b): (w, d, labels[t]) for (q, b), (w, d, t) in rows.items()}
        native[name], _, _ = read_table(ROOT / 'inputs' / (name + '.native.tm'))
        need(renamed == native[name], 'Native relabeling mismatch')
    common = sorted(native['pa196'].keys() & native['pa209'].keys())
    changed = [{'row': k, 'pa209': native['pa209'][k], 'pa196': native['pa196'][k]}
               for k in common if native['pa209'][k] != native['pa196'][k]]
    need(len(common) == 268 and len(changed) == 3, '209-to-196 common-row comparison')
    result = {'status': 'EXACT_COMPARISON_PASS', 'pins': manifest['pins'],
              'tables': tables, 'classes': classes, 'sources': sources,
              'u208_source_words_equal': True, 'u208_source_graphs_equal': True,
              'james_common_native_rows': len(common), 'james_identical_common_rows': 265,
              'james_changed_common_rows': changed,
              'scope': 'Finite table and source identities. No nonhalting proof or global lower bound.'}
    if args.output:
        args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({k: v for k, v in result.items() if k not in ('tables', 'classes')}, indent=2))


if __name__ == '__main__':
    main()
