#!/usr/bin/env python3
"""Exhaust the 6^7 selector permutations of seven fixed logical-schema rows.

Standard library only. Run from any directory; inputs are relative to this file.
The measured objective is source DAG size with the association fixed, not the
number of states of a successfully compiled or calibrated Turing machine.
"""
import argparse
import collections
import hashlib
import itertools
import json
import random
import time
from functools import lru_cache
from pathlib import Path

ROOT = Path(__file__).resolve().parent

def require(condition, message):
    if not condition:
        raise ValueError(message)

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def parse(rows):
    leaves = {p: (op, arg) for p, op, arg in rows}
    require(len(leaves) == len(rows), 'Duplicate primitive source path')
    prefixes = {p[:j] for p in leaves for j in range(len(p))}
    require(not (prefixes & leaves.keys()), 'Primitive path is a prefix of another')
    require(all(set(p) <= {'0', '1'} for p in leaves), 'Nonbinary path')
    def visit(path=''):
        if path in leaves:
            return leaves[path]
        require(path in prefixes, 'Source tree is not full and binary')
        return visit(path+'0'), visit(path+'1')
    tree = visit()
    require(sites(tree) == [tuple(row) for row in rows], 'Source order mismatch')
    return tree

def is_leaf(node):
    return isinstance(node[0], str)

def sites(node, path=''):
    if is_leaf(node):
        return [(path, *node)]
    return sites(node[0], path+'0') + sites(node[1], path+'1')

class Dag:
    def __init__(self):
        self.nodes = []
        self.ids = {}
        self.sizes = []
    def add(self, key):
        if key not in self.ids:
            self.ids[key] = len(self.nodes)
            self.nodes.append(key)
            self.sizes.append(1 if isinstance(key[0], str) else
                              self.sizes[key[0]] + self.sizes[key[1]])
        return self.ids[key]
    def intern(self, tree):
        return self.add(tree if is_leaf(tree) else
                        (self.intern(tree[0]), self.intern(tree[1])))
    @lru_cache(None)
    def node_set(self, index):
        key = self.nodes[index]
        return (frozenset({index}) if isinstance(key[0], str) else
                frozenset({index}) | self.node_set(key[0]) | self.node_set(key[1]))
    @lru_cache(None)
    def expand(self, index):
        key = self.nodes[index]
        return key if isinstance(key[0], str) else (self.expand(key[0]), self.expand(key[1]))

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, default=ROOT/'results')
    args = parser.parse_args()
    started = time.monotonic()
    manifest = json.loads((ROOT/'inputs/manifest.json').read_text())
    for name, expected in manifest['input_files'].items():
        require(digest(ROOT/'inputs'/name) == expected, 'Input hash mismatch: '+name)
    rows = json.loads((ROOT/'inputs/sites.json').read_text())
    old = parse(rows)
    dag = Dag()
    root = dag.intern(old)
    require(len(rows) == manifest['baseline_primitive_occurrences'], 'Unexpected source length')
    require(len(dag.node_set(root)) == manifest['baseline_dag_nodes'], 'Unexpected baseline DAG')
    macro_rows = json.loads((ROOT/'inputs/selectors.json').read_text())
    macros = {role: dag.intern(parse(macro_rows[role])) for role in 'abc'}
    require(len(set(macros.values())) == 3, 'Selectors are not distinct')
    require(all(dag.sizes[k] == 26 for k in macros.values()), 'Unexpected selector length')
    roles = {index: role for role, index in macros.items()}
    regions = json.loads((ROOT/'inputs/regions.json').read_text())['rows']
    permutations = list(itertools.permutations('abc'))
    require(len(regions) == 7, 'Expected seven independent logical rows')
    require(all(row['end'] == regions[i+1]['start'] for i, row in enumerate(regions[:-1])),
            'Logical row intervals are not contiguous')

    # Find exact selector subtrees directly from the input, without an imported
    # emitter or a hardcoded list of edited paths. Each match is a whole macro.
    edits = {}
    counts = [collections.Counter() for _ in regions]
    def locate(index, path='', lo=0):
        hi = lo + dag.sizes[index]
        owners = [i for i, row in enumerate(regions) if row['start'] <= lo < hi <= row['end']]
        if owners and index in roles:
            require(len(owners) == 1, 'Overlapping row intervals')
            i = owners[0]
            role = roles[index]
            counts[i][role] += 1
            variants = tuple(macros[perm['abc'.index(role)]] for perm in permutations)
            edits[path] = (i, variants)
            return
        key = dag.nodes[index]
        if not isinstance(key[0], str):
            locate(key[0], path+'0', lo)
            locate(key[1], path+'1', lo+dag.sizes[key[0]])
    locate(root)
    for i, row in enumerate(regions):
        require(sum(counts[i].values()) == row['selector_count'], 'Selector count mismatch: '+row['name'])
        require({r: counts[i][r] for r in 'abc'} == row['role_counts'], 'Selector-role mismatch: '+row['name'])

    # Template nodes are either fixed subtrees, selector choices, or binary
    # pairs. Equal templates are shared. Unchanged subtrees contribute their
    # complete DAGs; all possible selector interiors must already occur there.
    fixed, unchanged, selector_nodes = set(), set(), set()
    template_ids, templates, sizes, dependencies = {}, [], [], []
    edit_prefixes = {p[:j] for p in edits for j in range(len(p))}
    def template(index, path=''):
        if path in edits:
            owner, variants = edits[path]
            key = ('choice', owner, variants)
            for k in variants:
                require(dag.sizes[k] == dag.sizes[index], 'Selector substitution changes source length')
                selector_nodes.update(dag.node_set(k))
                fixed.update(dag.node_set(k))
        elif path not in edit_prefixes:
            key = ('fixed', index)
            unchanged.update(dag.node_set(index))
            fixed.update(dag.node_set(index))
        else:
            left, right = dag.nodes[index]
            key = ('pair', template(left, path+'0'), template(right, path+'1'))
        if key not in template_ids:
            template_ids[key] = len(templates)
            templates.append(key)
            sizes.append(dag.sizes[index])
            dependencies.append(frozenset() if key[0] == 'fixed' else
                                frozenset({key[1]}) if key[0] == 'choice' else
                                dependencies[key[1]] | dependencies[key[2]])
        return template_ids[key]
    root_template = template(root)
    require(selector_nodes <= unchanged,
            'A selector interior is not guaranteed by the unchanged source')
    require(fixed == unchanged, 'The allegedly constant DAG depends on a choice')

    by_size = collections.defaultdict(list)
    for index, key in enumerate(templates):
        if key[0] == 'pair':
            by_size[sizes[index]].append(index)
    fixed_sizes = {dag.sizes[k] for k in fixed}
    constant_singletons, ambiguous = 0, []
    for size, family in by_size.items():
        if len(family) == 1 and size not in fixed_sizes:
            # Primitive length is invariant under every selector permutation.
            # This template can coincide with no other node in any assignment.
            constant_singletons += 1
        else:
            ambiguous.extend(family)

    @lru_cache(None)
    def instantiate(index, combo):
        key = templates[index]
        if key[0] == 'fixed':
            return key[1]
        if key[0] == 'choice':
            return key[2][combo[key[1]]]
        return dag.add((instantiate(key[1], combo), instantiate(key[2], combo)))

    lookup = []
    for index in ambiguous:
        coordinates = tuple(sorted(dependencies[index]))
        values = []
        for sub in itertools.product(range(6), repeat=len(coordinates)):
            combo = [0]*7
            for coordinate, value in zip(coordinates, sub):
                combo[coordinate] = value
            values.append(instantiate(index, tuple(combo)))
        lookup.append((coordinates, values))
    all_ids = fixed | {k for _, values in lookup for k in values}
    positions = {k: i for i, k in enumerate(sorted(all_ids))}
    base_bits = sum(1 << positions[k] for k in fixed)
    look_bits = [(coordinates, [1 << positions[k] for k in values])
                 for coordinates, values in lookup]
    def cost(combo):
        bits = base_bits
        for coordinates, values in look_bits:
            index = 0
            for coordinate in coordinates:
                index = 6*index + combo[coordinate]
            bits |= values[index]
        return constant_singletons + bits.bit_count()

    # Independent tree construction checks the scoring identity on a fixed,
    # reproducible set. The identity for all assignments follows from the
    # exact partition by invariant subtree length and exhaustive lookup tables.
    def direct(index, path, combo):
        if path in edits:
            owner, variants = edits[path]
            return variants[combo[owner]]
        if path not in edit_prefixes:
            return index
        left, right = dag.nodes[index]
        return dag.add((direct(left, path+'0', combo), direct(right, path+'1', combo)))
    check_combos = [(0,)*7]
    for coordinate in range(7):
        for value in range(6):
            combo = [0]*7
            combo[coordinate] = value
            check_combos.append(tuple(combo))
    rng = random.Random(97410)
    check_combos += [tuple(rng.randrange(6) for _ in range(7)) for _ in range(300)]
    for combo in check_combos:
        require(cost(combo) == len(dag.node_set(direct(root, '', combo))),
                'Decomposed score disagrees with direct tree construction')

    best, minimizers, histogram, total = 1000000, [], collections.Counter(), 0
    for combo in itertools.product(range(6), repeat=7):
        value = cost(combo)
        histogram[value] += 1
        total += 1
        if value < best:
            best, minimizers = value, [combo]
        elif value == best:
            minimizers.append(combo)
    require(total == 6**7 == manifest['expected_combinations'], 'Exhaustion count mismatch')
    require(sum(histogram.values()) == total, 'Histogram count mismatch')
    require(histogram[best] == len(minimizers), 'Minimum multiplicity mismatch')
    args.output.mkdir(parents=True, exist_ok=True)
    source_outputs = {}
    for combo in minimizers:
        node = direct(root, '', combo)
        require(len(dag.node_set(node)) == best, 'Minimizer direct count mismatch')
        new_rows = sites(dag.expand(node))
        require(len(new_rows) == len(rows), 'Minimizer changed primitive count')
        name = 'perm'+''.join(map(str, combo))+'.sites.json'
        output = args.output/name
        output.write_text(json.dumps(new_rows, separators=(',', ':'))+'\n')
        source_outputs[name] = digest(output)
    report = {
        'status': 'EXHAUSTIVE_FIXED_ASSOCIATION_SELECTOR_PERMUTATION_CENSUS',
        'scope': manifest['scope'],
        'combinations': total,
        'minimum_dag_nodes': best,
        'minimizers': minimizers,
        'permutations': permutations,
        'regions': regions,
        'histogram': dict(sorted(histogram.items())),
        'decomposition': {
            'constant_nodes': len(fixed),
            'uncontested_dynamic_nodes': constant_singletons,
            'contested_dynamic_templates': len(ambiguous),
            'max_template_dependencies': max(len(dependencies[k]) for k in ambiguous),
            'finite_lookup_nodes': len(all_ids),
            'independent_full_tree_crosschecks': len(check_combos),
            'all_minimizers_directly_checked': True,
        },
        'input_hashes': manifest['input_files'],
        'minimizer_hashes': source_outputs,
        'seconds': time.monotonic()-started,
        'limitations': 'This is not a machine-state lower bound, and does not optimize row order, source association, engine code, tape representation, or logical presentation.',
    }
    (args.output/'census.json').write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps(report, indent=2))

if __name__ == '__main__':
    main()
