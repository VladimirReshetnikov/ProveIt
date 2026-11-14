#!/usr/bin/env python3
"""Independent portable comparison of the supplied U209 and U208 tables.

Uses only the Python standard library and local data snapshots. Explicit
exceptions, including all semantic checks, remain active under python -O.
This establishes literal graph/source relationships, not nonhalting or PA's
consistency. Native labels are names; state census is by defined source rows.
"""
from collections import deque
import argparse
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SNAPSHOTS = ROOT / 'baseline/snapshots'


def require(condition, message):
    if not condition:
        raise ValueError(message)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def compact(value):
    return json.dumps(value, separators=(',', ':'), sort_keys=True).encode('ascii')


def local_path(relative):
    relative = Path(relative)
    require(not relative.is_absolute() and '..' not in relative.parts,
            'Unsafe local snapshot path')
    path = SNAPSHOTS / relative
    require(path.is_file(), 'Missing snapshot file: ' + str(relative))
    return path


def read_table(path, count, halt, dense=False):
    table = {}
    for line_number, line in enumerate(path.read_text().splitlines(), 1):
        if not line.strip() or line.startswith('#'):
            continue
        fields = line.split()
        require(len(fields) == 5, f'{path.name}:{line_number}: malformed row')
        q, bit, write, direction, target = fields
        q, bit, write, target = map(int, (q, bit, write, target))
        require(bit in (0, 1) and write in (0, 1) and direction in ('L', 'R'),
                'Nonbinary alphabet or invalid move')
        require((q, bit) not in table, 'Duplicate transition')
        table[q, bit] = write, direction, target
    states = {q for q, bit in table}
    require(len(states) == count and len(table) == 2 * count, 'Wrong state/row census')
    require(set(table) == {(q, bit) for q in states for bit in (0, 1)},
            'Incomplete transition function')
    require(0 in states and halt not in states, 'Start/halt convention')
    require({target for _, _, target in table.values()} - states == {halt},
            'Missing halt or unknown target')
    if dense:
        require(states == set(range(count)) and halt == count, 'Dense label convention')
    return table


def canonical(table, halt):
    mapping = {0: 0}
    queue = deque([0])
    rows = []
    while queue:
        q = queue.popleft()
        for bit in (0, 1):
            write, direction, target = table[q, bit]
            if target == halt:
                projected = 'HALT'
            else:
                if target not in mapping:
                    mapping[target] = len(mapping)
                    queue.append(target)
                projected = mapping[target]
            rows.append([mapping[q], bit, write, direction, projected])
    require(set(mapping) == {q for q, bit in table}, 'Graph-unreachable working state')
    return rows, mapping


def exact_map(left, right, left_halt, right_halt):
    lrows, lm = canonical(left, left_halt)
    rrows, rm = canonical(right, right_halt)
    require(lrows == rrows, 'Claimed rooted labeled graphs differ')
    inverse = {number: q for q, number in rm.items()}
    mapping = {q: inverse[number] for q, number in lm.items()}
    mapping[left_halt] = right_halt
    require(len(set(mapping.values())) == len(mapping), 'Nonbijective graph map')
    translated = {(mapping[q], bit): (write, direction, mapping[target])
                  for (q, bit), (write, direction, target) in left.items()}
    require(translated == right, 'Literal transition-map equality failed')
    return mapping


def read_source(path):
    rows = json.loads(path.read_text())
    require(isinstance(rows, list) and rows, 'Invalid source list')
    leaves = set()
    internal = set()
    for row in rows:
        require(isinstance(row, list) and len(row) == 3, 'Invalid source row')
        address, op, arg = row
        require(isinstance(address, str) and address and set(address) <= {'0', '1'},
                'Invalid source address')
        require(address not in leaves, 'Duplicate source address')
        leaves.add(address)
        internal.update(address[:k] for k in range(len(address)))
        require(op in ('CI', 'CD', 'CB', 'CC', 'CH'), 'Invalid source opcode')
        if op == 'CH':
            require(arg is None, 'Halting operand must be null')
        else:
            require(type(arg) is int and arg >= 0, 'Invalid source operand')
            require(op not in ('CI', 'CD') or arg < 9, 'Invalid primary register')
            require(op not in ('CB', 'CC') or arg >= 1, 'Invalid cut depth')
    require(not leaves & internal, 'Source prefix collision')
    require([row[0] for row in rows] == sorted(leaves), 'Noncanonical source order')
    require(len(internal) + 1 == len(leaves), 'Source is not a full binary tree')
    nodes = leaves | internal
    require(all(p + '0' in nodes and p + '1' in nodes
                for p in internal), 'Source tree has a missing child')
    first, after = {}, {}
    for index, (address, _, _) in enumerate(rows):
        for length in range(len(address) + 1):
            prefix = address[:length]
            first.setdefault(prefix, index)
            after[prefix] = index + 1
    def cut(address, bit, depth):
        for offset in range(len(address) - 1, -1, -1):
            if address[offset] == bit:
                depth -= 1
                if depth == 0:
                    prefix = address[:offset]
                    return after[prefix] % len(rows) if bit == '0' else first[prefix]
        return 0
    graph = []
    for index, (address, op, arg) in enumerate(rows):
        successor = (index + 1) % len(rows)
        if op == 'CI':
            targets = [successor]
        elif op == 'CD':
            targets = [cut(address, '0', 1), successor]
        elif op == 'CB':
            targets = [cut(address, '0', arg)]
        elif op == 'CC':
            targets = [cut(address, '1', arg)]
        else:
            targets = []
        graph.append([op, arg, targets])
    word = [row[1:] for row in rows]
    return rows, word, graph, {
        'primitives': len(rows), 'internal_prefixes': len(internal),
        'control_edges': sum(len(row[2]) for row in graph),
        'maximum_depth': max(len(row[0]) for row in rows),
        'maximum_zero_run': max(len(run) for address, _, _ in rows
                                for run in address.split('1')),
        'primitive_word_sha256': sha(compact(word)),
        'ordinal_control_graph_sha256': sha(compact(graph))}


def compare():
    manifest = json.loads((SNAPSHOTS / 'manifest.json').read_text())
    require(manifest['format'] == 1, 'Unknown snapshot manifest format')
    for relative, item in manifest['files'].items():
        require(item['path'] == relative, 'Manifest path disagreement')
        require(sha(local_path(relative).read_bytes()) == item['sha256'],
                'Snapshot hash mismatch: ' + relative)
    expected = {int(k): v for k, v in manifest['expected_presentations'].items()}
    census = {count: 0 for count in expected}
    representatives = {}
    fingerprints = {count: {} for count in expected}
    reports = []
    identities = set()
    baseline_word = baseline_graph = None
    source_representatives = {}
    for item in manifest['snapshots']:
        name, count, group = item['id'], item['working_states'], item['expected_class']
        require(name not in identities, 'Duplicate snapshot identity')
        identities.add(name)
        require(count in expected and group in ('A', 'B'), 'Unexpected snapshot family')
        census[count] += 1
        for key in ('native', 'dense', 'sites'):
            record = item['files'][key]
            require(manifest['files'].get(record['path']) == record,
                    'Per-snapshot/file manifest disagreement')
        native = read_table(local_path(item['files']['native']['path']), count, 254)
        dense = read_table(local_path(item['files']['dense']['path']), count, count, True)
        dense_map = exact_map(native, dense, 254, count)
        canonical_rows, _ = canonical(native, 254)
        fingerprint = sha(compact(canonical_rows))
        if fingerprint in fingerprints[count]:
            require(fingerprints[count][fingerprint] == group, 'Expected classes overlap')
        fingerprints[count][fingerprint] = group
        key = count, group
        if key not in representatives:
            representatives[key] = name, native
        rep_name, rep_table = representatives[key]
        state_map = exact_map(rep_table, native, 254, 254)
        source, word, graph, metrics = read_source(local_path(item['files']['sites']['path']))
        require(metrics['primitives'] == manifest['expected_source_primitives'], 'Primitive census')
        require(metrics['control_edges'] == manifest['expected_control_edges'], 'Control-edge census')
        if baseline_word is None:
            baseline_word, baseline_graph = word, graph
        require(word == baseline_word and graph == baseline_graph,
                'Source primitive word or ordinal control graph differs')
        if group not in source_representatives:
            source_representatives[group] = source
        require(source == source_representatives[group], 'Within-class source addresses differ')
        reports.append({'id': name, 'working_states': count, 'rows': len(native),
                        'class': group, 'rooted_graph_sha256': fingerprint,
                        'native_sha256': item['files']['native']['sha256'],
                        'dense_sha256': item['files']['dense']['sha256'],
                        'graph_reachable_working_states': count,
                        'native_to_dense_rows_checked': len(native),
                        'class_representative': rep_name,
                        'nonidentity_map_from_representative': [[q, z] for q, z in sorted(state_map.items()) if q != z],
                        'source': metrics})
    require(census == expected, 'Wrong number of snapshot presentations')
    require(all(len(fingerprints[count]) == manifest['expected_classes_per_state_count']
                for count in expected), 'Wrong number of rooted graph classes')
    require(set(source_representatives) == {'A', 'B'}, 'Missing source class')
    changed = sum(a[0] != b[0] for a, b in zip(source_representatives['A'],
                                             source_representatives['B']))
    require(changed == manifest['expected_different_class_addresses'],
            'Unexpected number of differing source addresses')
    return {'status': 'SNAPSHOT_COMPARISON_PASS',
            'scope': 'Literal rooted transition graphs, dense renamings and source syntax/ordinal CFG; no claim of nonhalting.',
            'manifest_files_checked': len(manifest['files']),
            'presentations': census, 'classes_per_state_count': {n: len(v) for n, v in fingerprints.items()},
            'same_source_primitive_word': True, 'same_ordinal_control_graph': True,
            'different_class_source_addresses': changed, 'machines': reports}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = compare()
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({k: v for k, v in result.items() if k != 'machines'}, indent=2))


if __name__ == '__main__':
    main()
