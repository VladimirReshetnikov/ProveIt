#!/usr/bin/env python3
"""Deterministically compile the combined G/seed-request source to 222 states.

Python 3.10+, standard library only. This script checks the complete source
syntax, preserves every live decoder representation of the pinned G223 table,
reuses obsolete decoder labels in a specified order, and checks every source
prefix against the intended decoded subtree on the literal result. All 49
instruction-engine states are preserved byte for byte. The resulting table has
222 working states, not counting the single terminal state.

This is an executable ordinary mathematical certificate. Its scope is the
source/table binding. The exact logical emitter calibration, full unbounded
binary instruction runtime, and blank initialization are separate obligations.
No search, subprocess, proof-assistant claim, or bounded nonhalting argument is
used by this compiler.

The source-tree utilities and decoder-reuse strategy are adapted from the
MIT No Attribution K_s223 construction packet (build223.py/source_language.py),
with the inherited K230/ProveIt attribution and notices retained by the package.
"""
from __future__ import annotations

import argparse
from collections import defaultdict
from functools import cache
import hashlib
import json
from pathlib import Path
import sys

HALT = 254
PARENT_TABLE_SHA = '5bcee335bc5cf45b6ebc6d1f97a10e3cc8aae2af303b82c5cc9ce506a4d22ed7'
PARENT_SITES_SHA = 'fe3713adaf008a71ba4fbc6433de760ef124b8638efbc5c75e3afa2c1142c24f'
SITES_SHA = 'cc1fbb3a16dd446af9c7cdb678317d31060082e6794b9c7074ce02b46584a75e'
TABLE_SHA = '8fdc7a7ed02a4cc4311ae739c19dcf11a406f9e092e5d9d9a99f0d8362462079'


def require(condition, message):
    if not condition:
        raise ValueError(message)


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def compact(data):
    return (json.dumps(data, separators=(',', ':')) + '\n').encode('ascii')


def dump(path, data):
    path.write_text(json.dumps(data, indent=2) + '\n')


def leaf(node):
    return isinstance(node[0], str)


def sites(node, prefix=''):
    if leaf(node):
        return [[prefix, *node]]
    return sites(node[0], prefix + '0') + sites(node[1], prefix + '1')


def source_tree(rows):
    root = {}
    for path, operation, argument in rows:
        require(path and set(path) <= {'0', '1'}, 'Invalid source address')
        require(operation in ('CI', 'CD', 'CB', 'CC', 'CH'), 'Invalid source operation')
        require((operation == 'CH' and argument is None) or
                (operation != 'CH' and type(argument) is int and argument >= 0), 'Invalid operand')
        require(operation not in ('CI', 'CD') or argument < 9, 'Invalid register')
        require(operation not in ('CB', 'CC') or argument >= 1, 'Invalid control depth')
        cursor = root
        for bit in path:
            require('instruction' not in cursor, 'Overlapping source leaves')
            cursor = cursor.setdefault(bit, {})
        require(not cursor, 'Duplicate or overlapping source address')
        cursor['instruction'] = operation, argument

    def visit(cursor):
        if 'instruction' in cursor:
            require(set(cursor) == {'instruction'}, 'Source leaf has children')
            return cursor['instruction']
        require(set(cursor) == {'0', '1'}, 'Source tree is not full')
        return visit(cursor['0']), visit(cursor['1'])

    result = visit(root)
    require(sites(result) == rows, 'Noncanonical source ordinal order')
    return result


def metrics(tree):
    nodes = set()

    def visit(node):
        if node in nodes:
            return
        nodes.add(node)
        if not leaf(node):
            visit(node[0]); visit(node[1])

    visit(tree)
    rows = sites(tree)
    return {'dag_nodes': len(nodes), 'leaf_occurrences': len(rows),
            'maximum_depth': max(len(p) for p, _, _ in rows),
            'maximum_zero_run': max(len(z) for p, _, _ in rows for z in p.split('1'))}


def read_table(raw):
    rows, starts = {}, []
    for line in raw.decode('ascii').splitlines():
        if line.startswith('#! start '):
            starts.append(int(line[9:])); continue
        if not line or line.startswith('#'):
            continue
        q, bit, write, direction, target = line.split()
        q, bit, write, target = map(int, (q, bit, write, target))
        require((q, bit) not in rows, 'Duplicate transition')
        require(bit in (0, 1) and write in (0, 1) and direction in ('L', 'R'), 'Bad transition')
        rows[q, bit] = write, 1 if direction == 'R' else -1, target
    require(starts == [0], 'Expected unique K-labelled start state 0')
    validate_table(rows)
    return rows


def validate_table(table):
    states = {q for q, bit in table}
    require(0 in states and HALT not in states, 'Incorrect start or halt convention')
    require(set(table) == {(q, bit) for q in states for bit in (0, 1)}, 'Incomplete table')
    require({q for write, direction, q in table.values()} - states == {HALT}, 'Incorrect terminal target')
    return states


def table_bytes(rows, start=0):
    return (f'#! start {start}\n' + ''.join(
        f'{q} {bit} {write} {"R" if direction == 1 else "L"} {target}\n'
        for (q, bit), (write, direction, target) in sorted(rows.items()))).encode('ascii')


def decoder_map(table, tree):
    """Prove every compound-child entry using just the known finite prefix.

    All other tape cells are arbitrary: touching an unknown cell is rejected.
    Positive paths must preserve the whole represented prefix and reach the
    next address cell. The caller checks the reached subtree, independently
    of these paths; accepting any reached state would be insufficient.
    """
    groups, paths, records = defaultdict(set), defaultdict(list), []

    def visit(node, prefix, entry):
        if leaf(node):
            return
        groups[entry].add(node); paths[entry].append(prefix)
        for bit, child in enumerate(node):
            if leaf(child):
                continue
            initial = {i: int(value) for i, value in enumerate(prefix + str(bit))}
            initial[-1] = 1
            tape, head, state = dict(initial), len(prefix), entry
            trace = []
            for tick in range(100):
                if head == len(prefix) + 1:
                    break
                require(head in tape, 'Decoder read outside known prefix')
                before_state, before_head = state, head
                read = tape[head]
                write, direction, state = table[state, read]
                tape[head] = write; head += direction
                trace.append([before_state, before_head, read, write, direction, state])
            require(tape == initial and head == len(prefix) + 1,
                    'Decoder changed its prefix or failed to advance')
            require(trace, 'Decoder path has no positive progress')
            records.append({'prefix': prefix, 'read': bit, 'entry': entry,
                            'target': state, 'steps': len(trace)})
            visit(child, prefix + str(bit), state)

    visit(tree, '', 84)
    return groups, paths, records


def compile_table(old, oldtree, tree):
    oldgroups, oldpaths, _ = decoder_map(old, oldtree)
    interior = set()

    def collect(node):
        if node in interior or leaf(node):
            return
        interior.add(node); collect(node[0]); collect(node[1])

    collect(tree)
    oldmap = {node: state for state, alternatives in oldgroups.items() for node in alternatives}
    intended = {node: oldmap[node] for node in interior if node in oldmap}
    occupied = set(intended.values())

    # Reuse an obsolete singleton label at the same structural position first.
    def align(before, after):
        if leaf(before) or leaf(after):
            return
        state = oldmap[before]
        if after not in intended and state not in occupied and len(oldgroups[state]) == 1:
            intended[after] = state; occupied.add(state)
        align(before[0], after[0]); align(before[1], after[1])

    align(oldtree, tree)
    free = sorted(set(oldgroups) - occupied, key=lambda state: (
        any(direction != 1 or write != bit
            for bit, (write, direction, target) in enumerate((old[state, 0], old[state, 1]))), state))

    def assign(node):
        if leaf(node):
            return
        if node not in intended:
            require(bool(free), 'A new decoder state would be required')
            intended[node] = free.pop(0)
        assign(node[0]); assign(node[1])

    assign(tree)
    table = dict(old)

    def primitive_entry(node, bit):
        operation, argument = node
        if operation == 'CI' and argument == 1: return bit, 1, 61
        if operation == 'CB' and argument == 1 and bit == 1: return 0, -1, 40
        if operation == 'CH' and bit == 1: return 1, 1, HALT
        if operation == 'CD' and bit == 0:
            return 0, 1, {0: 14, 1: 41, 2: 56, 3: 17, 4: 144, 5: 45, 6: 21, 7: 62, 8: 39}[argument]
        if operation == 'CI':
            return bit, 1, {0: 14, 1: 61, 2: 56, 3: 161, 4: 71, 5: 63, 6: 13, 7: 82, 8: 39}[argument]
        if operation == 'CC' and bit == 1:
            return 0, -1, {1: 1, 2: 16, 3: 42}[argument]
        raise ValueError(('Unsupported new primitive entry', node, bit))

    for node, state in intended.items():
        if node in oldmap:
            continue
        for bit, child in enumerate(node):
            alternatives = oldgroups.get(state, set())
            if len(alternatives) == 1 and next(iter(alternatives))[bit] == child:
                continue  # Preserve inherited details when the child is unchanged.
            table[state, bit] = (primitive_entry(child, bit) if leaf(child)
                                 else (bit, 1, intended[child]))
    require(intended[tree] == 84, 'Dispatcher root label changed')

    reachable, pending = {0}, [0]
    for state in pending:
        for bit in (0, 1):
            target = table[state, bit][2]
            if target != HALT and target not in reachable:
                reachable.add(target); pending.append(target)
    table = {key: row for key, row in table.items() if key[0] in reachable}
    require(validate_table(table) == reachable, 'Graph reachability mismatch')
    require(len(table) == 444 and len(reachable) == 222, 'Expected 222-state table')
    require(validate_table(old) - reachable == {305}, 'Unexpected deleted K-labelled state')
    require(not reachable - validate_table(old), 'Unexpected added state')

    actual, paths, records = decoder_map(table, tree)
    expected = defaultdict(set)
    for node, state in intended.items():
        expected[state].add(node)
    require(set(actual) == set(expected), 'Decoder state inventories disagree')
    for state, alternatives in actual.items():
        require(alternatives == expected[state], 'Decoder reaches wrong subtree at ' + str(state))

    engine = validate_table(old) - set(oldgroups)
    require(len(engine) == 49, 'Parent engine census changed')
    require(all(table[state, bit] == old[state, bit] for state in engine for bit in (0, 1)),
            'An instruction-engine row changed')
    edits = [{'state': state, 'read': bit, 'old': old[state, bit], 'new': row}
             for (state, bit), row in sorted(table.items()) if old[state, bit] != row]
    require(len(edits) == 24, 'Unexpected retained-row edit count')
    require(len(actual) == 173 and sum(map(len, actual.values())) == 185,
            'Unexpected decoder sharing census')
    bindings = [{'state': state, 'subtree_sha256': sha(compact(node))}
                for node, state in intended.items()]
    bindings.sort(key=lambda row: (row['state'], row['subtree_sha256']))
    return table, {'status': 'EXACT_SOURCE_PREFIX_BINDING_PASS',
                   'states': 222, 'rows': 444, 'engine_states': sorted(engine),
                   'engine_rows_unchanged': 98, 'interior_source_nodes': 185,
                   'decoder_states': 173, 'contextual_alias_savings': 12,
                   'compound_decoder_edges_checked': len(records),
                   'source_prefix_occurrences': sum(map(len, paths.values())),
                   'bindings': bindings, 'paths': dict(paths), 'edges': records}, edits


def canonicalize(table):
    order, mapping = [0], {0: 0}
    for state in order:
        for bit in (0, 1):
            target = table[state, bit][2]
            if target != HALT and target not in mapping:
                mapping[target] = len(order); order.append(target)
    require(len(order) == 222, 'Canonical state count differs')
    mapping[HALT] = 222
    canonical = {(mapping[q], bit): (write, direction, mapping[target])
                 for (q, bit), (write, direction, target) in table.items()}
    return canonical, mapping


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--parent-table', type=Path, required=True)
    parser.add_argument('--parent-sites', type=Path, required=True)
    parser.add_argument('--sites', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    require(__debug__ and not sys.flags.optimize, 'Run without Python optimization')
    parent_table_raw = args.parent_table.read_bytes()
    parent_sites_raw = args.parent_sites.read_bytes()
    sites_raw = args.sites.read_bytes()
    require(sha(parent_table_raw) == PARENT_TABLE_SHA, 'Parent table pin differs')
    require(sha(parent_sites_raw) == PARENT_SITES_SHA, 'Parent source pin differs')
    require(sha(sites_raw) == SITES_SHA, 'Combined source pin differs')
    old = read_table(parent_table_raw)
    require(len(old) == 446, 'Expected G223 parent')
    oldtree = source_tree(json.loads(parent_sites_raw))
    tree = source_tree(json.loads(sites_raw))
    require(metrics(tree) == {'dag_nodes': 208, 'leaf_occurrences': 4744,
                             'maximum_depth': 36, 'maximum_zero_run': 6}, 'Source metrics differ')
    table, decoder, edits = compile_table(old, oldtree, tree)
    raw = table_bytes(table)
    require(sha(raw) == TABLE_SHA, 'Literal compiled table hash differs')
    canonical, mapping = canonicalize(table)
    output = args.output
    output.mkdir(parents=True, exist_ok=True)
    (output / 'candidate222.k.tm').write_bytes(raw)
    (output / 'candidate222.tm').write_bytes(table_bytes(canonical))
    (output / 'sites222.json').write_bytes(sites_raw)
    dump(output / 'decoder222.json', decoder)
    dump(output / 'binary_delta222.json', {'parent_states': 223, 'new_states': 222,
         'deleted_k_states': [305], 'added_states': [], 'retained_row_changes': edits})
    dump(output / 'canonical_map.json', {'k_to_canonical': mapping,
         'canonical_to_k': {value: key for key, value in mapping.items()}})
    receipt = {'status': 'DETERMINISTIC_222_CONSTRUCTION_PASS',
               'working_states': 222, 'rows': 444, 'start': 0, 'halt': 222,
               'parent_table_sha256': PARENT_TABLE_SHA, 'parent_sites_sha256': PARENT_SITES_SHA,
               'source_sha256': SITES_SHA, 'k_table_sha256': TABLE_SHA,
               'canonical_table_sha256': sha(table_bytes(canonical)),
               'source_metrics': metrics(tree), 'engine_states': 49,
               'interior_source_nodes': 185, 'decoder_states': 173, 'alias_savings': 12,
               'deleted_k_states': [305], 'added_states': [], 'retained_row_changes': 24,
               'scope': 'Exact source/table binding. Logical calibration, whole-tape instruction '
                        'runtime and blank startup are separately necessary certificates.'}
    dump(output / 'construction222.json', receipt)
    print(json.dumps(receipt, indent=2))


if __name__ == '__main__':
    main()
