#!/usr/bin/env python3
"""Replay the pinned K229 -> recompiled229 -> split228 -> K227 construction.

Python 3.10+, standard library only. The source stages and the 49-atom binary
parenthesization are literal data; this program does not run a search or an
optimizer. It checks two independent source graph resolvers, all no-stray
successor conditions, complete blank startup, and the six whole-tape blocks
for the boundary fold. The unbounded source-to-binary runtime proof is a
separate required certificate.
"""
from __future__ import annotations
from collections import Counter
from functools import cache
from pathlib import Path
import argparse
import hashlib
import json
import sys

HERE = Path(__file__).resolve().parent
START, DISPATCH, HALT = 95, 96, 254


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


def tree(rows):
    root = {}
    for path, op, arg in rows:
        require(path and set(path) <= {'0', '1'}, 'Invalid source path')
        require(op in ('CI', 'CD', 'CB', 'CC', 'CH'), 'Invalid opcode')
        require((op == 'CH' and arg is None) or
                (op != 'CH' and type(arg) is int and arg >= 0), 'Invalid operand')
        require(op not in ('CI', 'CD') or arg < 9, 'Invalid register')
        require(op not in ('CB', 'CC') or arg >= 1, 'Invalid control depth')
        at = root
        for bit in path:
            require('instruction' not in at, 'Overlapping source paths')
            at = at.setdefault(bit, {})
        require(not at, 'Duplicate or overlapping source path')
        at['instruction'] = (op, arg)
    def visit(node):
        if 'instruction' in node:
            require(set(node) == {'instruction'}, 'Leaf has children')
            return node['instruction']
        require(set(node) == {'0', '1'}, 'Source tree is not full')
        return visit(node['0']), visit(node['1'])
    result = visit(root)
    require(sites(result) == rows, 'Source rows are not in canonical ordinal order')
    return result


def sites(node, prefix=''):
    if leaf(node):
        return [[prefix, *node]]
    return sites(node[0], prefix + '0') + sites(node[1], prefix + '1')


@cache
def boundary(node):
    if leaf(node):
        op, arg = node
        if op == 'CD': return 1, 0, False
        if op == 'CB': return arg, 0, False
        if op == 'CC': return 0, arg, False
        return 0, 0, op == 'CH'
    a, b = boundary(node[0]), boundary(node[1])
    return (max(max(a[0] - 1, 0), b[0]),
            max(a[1], max(b[1] - 1, 0)), a[2] or b[2])


def metrics(root):
    seen = set()
    def visit(node):
        if node in seen: return
        seen.add(node)
        if not leaf(node):
            visit(node[0]); visit(node[1])
    visit(root)
    rows = sites(root)
    return {'dag_nodes': len(seen), 'leaf_occurrences': len(rows),
            'maximum_depth': max(len(p) for p, _, _ in rows),
            'maximum_zero_run': max(len(z) for p, _, _ in rows for z in p.split('1'))}


def graph_arithmetic(rows):
    """Binary successor/cut resolver, including the no-stray-suffix premise."""
    leaves = {p: i for i, (p, _, _) in enumerate(rows)}
    depth = max(map(len, leaves))
    checks = 0
    def locate(prefix):
        nonlocal checks
        word = prefix + '0' * depth
        for length in range(1, depth + 1):
            if word[:length] in leaves:
                require('1' not in prefix[length:], 'Stray one beyond successor leaf')
                checks += 1
                return leaves[word[:length]]
        raise ValueError('Successor has no leaf')
    def increment(path):
        if not path: return ''
        return format((int(path, 2) + 1) % (1 << len(path)), '0' + str(len(path)) + 'b')
    def cut(path, edge, level):
        positions = [i for i, bit in enumerate(path) if bit == edge]
        return path[:positions[-level]] if len(positions) >= level else ''
    graph = []
    for path, op, arg in rows:
        if op == 'CI':
            effect, targets = ['increment', arg], [locate(increment(path))]
        elif op == 'CD':
            effect = ['decrement', arg]
            targets = [locate(increment(cut(path, '0', 1))), locate(increment(path))]
        elif op == 'CB':
            effect, targets = ['identity'], [locate(increment(cut(path, '0', arg)))]
        elif op == 'CC':
            effect, targets = ['identity'], [locate(cut(path, '1', arg))]
        else:
            effect, targets = ['halt'], []
        graph.append([effect, targets])
    require(locate('') == 0, 'Initial ordinal leaf is not zero')
    return graph, checks


def graph_intervals(rows):
    """Independent resolver: subtree intervals and outward ancestor walking."""
    indices = {path: i for i, (path, _, _) in enumerate(rows)}
    intervals = {}
    def visit(path):
        if path in indices:
            answer = indices[path], indices[path] + 1
        else:
            a, b = visit(path + '0'), visit(path + '1')
            require(a[1] == b[0], 'Noncontiguous source subtree')
            answer = a[0], b[1]
        intervals[path] = answer
        return answer
    require(visit('') == (0, len(rows)), 'Source interval census')
    def unwind(path, edge, count):
        while path:
            last, path = path[-1], path[:-1]
            if last == edge:
                count -= 1
                if count == 0:
                    return intervals[path][1] % len(rows) if edge == '0' else intervals[path][0]
        return 0
    graph = []
    for i, (path, op, arg) in enumerate(rows):
        after = (i + 1) % len(rows)
        if op == 'CI':
            effect, targets = ['increment', arg], [after]
        elif op == 'CD':
            effect, targets = ['decrement', arg], [unwind(path, '0', 1), after]
        elif op == 'CB':
            effect, targets = ['identity'], [unwind(path, '0', arg)]
        elif op == 'CC':
            effect, targets = ['identity'], [unwind(path, '1', arg)]
        else:
            effect, targets = ['halt'], []
        graph.append([effect, targets])
    return graph


def subtree(root, path):
    for bit in path:
        require(not leaf(root), 'Stage path extends past a leaf')
        root = root[int(bit)]
    return root


def replace(root, path, node):
    if not path: return node
    bit = int(path[0]); children = list(root)
    children[bit] = replace(children[bit], path[1:], node)
    return tuple(children)


def replay_source(root, stages):
    baseline = sites(root)
    reference, _ = graph_arithmetic(baseline)
    require(graph_intervals(baseline) == reference, 'Baseline source resolvers disagree')
    receipts = []
    for number, stage in enumerate(stages, 1):
        paths = stage['paths']
        require(paths and len(set(paths)) == len(paths), 'Missing or duplicated stage path')
        require(not any(a != b and b.startswith(a) for a in paths for b in paths), 'Stage paths overlap')
        before = subtree(root, paths[0])
        require(all(subtree(root, p) == before for p in paths), 'Stage occurrences differ')
        require(sha(compact(sites(before))) == stage['old_subtree_sha256'], 'Stage source pin failed')
        if stage['kind'] == 'rotation':
            if stage['direction'] == 'left':
                a, (b, c) = before; after = ((a, b), c)
            else:
                (a, b), c = before; after = (a, (b, c))
            boundaries = [list(boundary(n)) for n in (a, b, c)]
            require(boundaries == stage['chunk_boundaries'], 'Chunk boundary changed')
            require([len(sites(n)) for n in (a, b, c)] == stage['chunk_leaves'], 'Chunk census changed')
            require(boundaries[:2] == [[0, 0, False]] * 2, 'First two chunks are not closed')
            require(boundaries[2] == [0, 0, False] or
                    (stage['direction'] == 'right' and c == ('CB', 1)), 'Unproved boundary rotation')
        elif stage['kind'] == 'reassociation':
            atoms = []
            def extract(node, pattern):
                if type(pattern) is int:
                    require(pattern == len(atoms), 'Atoms are not in ordinal order')
                    atoms.append(node); return
                require(isinstance(pattern, list) and len(pattern) == 2 and not leaf(node), 'Bad old atom pattern')
                extract(node[0], pattern[0]); extract(node[1], pattern[1])
            extract(before, stage['old_pattern'])
            require(len(atoms) == 49 == len(stage['atoms']), 'Wrong atom count')
            for i, (node, record) in enumerate(zip(atoms, stage['atoms'])):
                require(record['index'] == i and record['source_sha256'] == sha(compact(sites(node))), 'Atom pin failed')
                require(boundary(node) == (0, 0, False), 'A reassociated atom is not closed')
                require(record['leaves'] == len(sites(node)), 'Atom size changed')
            order = []
            def assemble(pattern):
                if type(pattern) is int:
                    require(pattern == len(order), 'New pattern permutes or duplicates an atom')
                    order.append(pattern); return atoms[pattern]
                require(isinstance(pattern, list) and len(pattern) == 2, 'Bad new atom pattern')
                return assemble(pattern[0]), assemble(pattern[1])
            after = assemble(stage['new_pattern'])
            require(order == list(range(49)), 'New pattern drops atoms')
        else:
            raise ValueError('Unknown source stage')
        require(sha(compact(sites(after))) == stage['new_subtree_sha256'], 'Replacement source pin failed')
        for path in paths:
            root = replace(root, path, after)
        current = sites(root)
        require([r[1:] for r in current] == [r[1:] for r in baseline], 'Instruction order changed')
        graph, checks = graph_arithmetic(current)
        require(graph == reference == graph_intervals(current), 'Guarded source graph changed')
        require(metrics(root) == stage['metrics'], 'Stage source metrics changed')
        receipts.append({'number': number, 'name': stage['name'], 'occurrences': len(paths),
                         'source_sha256': sha(compact(current)), 'source_graph_equal': True,
                         'independent_interval_graph_equal': True, 'no_stray_checks': checks,
                         'metrics': metrics(root)})
    return root, receipts, sha(compact(reference))


def read_table(raw):
    table = {}; starts = []
    for line in raw.decode('ascii').splitlines():
        if line.startswith('#! start '):
            starts.append(int(line[9:])); continue
        if not line or line.startswith('#'): continue
        q, b, w, direction, target = line.split()
        q, b, w, target = map(int, (q, b, w, target))
        require((q, b) not in table and b in (0, 1) and w in (0, 1) and direction in ('L', 'R'), 'Bad table row')
        table[q, b] = w, 1 if direction == 'R' else -1, target
    states = {q for q, _ in table}
    require(starts == [START] and START in states and HALT not in states, 'Wrong start or halt')
    require(set(table) == {(q, b) for q in states for b in (0, 1)}, 'Partial table')
    require({z for _, _, z in table.values()} - states == {HALT}, 'Undefined target')
    return table


def encode(table):
    return (f'#! start {START}\n' + ''.join(
        f'{q} {b} {w} {"R" if d == 1 else "L"} {z}\n'
        for (q, b), (w, d, z) in sorted(table.items()))).encode('ascii')


def ports(table, target):
    return sorted((q, b, w, d) for (q, b), (w, d, z) in table.items() if z == target)


def split_boundary(old):
    require(all(w == 0 and d == 1 for q, b, w, d in ports(old, 179)), 'State179 lacks its preceding zero')
    require(ports(old, 179), 'Missing ordinary state179 callers')
    require(all(d == 1 for q, b, w, d in ports(old, 218)), 'A state218 caller is not a right move')
    require(ports(old, 529) == [(218, 0, 0, -1)], 'Helper529 has another incoming port')
    new = {(q, b): (w, d, (529 if w == 0 else 179) if z == 218 else z)
           for (q, b), (w, d, z) in old.items() if q != 218}
    new[179, 1] = 1, -1, 215
    new[529, 0] = 0, 1, 23
    new[529, 1] = 1, 1, 70
    require(len(new) == len(old) - 2 == 456, 'Boundary fold state census')
    def block(table, q, tag, read, steps):
        tape = {-1: tag, 0: read}; head = 0; trace = []
        for tick in range(steps):
            require(head in tape, 'Block reads an unspecified cell')
            bit = tape[head]; w, d, z = table[q, bit]
            trace.append([q, head, bit, w, d, z])
            tape[head] = w; head += d; q = z
        return (q, head, tape), trace
    obligations = [(179, 0, 0, 179, 1, 1, 105), (179, 0, 1, 179, 1, 5, 105),
                   (218, 0, 0, 529, 3, 1, 23), (218, 0, 1, 529, 1, 1, 70),
                   (218, 1, 0, 179, 3, 1, 105), (218, 1, 1, 179, 1, 3, 70)]
    checked = []
    for q, tag, read, mapped, old_steps, new_steps, endpoint in obligations:
        a, at = block(old, q, tag, read, old_steps)
        b, bt = block(new, mapped, tag, read, new_steps)
        require(a == b == (endpoint, 1, {-1: tag, 0: read}), 'Whole-tape block identity failed')
        checked.append({'old_state': q, 'left_tag': tag, 'read': read, 'new_state': mapped,
                        'old_steps': old_steps, 'new_steps': new_steps, 'endpoint': endpoint,
                        'old_trace': at, 'new_trace': bt})
    for (q, b), (w, d, z) in old.items():
        if q in (179, 218, 529): continue
        require(new[q, b] == (w, d, (529 if w == 0 else 179) if z == 218 else z), 'Ordinary transition changed')
    return new, {'status': 'PASS_SIX_WHOLE_TAPE_BLOCKS', 'blocks': checked,
                 'incoming_ports': {str(q): ports(old, q) for q in (179, 218, 529)},
                 'arbitrary_outside_cells': True, 'explicit_cells': [-1, 0],
                 'scope': 'Positive-block simulation from start95 on every binary tape; helper529 is internal to old218/0.'}


def delayed_fold(old):
    require(ports(old, 169) == [(147, 0, 0, 1)], 'Delayed fold incoming port changed')
    new = {(q, b): (w, d, 80 if z == 169 else z) for (q, b), (w, d, z) in old.items() if q != 169}
    new[80, 0] = 0, -1, 106
    new[91, 1] = 1, -1, 167
    require(len(new) == 454, 'Final state census')
    return new


def boot(table, steps):
    q, head, ones = START, 0, set()
    visited = Counter()
    for tick in range(steps):
        require(q != HALT, 'Startup halted')
        bit = int(head in ones); visited[q, bit] += 1
        w, direction, q = table[q, bit]
        if w: ones.add(head)
        else: ones.discard(head)
        head += direction
    require((q, head, len(ones)) == (DISPATCH, -5, 351), 'Wrong startup endpoint')
    return {'steps': steps, 'state': q, 'head': head, 'one_cells': sorted(ones),
            'all_other_cells': 0,
            'visited_rows': [{'row': list(row), 'visits': count} for row, count in sorted(visited.items())]}


def construct(table_path, source_path, spec_path, output):
    require(__debug__ and not sys.flags.optimize, 'Run without -O/-OO')
    spec = json.loads(spec_path.read_text())
    table_bytes, source_bytes = table_path.read_bytes(), source_path.read_bytes()
    require(sha(table_bytes) == spec['input_table_sha256'], 'Wrong pinned K229 table')
    require(sha(source_bytes) == spec['input_source_sha256'], 'Wrong pinned K229 source')
    table = read_table(table_bytes); require(len(table) == 458, 'K229 state census')
    root, stages, graph_hash = replay_source(tree(json.loads(source_bytes)), spec['source_stages'])
    basis = dict(table)
    seen = set()
    for edit in spec['basis_table_literal_edits']:
        row = tuple(edit['row']); require(row not in seen, 'Duplicate literal edit'); seen.add(row)
        require(basis.get(row) == (None if edit['before'] is None else tuple(edit['before'])), 'Literal edit precondition')
        if edit['after'] is None: del basis[row]
        else: basis[row] = tuple(edit['after'])
    require(len(basis) == 458, 'Recompiled basis state census')
    split, split_receipt = split_boundary(basis)
    final = delayed_fold(split)
    artifacts = {'basis229.tm': encode(basis), 'candidate228.tm': encode(split),
                 'candidate227.tm': encode(final), 'sites.json': compact(sites(root))}
    for name, raw in artifacts.items():
        require(sha(raw) == spec['outputs'][name], 'Unexpected artifact hash: ' + name)
        if name.endswith('.tm'): read_table(raw)
    reference_boot = boot(table, 409691)
    boots = {}
    for name, current, steps in [('basis229', basis, 409691), ('candidate228', split, 409691), ('candidate227', final, 409835)]:
        result = boot(current, steps)
        require(result['one_cells'] == reference_boot['one_cells'], 'Complete startup tapes differ')
        boots[name] = result
    receipt = {'status': 'PASS_EXACT_K227_RECONSTRUCTION',
               'input_table_sha256': sha(table_bytes), 'input_source_sha256': sha(source_bytes),
               'construction_spec_sha256': sha(spec_path.read_bytes()),
               'outputs': spec['outputs'], 'source_stages': stages,
               'ordinal_instruction_order_equal': True, 'all_guarded_successors_equal': True,
               'independent_source_resolver_agrees': True, 'no_stray_successor_bits': True,
               'common_guarded_graph_sha256': graph_hash,
               'leaves': len(sites(root)), 'guarded_cases': sum(2 if op == 'CD' else 1 for _, op, _ in sites(root)),
               'changed_leaf_paths': sum(a[0] != b[0] for a, b in zip(json.loads(source_bytes), sites(root))),
               'metrics': metrics(root), 'literal_basis_edits': len(seen),
               'complete_startup_equal': True, 'startup_steps': {name: b['steps'] for name, b in boots.items()},
               'proof_scope': 'Exact reconstruction, arbitrary-register source equivalence, startup and boundary fold. Requires separate unbounded binary-runtime certificate.'}
    output.mkdir(parents=True, exist_ok=True)
    for name, raw in artifacts.items(): (output / name).write_bytes(raw)
    dump(output / 'construction_receipt.json', receipt)
    dump(output / 'boundary_split_receipt.json', split_receipt)
    dump(output / 'startup_receipt.json', {'reference': reference_boot, 'candidates': boots})
    return receipt


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--table', type=Path, required=True)
    parser.add_argument('--source', type=Path, required=True)
    parser.add_argument('--spec', type=Path, default=HERE / 'construction227.json')
    parser.add_argument('--output-dir', type=Path, required=True)
    args = parser.parse_args()
    result = construct(args.table, args.source, args.spec, args.output_dir)
    print(json.dumps({k: v for k, v in result.items() if k != 'source_stages'}, indent=2))
