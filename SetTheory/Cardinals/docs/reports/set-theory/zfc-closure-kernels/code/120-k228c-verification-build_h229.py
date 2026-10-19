#!/usr/bin/env python3
"""Portable exact K230 -> shifted-transfer source -> H229 construction/checker.

Usage (Python3.9+, standard library, assertions enabled):
  python3 -B build_h229.py --table k230.tm --sites sites230.json --output OUT

All input pins, table rows, source contexts, local all-tape blocks and the blank
startup are checked. The all-source symbolic binary-runtime certificate is a
separate proof. This script does not produce a new Rocq theorem.
"""
import argparse
from collections import Counter, deque
from hashlib import sha256
import json
from pathlib import Path
import sys

TABLE_PIN = 'e7ccbcec074534cfd955f0ab94d16f13594e81974074309dc2ce663b9dfd7ba8'
SITES_PIN = '400fad2b1c5f99ed8490f6346ff63088ba94fc39ada376962cee2f68c092e487'
H229_PIN = '0563605ee4def660106e4cdb6dbac828d0fc01185bb039b32cb3309b8fd02089'
START, DISPATCH, HALT, KEEP, DROP = 0, 84, 230, 63, 79


def require(ok, message):
    if not ok:
        raise ValueError(message)


def digest(data):
    return sha256(data).hexdigest()


def encode(table, start=START):
    return (f'#! start {start}\n' + ''.join(
        f'{q} {b} {w} {"R" if d == 1 else "L"} {z}\n'
        for (q, b), (w, d, z) in sorted(table.items()))).encode('ascii')


def parse_table(data):
    rows, starts = {}, []
    for line in data.decode('ascii').splitlines():
        if line.startswith('#! start '):
            starts.append(int(line[9:]))
        elif line and not line.startswith('#'):
            fields = line.split()
            require(len(fields) == 5, 'Malformed transition')
            q, b, w, direction, z = fields
            q, b, w, z = map(int, (q, b, w, z))
            require(b in (0, 1) and w in (0, 1) and direction in ('L', 'R'), 'Bad transition')
            require((q, b) not in rows, 'Duplicate transition')
            rows[q, b] = w, 1 if direction == 'R' else -1, z
    require(starts == [START], 'Wrong input start')
    require(set(rows) == {(q, b) for q in range(230) for b in (0, 1)}, 'Wrong input census')
    require({z for w, d, z in rows.values()} - set(range(230)) == {HALT}, 'Wrong input halt')
    return rows


def normalize_source(data):
    operations = {'EInc': 'CI', 'EDecnz': 'CD', 'EBreak': 'CB',
                  'EContinue': 'CC', 'ETrap': 'CH', 'EHalt': 'CH'}
    rows = []
    for item in json.loads(data):
        require(isinstance(item, list) and len(item) == 2, 'Expected original K230 source format')
        path, operation = item
        fields = operation.split()
        require(fields and fields[0] in operations, 'Unknown K230 instruction')
        op = operations[fields[0]]
        arg = int(fields[1]) if len(fields) == 2 else None
        require((op == 'CH' and len(fields) == 1) or (op != 'CH' and len(fields) == 2), 'Bad operand')
        rows.append((path, op, arg))
    return rows


def is_leaf(tree):
    return isinstance(tree[0], str)


def tree_of_sites(rows):
    trie = {}
    for path, op, arg in rows:
        require(isinstance(path, str) and path and set(path) <= {'0', '1'}, 'Bad source path')
        require(op in ('CI', 'CD', 'CB', 'CC', 'CH'), 'Bad source opcode')
        require((op == 'CH' and arg is None) or (op != 'CH' and type(arg) is int and arg >= 0), 'Bad source operand')
        require(op not in ('CI', 'CD') or arg < 9, 'Bad register index')
        node = trie
        for bit in path:
            require('leaf' not in node, 'Prefix conflict')
            node = node.setdefault(bit, {})
        require(not node, 'Repeated or overlapping source leaf')
        node['leaf'] = op, arg
    def visit(node):
        if 'leaf' in node:
            require(set(node) == {'leaf'}, 'Leaf with children')
            return node['leaf']
        require(set(node) == {'0', '1'}, 'Source tree is not full')
        return visit(node['0']), visit(node['1'])
    return visit(trie)


def sites_of_tree(tree, prefix=''):
    if is_leaf(tree):
        return [(prefix, *tree)]
    return sites_of_tree(tree[0], prefix + '0') + sites_of_tree(tree[1], prefix + '1')


def boundary(tree):
    if is_leaf(tree):
        op, arg = tree
        if op == 'CD': return 1, 0, False
        if op == 'CB': return arg, 0, False
        if op == 'CC': return 0, arg, False
        return 0, 0, op == 'CH'
    a, c = map(boundary, tree)
    return max(max(a[0] - 1, 0), c[0]), max(a[1], max(c[1] - 1, 0)), a[2] or c[2]


def metrics(tree):
    nodes = set()
    def visit(node):
        if node in nodes: return
        nodes.add(node)
        if not is_leaf(node): visit(node[0]); visit(node[1])
    visit(tree)
    rows = sites_of_tree(tree)
    return {'dag_nodes': len(nodes), 'leaf_occurrences': len(rows),
            'maximum_depth': max(len(p) for p, o, a in rows),
            'maximum_zero_run': max(len(s) for p, o, a in rows for s in p.split('1'))}


def source_graph(tree):
    """Exact guarded ancestor graph, accepting HX as an atomic fallthrough macro."""
    rows = sites_of_tree(tree)
    leaves = {path: i for i, (path, op, arg) in enumerate(rows)}
    def locate(word):
        node, path = tree, ''
        while not is_leaf(node):
            bit = word[len(path)] if len(path) < len(word) else '0'
            node, path = node[int(bit)], path + bit
        require('1' not in word[len(path):], 'Noncanonical successor suffix')
        return leaves[path]
    def increment(path):
        return format((int(path, 2) + 1) % (1 << len(path)), '0' + str(len(path)) + 'b') if path else ''
    def strip(path, bit, count):
        if count == 0: return path
        positions = [i for i, char in enumerate(path) if char == bit]
        return path[:positions[-count]] if len(positions) >= count else ''
    graph = []
    for path, op, arg in rows:
        if op in ('CI', 'HX'): graph.append((op, arg, locate(increment(path))))
        elif op == 'CD': graph.append(('CD', arg, locate(increment(path)), locate(increment(strip(path, '0', 1)))))
        elif op == 'CB': graph.append(('J', locate(increment(strip(path, '0', arg)))))
        elif op == 'CC': graph.append(('J', locate(strip(path, '1', arg))))
        else: graph.append(('HALT',))
    return rows, graph, locate('')


def transform_source(original):
    old = tree_of_sites([('00', 'CD', 6), ('010', 'CI', 5), ('011', 'CC', 2), ('1', 'CI', 5)])
    new = tree_of_sites([('0', 'CI', 5), ('10', 'CD', 6), ('11', 'CC', 2)])
    require(boundary(old) == boundary(new) == (0, 0, False), 'Macro is not closed')
    paths = []
    def replace(node, path=''):
        if node == old:
            paths.append(path)
            return new
        return node if is_leaf(node) else (replace(node[0], path + '0'), replace(node[1], path + '1'))
    changed = replace(original)
    expected = ['111010010010111111000011', '11101001001011111110011', '1110100101100011', '111110011']
    require(paths == expected, 'Unexpected macro occurrence inventory')
    targets = set(paths)
    require(not any(a != c and c.startswith(a) for a in paths for c in paths), 'Macro occurrences overlap')
    def collapse(node, pattern, path=''):
        if path in targets:
            require(node == pattern, 'Changed macro at an expected context')
            return 'HX', None
        return node if is_leaf(node) else (collapse(node[0], pattern, path + '0'), collapse(node[1], pattern, path + '1'))
    before_context, after_context = collapse(original, old), collapse(changed, new)
    require(before_context == after_context, 'The surrounding structured context changed')
    before_rows, before_graph, bi = source_graph(before_context)
    after_rows, after_graph, ai = source_graph(after_context)
    require((before_rows, before_graph, bi) == (after_rows, after_graph, ai), 'An external guarded successor changed')
    require(sum(op == 'HX' for path, op, arg in before_rows) == 4, 'Wrong macro census')
    require(len(before_rows) == 5113, 'Wrong collapsed context size')
    source_graph(original)
    source_graph(changed)
    receipt = {'status': 'EXACT_CLOSED_MACRO_CONTEXT_AND_GUARDED_GRAPH_PASS',
               'replacement_paths': paths, 'before': metrics(original), 'after': metrics(changed),
               'old_macro_sites': sites_of_tree(old), 'new_macro_sites': sites_of_tree(new),
               'macro_boundary': [0, 0, False], 'collapsed_context_leaves': len(before_rows),
               'collapsed_guarded_cases': sum(2 if op == 'CD' else 1 for path, op, arg in before_rows),
               'collapsed_graph_sha256': digest(json.dumps(before_graph, separators=(',', ':')).encode()),
               'outside_guarded_successors_identical': True,
               'macro_semantics': {'input': 'R5=a,R6=b, with arbitrary natural a,b and other registers',
                                   'output': 'R5=a+b+1,R6=0; every other register unchanged',
                                   'source_steps_each': '3*b+2', 'increments_each': 'b+1',
                                   'proof': 'Induction on b: old form transfers b units then increments once; new form increments once then transfers b units. Both macros terminate and fall through.'},
               'scope': 'Exact surrounding source context and all guarded external successors. Compose with the stated induction on arbitrary b; a binary runtime proof is separate.'}
    return changed, receipt


def bit_invariant(table, radius=5):
    states = {q for q, b in table} | {HALT}
    facts = {q: None for q in states}
    facts[START] = {}
    todo, queued = deque([START]), {START}
    while todo:
        q = todo.popleft(); queued.remove(q)
        if q == HALT: continue
        for bit in (0, 1):
            if 0 in facts[q] and facts[q][0] != bit: continue
            write, move, target = table[q, bit]
            post = {p - move: value for p, value in {**facts[q], 0: write}.items()
                    if -radius <= p - move <= radius}
            joined = post if facts[target] is None else {
                p: value for p, value in facts[target].items() if post.get(p) == value}
            if joined != facts[target]:
                facts[target] = joined
                if target not in queued: todo.append(target); queued.add(target)
    require(facts[START] == {}, 'The initial tape was constrained')
    for (q, bit), (write, move, target) in table.items():
        require(facts[q] is not None, 'Uncovered old working state')
        if 0 in facts[q] and facts[q][0] != bit: continue
        post = {p - move: value for p, value in {**facts[q], 0: write}.items()}
        require(facts[target] is not None and all(post.get(p) == value for p, value in facts[target].items()), 'Invariant is not inductive')
    return facts


def prove_fold(old, new):
    phi = lambda q: KEEP if q == DROP else q
    require({q for q, b in new} == {q for q, b in old} - {DROP}, 'Wrong deleted state')
    facts = bit_invariant(old)
    require(facts[KEEP].get(-2) == 1 and facts[KEEP].get(-1) == 0, 'Keep-state guard failed')
    require(facts[DROP].get(-1) == 1, 'Drop-state guard failed')
    ordinary = 0
    for (q, bit), (write, move, target) in old.items():
        if q in (KEEP, DROP): continue
        require(new[phi(q), bit] == (write, move, phi(target)), 'Noncommuting ordinary row')
        ordinary += 1
    cases = []
    for q in (KEEP, DROP):
        for bit in (0, 1):
            require(0 not in facts[q] or facts[q][0] == bit, 'Exceptional row is vacuous')
            initial = {**facts[q], 0: bit}
            tape = dict(initial)
            expected_write, expected_move, expected_target = old[q, bit]
            goal = {**initial, 0: expected_write}
            state, head = phi(q), 0
            steps = 9 if (q, bit) == (KEEP, 0) else 3
            trace = []
            for tick in range(steps):
                require(state != HALT and head in tape, 'Interior halt or unspecified exterior read')
                read = tape[head]
                write, move, target = new[state, read]
                trace.append([state, head, read, write, move, target])
                tape[head] = write; state = target; head += move
            require((state, head, tape) == (phi(expected_target), expected_move, goal), 'Exceptional whole-tape block failed')
            cases.append({'old_row': [q, bit], 'guard': initial, 'old_steps': 1,
                          'new_steps': steps, 'trace': trace, 'final_state': state,
                          'final_head': head, 'whole_tape_equal': True})
    require(ordinary == 456, 'Wrong ordinary row census')
    return {'status': 'INDEPENDENT_ALL_TAPE_POSITIVE_BLOCK_PASS', 'start': START, 'halt': HALT,
            'old_states': 230, 'new_states': 229, 'keep': KEEP, 'drop': DROP,
            'invariant_radius': 5, 'invariant': facts, 'initial_tape_unconstrained': True,
            'invariant_rows_checked': len(old), 'ordinary_rows': ordinary, 'exceptional_cases': cases,
            'block_length_histogram': {'1': 456, '3': 3, '9': 1},
            'scope': 'Every binary initial tape and integer head at start0. The inductive old-state bit invariant makes every old step simulate by a positive block with no interior halt and identical mapped final state, head and entire tape.'}


def sparse_run(table, ticks):
    state, head, ones = START, 0, set()
    for tick in range(ticks):
        require(state != HALT, 'Unexpected startup halt')
        write, move, target = table[state, int(head in ones)]
        if write: ones.add(head)
        else: ones.discard(head)
        state = target; head += move
    return state, head, ones


def prove_startup(original, basis, candidate, canonical, numbering):
    old_end = sparse_run(original, 408419)
    basis_end = sparse_run(basis, 408941)
    require(old_end == basis_end, 'Source rewrite changed the initialized frame')
    state, head, ones = old_end
    require((state, head, len(ones)) == (DISPATCH, -5, 351), 'Wrong initialized frame')
    qo = qn = START; ho = hn = 0; so = set(); sn = set()
    ticks_new = 0; visits = Counter()
    phi = lambda q: KEEP if q == DROP else q
    for tick in range(408941):
        require((qn, hn, sn) == (phi(qo), ho, so), 'Startup checkpoint mismatch')
        row = qo, int(ho in so)
        cost = (9 if row == (KEEP, 0) else 3) if qo in (KEEP, DROP) else 1
        if qo in (KEEP, DROP): visits[row] += 1
        w, d, z = basis[row]
        if w: so.add(ho)
        else: so.discard(ho)
        qo = z; ho += d
        for _ in range(cost):
            w, d, z = candidate[qn, int(hn in sn)]
            if w: sn.add(hn)
            else: sn.discard(hn)
            qn = z; hn += d
        ticks_new += cost
        require((qn, hn, sn) == (phi(qo), ho, so), 'Startup checkpoint mismatch')
    require(ticks_new == 409691 and (qn, hn, sn) == basis_end, 'Wrong candidate startup')
    tape = bytearray(2 * ticks_new + 3); offset = ticks_new + 1
    q, h = 0, offset
    for _ in range(ticks_new):
        w, d, z = canonical[q, tape[h]]
        tape[h] = w; h += d; q = z
    dense = {i - offset for i, bit in enumerate(tape) if bit}
    require((q, h - offset, dense) == (numbering[DISPATCH], head, ones), 'Independent dense startup failed')
    return {'status': 'EXACT_BLANK_STARTUP_AND_DENSE_CANONICAL_PASS',
            'original_steps': 408419, 'basis_steps': 408941, 'candidate_steps': 409691,
            'whole_tape_fold_checkpoints': 408942, 'state_oldlabels': DISPATCH,
            'state_canonical': numbering[DISPATCH], 'head': head, 'one_cells': sorted(ones),
            'other_cells': 0, 'exceptional_visits': [{'row': list(row), 'visits': count} for row, count in sorted(visits.items())],
            'clock_extra': 750, 'independent_dense_run': True}


def main():
    require(__debug__ and not sys.flags.optimize, 'Run without -O or -OO')
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--table', type=Path, required=True)
    parser.add_argument('--sites', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    table_bytes, site_bytes = args.table.read_bytes(), args.sites.read_bytes()
    require(digest(table_bytes) == TABLE_PIN, 'Wrong pinned K230 machine')
    require(digest(site_bytes) == SITES_PIN, 'Wrong pinned K230 source')
    original = parse_table(table_bytes)
    root = tree_of_sites(normalize_source(site_bytes))
    require(metrics(root) == {'dag_nodes': 212, 'leaf_occurrences': 5125, 'maximum_depth': 40, 'maximum_zero_run': 6}, 'Wrong source census')
    new_root, source_receipt = transform_source(root)
    basis = dict(original)
    require(basis[121, 0] == (0, 1, 31) and basis[121, 1] == (1, 1, 63), 'Wrong source decoder rows')
    basis[121, 0] = 0, 1, 63
    basis[121, 1] = 1, 1, 13
    candidate = {(q, bit): (w, d, KEEP if z == DROP else z)
                 for (q, bit), (w, d, z) in basis.items() if q != DROP}
    candidate[KEEP, 0] = 0, -1, 123
    candidate[KEEP, 1] = 1, -1, 30
    require(len(candidate) == 458, 'Wrong final row count')
    order = sorted({q for q, bit in candidate})
    numbering = {q: i for i, q in enumerate(order)} | {HALT: 229}
    canonical = {(numbering[q], bit): (w, d, numbering[z]) for (q, bit), (w, d, z) in candidate.items()}
    require(digest(encode(canonical)) == H229_PIN, 'Unexpected canonical H229 bytes')
    fold_receipt = prove_fold(basis, candidate)
    startup_receipt = prove_startup(original, basis, candidate, canonical, numbering)
    args.output.mkdir(parents=True, exist_ok=True)
    files = {'k230_h_basis.tm': encode(basis), 'k229_h_oldlabels.tm': encode(candidate),
             'k229.tm': encode(canonical),
             'sites_logical.json': (json.dumps(sites_of_tree(new_root), separators=(',', ':')) + '\n').encode()}
    for name, data in files.items(): (args.output / name).write_bytes(data)
    receipts = {'source_context.json': source_receipt, 'fold_independent.json': fold_receipt,
                'startup.json': startup_receipt,
                'renumbering.json': {'old_to_new': numbering, 'new_to_old': order + [HALT]}}
    manifest = {'status': 'PASS_EXACT_H229_SOURCE_CONTEXT_FOLD_AND_STARTUP', 'input_table_sha256': TABLE_PIN,
                'input_sites_sha256': SITES_PIN, 'script_sha256': digest(Path(__file__).read_bytes()),
                'states': 229, 'rows': 458, 'source_leaves': 5121, 'files': {name: digest(data) for name, data in files.items()},
                'separate_obligation': 'Universal binary runtime for the new source/table; compose with original K230 logical calibration. No new Rocq endpoint is claimed.'}
    receipts['construction.json'] = manifest
    for name, data in receipts.items(): (args.output / name).write_text(json.dumps(data, indent=2) + '\n')
    print(json.dumps({**manifest, 'startup_steps': startup_receipt['candidate_steps'],
                      'collapsed_source_context_leaves': source_receipt['collapsed_context_leaves'],
                      'fold_block_histogram': fold_receipt['block_length_histogram']}, indent=2))


if __name__ == '__main__':
    main()
