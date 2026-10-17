#!/usr/bin/env python3
"""Check decoder words, emitted edges, state counts and totalization.

This checker does not import the compiler, abstract interpreter, or backend.
It proves finite syntactic claims; it does not prove the binary interpreter.
"""
import hashlib
import json
import re
from pathlib import Path

HERE = Path(__file__).resolve().parent
REGS = ['nextproof', 'topwff', 'wffstack', 'axiomcode', 'param1',
        'param2', 'scratch1', 'scratch2', 'prooflist']
INPUT_SHA = '1fbc30fcf82a1442ed88d1a1dde412630a431d32a7265d22bdf8517bffe01746'

def require(condition, message):
    if not condition:
        raise ValueError(message)

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def source_tree():
    source = HERE / 'inputs/Prog254.v'
    require(sha(source) == INPUT_SHA, 'source hash differs')
    body = source.read_text().split('Definition p254_tab', 1)[1].split('[', 1)[1].split('].', 1)[0]
    rows = re.findall(r'\((C[A-Z](?: \d+)?),\s*(C[A-Z](?: \d+)?)\)', body)
    require(len(rows) == 6459, 'source tree node count differs')
    seen = set()
    def unfold(node):
        require(node not in seen, 'source repeats a tree node')
        seen.add(node)
        children = []
        for edge in rows[node]:
            words = edge.split()
            op = words[0][1:]
            if op == 'N':
                child = int(words[1])
                require(node < child < len(rows), 'source is not forward acyclic')
                children.append(unfold(child))
            else:
                children.append((op, int(words[1])) if len(words) == 2 else (op,))
        return ('N', *children)
    root = unfold(0)
    require(len(seen) == 6459, 'unused source tree node')
    return root

def leaf_words(tree, prefix=''):
    if tree[0] == 'N':
        yield from leaf_words(tree[1], prefix + '0')
        yield from leaf_words(tree[2], prefix + '1')
    else:
        yield [prefix, list(tree)]

def dag_tree(label):
    data = json.loads((HERE / (label + '.json')).read_text())
    nodes = {int(k): v for k, v in data['nodes'].items()}
    require(set(nodes) == set(range(len(nodes))), 'noncontiguous DAG identifiers')
    used = set()
    def unfold(node, ancestors=frozenset()):
        require(node in nodes and node not in ancestors, 'undefined/cyclic DAG node')
        used.add(node)
        pair = nodes[node]
        require(len(pair) == 2, 'DAG node is not binary')
        def edge(e):
            require(e[0] in ('N', 'I', 'D', 'B', 'C', 'H'), 'unknown DAG opcode')
            if e[0] == 'N':
                require(len(e) == 2, 'bad DAG target')
                return unfold(e[1], ancestors | {node})
            require(len(e) == (1 if e[0] == 'H' else 2), 'bad operation arity')
            if e[0] in ('I', 'D'):
                require(type(e[1]) is int and 0 <= e[1] < 9, 'bad register')
            if e[0] in ('B', 'C'):
                require(type(e[1]) is int and e[1] >= 0, 'bad control depth')
            return tuple(e)
        return ('N', *(edge(e) for e in pair))
    tree = unfold(data['root'])
    require(used == set(nodes), 'unreachable DAG node')
    return data, nodes, tree

def load_table(path):
    table = {}
    start = None
    for line in path.read_text().splitlines():
        if line.startswith('#! start '):
            start = line.split()[-1]
        if not line.strip() or line.startswith('#'):
            continue
        q, bit, write, move, dest = line.split()
        require(bit in ('0', '1') and write in ('0', '1'), 'nonbinary table')
        require(move in ('L', 'R') and (q, bit) not in table, 'bad/duplicate row')
        table[q, bit] = (write, move, dest)
    require(start is not None, 'missing start declaration')
    return start, table

def check_tables(label, data, nodes):
    start, raw = load_table(HERE / (label + '.tm'))
    numeric_start, numeric = load_table(HERE / (label + '_total.tm'))
    labels = json.loads((HERE / (label + '_labels.json')).read_text())
    states = {q for q, bit in raw}
    require(start in states and numeric_start == '0', 'bad start state')
    require(set(labels) == states | {'halt'}, 'label domain differs')
    require(set(labels.values()) == set(range(len(states) + 1)), 'label range differs')
    require(labels[start] == 0 and labels['halt'] == len(states), 'start/halt numbering differs')
    require(len(numeric) == 2 * len(states), 'numeric table not total')
    missing = []
    for q in states:
        for bit in ('0', '1'):
            action = raw.get((q, bit))
            if action is None:
                missing.append([q, int(bit)])
                action = (bit, 'R', 'halt')
            write, move, dest = action
            require(dest in labels, 'raw target undefined')
            expected = (write, move, str(labels[dest]))
            require(numeric[str(labels[q]), bit] == expected, 'renumbered row differs')
    require(missing == [['1.inc', 1]], 'unexpected missing row')
    order = [data['root']] + [n for n in sorted(nodes) if n != data['root']]
    names = {('main().0' if i == 0 else 'global.' + str(i)): n for i, n in enumerate(order)}
    require(set(names) <= states, 'missing decision state')
    for name, node in names.items():
        for bit in (0, 1):
            write, move, dest = raw[name, str(bit)]
            expected = nodes[node][bit]
            if dest in names:
                recovered = ['N', names[dest]]
            elif dest == 'halt':
                recovered = ['H']
            elif match := re.fullmatch(r'3\.(.*)\.(inc|decnz)', dest):
                recovered = ['I' if match[2] == 'inc' else 'D', REGS.index(match[1])]
            elif match := re.fullmatch(r'6\.break\.(\d+)', dest):
                recovered = ['B', int(match[1]) + 1 - bit]
            elif match := re.fullmatch(r'6\.continue\.(\d+)', dest):
                recovered = ['B', 0] if bit == 0 and write == '1' else ['C', int(match[1]) + bit]
            else:
                raise ValueError('unrecognized decision-edge target: ' + dest)
            require(recovered == expected, 'decision operation differs')
            direct = expected[0] in ('N', 'I', 'D', 'H')
            expected_write = str(bit) if direct else ('1' if expected == ['B', 0] and bit == 0 else '0')
            require(write == expected_write and move == ('R' if direct else 'L'), 'decision edge action differs')
    return {'label': label, 'decision_nodes': len(nodes), 'framework_states': len(states) - len(nodes),
            'working_states': len(states), 'raw_rows': len(raw), 'total_rows': len(numeric),
            'decoder_edge_checks': 2 * len(nodes), 'filled_halt_rows': missing,
            'total_table_sha256': sha(HERE / (label + '_total.tm'))}

def closed(tree):
    # Maximum unbound break/continue depth. A closed macro has both zero.
    def demand(t):
        if t[0] == 'N':
            lb, lc = demand(t[1])
            rb, rc = demand(t[2])
            return max(0, lb - 1, rb), max(0, lc, rc - 1)
        return (1 if t[0] == 'D' else t[1] if t[0] == 'B' else 0,
                t[1] if t[0] == 'C' else 0)
    return demand(tree) == (0, 0)

def specialized(tree, simplify=False):
    replacements = {
        '11101001011000110': ('N', ('D', 6), ('N', ('I', 5), ('C', 2))),
        '11111100': ('N', ('D', 1), ('N', ('I', 6), ('C', 2))),
    }
    hits = set()
    def visit(t, prefix):
        if prefix in replacements:
            require(t == replacements[prefix] and closed(t), 'replacement is not the claimed closed loop')
            hits.add(prefix)
            return ('B', 0)
        if t[0] != 'N':
            return t
        left, right = visit(t[1], prefix + '0'), visit(t[2], prefix + '1')
        if simplify and left == ('B', 0) and closed(right):
            return right
        if simplify and right == ('B', 0) and closed(left):
            return left
        return ('N', left, right)
    result = visit(tree, '')
    require(hits == set(replacements), 'a claimed loop was not replaced')
    return result

def main():
    source = source_tree()
    source_words = list(leaf_words(source))
    require(len(source_words) == 6460, 'source leaf count differs')
    expected = {
        'global_baseline': source,
        'global_empty_loops': specialized(source),
        'global_empty_loops_simplified': specialized(source, True),
        'global_zero_macro_best': source,
    }
    results = []
    for label, wanted in expected.items():
        data, nodes, tree = dag_tree(label)
        require(tree == wanted, 'unfolded ' + label + ' differs from its exact source transformation')
        words = list(leaf_words(tree))
        if label in ('global_baseline', 'global_zero_macro_best'):
            require(words == source_words, 'an exact baseline leaf path/operation differs')
        result = check_tables(label, data, nodes)
        result['unfolded_leaf_count'] = len(words)
        result['leaf_words_sha256'] = hashlib.sha256(json.dumps(words, separators=(',', ':')).encode()).hexdigest()
        results.append(result)
    for suffix in ('.tm', '_total.tm', '.json', '_labels.json'):
        require((HERE / ('global_baseline' + suffix)).read_bytes() ==
                (HERE / ('global_zero_macro_best' + suffix)).read_bytes(), 'finite-search winner differs from baseline')
    report = {'passed': True, 'source_sha256': INPUT_SHA, 'exact_baseline_leaf_words': 6460,
              'baseline_maximum_path_depth': max(len(p) for p, op in source_words),
              'baseline_maximum_zero_run': max(len(run) for p, op in source_words for run in p.split('1')),
              'results': results,
              'scope': 'Finite assembly/leaf-word checks. Totalization preserves undefined-row halting; binary interpreter correctness is a separate obligation.'}
    (HERE / 'assembly_verification.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(report, indent=2))

if __name__ == '__main__':
    main()
