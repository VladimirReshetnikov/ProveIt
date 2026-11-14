#!/usr/bin/env python3
"""Independent finite audit of the Q + no-push composition.

The checks here bind the literal changed source, symbolically execute the
changed AX formula block, and replay the inherited K/S/MP exchange certificate.
They do not constitute an end-to-end proof assistant proof of Con(PA).
"""
from pathlib import Path
import argparse
import hashlib
import json


def require(p, msg):
    if not p:
        raise ValueError(msg)


def load(p):
    return json.loads(p.read_text())


def freeze(x):
    return tuple(map(freeze, x)) if isinstance(x, (tuple, list)) else x


def imp(a, b):
    return ('I', a, b)


def macro_word(grammar):
    rules = grammar['rules']
    def visit(x):
        if isinstance(x, str) and x in rules:
            return visit(rules[x])
        if x == 'node60':
            return [['leaf', 'inc', 1]] * 2
        if x == 'node61':
            return [['leaf', 'inc', 1]] * 4
        if isinstance(x, list) and len(x) == 2:
            return visit(x[0]) + visit(x[1])
        return [x]
    return visit(grammar['root'])


def execute_block(word):
    stack, top = [], 'old_T'
    registers = {'node70': 'A', 'node55': 'D', 'node58': 'H'}
    for token in word:
        if isinstance(token, str) and token in registers:
            stack.append(top)
            top = registers[token]
        elif token == 'node65':
            require(bool(stack), 'block stack underflow')
            top = ('pair4', stack.pop(), top, 0)
        else:
            require(token == ['leaf', 'inc', 1], 'unexpected block token')
            require(isinstance(top, tuple) and top[0] == 'pair4', 'tag base')
            top = (*top[:3], top[3] + 1)
    return stack, top


def raw(f):
    if isinstance(f, str):
        return f
    op, a, b = f
    return ('pair4', raw(a), raw(b), 0) if op == 'I' else ('pair4', raw(b), raw(a), 2)


def flatten(nodes, grammar):
    sites = []
    def walk(x, path):
        if isinstance(x, str):
            if x == 'x67':
                return walk(grammar['root'], path)
            return walk(grammar['rules'][x] if x in grammar['rules'] else nodes[x], path)
        if x[0] == 'leaf':
            sites.append([path, x[1], x[2]])
        else:
            require(len(x) == 2, 'nonbinary tree')
            walk(x[0], path + '0')
            walk(x[1], path + '1')
    walk('node172', '')
    return sites


def resolve_by_intervals(sites):
    intervals = {}
    for i, (p, _, _) in enumerate(sites):
        for j in range(len(p) + 1):
            prefix = p[:j]
            if prefix not in intervals:
                intervals[prefix] = [i, i + 1]
            else:
                intervals[prefix][1] = i + 1
    def ancestor(p, bit, depth):
        positions = [i for i, b in enumerate(p) if b == bit]
        require(len(positions) >= depth, 'unclosed jump')
        return p[:positions[-depth]]
    result = []
    for i, (p, op, arg) in enumerate(sites):
        if op == 'inc':
            result.append(['inc', arg, i + 1])
        elif op == 'dec':
            result.append(['dec', arg, intervals[ancestor(p, '0', 1)][1], i + 1])
        elif op == 'breakTo':
            result.append(['jump', intervals[ancestor(p, '0', arg)][1]])
        elif op == 'continueTo':
            result.append(['jump', intervals[ancestor(p, '1', arg)][0]])
        else:
            require(op == 'halt', 'unknown source instruction')
            result.append(['halt'])
    require(all(0 <= t < len(sites) for row in result
                for t in (row[2:] if row[0] in ('inc', 'dec') else row[1:])), 'source edge escapes')
    return result


def check_exchange(cert):
    lines = cert['lines']
    require(cert['assumptions'] == [], 'exchange assumptions')
    count = {'K': 0, 'S': 0, 'MP': 0}
    for i, line in enumerate(lines):
        f = freeze(line['formula'])
        rule = line['rule']
        count[rule] += 1
        if rule == 'K':
            a, b = map(freeze, line['parameters'])
            require(f == imp(a, imp(b, a)), 'bad K axiom')
        elif rule == 'S':
            a, b, c = map(freeze, line['parameters'])
            require(f == imp(imp(a, imp(b, c)), imp(imp(a, b), imp(a, c))), 'bad S axiom')
        else:
            require(rule == 'MP', 'unexpected proof rule')
            major, minor = line['major'], line['minor']
            require(0 <= major < i and 0 <= minor < i, 'forward proof reference')
            require(freeze(lines[major]['formula']) == imp(freeze(lines[minor]['formula']), f), 'bad MP')
    goal = imp(imp('P', imp('Q', 'R')), imp('Q', imp('P', 'R')))
    require(freeze(lines[cert['conclusion_line']]['formula']) == goal, 'wrong exchange conclusion')
    return {'lines': len(lines), 'rules': count, 'assumptions': [],
            'scope': 'K and S remain inherited derived rules of the unchanged rho8 basis'}


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--candidate', type=Path, required=True)
    ap.add_argument('--package', type=Path, default=Path(__file__).resolve().parent.parent)
    ap.add_argument('--output', type=Path, required=True)
    args = ap.parse_args()
    q, candidate = args.package, args.candidate
    grammar = load(q / 'construction/inputs/q.grammar.json')
    original_grammar = load(q / 'construction/inputs/primary.grammar.json')
    new_word, old_word = macro_word(grammar), macro_word(original_grammar)
    require(len(new_word) == len(old_word) == 190, 'AX word length')
    require(new_word[:102] == old_word[:102] and new_word[121:] == old_word[121:], 'AX external tokens changed')
    U = lambda i, f: ('U', i, f)
    P, Q, R = U('D', 'A'), U('D', imp('A', 'H')), U('D', 'H')
    require(execute_block(old_word[102:121]) == (['old_T'], raw(imp(P, imp(Q, R)))), 'old head formula')
    require(execute_block(new_word[102:121]) == (['old_T'], raw(imp(Q, imp(P, R)))), 'new head formula')

    nodes = load(candidate / 'nodes.json')
    require(nodes['node163'] == ['node6', 'node54'], 'no-push source splice missing')
    sites = flatten(nodes, grammar)
    require(sites == load(candidate / 'sites.json'), 'candidate site binding')
    instructions = resolve_by_intervals(sites)
    require(instructions == load(candidate / 'instructions.json'), 'candidate instruction binding')
    old_instructions = load(q / 'construction/inputs/pa194N.instructions.json')
    require(len(instructions) == len(old_instructions) == 3654, 'source size')
    changes = [i for i, (a, b) in enumerate(zip(old_instructions, instructions)) if a != b]
    require(len(changes) == 79 and min(changes) == 1953 and max(changes) == 2067,
            'unexpected instruction changes in Q emitter block')
    exchange = check_exchange(load(q / 'verification/exchange_certificate.json'))
    result = {'status': 'PASS', 'dense_sha256': hashlib.sha256((candidate / 'machine.tm').read_bytes()).hexdigest(),
              'macro_tokens': 190, 'only_changed_macro_interval_half_open': [102, 121],
              'old_head': imp(P, imp(Q, R)), 'new_head': imp(Q, imp(P, R)),
              'block_stack_effect': 'push incoming top; leave older stack untouched',
              'source_sites': len(sites), 'source_resolved_by_independent_interval_method': True,
              'changed_instruction_count_relative_to_N': len(changes),
              'changed_instruction_range_relative_to_N': [min(changes), max(changes)],
              'source_changes_relative_to_N': [[i, old_instructions[i], instructions[i]] for i in changes],
              'exchange': exchange,
              'proof_boundary': 'No new end-to-end Lean/Rocq proof; inherited PA-calibration suppliers remain identified.'}
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({k: v for k, v in result.items() if k != 'source_changes_relative_to_N'}, indent=2))


if __name__ == '__main__':
    main()
