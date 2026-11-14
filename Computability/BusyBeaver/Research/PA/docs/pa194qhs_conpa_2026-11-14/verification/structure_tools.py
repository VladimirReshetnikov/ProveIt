"""Unchanged source/propositional audit helpers from the supplied QH packet.
See NOTICE.txt and licenses/ for attribution.
"""
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
