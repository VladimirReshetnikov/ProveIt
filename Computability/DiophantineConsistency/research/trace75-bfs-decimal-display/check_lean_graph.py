#!/usr/bin/env python3
"""Compare the printed JSON circuit with the Lean ring evaluator structurally.

This finite external checker parses only the small arithmetic fragment used
by the pinned Lean evaluator. It normalizes sums and products modulo their
commutative-ring associativity, commutativity, identities, and additive
inverses. It does not expand products over sums or rely on random samples.
It is not a Lean theorem about files or a general Lean parser.
"""
import ast
from hashlib import sha256
import json
from pathlib import Path
import re
import sys

if sys.flags.optimize:
    raise SystemExit('optimized Python refused')
H = Path(__file__).resolve().parent
D = H.parents[1]
GRAPH = D / 'con-zfc-diophantine-forms/163-trace-radical/compact/equations/trace75_degree402.json'
LEAN = D / 'Lean/DiophantineConsistency/TenPositiveTrace75.lean'
PINS = {GRAPH: '8b9b9421ae8a0762725852034b3db6d29b14660b3a4d0587e1494a933b5271c9',
        LEAN: '0df718ab69ae7aef32dd341ee355ea2e21214e97fbea225af8816519fe383db9'}


def need(condition, message):
    if not condition:
        raise RuntimeError(message)


def sha(path):
    return sha256(path.read_bytes()).hexdigest()


# IDs are interned from exact Python tuples, rather than compared via hashes.
keys = []
ids = {}


def node(key):
    if key not in ids:
        ids[key] = len(keys)
        keys.append(key)
    return ids[key]


def number(n):
    return node(('const', n))


def symbol(s):
    return node(('symbol', s))


def add(a, b, sign=1):
    terms = {}
    constant = 0
    for value, factor in ((a, 1), (b, sign)):
        key = keys[value]
        if key[0] == 'const':
            constant += factor * key[1]
        elif key[0] == 'add':
            constant += factor * key[1]
            for term, coefficient in key[2]:
                terms[term] = terms.get(term, 0) + factor * coefficient
        else:
            terms[value] = terms.get(value, 0) + factor
    terms = tuple(sorted((term, coefficient) for term, coefficient in terms.items() if coefficient))
    if not terms:
        return number(constant)
    if constant == 0 and len(terms) == 1 and terms[0][1] == 1:
        return terms[0][0]
    return node(('add', constant, terms))


def mul(a, b):
    factors = []
    constant = 1
    for value in (a, b):
        key = keys[value]
        if key[0] == 'const':
            constant *= key[1]
        elif key[0] == 'mul':
            constant *= key[1]
            factors.extend(key[2])
        else:
            factors.append(value)
    if constant == 0:
        return number(0)
    if not factors:
        return number(constant)
    if constant == 1 and len(factors) == 1:
        return factors[0]
    return node(('mul', constant, tuple(sorted(factors))))


def operation(op, a, b):
    if op == '+':
        return add(a, b)
    if op == '-':
        return add(a, b, -1)
    if op == '*':
        return mul(a, b)
    raise RuntimeError('unsupported operation ' + str(op))


def parse_expression(text, environment):
    text = re.sub(r'\b([pv])\s+(\d+)\b', lambda m: m[1] + m[2], text)
    text = re.sub(r'\br\.([A-Za-z][A-Za-z0-9_]*)\b', lambda m: 'r_' + m[1], text)
    parsed = ast.parse(text.strip(), mode='eval')

    def visit(expr):
        if isinstance(expr, ast.Name):
            need(expr.id in environment, 'unknown identifier: ' + expr.id)
            return environment[expr.id]
        if isinstance(expr, ast.Constant) and type(expr.value) is int and expr.value >= 0:
            return number(expr.value)
        if isinstance(expr, ast.BinOp):
            op = {ast.Add: '+', ast.Sub: '-', ast.Mult: '*'}.get(type(expr.op))
            need(op is not None, 'unsupported binary operator')
            return operation(op, visit(expr.left), visit(expr.right))
        raise RuntimeError('unsupported expression: ' + ast.dump(expr))
    return visit(parsed.body)


def main():
    for path, expected in PINS.items():
        need(sha(path) == expected, 'input pin: ' + str(path))
    graph = json.loads(GRAPH.read_text())
    witnesses = ['J', 'F', 'alpha', 'i', 'T', 'w', 's', 'n', 'eta', 'zeta']
    ports = ['beta', 'K0', 'MC', 'MF']
    need(graph['witnesses'] == witnesses and graph['fixed_numerals'] == ports and
         len(graph['source']) == graph['operations'] == 75, 'graph metadata')
    json_env = {name: symbol(name) for name in witnesses + ports}
    for name, op, left, right in graph['source']:
        need(name not in json_env, 'duplicate JSON register: ' + name)
        def operand(value):
            if type(value) is int and value >= 0:
                return number(value)
            need(value in json_env, 'unknown JSON operand')
            return json_env[value]
        json_env[name] = operation(op, operand(left), operand(right))

    text = LEAN.read_text()
    decl = text.split('structure Regs (R : Type*) where\n', 1)[1].split('\n/--', 1)[0]
    fields = re.findall(r'^  ([A-Za-z][A-Za-z0-9_]*) : R$', decl, re.M)
    need(len(fields) == 27 and len(set(fields)) == len(fields), 'Lean field inventory')
    block = text.split('def regs (p : Fin 4 → R) (v : Fin 10 → R) : Regs R :=\n', 1)[1].split('\n\n/--', 1)[0]
    local_lines, record = block.split('\n  { ', 1)
    need(record.endswith(' }'), 'Lean record shape')
    env = {f'v{i}': symbol(n) for i, n in enumerate(witnesses)}
    env.update({f'p{i}': symbol(n) for i, n in enumerate(ports)})
    for line in local_lines.splitlines():
        match = re.fullmatch(r'  let ([A-Za-z][A-Za-z0-9_]*) := (.+)', line)
        need(match is not None and match[1] not in env, 'unexpected Lean let')
        env[match[1]] = parse_expression(match[2], env)
    assignments = {}
    for item in re.split(r',\s*', record[:-2]):
        parts = item.split(' := ')
        need(len(parts) in (1, 2), 'unexpected Lean record entry')
        field = parts[0]
        need(field in fields and field not in assignments, 'unknown or duplicate field')
        assignments[field] = parse_expression(parts[1] if len(parts) == 2 else field, env)
    need(set(assignments) == set(fields), 'missing Lean record field')
    result_body = text.split('def value75 (p : Fin 4 → R) (v : Fin 10 → R) : R :=\n', 1)[1].split('\n\n\n/-!', 1)[0]
    need(result_body.startswith('  let r := regs p v\n'), 'unexpected evaluator body')
    expr = ' '.join(result_body.splitlines()[1:])
    value = parse_expression(expr, {'r_' + name: value for name, value in assignments.items()})
    need(value == json_env[graph['output']], 'Lean and JSON outputs differ after ring normalization')
    for path, expected in PINS.items():
        need(sha(path) == expected, 'input changed: ' + str(path))
    print(json.dumps({'status': 'PASS', 'graph_sha256': PINS[GRAPH], 'lean_source_sha256': PINS[LEAN],
                      'graph_rows': len(graph['source']), 'lean_registers': len(fields),
                      'interned_nodes': len(keys), 'comparison': 'exact structural normalization in commutative rings',
                      'scope': 'external restricted-fragment parser; no Lean theorem about file bytes'}, sort_keys=True))


if __name__ == '__main__':
    main()
