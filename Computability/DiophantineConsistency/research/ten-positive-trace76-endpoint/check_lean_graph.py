#!/usr/bin/env python3
"""Bind the Lean literal of package 163's 76/352 circuit to its pinned JSON.

Usage (from anywhere): py -I -X utf8 -B check_lean_graph.py

The Lean circuit is `TenPositiveTrace76.value76` (BFS943/Trace76Circuit.lean):
the 75 register map `TenPositiveTrace75.regs` (TenPositiveTrace75.lean) for
every row except the carrier, plus `L := r.b * r.V` and the 76 carrier `Z`.
This checker

* pins the SHA-256 of the JSON graph and of both Lean files;
* parses `regs` (lets and record) and the body of `value76` in the small
  arithmetic fragment they use, and the JSON rows, into one interned DAG,
  normalizing sums and products modulo commutative-ring associativity,
  commutativity, identities and additive inverses (no distribution, no
  sampling), and requires the two outputs to be the same node;
* requires the literal and endpoint definitions to read `value76` at the
  ports `CompactSymbolicPorts.ports betaNat (paramKernel rho) lowNat highNat`,
  verbatim as in `IPRATrace75`, and the JSON `coefficient_binding` to equal
  the 75 graph's, so `reviews/bfs943-source-promotion/tools/check_ports.py`
  (which binds those four integers to the 75 graph's hashes) covers 76 too.

It is finite external evidence for the transcription, not a Lean theorem
about files, and it reuses the normalizer of
`research/trace75-bfs-decimal-display/check_lean_graph.py`.
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
EQ = D / 'con-zfc-diophantine-forms/163-trace-radical/compact/equations'
GRAPH = EQ / 'trace76_degree352.json'
GRAPH75 = EQ / 'trace75_degree402.json'
L = D / 'Lean/DiophantineConsistency'
REGS = L / 'TenPositiveTrace75.lean'
CIRCUIT = L / 'BFS943/Trace76Circuit.lean'
SYNTAX = L / 'BFS943/Trace76Syntax.lean'
ENDPOINT = L / 'BFS943/IPRATrace76.lean'
ENDPOINT75 = L / 'BFS943/IPRATrace75.lean'
PINS = {GRAPH: 'd2e4de6870924d24e0d0967d57ed50e20e0d723d223998fafa6cee66c47f1ee8',
        GRAPH75: '8b9b9421ae8a0762725852034b3db6d29b14660b3a4d0587e1494a933b5271c9',
        REGS: '0df718ab69ae7aef32dd341ee355ea2e21214e97fbea225af8816519fe383db9'}


def need(condition, message):
    if not condition:
        raise RuntimeError(message)


def sha(path):
    return sha256(path.read_bytes()).hexdigest()


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
    lean_pins = {path: sha(path) for path in (CIRCUIT, SYNTAX, ENDPOINT)}
    graph = json.loads(GRAPH.read_text(encoding='utf8'))
    graph75 = json.loads(GRAPH75.read_text(encoding='utf8'))
    witnesses = ['J', 'F', 'alpha', 'i', 'T', 'w', 's', 'n', 'eta', 'zeta']
    ports = ['beta', 'K0', 'MC', 'MF']
    need(graph['witnesses'] == witnesses and graph['fixed_numerals'] == ports and
         len(graph['source']) == graph['operations'] == 76 and graph['exact_degree'] == 352 and
         graph['transport_weight'] == 'bV' and graph['chart'] == 'q3', 'graph metadata')
    need(graph['coefficient_binding'] == graph75['coefficient_binding'], 'port binding differs from 75')
    json_env = {name: symbol(name) for name in witnesses + ports}
    for name, op, left, right in graph['source']:
        need(name not in json_env, 'duplicate JSON register: ' + name)

        def operand(value):
            if type(value) is int and value >= 0:
                return number(value)
            need(value in json_env, 'unknown JSON operand')
            return json_env[value]
        json_env[name] = operation(op, operand(left), operand(right))

    text = REGS.read_text(encoding='utf8')
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

    circuit = CIRCUIT.read_text(encoding='utf8')
    body = circuit.split('def value76 (p : Fin 4 → R) (v : Fin 10 → R) : R :=\n', 1)[1].split('\n\n', 1)[0]
    lines = body.splitlines()
    need(lines[0] == '  let r := regs p v', 'unexpected value76 body')
    venv = {'r_' + name: value for name, value in assignments.items()}
    venv.update({f'v{i}': symbol(n) for i, n in enumerate(witnesses)})
    for line in lines[1:-1]:
        match = re.fullmatch(r'  let ([A-Za-z][A-Za-z0-9_]*) := (.+)', line)
        need(match is not None and match[1] not in venv, 'unexpected value76 let')
        venv[match[1]] = parse_expression(match[2], venv)
    need(set(venv) - set('r_' + f for f in fields) - {f'v{i}' for i in range(10)} == {'L', 'Z'},
         'value76 lets')
    value = parse_expression(lines[-1], venv)
    need(value == json_env[graph['output']], 'Lean and JSON outputs differ after ring normalization')
    # The 76 weight row and carrier are the JSON's, register by register.
    need(venv['L'] == json_env['L'], 'weight row L differs')
    need(venv['Z'] == json_env['Znum'], 'carrier row Znum differs')

    syntax = SYNTAX.read_text(encoding='utf8')
    need('def expression (p : Fin 4 → ℤ) : Expr (Fin 10) := value76 (TenPositiveTrace75.ports p) Expr.var\n'
         in syntax, 'literal expression definition')
    need('def literal (p : Fin 4 → ℕ) : Expr (Fin 10) :=\n'
         '  TenPositiveTrace76.expression (fun j => (p j : ℤ))\n' in syntax, 'literal definition')
    endpoint = ENDPOINT.read_text(encoding='utf8')
    ports_text = ('def fixedPorts : Fin 4 → ℕ :=\n'
                  '  CompactSymbolicPorts.ports CompactFixedBeta.betaNat\n'
                  '    (DirectBFSSymbolicKernel.paramKernel CompactSymbolicKernel.rho)\n'
                  '    CompactSymbolicPorts.lowNat CompactSymbolicPorts.highNat\n')
    need(ports_text in endpoint and ports_text in ENDPOINT75.read_text(encoding='utf8'),
         'fixedPorts differs from IPRATrace75')
    need('def expression : Expr (Fin 10) := Trace76BFSSyntax.literal fixedPorts\n' in endpoint,
         'endpoint expression')
    for path, expected in PINS.items():
        need(sha(path) == expected, 'input changed: ' + str(path))
    for path, expected in lean_pins.items():
        need(sha(path) == expected, 'input changed: ' + str(path))
    print(json.dumps({'status': 'PASS', 'graph_sha256': PINS[GRAPH],
                      'regs_source_sha256': PINS[REGS],
                      'circuit_source_sha256': lean_pins[CIRCUIT],
                      'syntax_source_sha256': lean_pins[SYNTAX],
                      'endpoint_source_sha256': lean_pins[ENDPOINT],
                      'graph_rows': len(graph['source']), 'lean_registers': len(fields),
                      'interned_nodes': len(keys),
                      'port_binding': 'identical to trace75_degree402.json',
                      'comparison': 'exact structural normalization in commutative rings',
                      'scope': 'external restricted-fragment parser; no Lean theorem about file bytes'},
                     sort_keys=True))


if __name__ == '__main__':
    main()
