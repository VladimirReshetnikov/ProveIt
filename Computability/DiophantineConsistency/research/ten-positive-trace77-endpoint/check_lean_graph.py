#!/usr/bin/env python3
"""Bind the Lean literal of package 171's 77/348 circuit to its pinned JSON.

Usage (from anywhere): py -I -X utf8 -B check_lean_graph.py

The Lean circuit is `TenPositiveTrace77.value77` (BFS943/Trace77Circuit.lean):
the 75 register map `TenPositiveTrace75.regs` (TenPositiveTrace75.lean) for
every row except the denominator, carrier and multiplier, plus
`L := r.b * r.V`, `D := r.q * r.q * (r.q * r.q)` and the 77 carrier `Z` and
multiplier `M`. This checker

* pins the SHA-256 of the 77 JSON graph, of the 75 and 76 JSON graphs, and
  of `TenPositiveTrace75.lean`;
* checks that the 77 rows differ from the 76 rows exactly by the new row
  `q4 = q2 * q2` and the two uses of `q4` in place of `XY` (`P1mu2`,
  `mu2inner`);
* parses `regs` (lets and record) and the body of `value77` in the small
  arithmetic fragment they use, and the JSON rows, into one interned DAG,
  normalizing sums and products modulo commutative-ring associativity,
  commutativity, identities and additive inverses (no distribution, no
  sampling), and requires the two outputs to be the same node (also the
  rows `L`, `q4`, `Znum`, `Mtot` individually);
* rejects three mutations of the `value77` body (denominator `q³`,
  multiplier with the 75 denominator `XY`, sign of the offset term);
* requires the literal and endpoint definitions to read `value77` at the
  ports `CompactSymbolicPorts.ports betaNat (paramKernel rho) lowNat highNat`,
  verbatim as in `IPRATrace75`, and the JSON `coefficient_binding` to name
  the same four files with the same bit lengths and raw/gzip SHA-256 and the
  same tuple as the 75 graph (only its relative `path` and an added
  `endianness: little` differ), so
  `reviews/bfs943-source-promotion/tools/check_ports.py` (which binds those
  four integers to the 75 graph's raw hashes) covers 77 too.

It is finite external evidence for the transcription, not a Lean theorem
about files, and it reuses the normalizer of
`research/ten-positive-trace76-endpoint/check_lean_graph.py`.
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
FORMS = D / 'con-zfc-diophantine-forms'
GRAPH = FORMS / '171-pooled-powers-separated-radicals/positive/q4_interpolation/equation.json'
EQ = FORMS / '163-trace-radical/compact/equations'
GRAPH75 = EQ / 'trace75_degree402.json'
GRAPH76 = EQ / 'trace76_degree352.json'
L = D / 'Lean/DiophantineConsistency'
REGS = L / 'TenPositiveTrace75.lean'
CIRCUIT = L / 'BFS943/Trace77Circuit.lean'
SYNTAX = L / 'BFS943/Trace77Syntax.lean'
ENDPOINT = L / 'BFS943/IPRATrace77.lean'
ENDPOINT75 = L / 'BFS943/IPRATrace75.lean'
PINS = {GRAPH: '74b27a42929aafe87b273dc7d9d2811fb61dee1c6f211bb54d5c5eeefac5ab78',
        GRAPH75: '8b9b9421ae8a0762725852034b3db6d29b14660b3a4d0587e1494a933b5271c9',
        GRAPH76: 'd2e4de6870924d24e0d0967d57ed50e20e0d723d223998fafa6cee66c47f1ee8',
        REGS: '0df718ab69ae7aef32dd341ee355ea2e21214e97fbea225af8816519fe383db9'}
WITNESSES = ['J', 'F', 'alpha', 'i', 'T', 'w', 's', 'n', 'eta', 'zeta']
PORTS = ['beta', 'K0', 'MC', 'MF']
MUTATIONS = [
    ('denominator q^3', '  let D := r.q * r.q * (r.q * r.q)', '  let D := r.q * r.q * r.q'),
    ('multiplier with XY', '  let M := r.h * D * r.H', '  let M := r.h * r.D * r.H'),
    ('offset sign', 'r.H * (D * r.B + r.h * r.e)', 'r.H * (D * r.B - r.h * r.e)'),
]


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


def json_registers(graph):
    env = {name: symbol(name) for name in WITNESSES + PORTS}
    for name, op, left, right in graph['source']:
        need(name not in env, 'duplicate JSON register: ' + name)

        def operand(value):
            if type(value) is int and value >= 0:
                return number(value)
            need(value in env, 'unknown JSON operand')
            return env[value]
        env[name] = operation(op, operand(left), operand(right))
    return env


def lean_registers():
    text = REGS.read_text(encoding='utf8')
    decl = text.split('structure Regs (R : Type*) where\n', 1)[1].split('\n/--', 1)[0]
    fields = re.findall(r'^  ([A-Za-z][A-Za-z0-9_]*) : R$', decl, re.M)
    need(len(fields) == 27 and len(set(fields)) == len(fields), 'Lean field inventory')
    block = text.split('def regs (p : Fin 4 → R) (v : Fin 10 → R) : Regs R :=\n', 1)[1].split('\n\n/--', 1)[0]
    local_lines, record = block.split('\n  { ', 1)
    need(record.endswith(' }'), 'Lean record shape')
    env = {f'v{i}': symbol(n) for i, n in enumerate(WITNESSES)}
    env.update({f'p{i}': symbol(n) for i, n in enumerate(PORTS)})
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
    return fields, assignments


def lean_value(body, fields, assignments):
    lines = body.splitlines()
    need(lines[0] == '  let r := regs p v', 'unexpected value77 body')
    venv = {'r_' + name: value for name, value in assignments.items()}
    venv.update({f'v{i}': symbol(n) for i, n in enumerate(WITNESSES)})
    for line in lines[1:-1]:
        match = re.fullmatch(r'  let ([A-Za-z][A-Za-z0-9_]*) := (.+)', line)
        need(match is not None and match[1] not in venv, 'unexpected value77 let')
        venv[match[1]] = parse_expression(match[2], venv)
    need(set(venv) - set('r_' + f for f in fields) - {f'v{i}' for i in range(10)} ==
         {'L', 'D', 'Z', 'M'}, 'value77 lets')
    return venv, parse_expression(lines[-1], venv)


def main():
    for path, expected in PINS.items():
        need(sha(path) == expected, 'input pin: ' + str(path))
    lean_pins = {path: sha(path) for path in (CIRCUIT, SYNTAX, ENDPOINT)}
    graph = json.loads(GRAPH.read_text(encoding='utf8'))
    graph75 = json.loads(GRAPH75.read_text(encoding='utf8'))
    graph76 = json.loads(GRAPH76.read_text(encoding='utf8'))
    need(graph['witnesses'] == WITNESSES and graph['fixed_numerals'] == PORTS and
         len(graph['source']) == graph['operations'] == 77 and graph['exact_degree'] == 348 and
         graph['transport_weight'] == 'bV' and graph['chart'] == 'q4' and
         graph['denominator'] == 'q4', 'graph metadata')
    binding, binding75 = graph['coefficient_binding'], graph75['coefficient_binding']
    need(binding['ports'] == binding75['ports'] and binding['tuple'] == binding75['tuple'] and
         set(binding) - set(binding75) == {'endianness'} and binding['endianness'] == 'little',
         'port binding differs from 75')
    # The row difference from 76/352: one new row, two operands XY -> q4.
    rows76 = [tuple(r) for r in graph76['source']]
    rows77 = [tuple(r) for r in graph['source']]
    expected = list(rows76)
    expected.insert(3, ('q4', '*', 'q2', 'q2'))
    expected = [('P1mu2', '*', 'bJ', 'q4') if r == ('P1mu2', '*', 'bJ', 'XY') else
                ('mu2inner', '*', 'q4', 'Bt') if r == ('mu2inner', '*', 'XY', 'Bt') else r
                for r in expected]
    need(rows77 == expected and graph['output'] == graph76['output'] == 'N',
         'row difference from 76/352')

    json_env = json_registers(graph)
    fields, assignments = lean_registers()
    circuit = CIRCUIT.read_text(encoding='utf8')
    body = circuit.split('def value77 (p : Fin 4 → R) (v : Fin 10 → R) : R :=\n', 1)[1].split('\n\n', 1)[0]
    venv, value = lean_value(body, fields, assignments)
    need(value == json_env[graph['output']], 'Lean and JSON outputs differ after ring normalization')
    need(venv['L'] == json_env['L'], 'weight row L differs')
    need(venv['D'] == json_env['q4'], 'denominator row q4 differs')
    need(venv['Z'] == json_env['Znum'], 'carrier row Znum differs')
    need(venv['M'] == json_env['Mtot'], 'multiplier row Mtot differs')
    rejected = []
    for label, old, new in MUTATIONS:
        need(body.count(old) == 1, 'mutation anchor: ' + label)
        _, mutated = lean_value(body.replace(old, new), fields, assignments)
        need(mutated != json_env[graph['output']], 'mutation accepted: ' + label)
        rejected.append(label)

    syntax = SYNTAX.read_text(encoding='utf8')
    need('def expression (p : Fin 4 → ℤ) : Expr (Fin 10) := value77 (TenPositiveTrace75.ports p) Expr.var\n'
         in syntax, 'literal expression definition')
    need('def literal (p : Fin 4 → ℕ) : Expr (Fin 10) :=\n'
         '  TenPositiveTrace77.expression (fun j => (p j : ℤ))\n' in syntax, 'literal definition')
    endpoint = ENDPOINT.read_text(encoding='utf8')
    ports_text = ('def fixedPorts : Fin 4 → ℕ :=\n'
                  '  CompactSymbolicPorts.ports CompactFixedBeta.betaNat\n'
                  '    (DirectBFSSymbolicKernel.paramKernel CompactSymbolicKernel.rho)\n'
                  '    CompactSymbolicPorts.lowNat CompactSymbolicPorts.highNat\n')
    need(ports_text in endpoint and ports_text in ENDPOINT75.read_text(encoding='utf8'),
         'fixedPorts differs from IPRATrace75')
    need('def expression : Expr (Fin 10) := Trace77BFSSyntax.literal fixedPorts\n' in endpoint,
         'endpoint expression')
    for path, expected_sha in PINS.items():
        need(sha(path) == expected_sha, 'input changed: ' + str(path))
    for path, expected_sha in lean_pins.items():
        need(sha(path) == expected_sha, 'input changed: ' + str(path))
    print(json.dumps({'status': 'PASS', 'graph_sha256': PINS[GRAPH],
                      'regs_source_sha256': PINS[REGS],
                      'circuit_source_sha256': lean_pins[CIRCUIT],
                      'syntax_source_sha256': lean_pins[SYNTAX],
                      'endpoint_source_sha256': lean_pins[ENDPOINT],
                      'graph_rows': len(graph['source']), 'lean_registers': len(fields),
                      'interned_nodes': len(keys),
                      'row_difference': 'trace76 + q4=q2*q2; P1mu2, mu2inner use q4 for XY',
                      'mutations_rejected': rejected,
                      'port_binding': 'same files, bits, hashes and tuple as trace75_degree402.json',
                      'comparison': 'exact structural normalization in commutative rings',
                      'scope': 'external restricted-fragment parser; no Lean theorem about file bytes'},
                     sort_keys=True))


if __name__ == '__main__':
    main()
