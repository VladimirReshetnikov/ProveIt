#!/usr/bin/env python3
"""Bind the Lean Carrier65 literal at the direct-BFS943 ports to its JSON circuit.

Usage (from anywhere): py -I -X utf8 -B check_lean_graph.py

The Lean polynomial is `ObjectCurrentEquation2011.expressionAt`
(`Lean/DiophantineConsistency/CurrentEquationSyntax2011.lean`), a literal
`Expr (Fin 14)` over port constants `p 0 .. p 3`. The endpoint
`BFS943/IPRACarrier65BFS943.lean` takes it at `fixedPorts`. This checker

* pins the SHA-256 of package 183's `equation/carrier65.json` (the Carrier65
  circuit), of package 163's `trace75_degree402.json` (the direct-BFS943 port
  binding) and of package 170's `compact/COEFFICIENTS.json`;
* checks the circuit metadata (fourteen witnesses in the Lean coordinate
  order, ports `beta, K0, MC, MF`, 65 operations, exact degree 150, no dead
  rows) and that package 170's four raw port hashes are the direct-BFS943
  hashes of the 75 graph;
* parses `expressionAt` (every `let` row and the output) and the JSON rows into
  one interned DAG, normalizing sums and products modulo commutative-ring
  associativity, commutativity, identities and additive inverses (no
  distribution, no sampling), and requires the outputs to be the same node;
  also the rows `R`, `tau`, `N0` (first norm), `N1` (main norm), `Nt`
  (transport), `V`, `normalized_S`, `Na` (auxiliary norm) and `scaled_Ns`;
* rejects single-gate mutations of the Lean text;
* requires `fixedPorts` in the endpoint to be textually that of
  `IPRATrace75`, and the endpoint `expression` / `expression_def` verbatim, so
  `reviews/bfs943-source-promotion/tools/check_ports.py` covers the ports.

The circuit file carries the admissible942 coefficient tuple of package 183;
only its arithmetic program is compared here. The endpoint's ports are the
direct-BFS943 ones. Finite external evidence for the transcription, not a
Lean theorem about files.
"""
from hashlib import sha256
import ast
import json
from pathlib import Path
import re
import sys

if sys.flags.optimize:
    raise SystemExit('optimized Python refused')
H = Path(__file__).resolve().parent
D = H.parents[1]
GRAPH = D / 'con-zfc-diophantine-forms/183-pell-carrier65/equation/carrier65.json'
GRAPH75 = D / 'con-zfc-diophantine-forms/163-trace-radical/compact/equations/trace75_degree402.json'
COEF170 = D / 'con-zfc-diophantine-forms/170-quotient-carriers/compact/COEFFICIENTS.json'
L = D / 'Lean/DiophantineConsistency'
SYNTAX = L / 'CurrentEquationSyntax2011.lean'
ENDPOINT = L / 'BFS943/IPRACarrier65BFS943.lean'
ENDPOINT75 = L / 'BFS943/IPRATrace75.lean'
PINS = {GRAPH: 'bf58ed6600eee34d86a802a992e3fd9b999e1835b57a5a83734a40073e1658a7',
        GRAPH75: '8b9b9421ae8a0762725852034b3db6d29b14660b3a4d0587e1494a933b5271c9',
        COEF170: '0fe6f62525317c4019e4ba234b90b3d5d259b9e1f1e2f58c1403e5f2a6649ced'}
RAW = {'K0': '0a86821a704294199c2e1a50379d242c96840a3366e9d965689ba3d74605203f',
       'MC': '6007cabd5f5228618e8fb613f386d8fc3692a24520d6e4cd72af0262aae1ade4',
       'MF': '48333b0d30a4edeb8579f44286cb59806c5622cb42b367f5b5f9ee827711c737',
       'beta': '0664a868cbfef9869ea05c40a1c445563f685ff857092594c1c1223bc4b21f9d'}
WITNESSES = ['J', 'F', 'alpha', 'z', 'f', 'i', 'T', 's', 'w', 'n', 'eta', 'zeta', 'y', 'gamma']
PORTS = ['beta', 'K0', 'MC', 'MF']
HEADER = 'def expressionAt (p : Fin 4 → ℤ) : Expr (Fin 14) :=\n'
MUTATIONS = [
    ('H offset', '  let H := 4 * a + 3\n', '  let H := 4 * a + 1\n'),
    ('Delta square', '  let delta := a ^ 2 + H\n', '  let delta := a ^ 3 + H\n'),
    ('first parameter uses X', '  let ell := E * k * Y\n', '  let ell := E * k * X\n'),
    ('strip uses zeta', '  let c := k * Y + eta\n', '  let c := k * Y + zeta\n'),
    ('carrier sign', '  let tau := E * n + k - rank\n', '  let tau := E * n - k - rank\n'),
    ('auxiliary rank sign', '  let V := f ^ 2 * (c * T - rank) - c\n', '  let V := f ^ 2 * (c * T + rank) - c\n'),
    ('normalized multiplier c^3', '  let S := i * delta * c ^ 2\n', '  let S := i * delta * c ^ 3\n'),
    ('auxiliary norm sign', '  let U := S ^ 2 * (V ^ 2 - y ^ 2) + y ^ 2\n', '  let U := S ^ 2 * (V ^ 2 + y ^ 2) + y ^ 2\n'),
    ('transport quotient sign', '  let W := (Expr.constant (p 1) + w) * C + (q - F) - z * b\n',
     '  let W := (Expr.constant (p 1) + w) * C + (q - F) + z * b\n'),
    ('scaled strong norm', '  let Z := delta * f ^ 2 - S ^ 2\n', '  let Z := delta * f ^ 2 - S ^ 3\n'),
    ('output offset', '  P * Q * U * W * Z - delta\n', '  P * Q * U * W * Z - 1\n'),
    ('mask port order', '(Expr.constant (p 2) + q * Expr.constant (p 3)) * J',
     '(Expr.constant (p 3) + q * Expr.constant (p 2)) * J'),
]


def need(condition, message):
    if not condition:
        raise RuntimeError(message)


def sha(path):
    return sha256(path.read_bytes()).hexdigest()


keys, ids = [], {}


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
    terms, constant = {}, 0
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
    terms = tuple(sorted((t, c) for t, c in terms.items() if c))
    if not terms:
        return number(constant)
    if constant == 0 and len(terms) == 1 and terms[0][1] == 1:
        return terms[0][0]
    return node(('add', constant, terms))


def mul(a, b):
    factors, constant = [], 1
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


def parse_expression(text, env):
    text = re.sub(r'Expr\.constant\s*\(\s*p\s+(\d)\s*\)', lambda m: 'PORT' + m[1], text)
    text = text.replace('^', '**')
    parsed = ast.parse(text.strip(), mode='eval')

    def visit(expr):
        if isinstance(expr, ast.Name):
            need(expr.id in env, 'unknown identifier: ' + expr.id)
            return env[expr.id]
        if isinstance(expr, ast.Constant) and type(expr.value) is int and expr.value >= 0:
            return number(expr.value)
        if isinstance(expr, ast.BinOp) and isinstance(expr.op, ast.Pow):
            need(isinstance(expr.right, ast.Constant) and type(expr.right.value) is int and
                 1 <= expr.right.value <= 8, 'unsupported power')
            base = visit(expr.left)
            out = base
            for _ in range(expr.right.value - 1):
                out = mul(out, base)
            return out
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
            need(value in env, 'unknown JSON operand ' + str(value))
            return env[value]
        env[name] = operation(op, operand(left), operand(right))
    return env


def lean_value(text):
    need(text.count(HEADER) == 1, 'expressionAt header')
    body = text.split(HEADER, 1)[1].split('\n\n', 1)[0]
    lines = []
    for line in body.split('\n'):
        if line.startswith('    ') and lines:
            lines[-1] += ' ' + line.strip()
        else:
            lines.append(line)
    env = {'PORT%d' % i: symbol(n) for i, n in enumerate(PORTS)}
    lets = {}
    for st in lines[:-1]:
        m = re.fullmatch(r'  let ([A-Za-z][A-Za-z0-9_]*) : Expr \(Fin 14\) := \.var (\d+)', st)
        if m:
            need(m[1] not in env and WITNESSES[int(m[2])] == m[1], 'variable row ' + st)
            env[m[1]] = symbol(WITNESSES[int(m[2])])
            continue
        m = re.fullmatch(r'  let ([A-Za-z][A-Za-z0-9_]*) := (.+)', st)
        need(m is not None and m[1] not in env, 'let row ' + st)
        env[m[1]] = parse_expression(m[2], env)
        lets[m[1]] = env[m[1]]
    need(lines[-1].startswith('  ') and ':=' not in lines[-1], 'output row')
    return lets, parse_expression(lines[-1], env)


def main():
    for path, expected in PINS.items():
        need(sha(path) == expected, 'input pin: ' + str(path))
    lean_pins = {path: sha(path) for path in (SYNTAX, ENDPOINT, ENDPOINT75)}
    graph = json.loads(GRAPH.read_text(encoding='utf8'))
    graph75 = json.loads(GRAPH75.read_text(encoding='utf8'))
    coef = json.loads(COEF170.read_text(encoding='utf8'))
    need(graph['witnesses'] == WITNESSES and graph['fixed_numerals'] == PORTS and
         len(graph['source']) == graph['operations'] == 65 and graph['exact_degree'] == 150 and
         graph['output'] == 'polynomial' and graph['witness_domain'] == 'strictly positive integers',
         'graph metadata')
    used = {x for row in graph['source'] for x in row[2:] if isinstance(x, str)}
    need(all(row[0] in used for row in graph['source'] if row[0] != graph['output']), 'dead JSON row')
    need({k: graph75['coefficient_binding']['ports'][k]['raw_sha256'] for k in RAW} == RAW,
         'direct-BFS943 raw hashes (75 graph)')
    need({k: coef['ports'][k]['raw_sha256'] for k in RAW} == RAW,
         'package 170 raw hashes differ from the direct-BFS943 ones')

    text = SYNTAX.read_text(encoding='utf8')
    J = json_registers(graph)
    lets, value = lean_value(text)
    need(value == J[graph['output']], 'Lean and JSON outputs differ after ring normalization')
    rows = [('rank', 'R'), ('tau', 'tau'), ('P', 'N0'), ('Q', 'N1'), ('W', 'Nt'), ('V', 'V'),
            ('S', 'normalized_S'), ('U', 'Na'), ('Z', 'scaled_Ns'), ('delta', 'Delta')]
    for lean_name, json_name in rows:
        need(lets[lean_name] == J[json_name], 'row differs: ' + lean_name)
    rejected = []
    for label, old, new in MUTATIONS:
        need(text.count(old) == 1, 'mutation anchor: ' + label)
        _, mutated = lean_value(text.replace(old, new))
        need(mutated != J[graph['output']], 'mutation accepted: ' + label)
        rejected.append(label)

    endpoint = ENDPOINT.read_text(encoding='utf8')
    ports_text = ('def fixedPorts : Fin 4 → ℕ :=\n'
                  '  CompactSymbolicPorts.ports CompactFixedBeta.betaNat\n'
                  '    (DirectBFSSymbolicKernel.paramKernel CompactSymbolicKernel.rho)\n'
                  '    CompactSymbolicPorts.lowNat CompactSymbolicPorts.highNat\n')
    need(ports_text in endpoint and ports_text in ENDPOINT75.read_text(encoding='utf8'),
         'fixedPorts differs from IPRATrace75')
    need('def expression : Expr (Fin 14) := ObjectCurrentEquation2011.expressionAt '
         '(fun j => (fixedPorts j : ℤ))\n' in endpoint, 'endpoint expression')
    need('theorem expression_def :\n'
         '    expression = ObjectCurrentEquation2011.expressionAt (fun j => (fixedPorts j : ℤ)) := rfl\n'
         in endpoint, 'endpoint expression_def')
    for path, expected in list(PINS.items()) + list(lean_pins.items()):
        need(sha(path) == expected, 'input changed: ' + str(path))
    print(json.dumps({'status': 'PASS', 'graph_sha256': PINS[GRAPH],
                      'graph75_sha256': PINS[GRAPH75],
                      'coefficients170_sha256': PINS[COEF170],
                      'syntax_source_sha256': lean_pins[SYNTAX],
                      'endpoint_source_sha256': lean_pins[ENDPOINT],
                      'graph_rows': len(graph['source']), 'lean_lets': len(lets),
                      'interned_nodes': len(keys),
                      'rows_compared': [r[0] for r in rows],
                      'mutations_rejected': rejected,
                      'port_binding': 'endpoint fixedPorts textually equal to IPRATrace75; '
                                      'package 170 raw hashes equal to trace75_degree402.json',
                      'raw_sha256': RAW,
                      'comparison': 'exact structural normalization in commutative rings',
                      'scope': 'external restricted-fragment parser; no Lean theorem about file bytes'},
                     sort_keys=True, indent=1))


if __name__ == '__main__':
    main()
