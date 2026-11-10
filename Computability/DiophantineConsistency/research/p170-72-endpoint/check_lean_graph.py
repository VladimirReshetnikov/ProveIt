#!/usr/bin/env python3
"""Bind the Lean literal of package 170's 13-positive 72/154 q⁴ residue carrier to its pinned JSON.

Usage (from anywhere): py -I -X utf8 -B check_lean_graph.py

The Lean circuit is `Q170Form72.value72` (`BFS943/Q170Syntax72.lean`), a
`let` chain over ports `p 0 .. p 3` and the unknowns `v 0 .. v 12`, read
in `Expr` by `Q170Form72.expression`. The endpoint
`BFS943/IPRAQuot170p72.lean` takes it at `fixedPorts`. This checker

* pins the SHA-256 of the JSON circuit, of package 170's
  `compact/COEFFICIENTS.json` and of package 163's `trace75_degree402.json`;
* checks the circuit metadata (witnesses in the Lean order, ports
  `beta, K0, MC, MF`, 72 operations, exact degree 154, output `output`, no dead
  rows), that the circuit's `coefficient_binding` raw hashes equal
  `COEFFICIENTS.json`'s, and that these are the direct-BFS943 raw hashes of the
  75 graph (`check_ports.py` binds the Lean ports to those);
* parses every `let` row and the output of `value72` into one interned DAG with
  the JSON rows, normalizing sums and products modulo commutative-ring
  associativity, commutativity, identities and additive inverses (no
  distribution, no sampling), and requires the outputs to be the same node;
  also the named rows listed in `ROWS`;
* rejects single-gate mutations of the Lean text;
* requires the literal and endpoint definitions verbatim and `fixedPorts`
  textually equal to `IPRATrace75`'s.

Finite external evidence for the transcription, not a Lean theorem about files.
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
PKG = D / 'con-zfc-diophantine-forms/170-quotient-carriers/compact'
GRAPH = PKG / 'fixed_13_residue_q4_72_degree154.json'
COEF = PKG / 'COEFFICIENTS.json'
GRAPH75 = D / 'con-zfc-diophantine-forms/163-trace-radical/compact/equations/trace75_degree402.json'
L = D / 'Lean/DiophantineConsistency'
CIRCUIT = L / 'BFS943/Q170Syntax72.lean'
ENDPOINT = L / 'BFS943/IPRAQuot170p72.lean'
ENDPOINT75 = L / 'BFS943/IPRATrace75.lean'
PINS = {GRAPH: '27c220078b955fa449bad0cb7278af56f6cf701fa286ec08bd2811a509f09b6e',
        COEF: '0fe6f62525317c4019e4ba234b90b3d5d259b9e1f1e2f58c1403e5f2a6649ced',
        GRAPH75: '8b9b9421ae8a0762725852034b3db6d29b14660b3a4d0587e1494a933b5271c9'}
RAW = {'K0': '0a86821a704294199c2e1a50379d242c96840a3366e9d965689ba3d74605203f',
       'MC': '6007cabd5f5228618e8fb613f386d8fc3692a24520d6e4cd72af0262aae1ade4',
       'MF': '48333b0d30a4edeb8579f44286cb59806c5622cb42b367f5b5f9ee827711c737',
       'beta': '0664a868cbfef9869ea05c40a1c445563f685ff857092594c1c1223bc4b21f9d'}
WITNESSES = ['J', 'F', 'alpha', 'z', 'f', 'n', 'i', 'T', 's', 'w', 'eta', 'zeta', 'gamma']
PORTS = ['beta', 'K0', 'MC', 'MF']
HEADER = 'def value72 (p : Fin 4 → R) (v : Fin 13 → R) : R :=\n'
ROWS = [('A', 'A'), ('c', 'c'), ('Delta', 'Delta'), ('D', 'main_root'), ('N1', 'N1'), ('R', 'R'), ('q4', 'carrier_q4'), ('t', 't'), ('Nt', 'Nt'), ('iA', 'iA'), ('S', 'S'), ('I', 'I'), ('Ns', 'Ns'), ('Q', 'Q'), ('V', 'V'), ('B', 'Eprod')]
MUTATIONS = [
    ('first radicand offset', '  let A := ell * (ell + k) + 1\n',
     '  let A := ell * (ell + k) + 2\n'),
    ('H offset', '  let H := 4 * a + 3\n',
     '  let H := 4 * a + 1\n'),
    ('transport sign', '  let Nt := (p 1 + w) * C + qF - z * qm\n',
     '  let Nt := (p 1 + w) * C + qF + z * qm\n'),
    ('Q uses f2', '  let Q := Delta * (f2 - 1)\n',
     '  let Q := Delta * f2\n'),
    ('auxiliary sign', '  let B := Q * (t2 - A * (V * V)) - t2 + A\n',
     '  let B := Q * (t2 + A * (V * V)) - t2 + A\n'),
    ('auxiliary weight 1', '  let B := Q * (t2 - A * (V * V)) - t2 + A\n',
     '  let B := Q * (t2 - V * V) - t2 + A\n'),
    ('unit factor 2B+1', '  N1 * Nt * (3 * B + 1) * Ns - 1\n',
     '  N1 * Nt * (2 * B + 1) * Ns - 1\n'),
    ('strong norm S*S', '  let Ns := f2 - I * S\n',
     '  let Ns := f2 - S * S\n'),
    ('rank sign in V', '  let V := f2 * (c * T - R) - c\n',
     '  let V := f2 * (c * T + R) - c\n'),
    ('main norm c', '  let N1 := D * D - Dc2\n',
     '  let N1 := D * D - c2\n'),
    ('carrier sign', '  let t := q4 * n - k + R\n',
     '  let t := q4 * n + k + R\n'),
    ('carrier modulus q^3', '  let q4 := q2 * q2\n',
     '  let q4 := q2 * q\n'),
    ('multiplier q', '  let iA := q2 * i * A\n',
     '  let iA := q * i * A\n'),
    ('multiplier drops A', '  let iA := q2 * i * A\n',
     '  let iA := q2 * i\n'),
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
    text = re.sub(r'\b([pv])\s+(\d+)\b', lambda m: m[1] + m[2], text)
    parsed = ast.parse(text.strip(), mode='eval')

    def visit(expr):
        if isinstance(expr, ast.Name):
            need(expr.id in env, 'unknown identifier: ' + expr.id)
            return env[expr.id]
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
            need(value in env, 'unknown JSON operand ' + str(value))
            return env[value]
        env[name] = operation(op, operand(left), operand(right))
    return env


def lean_value(text):
    need(text.count(HEADER) == 1, 'value header')
    body = text.split(HEADER, 1)[1].split('\n\n', 1)[0]
    lines = body.split('\n')
    env = {'p%d' % i: symbol(n) for i, n in enumerate(PORTS)}
    env.update({'v%d' % i: symbol(n) for i, n in enumerate(WITNESSES)})
    lets = {}
    for st in lines[:-1]:
        m = re.fullmatch(r'  let ([A-Za-z][A-Za-z0-9_]*) := (.+)', st)
        need(m is not None and m[1] not in env and m[1] not in lets, 'let row ' + st)
        lets[m[1]] = env[m[1]] = parse_expression(m[2], env)
    need(lines[-1].startswith('  ') and ':=' not in lines[-1], 'output row')
    return lets, parse_expression(lines[-1], env)


def main():
    for path, expected in PINS.items():
        need(sha(path) == expected, 'input pin: ' + str(path))
    lean_pins = {path: sha(path) for path in (CIRCUIT, ENDPOINT, ENDPOINT75)}
    graph = json.loads(GRAPH.read_text(encoding='utf8'))
    coef = json.loads(COEF.read_text(encoding='utf8'))
    graph75 = json.loads(GRAPH75.read_text(encoding='utf8'))
    need(graph['witnesses'] == WITNESSES and graph['fixed_numerals'] == PORTS and
         len(graph['source']) == graph['operations'] == 72 and graph['exact_degree'] == 154 and
         graph['output'] == 'output' and graph['domain'] == 'strictly positive integers',
         'graph metadata')
    used = {x for row in graph['source'] for x in row[2:] if isinstance(x, str)}
    need(all(row[0] in used for row in graph['source'] if row[0] != 'output'), 'dead JSON row')
    gports = {k: graph['coefficient_binding']['ports'][k]['raw_sha256'] for k in RAW}
    need(gports == RAW, 'circuit raw hashes are not the direct-BFS943 ones')
    need({k: coef['ports'][k]['raw_sha256'] for k in RAW} == RAW, 'COEFFICIENTS.json raw hashes')
    need({k: graph75['coefficient_binding']['ports'][k]['raw_sha256'] for k in RAW} == RAW,
         'trace75 raw hashes')

    text = CIRCUIT.read_text(encoding='utf8')
    J = json_registers(graph)
    lets, value = lean_value(text)
    need(value == J['output'], 'Lean and JSON outputs differ after ring normalization')
    for lean_name, json_name in ROWS:
        need(lets[lean_name] == J[json_name], 'row differs: ' + lean_name)
    rejected = []
    for label, old, new in MUTATIONS:
        need(text.count(old) == 1, 'mutation anchor: ' + label)
        _, mutated = lean_value(text.replace(old, new))
        need(mutated != J['output'], 'mutation accepted: ' + label)
        rejected.append(label)

    need('def ports (p : Fin 4 → ℤ) : Fin 4 → Expr (Fin 13) := fun j => .constant (p j)\n'
         in text, 'literal ports definition')
    need('def expression (p : Fin 4 → ℤ) : Expr (Fin 13) := value72 (ports p) Expr.var\n'
         in text, 'literal expression definition')
    need('def literal (p : Fin 4 → ℕ) : Expr (Fin 13) :=\n'
         '  Q170Form72.expression (fun j => (p j : ℤ))\n' in text, 'literal definition')
    endpoint = ENDPOINT.read_text(encoding='utf8')
    ports_text = ('def fixedPorts : Fin 4 → ℕ :=\n'
                  '  CompactSymbolicPorts.ports CompactFixedBeta.betaNat\n'
                  '    (DirectBFSSymbolicKernel.paramKernel CompactSymbolicKernel.rho)\n'
                  '    CompactSymbolicPorts.lowNat CompactSymbolicPorts.highNat\n')
    need(ports_text in endpoint and ports_text in ENDPOINT75.read_text(encoding='utf8'),
         'fixedPorts differs from IPRATrace75')
    need('def expression : Expr (Fin 13) := Q170Syntax72.literal fixedPorts\n' in endpoint,
         'endpoint expression')
    need('theorem expression_def :\n'
         '    expression = Q170Form72.expression (fun j => (fixedPorts j : ℤ)) := rfl\n'
         in endpoint, 'endpoint expression_def')
    for path, expected in list(PINS.items()) + list(lean_pins.items()):
        need(sha(path) == expected, 'input changed: ' + str(path))
    print(json.dumps({'status': 'PASS', 'graph_sha256': PINS[GRAPH],
                      'coefficients_sha256': PINS[COEF], 'graph75_sha256': PINS[GRAPH75],
                      'circuit_source_sha256': lean_pins[CIRCUIT],
                      'endpoint_source_sha256': lean_pins[ENDPOINT],
                      'graph_rows': len(graph['source']), 'lean_lets': len(lets),
                      'interned_nodes': len(keys),
                      'rows_compared': [r[0] for r in ROWS],
                      'mutations_rejected': rejected,
                      'port_binding': 'circuit and COEFFICIENTS.json raw hashes equal to '
                                      'trace75_degree402.json; endpoint fixedPorts textually '
                                      'equal to IPRATrace75',
                      'raw_sha256': RAW,
                      'comparison': 'exact structural normalization in commutative rings',
                      'scope': 'external restricted-fragment parser; no Lean theorem about file bytes'},
                     sort_keys=True, indent=1))


if __name__ == '__main__':
    main()
