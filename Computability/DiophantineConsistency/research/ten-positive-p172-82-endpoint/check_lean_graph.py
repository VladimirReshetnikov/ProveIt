#!/usr/bin/env python3
"""Bind the Lean literal of package 172's 82/240 free-plain circuit to its pinned JSON.

Usage (from anywhere): py -I -X utf8 -B check_lean_graph.py

The Lean circuit is `TenPositiveTrace82.value82` (BFS943/Trace82Regs.lean):
the register map `regsAtC p v X Y W c` (the 75 register map with the chart
coordinates, the transport base and the strip value `c` as parameters) at the
free-plain instance `X = q (q w)`, `Y = q s` (the Pell scale `λ = q` times
`s`), `W = q w`, `c = (η + ζ) s + η`, with the 82 denominator `D = q⁷`,
carrier `Z` and multiplier `M` set by a structure update. This checker

* pins the SHA-256 of the 82 JSON graph, of the 75 JSON graph (for the port
  binding), of `TenPositiveTrace75.lean` and of `Trace79Regs.lean`;
* checks the graph metadata (`free_plain`, `q^7`, 82 operations, degree 240,
  weight `bV`, every row used once by construction of the DAG);
* checks that the body of `regsAtC` is the body of
  `TenPositiveTrace79.regsAt` with the unused `w` let and the `c` let removed
  (so `c` is the only new parameter), and that `regsAt` is the parameterized
  `TenPositiveTrace75.regs`, exactly as in the 80 record;
* parses `regsAtC`, the 82 instance and structure update in `regs`, and the
  body of `value82`, and the JSON rows, into one interned DAG, normalizing
  sums and products modulo commutative-ring associativity, commutativity,
  identities and additive inverses (no distribution, no sampling), and
  requires the two outputs to be the same node (also the rows `X`, `qY`, `c`,
  `D`, `Bt`, `Znum`, `Mtot` individually);
* rejects five mutations of `regs` (denominator `q⁶`, strip `c = k q s + η`,
  Pell scale `λ = 1`, transport base `w`, sign of the `q⁴ s` correction);
* requires the literal and endpoint definitions to read `value82` at the
  ports `CompactSymbolicPorts.ports betaNat (paramKernel rho) lowNat highNat`,
  verbatim as in `IPRATrace75`, and the JSON `coefficient_binding` to equal
  the 75 graph's in every port field (only the relative `path` differs), with
  the direct-BFS943 raw hashes, so
  `reviews/bfs943-source-promotion/tools/check_ports.py` covers 82 too.

It is finite external evidence for the transcription, not a Lean theorem
about files, and it reuses the normalizer of
`research/ten-positive-trace80-endpoint/check_lean_graph.py`.
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
GRAPH = (D / 'con-zfc-diophantine-forms/172-pooled-powers-round21/part2/'
         'ConZFC_Pooled_Powers_Round21_2026-10-25/scalar/positive10/positive10_degree240_ops82.json')
GRAPH75 = D / 'con-zfc-diophantine-forms/163-trace-radical/compact/equations/trace75_degree402.json'
L = D / 'Lean/DiophantineConsistency'
REGS75 = L / 'TenPositiveTrace75.lean'
REGSAT = L / 'BFS943/Trace79Regs.lean'
CIRCUIT = L / 'BFS943/Trace82Regs.lean'
SYNTAX = L / 'BFS943/Trace82Syntax.lean'
ENDPOINT = L / 'BFS943/IPRATrace82.lean'
ENDPOINT75 = L / 'BFS943/IPRATrace75.lean'
PINS = {GRAPH: 'ea786ee1762b59332cf45ab9d1e280d0c68c5c244ee75437e0151b77a5ee3e02',
        GRAPH75: '8b9b9421ae8a0762725852034b3db6d29b14660b3a4d0587e1494a933b5271c9',
        REGS75: '0df718ab69ae7aef32dd341ee355ea2e21214e97fbea225af8816519fe383db9',
        REGSAT: 'e5ce1cc341749207edd6546835afc02a61a7d6225a2c73d06f0e430e524a63f9'}
RAW = {'K0': '0a86821a704294199c2e1a50379d242c96840a3366e9d965689ba3d74605203f',
       'MC': '6007cabd5f5228618e8fb613f386d8fc3692a24520d6e4cd72af0262aae1ade4',
       'MF': '48333b0d30a4edeb8579f44286cb59806c5622cb42b367f5b5f9ee827711c737',
       'beta': '0664a868cbfef9869ea05c40a1c445563f685ff857092594c1c1223bc4b21f9d'}
WITNESSES = ['J', 'F', 'alpha', 'i', 'T', 'w', 's', 'n', 'eta', 'zeta']
PORTS = ['beta', 'K0', 'MC', 'MF']
MUTATIONS = [
    ('denominator q^6', '  let D := r.q * r.q * (r.q * r.q) * (r.q * r.q) * r.q\n',
     '  let D := r.q * r.q * (r.q * r.q) * (r.q * r.q)\n'),
    ('strip c = k q s + eta', ' ((v 8 + v 9) * v 6 + v 8)\n', ' ((v 8 + v 9) * ((p 0 * v 0 + 1) * v 6) + v 8)\n'),
    ('Pell scale 1', ' ((p 0 * v 0 + 1) * v 6)\n    ((p 0 * v 0 + 1) * v 5)', ' (v 6)\n    ((p 0 * v 0 + 1) * v 5)'),
    ('transport base w', '\n    ((p 0 * v 0 + 1) * v 5) ((v 8', '\n    (v 5) ((v 8'),
    ('correction sign', '(r.e - r.q * r.q * (r.q * r.q) * v 6)', '(r.e + r.q * r.q * (r.q * r.q) * v 6)'),
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


def top_split(text, sep):
    parts, depth, cur = [], 0, ''
    for ch in text:
        if ch in '({[':
            depth += 1
        elif ch in ')}]':
            depth -= 1
        if ch == sep and depth == 0:
            parts.append(cur)
            cur = ''
        else:
            cur += ch
    parts.append(cur)
    return parts


def call_args(text):
    """The parenthesized arguments `(a) (b) (c)` of a call, in order."""
    args, depth, cur = [], 0, ''
    for ch in text:
        if ch == '(':
            if depth > 0:
                cur += ch
            depth += 1
        elif ch == ')':
            depth -= 1
            if depth == 0:
                args.append(cur)
                cur = ''
            else:
                cur += ch
        elif depth > 0:
            cur += ch
    return args


def body_of(text, header):
    return text.split(header, 1)[1].split('\n\n', 1)[0]


REGSAT_HEADER = 'def regsAt (p : Fin 4 → R) (v : Fin 10 → R) (X Y W : R) : Regs R :=\n'
REGSATC_HEADER = 'def regsAtC (p : Fin 4 → R) (v : Fin 10 → R) (X Y W c : R) : Regs R :=\n'


def lean_value(circuit, fields):
    """Interned output of `value82` read from the module text `circuit`."""
    body = body_of(circuit, REGSATC_HEADER)
    local_lines, record = body.split('\n  { ', 1)
    need(record.endswith(' }'), 'regsAtC record shape')
    regs_def = body_of(circuit, 'def regs (p : Fin 4 → R) (v : Fin 10 → R) : Regs R :=\n')
    lines = regs_def.split('\n')
    need(lines[1].startswith('    (') and not lines[2].startswith('    ('), 'regs instance continuation')
    lines = [lines[0] + lines[1][3:]] + lines[2:]
    need(lines[0].startswith('  let r := regsAtC p v '), 'regs instance line')
    args = call_args(lines[0][len('  let r := regsAtC p v '):])
    need(len(args) == 4, 'regsAtC instance arguments')
    env = {f'v{i}': symbol(n) for i, n in enumerate(WITNESSES)}
    env.update({f'p{i}': symbol(n) for i, n in enumerate(PORTS)})
    inst = {name: parse_expression(arg, env) for name, arg in zip(['X', 'Y', 'W', 'c'], args)}
    env.update(inst)
    for line in local_lines.splitlines():
        match = re.fullmatch(r'  let ([A-Za-z][A-Za-z0-9_]*) := (.+)', line)
        need(match is not None and match[1] not in env, 'unexpected regsAtC let')
        env[match[1]] = parse_expression(match[2], env)
    assignments = {}
    for item in re.split(r',\s*', record[:-2]):
        parts = item.split(' := ')
        need(len(parts) in (1, 2), 'unexpected regsAtC record entry')
        field = parts[0]
        need(field in fields and field not in assignments, 'unknown or duplicate field')
        assignments[field] = parse_expression(parts[1] if len(parts) == 2 else field, env)
    need(set(assignments) == set(fields), 'missing regsAtC record field')
    renv = {'r_' + name: value for name, value in assignments.items()}
    renv.update({f'v{i}': symbol(n) for i, n in enumerate(WITNESSES)})
    rest = '\n'.join(lines[1:])
    head, update = rest.split('\n  { r with ', 1)
    for line in head.splitlines():
        match = re.fullmatch(r'  let ([A-Za-z][A-Za-z0-9_]*) := (.+)', line)
        need(match is not None and match[1] not in renv, 'unexpected regs let')
        renv[match[1]] = parse_expression(match[2], renv)
    need(set(renv) - set('r_' + f for f in fields) - {f'v{i}' for i in range(10)} == {'D', 'L'},
         'regs lets')
    need(update.endswith(' }'), 'structure update shape')
    final = dict(assignments)
    for item in top_split(' '.join(update[:-2].split()), ','):
        parts = item.split(' := ')
        need(len(parts) == 2 and parts[0].strip() in ('D', 'Z', 'M'), 'unexpected update entry')
        final[parts[0].strip()] = parse_expression(parts[1], renv)
    need(len(final) == len(fields), 'update fields')
    vbody = body_of(circuit, 'def value82 (p : Fin 4 → R) (v : Fin 10 → R) : R :=\n')
    vlines = vbody.splitlines()
    need(vlines[0] == '  let r := regs p v', 'unexpected value82 body')
    venv = {'r_' + name: value for name, value in final.items()}
    value = parse_expression(' '.join(x.strip() for x in vlines[1:]), venv)
    return final, value


def main():
    for path, expected in PINS.items():
        need(sha(path) == expected, 'input pin: ' + str(path))
    lean_pins = {path: sha(path) for path in (CIRCUIT, SYNTAX, ENDPOINT)}
    graph = json.loads(GRAPH.read_text(encoding='utf8'))
    graph75 = json.loads(GRAPH75.read_text(encoding='utf8'))
    need(graph['witnesses'] == WITNESSES and graph['fixed_numerals'] == PORTS and
         len(graph['source']) == graph['operations'] == 82 and graph['exact_degree'] == 240 and
         graph['transport_weight'] == 'bV' and graph['mode'] == 'free_plain' and
         graph['denominator'] == 'q^7' and graph['output'] == 'N', 'graph metadata')
    binding, binding75 = graph['coefficient_binding'], graph75['coefficient_binding']
    need({k: v for k, v in binding.items() if k != 'path'} ==
         {k: v for k, v in binding75.items() if k != 'path'}, 'port binding differs from 75')
    need({k: binding['ports'][k]['raw_sha256'] for k in RAW} == RAW, 'direct-BFS943 raw hashes')
    used = {x for row in graph['source'] for x in row[2:] if isinstance(x, str)}
    need(all(row[0] in used for row in graph['source'] if row[0] != 'N'), 'dead JSON row')

    text75 = REGS75.read_text(encoding='utf8')
    decl = text75.split('structure Regs (R : Type*) where\n', 1)[1].split('\n/--', 1)[0]
    fields = re.findall(r'^  ([A-Za-z][A-Za-z0-9_]*) : R$', decl, re.M)
    need(len(fields) == 27 and len(set(fields)) == len(fields), 'Lean field inventory')
    body75 = body_of(text75, 'def regs (p : Fin 4 → R) (v : Fin 10 → R) : Regs R :=\n')
    regsat_text = REGSAT.read_text(encoding='utf8')
    expected_at = (body75.replace('  let Y := q * q * q * s\n', '').replace('  let X := w * q\n', '')
                   .replace('  let s := v 6\n', '')
                   .replace('  let B := (p 1 + w) * C - F\n', '  let B := (p 1 + W) * C - F\n'))
    need(body_of(regsat_text, REGSAT_HEADER) == expected_at,
         'regsAt is not the parameterized 75 register map')
    circuit = CIRCUIT.read_text(encoding='utf8')
    expected_atc = (body_of(regsat_text, REGSAT_HEADER).replace('  let w := v 5\n', '')
                    .replace('  let c := k * Y + eta\n', ''))
    need(body_of(circuit, REGSATC_HEADER) == expected_atc,
         'regsAtC is not regsAt with c as a parameter')

    json_env = json_registers(graph)
    final, value = lean_value(circuit, fields)
    need(value == json_env[graph['output']], 'Lean and JSON outputs differ after ring normalization')
    need(final['X'] == json_env['X'], 'row X differs')
    need(final['Y'] == json_env['qY'], 'row qY (register Y) differs')
    need(final['c'] == json_env['c'], 'strip row c differs')
    need(final['B'] == json_env['Bt'], 'transport row Bt differs')
    need(final['D'] == json_env['D'], 'denominator row D differs')
    need(final['Z'] == json_env['Znum'], 'carrier row Znum differs')
    need(final['M'] == json_env['Mtot'], 'multiplier row Mtot differs')
    rejected = []
    for label, old, new in MUTATIONS:
        need(circuit.count(old) == 1, 'mutation anchor: ' + label)
        _, mutated = lean_value(circuit.replace(old, new), fields)
        need(mutated != json_env[graph['output']], 'mutation accepted: ' + label)
        rejected.append(label)

    syntax = SYNTAX.read_text(encoding='utf8')
    need('def expression (p : Fin 4 → ℤ) : Expr (Fin 10) := value82 (ports p) Expr.var\n'
         in syntax, 'literal expression definition')
    need('def ports (p : Fin 4 → ℤ) : Fin 4 → Expr (Fin 10) := fun j => .constant (p j)\n'
         in syntax, 'literal ports definition')
    need('def literal (p : Fin 4 → ℕ) : Expr (Fin 10) :=\n'
         '  TenPositiveTrace82.expression (fun j => (p j : ℤ))\n' in syntax, 'literal definition')
    endpoint = ENDPOINT.read_text(encoding='utf8')
    ports_text = ('def fixedPorts : Fin 4 → ℕ :=\n'
                  '  CompactSymbolicPorts.ports CompactFixedBeta.betaNat\n'
                  '    (DirectBFSSymbolicKernel.paramKernel CompactSymbolicKernel.rho)\n'
                  '    CompactSymbolicPorts.lowNat CompactSymbolicPorts.highNat\n')
    need(ports_text in endpoint and ports_text in ENDPOINT75.read_text(encoding='utf8'),
         'fixedPorts differs from IPRATrace75')
    need('def expression : Expr (Fin 10) := Trace82BFSSyntax.literal fixedPorts\n' in endpoint,
         'endpoint expression')
    for path, expected_sha in PINS.items():
        need(sha(path) == expected_sha, 'input changed: ' + str(path))
    for path, expected_sha in lean_pins.items():
        need(sha(path) == expected_sha, 'input changed: ' + str(path))
    print(json.dumps({'status': 'PASS', 'graph_sha256': PINS[GRAPH],
                      'regs75_source_sha256': PINS[REGS75],
                      'regsAt_source_sha256': PINS[REGSAT],
                      'circuit_source_sha256': lean_pins[CIRCUIT],
                      'syntax_source_sha256': lean_pins[SYNTAX],
                      'endpoint_source_sha256': lean_pins[ENDPOINT],
                      'graph_rows': len(graph['source']), 'lean_registers': len(fields),
                      'interned_nodes': len(keys),
                      'regsAtC': 'TenPositiveTrace79.regsAt body with c as a parameter',
                      'instance': 'X=q(qw), Y=qs, W=qw, c=(eta+zeta)s+eta, D=q^7',
                      'mutations_rejected': rejected,
                      'port_binding': 'equal to trace75_degree402.json except the relative path',
                      'raw_sha256': RAW,
                      'comparison': 'exact structural normalization in commutative rings',
                      'scope': 'external restricted-fragment parser; no Lean theorem about file bytes'},
                     sort_keys=True))


if __name__ == '__main__':
    main()
