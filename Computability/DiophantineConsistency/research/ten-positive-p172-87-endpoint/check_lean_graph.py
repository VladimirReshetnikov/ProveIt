#!/usr/bin/env python3
"""Bind the Lean literal of package 172's 87/214 free-inverse circuit to its pinned JSON.

Usage (from anywhere): py -I -X utf8 -B check_lean_graph.py

The Lean circuit is `TenPositiveTrace87.value87` (BFS943/Trace87Regs.lean):
the register map `TenPositiveTrace82.regsAtC p v X Y W c` (BFS943/Trace82Regs.lean;
the 75 register map with the chart coordinates, the transport base and the
strip value `c` as parameters) at the free-inverse instance `X = q w`,
`Y = q s` (the Pell scale `lambda = q` times `s`), `W = w`,
`c = (eta + zeta) s + eta`, with the 87 denominator `D = 6 q^7`, the
inverse-Lucas offset `ecl = 6 (e - q^4 s) - X Y^2 k (k^2 - 4)`, carrier `Z`
and multiplier `M` set by a structure update. This checker

* pins the SHA-256 of the 87 JSON graph, of the 75 JSON graph (for the port
  binding), of `TenPositiveTrace75.lean`, `Trace79Regs.lean` and
  `Trace82Regs.lean`;
* checks the graph metadata (`free_inverse`, `6*q^7`, 87 operations, degree
  214, weight `bV`, no dead rows);
* checks that `regsAt` is the parameterized 75 register map and `regsAtC` is
  `regsAt` with `c` as a parameter, exactly as in the 82 record;
* parses `regsAtC`, the 87 instance, lets and structure update in `regs`, and
  the body of `value87`, and the JSON rows, into one interned DAG, normalizing
  sums and products modulo commutative-ring associativity, commutativity,
  identities and additive inverses (no distribution, no sampling), and
  requires the two outputs to be the same node (also the rows `X`, `qY`, `c`,
  `sixq7`, `eclear`, `Bt`, `Znum`, `Mtot` individually);
* rejects seven mutations of `regs` (denominator `q^7`, chart `X = q (q w)`,
  strip `c = k q s + eta`, Pell scale `lambda = 1`, transport base `q w`, sign
  of the `q^4 s` correction, sign of the inverse cubic);
* requires the literal and endpoint definitions to read `value87` at the
  ports `CompactSymbolicPorts.ports betaNat (paramKernel rho) lowNat highNat`,
  verbatim as in `IPRATrace75`, and the JSON `coefficient_binding` to equal
  the 75 graph's in every port field (only the relative `path` differs), with
  the direct-BFS943 raw hashes, so
  `reviews/bfs943-source-promotion/tools/check_ports.py` covers 87 too.

It is finite external evidence for the transcription, not a Lean theorem
about files, and it reuses the normalizer of
`research/ten-positive-p172-82-endpoint/check_lean_graph.py`.
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
         'ConZFC_Pooled_Powers_Round21_2026-10-25/scalar/positive10/positive10_degree214_ops87.json')
GRAPH75 = D / 'con-zfc-diophantine-forms/163-trace-radical/compact/equations/trace75_degree402.json'
L = D / 'Lean/DiophantineConsistency'
REGS75 = L / 'TenPositiveTrace75.lean'
REGSAT = L / 'BFS943/Trace79Regs.lean'
REGSATC = L / 'BFS943/Trace82Regs.lean'
CIRCUIT = L / 'BFS943/Trace87Regs.lean'
SYNTAX = L / 'BFS943/Trace87Syntax.lean'
ENDPOINT = L / 'BFS943/IPRATrace87.lean'
ENDPOINT75 = L / 'BFS943/IPRATrace75.lean'
PINS = {GRAPH: '6af0c97120fefba17920dbb517facc1d1ee403ad8388c8dee9523ee2e94b2449',
        GRAPH75: '8b9b9421ae8a0762725852034b3db6d29b14660b3a4d0587e1494a933b5271c9',
        REGS75: '0df718ab69ae7aef32dd341ee355ea2e21214e97fbea225af8816519fe383db9',
        REGSAT: 'e5ce1cc341749207edd6546835afc02a61a7d6225a2c73d06f0e430e524a63f9',
        REGSATC: '59abf251f248c84cbb425cda0d0952e5d9a82651e0a938eb494a94c97c130f8e'}
RAW = {'K0': '0a86821a704294199c2e1a50379d242c96840a3366e9d965689ba3d74605203f',
       'MC': '6007cabd5f5228618e8fb613f386d8fc3692a24520d6e4cd72af0262aae1ade4',
       'MF': '48333b0d30a4edeb8579f44286cb59806c5622cb42b367f5b5f9ee827711c737',
       'beta': '0664a868cbfef9869ea05c40a1c445563f685ff857092594c1c1223bc4b21f9d'}
WITNESSES = ['J', 'F', 'alpha', 'i', 'T', 'w', 's', 'n', 'eta', 'zeta']
PORTS = ['beta', 'K0', 'MC', 'MF']
MUTATIONS = [
    ('denominator q^7', '  let D := 6 * (r.q * r.q * (r.q * r.q) * (r.q * r.q) * r.q)\n',
     '  let D := (r.q * r.q * (r.q * r.q) * (r.q * r.q) * r.q)\n'),
    ('chart X = q (q w)', 'regsAtC p v ((p 0 * v 0 + 1) * v 5)',
     'regsAtC p v ((p 0 * v 0 + 1) * ((p 0 * v 0 + 1) * v 5))'),
    ('strip c = k q s + eta', ' ((v 8 + v 9) * v 6 + v 8)\n', ' ((v 8 + v 9) * ((p 0 * v 0 + 1) * v 6) + v 8)\n'),
    ('Pell scale 1', ' ((p 0 * v 0 + 1) * v 6)\n', ' (v 6)\n'),
    ('transport base q w', '\n    (v 5) ((v 8', '\n    ((p 0 * v 0 + 1) * v 5) ((v 8'),
    ('correction sign', '  let ecl := 6 * (r.e - r.q', '  let ecl := 6 * (r.e + r.q'),
    ('inverse cubic sign', 'v 6) - r.X * r.Y * r.Y * r.k * (r.k * r.k - 4)\n  { r with',
     'v 6) + r.X * r.Y * r.Y * r.k * (r.k * r.k - 4)\n  { r with'),
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
    """Interned output of `value87` read from the module texts."""
    body = body_of(REGSATC.read_text(encoding='utf8'), REGSATC_HEADER)
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
    need(set(renv) - set('r_' + f for f in fields) - {f'v{i}' for i in range(10)} == {'D', 'L', 'ecl'},
         'regs lets')
    need(update.endswith(' }'), 'structure update shape')
    final = dict(assignments)
    for item in top_split(' '.join(update[:-2].split()), ','):
        parts = item.split(' := ')
        need(len(parts) == 2 and parts[0].strip() in ('D', 'Z', 'M'), 'unexpected update entry')
        final[parts[0].strip()] = parse_expression(parts[1], renv)
    need(len(final) == len(fields), 'update fields')
    vbody = body_of(circuit, 'def value87 (p : Fin 4 → R) (v : Fin 10 → R) : R :=\n')
    vlines = vbody.splitlines()
    need(vlines[0] == '  let r := regs p v', 'unexpected value87 body')
    venv = {'r_' + name: value for name, value in final.items()}
    value = parse_expression(' '.join(x.strip() for x in vlines[1:]), venv)
    return final, renv['ecl'], value


def main():
    for path, expected in PINS.items():
        need(sha(path) == expected, 'input pin: ' + str(path))
    lean_pins = {path: sha(path) for path in (CIRCUIT, SYNTAX, ENDPOINT)}
    graph = json.loads(GRAPH.read_text(encoding='utf8'))
    graph75 = json.loads(GRAPH75.read_text(encoding='utf8'))
    need(graph['witnesses'] == WITNESSES and graph['fixed_numerals'] == PORTS and
         len(graph['source']) == graph['operations'] == 87 and graph['exact_degree'] == 214 and
         graph['transport_weight'] == 'bV' and graph['mode'] == 'free_inverse' and
         graph['denominator'] == '6*q^7' and graph['output'] == 'N', 'graph metadata')
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
    regsatc_text = REGSATC.read_text(encoding='utf8')
    expected_atc = (body_of(regsat_text, REGSAT_HEADER).replace('  let w := v 5\n', '')
                    .replace('  let c := k * Y + eta\n', ''))
    need(body_of(regsatc_text, REGSATC_HEADER) == expected_atc,
         'regsAtC is not regsAt with c as a parameter')

    json_env = json_registers(graph)
    final, ecl, value = lean_value(circuit, fields)
    need(value == json_env[graph['output']], 'Lean and JSON outputs differ after ring normalization')
    need(final['X'] == json_env['X'], 'row X differs')
    need(final['Y'] == json_env['qY'], 'row qY (register Y) differs')
    need(final['c'] == json_env['c'], 'strip row c differs')
    need(final['B'] == json_env['Bt'], 'transport row Bt differs')
    need(final['D'] == json_env['sixq7'], 'denominator row sixq7 differs')
    need(ecl == json_env['eclear'], 'inverse-Lucas offset row eclear differs')
    need(final['Z'] == json_env['Znum'], 'carrier row Znum differs')
    need(final['M'] == json_env['Mtot'], 'multiplier row Mtot differs')
    rejected = []
    for label, old, new in MUTATIONS:
        need(circuit.count(old) == 1, 'mutation anchor: ' + label)
        _, _, mutated = lean_value(circuit.replace(old, new), fields)
        need(mutated != json_env[graph['output']], 'mutation accepted: ' + label)
        rejected.append(label)

    syntax = SYNTAX.read_text(encoding='utf8')
    need('def expression (p : Fin 4 → ℤ) : Expr (Fin 10) := value87 (ports p) Expr.var\n'
         in syntax, 'literal expression definition')
    need('def ports (p : Fin 4 → ℤ) : Fin 4 → Expr (Fin 10) := fun j => .constant (p j)\n'
         in syntax, 'literal ports definition')
    need('def literal (p : Fin 4 → ℕ) : Expr (Fin 10) :=\n'
         '  TenPositiveTrace87.expression (fun j => (p j : ℤ))\n' in syntax, 'literal definition')
    endpoint = ENDPOINT.read_text(encoding='utf8')
    ports_text = ('def fixedPorts : Fin 4 → ℕ :=\n'
                  '  CompactSymbolicPorts.ports CompactFixedBeta.betaNat\n'
                  '    (DirectBFSSymbolicKernel.paramKernel CompactSymbolicKernel.rho)\n'
                  '    CompactSymbolicPorts.lowNat CompactSymbolicPorts.highNat\n')
    need(ports_text in endpoint and ports_text in ENDPOINT75.read_text(encoding='utf8'),
         'fixedPorts differs from IPRATrace75')
    need('def expression : Expr (Fin 10) := Trace87BFSSyntax.literal fixedPorts\n' in endpoint,
         'endpoint expression')
    for path, expected_sha in PINS.items():
        need(sha(path) == expected_sha, 'input changed: ' + str(path))
    for path, expected_sha in lean_pins.items():
        need(sha(path) == expected_sha, 'input changed: ' + str(path))
    print(json.dumps({'status': 'PASS', 'graph_sha256': PINS[GRAPH],
                      'regs75_source_sha256': PINS[REGS75],
                      'regsAt_source_sha256': PINS[REGSAT],
                      'regsAtC_source_sha256': PINS[REGSATC],
                      'circuit_source_sha256': lean_pins[CIRCUIT],
                      'syntax_source_sha256': lean_pins[SYNTAX],
                      'endpoint_source_sha256': lean_pins[ENDPOINT],
                      'graph_rows': len(graph['source']), 'lean_registers': len(fields),
                      'interned_nodes': len(keys),
                      'regsAtC': 'TenPositiveTrace79.regsAt body with c as a parameter',
                      'instance': 'X=qw, Y=qs, W=w, c=(eta+zeta)s+eta, D=6q^7, ecl=6(e-q^4 s)-XY^2 k(k^2-4)',
                      'mutations_rejected': rejected,
                      'port_binding': 'equal to trace75_degree402.json except the relative path',
                      'raw_sha256': RAW,
                      'comparison': 'exact structural normalization in commutative rings',
                      'scope': 'external restricted-fragment parser; no Lean theorem about file bytes'},
                     sort_keys=True))


if __name__ == '__main__':
    main()
