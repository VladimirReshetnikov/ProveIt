#!/usr/bin/env python3
"""Bind the Lean literal of package 171's 85/232 scaled inverse-Lucas circuit to its pinned JSON.

Usage (from anywhere): py -I -X utf8 -B check_lean_graph.py

The Lean circuit is `TenPositiveTrace85.value85` (BFS943/Trace85Regs.lean):
the register map `TenPositiveTrace79.regsAt p v X Y W` (BFS943/Trace79Regs.lean;
the 75 register map with the chart coordinates and the transport base as
parameters, scaled strip `c = k Y + eta`) at `X = q w`, `Y = q s`, `W = w`,
with the 85 denominator `D = 6 q^6`, the inverse-Lucas offset
`ecl = 6 (e - q^4 s) - X Y^2 k (k^2 - 4)`, carrier `Z` and multiplier `M` set
by a structure update. This checker

* pins the SHA-256 of package 171's `positive/equation_bV.json`, of package
  172's `positive10_degree232_ops85.json`, of the 75 JSON graph (port binding),
  of the 87 record's checker (whose parser and normalizer it imports) and of
  `TenPositiveTrace75.lean` and `Trace79Regs.lean`;
* checks that the two 85 JSON files are one polynomial on one tuple: equal
  `source` rows, witnesses, ports, output and metadata, and both port
  bindings equal to the 75 graph's except the relative `path` (171 also
  carries `endianness: little`), with the four direct-BFS943 raw hashes;
* checks the graph metadata (85 operations, degree 232, weight `bV`,
  denominator `6q6`, no dead rows) and that `regsAt` is the parameterized 75
  register map;
* parses `regsAt`, the 85 instance, lets and structure update in `regs`, and
  `value85` into one interned DAG with the JSON rows, normalizing modulo
  commutative-ring associativity, commutativity, identities and additive
  inverses (no distribution, no sampling), and requires the outputs to be the
  same node (also `X`, `Y`, `c`, `sixq6`, `eclear`, `Bt`, `Znum`, `Mtot`);
* rejects mutations (denominator `6 q^7`, denominator without `6`, chart
  `X = q (q w)`, Pell scale `1`, transport base `q w`, sign of the `q^4 s`
  correction, sign of the inverse cubic);
* requires the literal and endpoint definitions verbatim and `fixedPorts`
  textually the `IPRATrace75` one, so
  `reviews/bfs943-source-promotion/tools/check_ports.py` covers this circuit.

It is finite external evidence for the transcription, not a Lean theorem
about files.
"""
from hashlib import sha256
import importlib.util
import json
from pathlib import Path
import re
import sys

if sys.flags.optimize:
    raise SystemExit('optimized Python refused')
H = Path(__file__).resolve().parent
D = H.parents[1]
GRAPH = D / 'con-zfc-diophantine-forms/171-pooled-powers-separated-radicals/positive/equation_bV.json'
GRAPH172 = (D / 'con-zfc-diophantine-forms/172-pooled-powers-round21/part2/'
            'ConZFC_Pooled_Powers_Round21_2026-10-25/scalar/positive10/positive10_degree232_ops85.json')
GRAPH75 = D / 'con-zfc-diophantine-forms/163-trace-radical/compact/equations/trace75_degree402.json'
CHECK87 = D / 'research/ten-positive-p172-87-endpoint/check_lean_graph.py'
L = D / 'Lean/DiophantineConsistency'
REGS75 = L / 'TenPositiveTrace75.lean'
REGSAT = L / 'BFS943/Trace79Regs.lean'
CIRCUIT = L / 'BFS943/Trace85Regs.lean'
SYNTAX = L / 'BFS943/Trace85Syntax.lean'
ENDPOINT = L / 'BFS943/IPRATrace85.lean'
ENDPOINT75 = L / 'BFS943/IPRATrace75.lean'
PINS = {GRAPH: '3e6f51cb149d7731fafda8774afb73c2d372f4425f144cecbaf0fe574a400035',
        GRAPH172: 'f65b694edaf42689e472ce10815fd0b46ad17909c98ce996e247362d4090d08e',
        GRAPH75: '8b9b9421ae8a0762725852034b3db6d29b14660b3a4d0587e1494a933b5271c9',
        CHECK87: '322d05e923d8b2f49b34719abe7a29a34ee3aa3d012f5f60ebfedb68dc83aa3a',
        REGS75: '0df718ab69ae7aef32dd341ee355ea2e21214e97fbea225af8816519fe383db9',
        REGSAT: 'e5ce1cc341749207edd6546835afc02a61a7d6225a2c73d06f0e430e524a63f9'}
WITNESSES = ['J', 'F', 'alpha', 'i', 'T', 'w', 's', 'n', 'eta', 'zeta']
PORTS = ['beta', 'K0', 'MC', 'MF']
D6 = '  let D := 6 * (r.q * r.q * (r.q * r.q) * (r.q * r.q))\n'
MUTATIONS = [
    ('denominator 6 q^7', D6, '  let D := 6 * (r.q * r.q * (r.q * r.q) * (r.q * r.q) * r.q)\n'),
    ('denominator q^6', D6, '  let D := (r.q * r.q * (r.q * r.q) * (r.q * r.q))\n'),
    ('chart X = q (q w)', 'regsAt p v ((p 0 * v 0 + 1) * v 5)',
     'regsAt p v ((p 0 * v 0 + 1) * ((p 0 * v 0 + 1) * v 5))'),
    ('Pell scale 1', ' ((p 0 * v 0 + 1) * v 6)\n', ' (v 6)\n'),
    ('transport base q w', '\n    (v 5)\n', '\n    ((p 0 * v 0 + 1) * v 5)\n'),
    ('correction sign', '  let ecl := 6 * (r.e - r.q', '  let ecl := 6 * (r.e + r.q'),
    ('inverse cubic sign', 'v 6) - r.X * r.Y * r.Y * r.k * (r.k * r.k - 4)\n  { r with',
     'v 6) + r.X * r.Y * r.Y * r.k * (r.k * r.k - 4)\n  { r with'),
]
REGSAT_HEADER = 'def regsAt (p : Fin 4 → R) (v : Fin 10 → R) (X Y W : R) : Regs R :=\n'


def need(condition, message):
    if not condition:
        raise RuntimeError(message)


def sha(path):
    return sha256(path.read_bytes()).hexdigest()


def load87():
    spec = importlib.util.spec_from_file_location('check87', CHECK87)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def lean_value(c, circuit, fields):
    """Interned output of `value85` read from the module texts."""
    body = c.body_of(REGSAT.read_text(encoding='utf8'), REGSAT_HEADER)
    local_lines, record = body.split('\n  { ', 1)
    need(record.endswith(' }'), 'regsAt record shape')
    regs_def = c.body_of(circuit, 'def regs (p : Fin 4 → R) (v : Fin 10 → R) : Regs R :=\n')
    lines = regs_def.split('\n')
    need(lines[1].startswith('    (') and not lines[2].startswith('    ('), 'regs instance continuation')
    lines = [lines[0] + lines[1][3:]] + lines[2:]
    need(lines[0].startswith('  let r := regsAt p v '), 'regs instance line')
    args = c.call_args(lines[0][len('  let r := regsAt p v '):])
    need(len(args) == 3, 'regsAt instance arguments')
    env = {f'v{i}': c.symbol(n) for i, n in enumerate(WITNESSES)}
    env.update({f'p{i}': c.symbol(n) for i, n in enumerate(PORTS)})
    inst = {name: c.parse_expression(arg, env) for name, arg in zip(['X', 'Y', 'W'], args)}
    env.update(inst)
    for line in local_lines.splitlines():
        match = re.fullmatch(r'  let ([A-Za-z][A-Za-z0-9_]*) := (.+)', line)
        need(match is not None and match[1] not in env, 'unexpected regsAt let')
        env[match[1]] = c.parse_expression(match[2], env)
    assignments = {}
    for item in re.split(r',\s*', record[:-2]):
        parts = item.split(' := ')
        need(len(parts) in (1, 2), 'unexpected regsAt record entry')
        field = parts[0]
        need(field in fields and field not in assignments, 'unknown or duplicate field')
        assignments[field] = c.parse_expression(parts[1] if len(parts) == 2 else field, env)
    need(set(assignments) == set(fields), 'missing regsAt record field')
    renv = {'r_' + name: value for name, value in assignments.items()}
    renv.update({f'v{i}': c.symbol(n) for i, n in enumerate(WITNESSES)})
    rest = '\n'.join(lines[1:])
    head, update = rest.split('\n  { r with ', 1)
    for line in head.splitlines():
        match = re.fullmatch(r'  let ([A-Za-z][A-Za-z0-9_]*) := (.+)', line)
        need(match is not None and match[1] not in renv, 'unexpected regs let')
        renv[match[1]] = c.parse_expression(match[2], renv)
    need(set(renv) - set('r_' + f for f in fields) - {f'v{i}' for i in range(10)} == {'D', 'L', 'ecl'},
         'regs lets')
    need(update.endswith(' }'), 'structure update shape')
    final = dict(assignments)
    for item in c.top_split(' '.join(update[:-2].split()), ','):
        parts = item.split(' := ')
        need(len(parts) == 2 and parts[0].strip() in ('D', 'Z', 'M'), 'unexpected update entry')
        final[parts[0].strip()] = c.parse_expression(parts[1], renv)
    need(len(final) == len(fields), 'update fields')
    vbody = c.body_of(circuit, 'def value85 (p : Fin 4 → R) (v : Fin 10 → R) : R :=\n')
    vlines = vbody.splitlines()
    need(vlines[0] == '  let r := regs p v', 'unexpected value85 body')
    venv = {'r_' + name: value for name, value in final.items()}
    value = c.parse_expression(' '.join(x.strip() for x in vlines[1:]), venv)
    return final, renv['ecl'], value


def main():
    for path, expected in PINS.items():
        need(sha(path) == expected, 'input pin: ' + str(path))
    lean_pins = {path: sha(path) for path in (CIRCUIT, SYNTAX, ENDPOINT)}
    c = load87()
    graph = json.loads(GRAPH.read_text(encoding='utf8'))
    graph172 = json.loads(GRAPH172.read_text(encoding='utf8'))
    graph75 = json.loads(GRAPH75.read_text(encoding='utf8'))
    # one polynomial on one tuple
    need(graph['source'] == graph172['source'], '171 and 172 rows differ')
    for key in ('witnesses', 'fixed_numerals', 'output', 'operations', 'operation_breakdown',
                'exact_degree', 'transport_weight', 'denominator', 'domain'):
        need(graph[key] == graph172[key], '171 and 172 metadata differ: ' + key)
    binding75 = {k: v for k, v in graph75['coefficient_binding'].items() if k != 'path'}
    b171 = graph['coefficient_binding']
    b172 = graph172['coefficient_binding']
    need({k: v for k, v in b171.items() if k not in ('path', 'endianness')} == binding75 and
         b171.get('endianness') == 'little', '171 port binding differs from 75')
    need({k: v for k, v in b172.items() if k != 'path'} == binding75, '172 port binding differs from 75')
    for b in (b171, b172):
        need({k: b['ports'][k]['raw_sha256'] for k in c.RAW} == c.RAW, 'direct-BFS943 raw hashes')
    need(graph['witnesses'] == WITNESSES and graph['fixed_numerals'] == PORTS and
         len(graph['source']) == graph['operations'] == 85 and graph['exact_degree'] == 232 and
         graph['transport_weight'] == 'bV' and graph['denominator'] == '6q6' and
         graph['output'] == 'N' and graph172['mode'] == 'scaled_inverse', 'graph metadata')
    used = {x for row in graph['source'] for x in row[2:] if isinstance(x, str)}
    need(all(row[0] in used for row in graph['source'] if row[0] != 'N'), 'dead JSON row')

    text75 = REGS75.read_text(encoding='utf8')
    decl = text75.split('structure Regs (R : Type*) where\n', 1)[1].split('\n/--', 1)[0]
    fields = re.findall(r'^  ([A-Za-z][A-Za-z0-9_]*) : R$', decl, re.M)
    need(len(fields) == 27 and len(set(fields)) == len(fields), 'Lean field inventory')
    body75 = c.body_of(text75, 'def regs (p : Fin 4 → R) (v : Fin 10 → R) : Regs R :=\n')
    expected_at = (body75.replace('  let Y := q * q * q * s\n', '').replace('  let X := w * q\n', '')
                   .replace('  let s := v 6\n', '')
                   .replace('  let B := (p 1 + w) * C - F\n', '  let B := (p 1 + W) * C - F\n'))
    need(c.body_of(REGSAT.read_text(encoding='utf8'), REGSAT_HEADER) == expected_at,
         'regsAt is not the parameterized 75 register map')
    circuit = CIRCUIT.read_text(encoding='utf8')
    json_env = c.json_registers(graph)
    final, ecl, value = lean_value(c, circuit, fields)
    need(value == json_env[graph['output']], 'Lean and JSON outputs differ after ring normalization')
    for field, row in (('X', 'X'), ('Y', 'Y'), ('c', 'c'), ('B', 'Bt'), ('D', 'sixq6'),
                       ('Z', 'Znum'), ('M', 'Mtot')):
        need(final[field] == json_env[row], 'row differs: ' + row)
    need(ecl == json_env['eclear'], 'inverse-Lucas offset row eclear differs')
    rejected = []
    for label, old, new in MUTATIONS:
        need(circuit.count(old) == 1, 'mutation anchor: ' + label)
        _, _, mutated = lean_value(c, circuit.replace(old, new), fields)
        need(mutated != json_env[graph['output']], 'mutation accepted: ' + label)
        rejected.append(label)

    syntax = SYNTAX.read_text(encoding='utf8')
    need('def expression (p : Fin 4 → ℤ) : Expr (Fin 10) := value85 (ports p) Expr.var\n'
         in syntax, 'literal expression definition')
    need('def ports (p : Fin 4 → ℤ) : Fin 4 → Expr (Fin 10) := fun j => .constant (p j)\n'
         in syntax, 'literal ports definition')
    need('def literal (p : Fin 4 → ℕ) : Expr (Fin 10) :=\n'
         '  TenPositiveTrace85.expression (fun j => (p j : ℤ))\n' in syntax, 'literal definition')
    endpoint = ENDPOINT.read_text(encoding='utf8')
    ports_text = ('def fixedPorts : Fin 4 → ℕ :=\n'
                  '  CompactSymbolicPorts.ports CompactFixedBeta.betaNat\n'
                  '    (DirectBFSSymbolicKernel.paramKernel CompactSymbolicKernel.rho)\n'
                  '    CompactSymbolicPorts.lowNat CompactSymbolicPorts.highNat\n')
    need(ports_text in endpoint and ports_text in ENDPOINT75.read_text(encoding='utf8'),
         'fixedPorts differs from IPRATrace75')
    need('def expression : Expr (Fin 10) := Trace85BFSSyntax.literal fixedPorts\n' in endpoint,
         'endpoint expression')
    for path, expected_sha in list(PINS.items()) + list(lean_pins.items()):
        need(sha(path) == expected_sha, 'input changed: ' + str(path))
    print(json.dumps({'status': 'PASS', 'graph_sha256': PINS[GRAPH], 'graph172_sha256': PINS[GRAPH172],
                      'same_polynomial': '171 equation_bV.json and 172 positive10_degree232_ops85.json: '
                                         'equal rows and metadata, same direct-BFS943 tuple',
                      'regs75_source_sha256': PINS[REGS75],
                      'regsAt_source_sha256': PINS[REGSAT],
                      'check87_sha256': PINS[CHECK87],
                      'circuit_source_sha256': lean_pins[CIRCUIT],
                      'syntax_source_sha256': lean_pins[SYNTAX],
                      'endpoint_source_sha256': lean_pins[ENDPOINT],
                      'graph_rows': len(graph['source']), 'lean_registers': len(fields),
                      'interned_nodes': len(c.keys),
                      'instance': 'regsAt at X=qw, Y=qs, W=w (strip c=kY+eta), D=6q^6, '
                                  'ecl=6(e-q^4 s)-XY^2 k(k^2-4)',
                      'mutations_rejected': rejected,
                      'port_binding': 'equal to trace75_degree402.json except the relative path '
                                      '(171 also endianness: little)',
                      'raw_sha256': c.RAW,
                      'comparison': 'exact structural normalization in commutative rings',
                      'scope': 'external restricted-fragment parser; no Lean theorem about file bytes'},
                     sort_keys=True))


if __name__ == '__main__':
    main()
