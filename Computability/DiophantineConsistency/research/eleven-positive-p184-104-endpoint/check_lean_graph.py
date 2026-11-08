#!/usr/bin/env python3
"""Bind the Lean literal of package 184's eleven-positive 104/174 circuit to its pinned JSON.

Usage (from anywhere): py -I -X utf8 -B check_lean_graph.py

The Lean circuit is `TenPositiveTrace104.value104` (BFS943/Trace104Regs.lean):
the core register map `regs` over the first ten unknowns (its `let` rows and
record), the offset `ecl`, and the eleven-unknown output
`(3 N + 1) (P0 + 1) - 1` with `M = h D`,
`Z = M (n + kappa - b V B) - (D B + h ecl)`, `P0 = Q (Z^2 - M^2 G V^2) + (M^2 G - Z^2)`
and `N = K - kappa H`. This checker

* pins the SHA-256 of the 104 JSON graph, of the 75 JSON graph (port binding)
  and of the 87 record's checker, whose interned normalizer it imports;
* checks the graph metadata (eleven witnesses in order, `lambda = 210`, 104
  operations, exact degree 174, output `P`, no dead rows) and the port
  binding: equal to the 75 graph's in `ports` and `tuple` (only `path` and the
  extra `endianness` field differ), with the four direct-BFS943 raw hashes;
* parses `regs` (every `let` row and the record), `ecl` and the body of
  `value104` into one interned DAG with the JSON rows, normalizing sums and
  products modulo commutative-ring associativity, commutativity, identities
  and additive inverses (no distribution, no sampling), and requires the
  outputs to be the same node; also the rows `X`, `c`, `Am1`, `Delta`, `H`,
  `E`, `R`, `B`, `Q`, `V`, `K`, `ec` (both the record's internal `ec` and the
  standalone `ecl`), `M`, `Z`, `P0`, `N` individually;
* rejects mutations of the Lean text (dilation, `44100`, each inverse
  coefficient, correction sign, `q^4 s` sign, denominator, `n - kappa`,
  `N = K + kappa H`, factor `2 N + 1`, carrier sign, multiplier `h D H`);
* requires the literal and endpoint definitions verbatim, and `fixedPorts`
  textually equal to `IPRATrace75`'s, so
  `reviews/bfs943-source-promotion/tools/check_ports.py` covers 104 too.

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
GRAPH = D / 'con-zfc-diophantine-forms/184-pell-growth-210/compact11/constant_dilation11.json'
GRAPH75 = D / 'con-zfc-diophantine-forms/163-trace-radical/compact/equations/trace75_degree402.json'
CHECK87 = D / 'research/ten-positive-p172-87-endpoint/check_lean_graph.py'
L = D / 'Lean/DiophantineConsistency'
CIRCUIT = L / 'BFS943/Trace104Regs.lean'
SYNTAX = L / 'BFS943/Trace104Syntax.lean'
ENDPOINT = L / 'BFS943/IPRATrace104.lean'
ENDPOINT75 = L / 'BFS943/IPRATrace75.lean'
PINS = {GRAPH: 'ef8ee046fd0f62fe9be84e18f24f8508678ed44c63f76cf8aa154ad8b52e6805',
        GRAPH75: '8b9b9421ae8a0762725852034b3db6d29b14660b3a4d0587e1494a933b5271c9',
        CHECK87: '322d05e923d8b2f49b34719abe7a29a34ee3aa3d012f5f60ebfedb68dc83aa3a'}
RAW = {'K0': '0a86821a704294199c2e1a50379d242c96840a3366e9d965689ba3d74605203f',
       'MC': '6007cabd5f5228618e8fb613f386d8fc3692a24520d6e4cd72af0262aae1ade4',
       'MF': '48333b0d30a4edeb8579f44286cb59806c5622cb42b367f5b5f9ee827711c737',
       'beta': '0664a868cbfef9869ea05c40a1c445563f685ff857092594c1c1223bc4b21f9d'}
WITNESSES = ['J', 'F', 'alpha', 'i', 'T', 'w', 's', 'n', 'eta', 'zeta', 'kappa']
PORTS = ['beta', 'K0', 'MC', 'MF']
FIELDS = ['h', 'q', 'C', 'X', 'Y', 'k', 'c', 'Am1', 'A', 'H', 'Delta', 'E', 'rank', 'e', 'B',
          'U', 'a', 'F0', 'f', 'Q', 'b', 'V', 'K', 'D', 'Z', 'M', 'Gn']
MUTATIONS = [
    ('dilation 1', '  let Am1 := 210 * (X * s + s)\n', '  let Am1 := 1 * (X * s + s)\n'),
    ('first parameter 210 v0', '  let ell := 44100 * (v0 * k)\n', '  let ell := 210 * (v0 * k)\n'),
    ('inverse coefficient 7350', '+ 7350)) - r.q * r.q', '+ 7349)) - r.q * r.q'),
    ('inverse coefficient 5402250', '      5402250 * (27 * (r.k * r.k) + 8)) + 7350))',
     '      5402249 * (27 * (r.k * r.k) + 8)) + 7350))'),
    ('inverse coefficient 5672362500', '(v0 * (5672362500 * v0 * (675 * (r.k',
     '(v0 * (5672362501 * v0 * (675 * (r.k'),
    ('inverse quartic 324', '- 324 * (r.k * r.k) + 160)', '- 325 * (r.k * r.k) + 160)'),
    ('inverse quadratic 27', '(27 * (r.k * r.k) + 8)', '(28 * (r.k * r.k) + 8)'),
    ('correction sign', '  (r.e - (v0 * r.k)', '  (r.e + (v0 * r.k)'),
    ('q4 s sign', '+ 7350)) - r.q * r.q', '+ 7350)) + r.q * r.q'),
    ('offset uses q^3 s', '+ 7350)) - r.q * r.q * (r.q * r.q) * v 6', '+ 7350)) - r.q * r.q * r.q * v 6'),
    ('denominator q^6', '  let q7 := q4 * q3\n', '  let q7 := q4 * q2\n'),
    ('carrier n - kappa', '  let Z := M * (v 7 + kappa - r.b * r.V * r.B)',
     '  let Z := M * (v 7 - kappa - r.b * r.V * r.B)'),
    ('carrier sign', '- (r.D * r.B + r.h * ecl p (core v))\n', '+ (r.D * r.B + r.h * ecl p (core v))\n'),
    ('unit N = K + kappa H', '  let N := r.K - kappa * r.H\n', '  let N := r.K + kappa * r.H\n'),
    ('unit factor 2 N + 1', '  (3 * N + 1) * (P0 + 1) - 1\n', '  (2 * N + 1) * (P0 + 1) - 1\n'),
    ('multiplier h D H', '  let M := r.h * r.D\n', '  let M := r.h * r.D * r.H\n'),
]


def need(condition, message):
    if not condition:
        raise RuntimeError(message)


def sha(path):
    return sha256(path.read_bytes()).hexdigest()


need(sha(CHECK87) == PINS[CHECK87], 'input pin: 87 checker')
_spec = importlib.util.spec_from_file_location('check87', CHECK87)
N87 = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(N87)
number, symbol, operation, parse_expression = N87.number, N87.symbol, N87.operation, N87.parse_expression


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


def body_of(text, header):
    need(text.count(header) == 1, 'header: ' + header.strip())
    return text.split(header, 1)[1].split('\n\n', 1)[0]


def statements(body):
    """Join continuation lines (indented by four or more) to their `let` line."""
    out = []
    for line in body.split('\n'):
        if line.startswith('    ') and out:
            out[-1] += ' ' + line.strip()
        else:
            out.append(line)
    return out


def lean_value(circuit):
    # the Lean row `v0 = X s²` would collide with the witness token `v0` (`v 0`)
    circuit = re.sub(r'\bv0\b', 'vzero', circuit)
    env = {f'v{i}': symbol(n) for i, n in enumerate(WITNESSES[:10])}
    env.update({f'p{i}': symbol(n) for i, n in enumerate(PORTS)})
    regs_body = body_of(circuit, 'def regs (p : Fin 4 → R) (v : Fin 10 → R) : Regs R :=\n')
    stmts = statements(regs_body)
    record = None
    for st in stmts:
        m = re.fullmatch(r'  let ([A-Za-z][A-Za-z0-9_]*) := (.+)', st)
        if m:
            need(m[1] not in env, 'duplicate regs let ' + m[1])
            env[m[1]] = parse_expression(m[2], env)
            continue
        need(st.startswith('  { ') and st.endswith(' }') and record is None, 'regs record shape')
        record = st[4:-2]
    need(record is not None, 'regs record')
    fields = {}
    for item in N87.top_split(record, ','):
        parts = item.strip().split(' := ')
        need(len(parts) in (1, 2) and parts[0] in FIELDS and parts[0] not in fields,
             'regs record entry ' + item)
        fields[parts[0]] = parse_expression(parts[1] if len(parts) == 2 else parts[0], env)
    need(set(fields) == set(FIELDS), 'regs record fields')
    internal_ec = env['ec']
    # the standalone offset `ecl`
    ecl_body = statements(body_of(circuit, 'def ecl (p : Fin 4 → R) (v : Fin 10 → R) : R :=\n'))
    need(ecl_body[0] == '  let r := regs p v', 'ecl body head')
    eenv = {'r_' + f: x for f, x in fields.items()}
    eenv.update({f'v{i}': symbol(n) for i, n in enumerate(WITNESSES[:10])})
    m = re.fullmatch(r'  let vzero := (.+)', ecl_body[1])
    need(m is not None, 'ecl v0 row')
    eenv['vzero'] = parse_expression(m[1], eenv)
    need(len(ecl_body) == 3, 'ecl body shape')
    ecl = parse_expression(ecl_body[2], eenv)
    # the literal
    vbody = statements(body_of(circuit, 'def value104 (p : Fin 4 → R) (v : Fin 11 → R) : R :=\n'))
    need(vbody[0] == '  let r := regs p (core v)', 'value104 body head')
    venv = {'r_' + f: x for f, x in fields.items()}
    # `core v j = v j` for `j < 10`; `v 10` is kappa
    venv.update({f'v{i}': symbol(n) for i, n in enumerate(WITNESSES)})
    venv['ECL'] = ecl
    lets = {}
    for st in vbody[1:-1]:
        m = re.fullmatch(r'  let ([A-Za-z][A-Za-z0-9_]*) := (.+)', st)
        need(m is not None and m[1] not in venv, 'value104 let ' + st)
        venv[m[1]] = parse_expression(m[2].replace('ecl p (core v)', 'ECL'), venv)
        lets[m[1]] = venv[m[1]]
    need(list(lets) == ['kappa', 'M', 'Z', 'P0', 'N'], 'value104 lets')
    value = parse_expression(vbody[-1].replace('ecl p (core v)', 'ECL'), venv)
    return env, fields, internal_ec, ecl, lets, value


def main():
    for path, expected in PINS.items():
        need(sha(path) == expected, 'input pin: ' + str(path))
    lean_pins = {path: sha(path) for path in (CIRCUIT, SYNTAX, ENDPOINT)}
    graph = json.loads(GRAPH.read_text(encoding='utf8'))
    graph75 = json.loads(GRAPH75.read_text(encoding='utf8'))
    need(graph['witnesses'] == WITNESSES and graph['fixed_numerals'] == PORTS and
         len(graph['source']) == graph['operations'] == 104 and graph['exact_degree'] == 174 and
         graph['lambda'] == 210 and graph['output'] == 'P' and
         graph['domain'] == 'strictly positive integers', 'graph metadata')
    binding, binding75 = graph['coefficient_binding'], graph75['coefficient_binding']
    need(binding['ports'] == binding75['ports'] and binding['tuple'] == binding75['tuple'] and
         set(binding) - set(binding75) == {'endianness'} and set(binding75) <= set(binding),
         'port binding differs from 75')
    need({k: binding['ports'][k]['raw_sha256'] for k in RAW} == RAW, 'direct-BFS943 raw hashes')
    used = {x for row in graph['source'] for x in row[2:] if isinstance(x, str)}
    need(all(row[0] in used for row in graph['source'] if row[0] != 'P'), 'dead JSON row')

    circuit = CIRCUIT.read_text(encoding='utf8')
    J = json_registers(graph)
    env, fields, internal_ec, ecl, lets, value = lean_value(circuit)
    need(value == J['P'], 'Lean and JSON outputs differ after ring normalization')
    rows = [('X', fields['X'], 'X'), ('c', fields['c'], 'c'), ('Am1', fields['Am1'], 'Am1'),
            ('Delta', fields['Delta'], 'Delta'), ('H', fields['H'], 'H'), ('E', fields['E'], 'E'),
            ('rank', fields['rank'], 'R'), ('B', fields['B'], 'B'), ('Q', fields['Q'], 'Q'),
            ('V', fields['V'], 'V'), ('K', fields['K'], 'K'), ('D', fields['D'], 'q7'),
            ('Gn', fields['Gn'], 'G'), ('ec (record)', internal_ec, 'ec'), ('ecl', ecl, 'ec'),
            ('M', lets['M'], 'M'), ('Z', lets['Z'], 'Z'), ('P0', lets['P0'], 'P0'), ('N', lets['N'], 'N')]
    for label, lean_node, row in rows:
        need(lean_node == J[row], 'row differs: ' + label)
    rejected = []
    for label, old, new in MUTATIONS:
        need(circuit.count(old) == 1, 'mutation anchor: ' + label)
        *_, mutated = lean_value(circuit.replace(old, new))
        need(mutated != J['P'], 'mutation accepted: ' + label)
        rejected.append(label)

    syntax = SYNTAX.read_text(encoding='utf8')
    need('def expression (p : Fin 4 → ℤ) : Expr (Fin 11) := value104 (ports p) Expr.var\n'
         in syntax, 'literal expression definition')
    need('def ports (p : Fin 4 → ℤ) : Fin 4 → Expr (Fin 11) := fun j => .constant (p j)\n'
         in syntax, 'literal ports definition')
    need('def literal (p : Fin 4 → ℕ) : Expr (Fin 11) :=\n'
         '  TenPositiveTrace104.expression (fun j => (p j : ℤ))\n' in syntax, 'literal definition')
    need('def core (v : Fin 11 → R) : Fin 10 → R := fun j => v j.castSucc\n' in circuit,
         'core coordinates')
    endpoint = ENDPOINT.read_text(encoding='utf8')
    ports_text = ('def fixedPorts : Fin 4 → ℕ :=\n'
                  '  CompactSymbolicPorts.ports CompactFixedBeta.betaNat\n'
                  '    (DirectBFSSymbolicKernel.paramKernel CompactSymbolicKernel.rho)\n'
                  '    CompactSymbolicPorts.lowNat CompactSymbolicPorts.highNat\n')
    need(ports_text in endpoint and ports_text in ENDPOINT75.read_text(encoding='utf8'),
         'fixedPorts differs from IPRATrace75')
    need('def expression : Expr (Fin 11) := Trace104BFSSyntax.literal fixedPorts\n' in endpoint,
         'endpoint expression')
    need('theorem expression_def :\n'
         '    expression = TenPositiveTrace104.expression (fun j => (fixedPorts j : ℤ)) := rfl\n'
         in endpoint, 'endpoint expression_def')
    for path, expected_sha in PINS.items():
        need(sha(path) == expected_sha, 'input changed: ' + str(path))
    for path, expected_sha in lean_pins.items():
        need(sha(path) == expected_sha, 'input changed: ' + str(path))
    print(json.dumps({'status': 'PASS', 'graph_sha256': PINS[GRAPH],
                      'graph75_sha256': PINS[GRAPH75],
                      'normalizer_source_sha256': PINS[CHECK87],
                      'circuit_source_sha256': lean_pins[CIRCUIT],
                      'syntax_source_sha256': lean_pins[SYNTAX],
                      'endpoint_source_sha256': lean_pins[ENDPOINT],
                      'graph_rows': len(graph['source']), 'lean_registers': len(FIELDS),
                      'interned_nodes': len(N87.keys),
                      'rows_compared': [r[0] for r in rows],
                      'mutations_rejected': rejected,
                      'port_binding': 'ports and tuple equal to trace75_degree402.json; path and endianness differ',
                      'raw_sha256': RAW,
                      'comparison': 'exact structural normalization in commutative rings',
                      'scope': 'external restricted-fragment parser; no Lean theorem about file bytes'},
                     sort_keys=True, indent=1))


if __name__ == '__main__':
    main()
