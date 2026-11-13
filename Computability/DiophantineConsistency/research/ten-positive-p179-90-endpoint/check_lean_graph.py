#!/usr/bin/env python3
"""Bind the Lean literal of package 179's centred 90/206 circuit to its pinned JSON.

Usage (from anywhere): py -I -X utf8 -B check_lean_graph.py

The Lean circuit is `TenPositiveTrace90.value90` (BFS943/Trace90Regs.lean):
`TenPositiveCentred87.valueAt p v (centre p v)` (BFS943/Centred87Regs.lean),
i.e. the 87/214 register map `TenPositiveTrace87.regs` with the carrier
replaced by `Z = h D [H (n - V (b B + g)) + K] - H [D B + h eclear]` at the
centre `g = A (U E)` (the Lean register `A = Am1 + 1` is package 179's `A`).
This checker

* pins the SHA-256 of the 90 JSON graph, of package 172's 87 JSON graph (the
  JSON's `parent`), of the 75 JSON graph (port binding), of the 87 record's
  checker (whose parser and normalizer it imports) and of the Lean register
  sources it reads through that checker (`TenPositiveTrace75.lean`,
  `Trace79Regs.lean`, `Trace82Regs.lean`, `Trace87Regs.lean`);
* checks the graph metadata (`centerA`, `6*q^7`, 90 operations, degree 206,
  weight `bV`, tuple `radix67`, parent hash, no dead rows) and that the JSON
  rows differ from the 87 rows exactly by the centring gates;
* parses the 87 registers with the 87 checker, then `regsAt`, `valueAt`,
  `centre` and `value90`, into the same interned DAG, normalizing modulo
  commutative-ring associativity, commutativity, identities and additive
  inverses (no distribution, no sampling), and requires the outputs to be the
  same node (also the rows `g0`, `bB_g0`, `LBt`, `Znum`, `Mtot`, `sixq7`,
  `eclear` individually);
* rejects mutations (the other centre `Am1 + 2`, gate sign `- g`, the
  uncentred 87 gate, centre without `E`, gate weight `b` for `V`);
* requires the literal and endpoint definitions verbatim, `fixedPorts`
  textually the `IPRATrace75` one, and the JSON `coefficient_binding` to equal
  the 75 graph's in every port field except the relative `path` and the
  explicit `endianness: little` annotation (the 75 graph's integers are
  little-endian), with the four direct-BFS943 raw hashes, so
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
POINT = {
    'ops': 90, 'degree': 206, 'mode': 'centerA', 'name': 'centerA_radix67',
    'graph': 'con-zfc-diophantine-forms/179-affine-horizons-centered-certificates/positive/late172/'
             'centerA_radix67.json',
    'sha': '10e986024c698542d1099b44cea7ab7bac5b7ca04bddf56cb73f1d18d1331839',
    'module': 'Trace90', 'value': 'value90',
    'centre': '  r.A * (r.U * r.E)\n',
    'extra_rows': {('A', '+', 'Am1', 1)},
    'new_rows': {('g0', '*', 'A', 'UE'), ('bB', '*', 'cTR', 'Bt'), ('bB_g0', '+', 'bB', 'g0')},
}
GRAPH = D / POINT['graph']
GRAPH87 = (D / 'con-zfc-diophantine-forms/172-pooled-powers-round21/part2/'
           'ConZFC_Pooled_Powers_Round21_2026-10-25/scalar/positive10/positive10_degree214_ops87.json')
GRAPH75 = D / 'con-zfc-diophantine-forms/163-trace-radical/compact/equations/trace75_degree402.json'
CHECK87 = D / 'research/ten-positive-p172-87-endpoint/check_lean_graph.py'
L = D / 'Lean/DiophantineConsistency'
CENTRED = L / 'BFS943/Centred87Regs.lean'
CIRCUIT = L / f"BFS943/{POINT['module']}Regs.lean"
SYNTAX = L / f"BFS943/{POINT['module']}Syntax.lean"
ENDPOINT = L / f"BFS943/IPRA{POINT['module']}.lean"
ENDPOINT75 = L / 'BFS943/IPRATrace75.lean'
PINS = {GRAPH: POINT['sha'],
        GRAPH87: '6af0c97120fefba17920dbb517facc1d1ee403ad8388c8dee9523ee2e94b2449',
        GRAPH75: '8b9b9421ae8a0762725852034b3db6d29b14660b3a4d0587e1494a933b5271c9',
        CHECK87: '322d05e923d8b2f49b34719abe7a29a34ee3aa3d012f5f60ebfedb68dc83aa3a',
        L / 'TenPositiveTrace75.lean': '0df718ab69ae7aef32dd341ee355ea2e21214e97fbea225af8816519fe383db9',
        L / 'BFS943/Trace79Regs.lean': 'e5ce1cc341749207edd6546835afc02a61a7d6225a2c73d06f0e430e524a63f9',
        L / 'BFS943/Trace82Regs.lean': '59abf251f248c84cbb425cda0d0952e5d9a82651e0a938eb494a94c97c130f8e',
        L / 'BFS943/Trace87Regs.lean': '7ca04a799671b4e4e6d3cc1c04ad1c3b409d4e81170478bdc66d55d423cff067'}
WITNESSES = ['J', 'F', 'alpha', 'i', 'T', 'w', 's', 'n', 'eta', 'zeta']
PORTS = ['beta', 'K0', 'MC', 'MF']
GATE = '(v 7 - r.V * (r.b * r.B + g))'
MUTATIONS = [
    ('centre gate sign - g', 'centred', GATE, '(v 7 - r.V * (r.b * r.B - g))'),
    ('uncentred 87 gate', 'centred', GATE, '(v 7 - r.b * r.V * r.B)'),
    ('gate weight b for V', 'centred', GATE, '(v 7 - r.b * (r.b * r.B + g))'),
    ('other centre', 'circuit', POINT['centre'],
     POINT['centre'].replace('Am1 + 2', 'Am1 + 1') if 'Am1 + 2' in POINT['centre']
     else POINT['centre'].replace('r.A *', '(r.Am1 + 2) *')),
    ('centre without E', 'circuit', POINT['centre'], POINT['centre'].replace('(r.U * r.E)', 'r.U')),
]


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


def body_of(text, header):
    need(text.count(header) == 1, 'definition header: ' + header.strip())
    return text.split(header, 1)[1].split('\n\n', 1)[0]


def centred_value(c87, final87, ecl, centred_text, circuit_text):
    """Interned output of `valueN` and the centred rows."""
    env = {'r_' + name: value for name, value in final87.items()}
    env.update({f'v{i}': c87.symbol(n) for i, n in enumerate(WITNESSES)})
    # the centre
    cbody = body_of(circuit_text, 'def centre (p : Fin 4 → R) (v : Fin 10 → R) : R :=\n').split('\n')
    need(cbody[0] == '  let r := TenPositiveTrace87.regs p v' and len(cbody) == 2, 'centre body')
    g = c87.parse_expression(cbody[1], env)
    vbody = body_of(circuit_text, f"def {POINT['value']} (p : Fin 4 → R) (v : Fin 10 → R) : R :=\n")
    need(vbody == '  TenPositiveCentred87.valueAt p v (centre p v)', 'value body')
    # the centred carrier
    rbody = body_of(centred_text,
                    'def regsAt (p : Fin 4 → R) (v : Fin 10 → R) (g : R) : Regs R :=\n')
    lines = rbody.split('\n')
    need(lines[0] == '  let r := TenPositiveTrace87.regs p v', 'regsAt instance line')
    update = ' '.join(x.strip() for x in lines[1:])
    need(update.startswith('{ r with Z := ') and update.endswith(' }'), 'regsAt update shape')
    ztext = update[len('{ r with Z := '):-2].replace('TenPositiveTrace87.ecl p v', 'ECL')
    zenv = dict(env)
    zenv.update({'g': g, 'ECL': ecl})
    Z = c87.parse_expression(ztext, zenv)
    final = dict(final87)
    final['Z'] = Z
    abody = body_of(centred_text, 'def valueAt (p : Fin 4 → R) (v : Fin 10 → R) (g : R) : R :=\n')
    alines = abody.splitlines()
    need(alines[0] == '  let r := regsAt p v g', 'valueAt body')
    venv = {'r_' + name: value for name, value in final.items()}
    value = c87.parse_expression(' '.join(x.strip() for x in alines[1:]), venv)
    rows = {'g0': g, 'bB_g0': c87.add(c87.mul(final87['b'], final87['B']), g),
            'LBt': c87.mul(final87['V'], c87.add(c87.mul(final87['b'], final87['B']), g))}
    return final, rows, value


def main():
    for path, expected in PINS.items():
        need(sha(path) == expected, 'input pin: ' + str(path))
    pins = {path: sha(path) for path in PINS}
    lean_pins = {path: sha(path) for path in (CENTRED, CIRCUIT, SYNTAX, ENDPOINT)}
    c87 = load87()
    graph = json.loads(GRAPH.read_text(encoding='utf8'))
    graph87 = json.loads(GRAPH87.read_text(encoding='utf8'))
    graph75 = json.loads(GRAPH75.read_text(encoding='utf8'))
    need(graph['witnesses'] == WITNESSES and graph['fixed_numerals'] == PORTS and
         len(graph['source']) == graph['operations'] == POINT['ops'] and
         graph['exact_degree'] == POINT['degree'] and graph['transport_weight'] == 'bV' and
         graph['mode'] == POINT['mode'] and graph['name'] == POINT['name'] and
         graph['tuple_name'] == 'radix67' and graph['denominator'] == '6*q^7' and
         graph['output'] == 'N' and graph['parent']['sha256'] == PINS[GRAPH87], 'graph metadata')
    # the rows differ from the 87 rows exactly by the centring gates
    rows87 = {tuple(r) for r in graph87['source']}
    rows = {tuple(r) for r in graph['source']}
    need(rows87 - rows == {('L', '*', 'cTR', 'V'), ('LBt', '*', 'L', 'Bt')}, 'removed 87 rows')
    need(rows - rows87 == POINT['new_rows'] | {('LBt', '*', 'V', 'bB_g0')} |
         POINT.get('extra_rows', set()), 'added centring rows')
    binding, binding75 = graph['coefficient_binding'], graph75['coefficient_binding']
    need({k: v for k, v in binding.items() if k not in ('path', 'endianness')} ==
         {k: v for k, v in binding75.items() if k != 'path'} and
         binding.get('endianness') == 'little' and 'endianness' not in binding75,
         'port binding differs from 75')
    need({k: binding['ports'][k]['raw_sha256'] for k in c87.RAW} == c87.RAW, 'direct-BFS943 raw hashes')
    used = {x for row in graph['source'] for x in row[2:] if isinstance(x, str)}
    need(all(row[0] in used for row in graph['source'] if row[0] != 'N'), 'dead JSON row')

    text75 = (L / 'TenPositiveTrace75.lean').read_text(encoding='utf8')
    decl = text75.split('structure Regs (R : Type*) where\n', 1)[1].split('\n/--', 1)[0]
    fields = re.findall(r'^  ([A-Za-z][A-Za-z0-9_]*) : R$', decl, re.M)
    need(len(fields) == 27 and len(set(fields)) == len(fields), 'Lean field inventory')
    circuit87 = (L / 'BFS943/Trace87Regs.lean').read_text(encoding='utf8')
    final87, ecl, value87 = c87.lean_value(circuit87, fields)
    json_env = c87.json_registers(graph)
    json87 = c87.json_registers(graph87)
    need(value87 == json87['N'], '87 transcription no longer matches the 87 JSON')
    centred_text = CENTRED.read_text(encoding='utf8')
    circuit = CIRCUIT.read_text(encoding='utf8')
    final, crow, value = centred_value(c87, final87, ecl, centred_text, circuit)
    need(value == json_env[graph['output']], 'Lean and JSON outputs differ after ring normalization')
    need(value != json87['N'], 'centred output equals the 87 output')
    for row, node in crow.items():
        need(node == json_env[row], 'row differs: ' + row)
    need(final['Z'] == json_env['Znum'], 'carrier row Znum differs')
    need(final['M'] == json_env['Mtot'], 'multiplier row Mtot differs')
    need(final['D'] == json_env['sixq7'], 'denominator row sixq7 differs')
    need(ecl == json_env['eclear'], 'inverse-Lucas offset row eclear differs')
    rejected = []
    for label, which, old, new in MUTATIONS:
        ctext, rtext = centred_text, circuit
        if which == 'centred':
            need(ctext.count(old) == 1, 'mutation anchor: ' + label)
            ctext = ctext.replace(old, new)
        else:
            need(rtext.count(old) == 1, 'mutation anchor: ' + label)
            rtext = rtext.replace(old, new)
        need(ctext != centred_text or rtext != circuit, 'mutation did not change text: ' + label)
        _, _, mutated = centred_value(c87, final87, ecl, ctext, rtext)
        need(mutated != json_env[graph['output']], 'mutation accepted: ' + label)
        rejected.append(label)

    syntax = SYNTAX.read_text(encoding='utf8')
    need(f"def expression (p : Fin 4 → ℤ) : Expr (Fin 10) := {POINT['value']} (ports p) Expr.var\n"
         in syntax, 'literal expression definition')
    need('open TenPositiveTrace87 (ports ' in syntax, 'literal ports are the 87 literal ports')
    need('def ports (p : Fin 4 → ℤ) : Fin 4 → Expr (Fin 10) := fun j => .constant (p j)\n'
         in (L / 'BFS943/Trace87Syntax.lean').read_text(encoding='utf8'), '87 literal ports definition')
    need('def literal (p : Fin 4 → ℕ) : Expr (Fin 10) :=\n'
         f"  TenPositive{POINT['module']}.expression (fun j => (p j : ℤ))\n" in syntax,
         'literal definition')
    endpoint = ENDPOINT.read_text(encoding='utf8')
    ports_text = ('def fixedPorts : Fin 4 → ℕ :=\n'
                  '  CompactSymbolicPorts.ports CompactFixedBeta.betaNat\n'
                  '    (DirectBFSSymbolicKernel.paramKernel CompactSymbolicKernel.rho)\n'
                  '    CompactSymbolicPorts.lowNat CompactSymbolicPorts.highNat\n')
    need(ports_text in endpoint and ports_text in ENDPOINT75.read_text(encoding='utf8'),
         'fixedPorts differs from IPRATrace75')
    need(f"def expression : Expr (Fin 10) := {POINT['module']}BFSSyntax.literal fixedPorts\n"
         in endpoint, 'endpoint expression')
    for path, digest in list(pins.items()) + list(lean_pins.items()):
        need(sha(path) == digest, 'input changed: ' + str(path))
    print(json.dumps({'status': 'PASS', 'graph': POINT['graph'], 'graph_sha256': PINS[GRAPH],
                      'parent_graph_sha256': PINS[GRAPH87],
                      'check87_sha256': pins[CHECK87],
                      'trace87regs_source_sha256': pins[L / 'BFS943/Trace87Regs.lean'],
                      'centred_source_sha256': lean_pins[CENTRED],
                      'circuit_source_sha256': lean_pins[CIRCUIT],
                      'syntax_source_sha256': lean_pins[SYNTAX],
                      'endpoint_source_sha256': lean_pins[ENDPOINT],
                      'graph_rows': len(graph['source']), 'lean_registers': len(fields),
                      'interned_nodes': len(c87.keys),
                      'instance': '87/214 registers, Z = hD[H(n - V(bB + g)) + K] - H[DB + h ecl], '
                                  'g = ' + POINT['centre'].strip(),
                      'mutations_rejected': rejected,
                      'port_binding': 'equal to trace75_degree402.json except the relative path '
                                      'and endianness: little',
                      'raw_sha256': c87.RAW,
                      'comparison': 'exact structural normalization in commutative rings',
                      'scope': 'external restricted-fragment parser; no Lean theorem about file bytes'},
                     sort_keys=True))


if __name__ == '__main__':
    main()
