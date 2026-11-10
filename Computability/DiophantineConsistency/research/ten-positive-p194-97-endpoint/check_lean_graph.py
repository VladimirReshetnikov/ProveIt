#!/usr/bin/env python3
"""Bind the Lean literal of package 194's quotient_t 97/202 circuit to its pinned JSON.

Usage (from anywhere): py -I -X utf8 -B check_lean_graph.py

The Lean circuit is `TenPositiveTrace97.value97` (BFS943/Trace97Regs.lean):
the root-scale-two norm `Q (Z^2 - M^2 (4 G) V^2) + (M^2 (4 G) - Z^2)` at the
centred carrier of `TenPositiveCentred87.regsAt p v (centre p v)`
(BFS943/Centred87Regs.lean), i.e. the 87/214 register map
`TenPositiveTrace87.regs` with the carrier
`Z = h D [H (n - V (b B + C2)) + K] - H [D B + h eclear]` at the quotient
centre `C2 = (Am1 + (Am1 + 2)) (U E) - U Qt`,
`Qt = (q (k s)) (X Y Y k + k - (q (k s)) Y)`. This checker

* pins the SHA-256 of the 97 JSON graph, of package 172's 87 JSON graph (the
  JSON's `parent`), of the 75 JSON graph (port binding), of the 87 record's
  checker (whose parser and normalizer it imports) and of the Lean register
  sources it reads through that checker (`TenPositiveTrace75.lean`,
  `Trace79Regs.lean`, `Trace82Regs.lean`, `Trace87Regs.lean`) and of
  `Centred87Regs.lean`;
* checks the graph metadata (`quotient_t`, `6*q^7`, 97 operations, degree 202,
  weight `bV`, root scale 2, tuple `radix67`, parent hash, no dead rows) and
  that the JSON rows differ from the 87 rows exactly by the centre gates, the
  centred transport gate and the scaled `4 G` gate;
* parses the 87 registers with the 87 checker, then `centre`, `regsAt` and
  `value97` into the same interned DAG, normalizing modulo commutative-ring
  associativity, commutativity, identities and additive inverses (no
  distribution, no sampling), and requires the outputs to be the same node
  (also the rows `Qt`, `center_root`, `bB_center`, `LBt`, `scaledG`, `RG`,
  `Znum`, `Mtot`, `sixq7`, `eclear` individually);
* rejects mutations (root scale 1, root scale 2 only inside the bracket,
  centre sign `+ U Qt`, `2A` read as `2A - 1`, `Qt` without the factor `k Ybar`,
  the uncentred 87 gate);
* requires the literal and endpoint definitions verbatim, `fixedPorts`
  textually the `IPRATrace75` one, and the JSON `coefficient_binding` to equal
  the 75 graph's in every port field except the relative `path` and the
  explicit `endianness: little` annotation, with the four direct-BFS943 raw
  hashes, so `reviews/bfs943-source-promotion/tools/check_ports.py` covers this
  circuit.

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
    'ops': 97, 'degree': 202, 'mode': 'quotient_t', 'name': 'quotient_t_radix67',
    'graph': 'con-zfc-diophantine-forms/194-guarded-resultants-early-projection/positive/'
             'quotient_t_radix67.json',
    'sha': 'b3de3e074f10914120fd0f23db613a7591237b8109d9169cf22b7b0846f58991',
    'module': 'Trace97', 'value': 'value97',
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
        CENTRED: '0e0083720428afa626bc3d2537c81b0d33e7b2e6b8d0b1ab8c03f002e1d82033',
        L / 'TenPositiveTrace75.lean': '0df718ab69ae7aef32dd341ee355ea2e21214e97fbea225af8816519fe383db9',
        L / 'BFS943/Trace79Regs.lean': 'e5ce1cc341749207edd6546835afc02a61a7d6225a2c73d06f0e430e524a63f9',
        L / 'BFS943/Trace82Regs.lean': '59abf251f248c84cbb425cda0d0952e5d9a82651e0a938eb494a94c97c130f8e',
        L / 'BFS943/Trace87Regs.lean': '7ca04a799671b4e4e6d3cc1c04ad1c3b409d4e81170478bdc66d55d423cff067'}
WITNESSES = ['J', 'F', 'alpha', 'i', 'T', 'w', 's', 'n', 'eta', 'zeta']
PORTS = ['beta', 'K0', 'MC', 'MF']
REMOVED = {('L', '*', 'cTR', 'V'), ('LBt', '*', 'L', 'Bt'), ('RG', '*', 'M2', 'Dg')}
ADDED = {('LBt', '*', 'V', 'bB_center'), ('Qt', '*', 'cy', 'qt_inner'), ('RG', '*', 'M2', 'scaledG'),
         ('UQt', '*', 'U', 'Qt'), ('bB', '*', 'cTR', 'Bt'), ('bB_center', '+', 'bB', 'center_root'),
         ('center_root', '-', 'twice_upper', 'UQt'), ('cy', '*', 'q', 'kY'), ('cyy', '*', 'cy', 'qY'),
         ('qt_inner', '-', 'V0kk', 'cyy'), ('scaledG', '*', 4, 'Dg'),
         ('twice_upper', '*', 'twoA', 'UE'), ('twoA', '+', 'Am1', 'Ap1')}
CENTRE_HEADER = 'def centre (p : Fin 4 → R) (v : Fin 10 → R) : R :=\n'
VALUE_HEADER = f"def {POINT['value']} (p : Fin 4 → R) (v : Fin 10 → R) : R :=\n"
GATE = '(v 7 - r.V * (r.b * r.B + g))'
MUTATIONS = [
    ('root scale 1', 'value', '(4 * r.Gn)', 'r.Gn'),
    ('root scale 2 only inside', 'value', 'r.Q * (r.Z * r.Z - r.M * r.M * (4 * r.Gn)',
     'r.Q * (r.Z * r.Z - r.M * r.M * r.Gn'),
    ('centre sign + U Qt', 'centre', ' -\n    r.U * (r.q', ' +\n    r.U * (r.q'),
    ('2A read as 2A - 1', 'centre', '(r.Am1 + (r.Am1 + 2))', '(r.Am1 + (r.Am1 + 1))'),
    ('Qt without k Ybar', 'centre', 'r.U * (r.q * (r.k * v 6) * (r.X', 'r.U * ((r.X'),
    ('uncentred 87 gate', 'centred', GATE, '(v 7 - r.b * r.V * r.B)'),
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


def circuit_value(c87, final87, ecl, centred_text, circuit_text):
    """Interned output of `value97` and the named rows."""
    env = {'r_' + name: value for name, value in final87.items()}
    env.update({f'v{i}': c87.symbol(n) for i, n in enumerate(WITNESSES)})
    cbody = body_of(circuit_text, CENTRE_HEADER).split('\n')
    need(cbody[0] == '  let r := TenPositiveTrace87.regs p v' and len(cbody) == 3, 'centre body')
    g = c87.parse_expression(' '.join(x.strip() for x in cbody[1:]), env)
    qt = c87.parse_expression(
        '(r.q * (r.k * v 6) * (r.X * r.Y * r.Y * r.k + r.k - r.q * (r.k * v 6) * r.Y))', env)
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
    vlines = body_of(circuit_text, VALUE_HEADER).splitlines()
    need(vlines[0] == '  let r := TenPositiveCentred87.regsAt p v (centre p v)', 'value body')
    venv = {'r_' + name: value for name, value in final.items()}
    value = c87.parse_expression(' '.join(x.strip() for x in vlines[1:]), venv)
    bB = c87.mul(final87['b'], final87['B'])
    scaledG = c87.mul(c87.number(4), final87['Gn'])
    rows = {'Qt': qt, 'center_root': g, 'bB_center': c87.add(bB, g),
            'LBt': c87.mul(final87['V'], c87.add(bB, g)), 'scaledG': scaledG,
            'RG': c87.mul(c87.mul(final87['M'], final87['M']), scaledG)}
    return final, rows, value


def main():
    for path, expected in PINS.items():
        need(sha(path) == expected, 'input pin: ' + str(path))
    pins = {path: sha(path) for path in PINS}
    lean_pins = {path: sha(path) for path in (CIRCUIT, SYNTAX, ENDPOINT)}
    c87 = load87()
    graph = json.loads(GRAPH.read_text(encoding='utf8'))
    graph87 = json.loads(GRAPH87.read_text(encoding='utf8'))
    graph75 = json.loads(GRAPH75.read_text(encoding='utf8'))
    need(graph['witnesses'] == WITNESSES and graph['fixed_numerals'] == PORTS and
         len(graph['source']) == graph['operations'] == POINT['ops'] and
         graph['exact_degree'] == POINT['degree'] and graph['transport_weight'] == 'bV' and
         graph['mode'] == POINT['mode'] and graph['name'] == POINT['name'] and
         graph['tuple_name'] == 'radix67' and graph['denominator'] == '6*q^7' and
         graph['root_scale'] == 2 and graph['domain'] == 'strictly positive integers' and
         graph['output'] == 'N' and graph['parent']['sha256'] == PINS[GRAPH87], 'graph metadata')
    rows87 = {tuple(r) for r in graph87['source']}
    rows = {tuple(r) for r in graph['source']}
    need(rows87 - rows == REMOVED, 'removed 87 rows')
    need(rows - rows87 == ADDED, 'added rows')
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
    final, crow, value = circuit_value(c87, final87, ecl, centred_text, circuit)
    need(value == json_env[graph['output']], 'Lean and JSON outputs differ after ring normalization')
    need(value != json87['N'], 'output equals the 87 output')
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
        elif which == 'centre':
            body = body_of(rtext, CENTRE_HEADER)
            need(body.count(old) == 1, 'mutation anchor: ' + label)
            rtext = rtext.replace(body, body.replace(old, new))
        else:
            body = body_of(rtext, VALUE_HEADER)
            need(body.count(old) >= 1, 'mutation anchor: ' + label)
            rtext = rtext.replace(body, body.replace(old, new))
        need(ctext != centred_text or rtext != circuit, 'mutation did not change text: ' + label)
        _, _, mutated = circuit_value(c87, final87, ecl, ctext, rtext)
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
    need('theorem expression_def :\n'
         f"    expression = TenPositive{POINT['module']}.expression (fun j => (fixedPorts j : ℤ)) := rfl\n"
         in endpoint, 'endpoint expression_def')
    for path, digest in list(pins.items()) + list(lean_pins.items()):
        need(sha(path) == digest, 'input changed: ' + str(path))
    print(json.dumps({'status': 'PASS', 'graph': POINT['graph'], 'graph_sha256': PINS[GRAPH],
                      'parent_graph_sha256': PINS[GRAPH87],
                      'check87_sha256': pins[CHECK87],
                      'trace87regs_source_sha256': pins[L / 'BFS943/Trace87Regs.lean'],
                      'centred_source_sha256': pins[CENTRED],
                      'circuit_source_sha256': lean_pins[CIRCUIT],
                      'syntax_source_sha256': lean_pins[SYNTAX],
                      'endpoint_source_sha256': lean_pins[ENDPOINT],
                      'graph_rows': len(graph['source']), 'lean_registers': len(fields),
                      'interned_nodes': len(c87.keys),
                      'instance': '87/214 registers, Z = hD[H(n - V(bB + C2)) + K] - H[DB + h ecl], '
                                  'C2 = (Am1 + (Am1 + 2))(UE) - U Qt, '
                                  'N = Q(Z^2 - M^2 (4G) V^2) + (M^2 (4G) - Z^2)',
                      'mutations_rejected': rejected,
                      'port_binding': 'equal to trace75_degree402.json except the relative path '
                                      'and endianness: little',
                      'raw_sha256': c87.RAW,
                      'comparison': 'exact structural normalization in commutative rings',
                      'scope': 'external restricted-fragment parser; no Lean theorem about file bytes'},
                     sort_keys=True))


if __name__ == '__main__':
    main()
