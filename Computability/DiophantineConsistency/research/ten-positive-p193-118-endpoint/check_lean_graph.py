#!/usr/bin/env python3
"""Bind the Lean literal of package 193's whole190 118/190 circuit to its pinned JSON.

Usage (from anywhere): py -I -X utf8 -B check_lean_graph.py

The Lean circuit is `TenPositiveTrace118.value118` (BFS943/Trace118Regs.lean):
the root-scale-four norm `Q (Z^2 - M^2 (16 G) V^2) + (M^2 (16 G) - Z^2)` at the
carrier of `TenPositiveTrace118.regs118 p v`, i.e. the 87/214 register map
`TenPositiveTrace87.regs` with the carrier
`Z = h D [H (n - OmegaFold) + K] - H [D B + h eclear]` at the folded
whole-product centre
`OmegaFold = U {(Am1 + 1) [4 (E V) - theta (Sc - b B)] + 2 (S Rc)}`,
`kY = k Y`, `S = kY (X Y Y k + k - kY (Y + 1))`, `e2 = kY kY`,
`theta = U U b`, `Rc = theta (3 E + e2) - (b - c)`,
`Sc = 4 (E E) + 3 (S S) + e2 e2`. This checker

* pins the SHA-256 of the 190 JSON graph, of package 172's 87 JSON graph (the
  JSON's `parent`), of the 75 JSON graph (port binding), of the 87 record's
  checker (whose parser and normalizer it imports) and of the Lean register
  sources it reads through that checker (`TenPositiveTrace75.lean`,
  `Trace79Regs.lean`, `Trace82Regs.lean`, `Trace87Regs.lean`);
* checks the graph metadata (`whole190`, `6*q^7`, 118 operations, degree 190,
  weight `A*U^3*b^2 (folded into Sc)`, root scale 4, parent hash, no dead
  rows) and that the JSON rows differ from the 87 rows exactly by the centre
  gates, the folded transport gate and the scaled `16 G` gate (the 87 weight
  rows `L = b V`, `LBt = L B` are gone);
* parses the 87 registers with the 87 checker, then `omegaFold`, `regs118`
  and `value118` into the same interned DAG, normalizing modulo
  commutative-ring associativity, commutativity, identities and additive
  inverses (no distribution, no sampling), and requires the outputs to be the
  same node (also the rows `new_kZ`, `new_S`, `new_e2`, `new_theta`, `new_Rc`,
  `new_Sc`, `new_bB`, `new_ScShift`, `new_Vdiff`, `new_Apart`, `new_SRc`,
  `new_Omega`, `center`, `new_scaledG`, `RG`, `Znum`, `Mtot`, `sixq7`,
  `eclear` individually);
* rejects mutations (root scale 2, root scale 4 only inside the bracket,
  fold sign `Sc + b B`, unfolded centre `Sc` (weight dropped), `theta = U b`,
  `S` with `Ybar` for `Ybar + 1`, `e2 = k Ybar`, `Rc` sign `+ (b - c)`, `Sc`
  without `3 S^2`, `A` read as `A - 1`, carrier sign `n + OmegaFold`);
* requires the literal and endpoint definitions verbatim, `fixedPorts`
  textually the `IPRATrace75` one, and the JSON `coefficient_binding` to equal
  the 75 graph's exactly, with the four direct-BFS943 raw hashes, so
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
    'ops': 118, 'degree': 190, 'name': 'whole190',
    'graph': 'con-zfc-diophantine-forms/193-transport-and-pell-reuse/positive/whole190.json',
    'sha': '28a663167232f745496ddc0b2bc89fdf8339fe274782495ce35683d5ea9db0d9',
    'module': 'Trace118', 'value': 'value118',
}
GRAPH = D / POINT['graph']
GRAPH87 = (D / 'con-zfc-diophantine-forms/172-pooled-powers-round21/part2/'
           'ConZFC_Pooled_Powers_Round21_2026-10-25/scalar/positive10/positive10_degree214_ops87.json')
GRAPH75 = D / 'con-zfc-diophantine-forms/163-trace-radical/compact/equations/trace75_degree402.json'
CHECK87 = D / 'research/ten-positive-p172-87-endpoint/check_lean_graph.py'
L = D / 'Lean/DiophantineConsistency'
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
REMOVED = {('L', '*', 'cTR', 'V'), ('LBt', '*', 'L', 'Bt'), ('RG', '*', 'M2', 'Dg'),
           ('center', '-', 'n', 'LBt')}
ADDED = {('RG', '*', 'M2', 'new_scaledG'), ('center', '-', 'n', 'new_Omega'),
         ('new_3Ee2', '+', 'new_threeE', 'new_e2'), ('new_A', '+', 'Am1', 1),
         ('new_Apart', '*', 'new_A', 'new_Vdiff'), ('new_E2', '*', 'Dtau', 'Dtau'),
         ('new_EV', '*', 'Dtau', 'V'), ('new_Omega', '*', 'U', 'new_omegainner'),
         ('new_Rc', '-', 'new_theta3Ee2', 'new_bmc'), ('new_S', '*', 'new_kZ', 'new_Sinner'),
         ('new_S2', '*', 'new_S', 'new_S'), ('new_SRc', '*', 'new_S', 'new_Rc'),
         ('new_Sc', '+', 'new_sc1', 'new_e22'), ('new_ScShift', '-', 'new_Sc', 'new_bB'),
         ('new_Sinner', '-', 'V0kk', 'new_kZZp1'), ('new_U2', '*', 'U', 'U'),
         ('new_Vdiff', '-', 'new_fourEV', 'new_thetaSc'), ('new_Zp1', '+', 'qY', 1),
         ('new_bB', '*', 'cTR', 'Bt'), ('new_bmc', '-', 'cTR', 'c'), ('new_e2', '*', 'new_kZ', 'new_kZ'),
         ('new_e22', '*', 'new_e2', 'new_e2'), ('new_fourE2', '*', 4, 'new_E2'),
         ('new_fourEV', '*', 4, 'new_EV'), ('new_kZ', '*', 'k', 'qY'),
         ('new_kZZp1', '*', 'new_kZ', 'new_Zp1'), ('new_omegainner', '+', 'new_Apart', 'new_twoSRc'),
         ('new_sc1', '+', 'new_fourE2', 'new_threeS2'), ('new_scaledG', '*', 16, 'Dg'),
         ('new_theta', '*', 'new_U2', 'cTR'), ('new_theta3Ee2', '*', 'new_theta', 'new_3Ee2'),
         ('new_thetaSc', '*', 'new_theta', 'new_ScShift'), ('new_threeE', '*', 3, 'Dtau'),
         ('new_threeS2', '*', 3, 'new_S2'), ('new_twoSRc', '*', 2, 'new_SRc')}
OMEGA_HEADER = 'def omegaFold (p : Fin 4 → R) (v : Fin 10 → R) : R :=\n'
REGS_HEADER = 'def regs118 (p : Fin 4 → R) (v : Fin 10 → R) : Regs R :=\n'
VALUE_HEADER = f"def {POINT['value']} (p : Fin 4 → R) (v : Fin 10 → R) : R :=\n"
OMEGA_LETS = ('kY', 'S', 'e2', 'theta', 'Rc', 'Sc')
GATE = '(v 7 - omegaFold p v)'
MUTATIONS = [
    ('root scale 2', 'value', '(16 * r.Gn)', '(4 * r.Gn)'),
    ('root scale 4 only inside', 'value', 'r.Q * (r.Z * r.Z - r.M * r.M * (16 * r.Gn)',
     'r.Q * (r.Z * r.Z - r.M * r.M * r.Gn'),
    ('fold sign Sc + b B', 'omega', 'theta * (Sc - r.b * r.B)', 'theta * (Sc + r.b * r.B)'),
    ('unfolded centre (weight dropped)', 'omega', 'theta * (Sc - r.b * r.B)', 'theta * Sc'),
    ('theta = U b', 'omega', 'let theta := r.U * r.U * r.b', 'let theta := r.U * r.b'),
    ('S with Ybar for Ybar + 1', 'omega', '(r.Y + 1))', 'r.Y)'),
    ('e2 = k Ybar', 'omega', 'let e2 := kY * kY', 'let e2 := kY'),
    ('Rc sign + (b - c)', 'omega', '- (r.b - r.c)', '+ (r.b - r.c)'),
    ('Sc without 3 S^2', 'omega', ' + 3 * (S * S)', ''),
    ('A read as A - 1', 'omega', '(r.Am1 + 1) *', 'r.Am1 *'),
    ('carrier sign n + OmegaFold', 'regs', GATE, '(v 7 + omegaFold p v)'),
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


def circuit_value(c87, final87, ecl, circuit_text):
    """Interned output of `value118` and the named rows."""
    env = {'r_' + name: value for name, value in final87.items()}
    env.update({f'v{i}': c87.symbol(n) for i, n in enumerate(WITNESSES)})
    obody = body_of(circuit_text, OMEGA_HEADER).split('\n')
    need(obody[0] == '  let r := TenPositiveTrace87.regs p v', 'omegaFold body')
    oenv = dict(env)
    rest = []
    order = []
    for line in obody[1:]:
        match = re.fullmatch(r'  let ([A-Za-z][A-Za-z0-9_]*) := (.+)', line)
        if match and not rest:
            need(match[1] not in oenv and match[1] in OMEGA_LETS, 'omegaFold let')
            oenv[match[1]] = c87.parse_expression(match[2], oenv)
            order.append(match[1])
        else:
            rest.append(line.strip())
    need(tuple(order) == OMEGA_LETS, 'omegaFold lets')
    omega = c87.parse_expression(' '.join(rest), oenv)
    # the folded carrier
    lines = body_of(circuit_text, REGS_HEADER).split('\n')
    need(lines[0] == '  let r := TenPositiveTrace87.regs p v', 'regs118 instance line')
    update = ' '.join(x.strip() for x in lines[1:])
    need(update.startswith('{ r with Z := ') and update.endswith(' }'), 'regs118 update shape')
    ztext = (update[len('{ r with Z := '):-2].replace('TenPositiveTrace87.ecl p v', 'ECL')
             .replace('omegaFold p v', 'OMEGA'))
    zenv = dict(env)
    zenv.update({'OMEGA': omega, 'ECL': ecl})
    Z = c87.parse_expression(ztext, zenv)
    final = dict(final87)
    final['Z'] = Z
    vlines = body_of(circuit_text, VALUE_HEADER).splitlines()
    need(vlines[0] == '  let r := regs118 p v', 'value body')
    venv = {'r_' + name: value for name, value in final.items()}
    value = c87.parse_expression(' '.join(x.strip() for x in vlines[1:]), venv)
    mul = c87.mul

    def sub(x, y):
        return c87.add(x, y, -1)
    E, V, b, B = final87['E'], final87['V'], final87['b'], final87['B']
    S, theta, Sc = oenv['S'], oenv['theta'], oenv['Sc']
    A = c87.add(final87['Am1'], c87.number(1))
    bB = mul(b, B)
    ScShift = sub(Sc, bB)
    Vdiff = sub(mul(c87.number(4), mul(E, V)), mul(theta, ScShift))
    SRc = mul(S, oenv['Rc'])
    scaledG = mul(c87.number(16), final87['Gn'])
    rows = {'new_kZ': oenv['kY'], 'new_S': S, 'new_e2': oenv['e2'], 'new_theta': theta,
            'new_Rc': oenv['Rc'], 'new_Sc': Sc, 'new_bB': bB, 'new_ScShift': ScShift,
            'new_Vdiff': Vdiff, 'new_Apart': mul(A, Vdiff), 'new_SRc': SRc, 'new_Omega': omega,
            'center': sub(c87.symbol('n'), omega), 'new_scaledG': scaledG,
            'RG': mul(mul(final87['M'], final87['M']), scaledG)}
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
         graph['exact_degree'] == POINT['degree'] and
         graph['transport_weight'] == 'A*U^3*b^2 (folded into Sc)' and
         graph['name'] == POINT['name'] and graph['denominator'] == '6*q^7' and
         graph['root_scale'] == 4 and graph['domain'] == 'strictly positive integers' and
         graph['output'] == 'N' and graph['parent']['sha256'] == PINS[GRAPH87], 'graph metadata')
    rows87 = {tuple(r) for r in graph87['source']}
    rows = {tuple(r) for r in graph['source']}
    need(rows87 - rows == REMOVED, 'removed 87 rows')
    need(rows - rows87 == ADDED, 'added rows')
    need(graph['coefficient_binding'] == graph75['coefficient_binding'], 'port binding differs from 75')
    binding = graph['coefficient_binding']
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
    circuit = CIRCUIT.read_text(encoding='utf8')
    final, crow, value = circuit_value(c87, final87, ecl, circuit)
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
        header = {'omega': OMEGA_HEADER, 'regs': REGS_HEADER, 'value': VALUE_HEADER}[which]
        body = body_of(circuit, header)
        need(body.count(old) >= 1, 'mutation anchor: ' + label)
        if which != 'value':
            need(body.count(old) == 1, 'mutation anchor not unique: ' + label)
        mutated_text = circuit.replace(body, body.replace(old, new))
        need(mutated_text != circuit, 'mutation did not change text: ' + label)
        _, _, mutated = circuit_value(c87, final87, ecl, mutated_text)
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
                      'circuit_source_sha256': lean_pins[CIRCUIT],
                      'syntax_source_sha256': lean_pins[SYNTAX],
                      'endpoint_source_sha256': lean_pins[ENDPOINT],
                      'graph_rows': len(graph['source']), 'lean_registers': len(fields),
                      'interned_nodes': len(c87.keys),
                      'instance': '87/214 registers, Z = hD[H(n - OmegaFold) + K] - H[DB + h ecl], '
                                  'OmegaFold = U{(Am1 + 1)[4EV - theta(Sc - bB)] + 2 S Rc}, '
                                  'Rc = theta(3E + e2) - (b - c), Sc = 4EE + 3SS + e2 e2, '
                                  'N = Q(Z^2 - M^2 (16G) V^2) + (M^2 (16G) - Z^2)',
                      'mutations_rejected': rejected,
                      'port_binding': 'equal to trace75_degree402.json',
                      'raw_sha256': c87.RAW,
                      'comparison': 'exact structural normalization in commutative rings',
                      'scope': 'external restricted-fragment parser; no Lean theorem about file bytes'},
                     sort_keys=True))


if __name__ == '__main__':
    main()
