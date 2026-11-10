#!/usr/bin/env python3
"""Emit and check the Lean literals of five eleven-integer equations of packages 135 and 144:

  352/125   Lean/DiophantineConsistency/P135/P135Syntax352.lean
            from 135-cofinal-anchors-round17/scalar/free_cofactor11_none.json
  340/129   Lean/DiophantineConsistency/P135/P135Syntax340.lean
            from 135-cofinal-anchors-round17/scalar/free_cofactor11_simple.json
  328/130   Lean/DiophantineConsistency/P135/P135Syntax328.lean
            from 135-cofinal-anchors-round17/scalar/free_cofactor11_sharp.json
  316/133   Lean/DiophantineConsistency/P144/P144Syntax316.lean
            from 144-shared-certificates-round18/scalar/free_whole_center11_c316.json
  308/140   Lean/DiophantineConsistency/P144/P144Syntax308.lean
            from 144-shared-certificates-round18/scalar/free_whole_center11_c308.json

(JSON paths below `con-zfc-diophantine-forms/`.) The JSON inputs are inert data with pinned
SHA-256 (below). The five circuits are the linear-cofactor circuit of package 172's 300/144
equation with another centre and a smaller radical weight; nodes 0..132 are the same in all five.

Each Lean literal has one definition per JSON node, in JSON order, exactly as the literals of
`research/p172-integer11/tools/gen_literal172.py`, whose leaf emitter, parser, comparison and DAG
evaluator are reused here:
  def n<i> (p : Fin 6 → ℤ) : Expr (Fin 11) := ...

Each node gets an evaluation lemma `e<i>`, proved from its two children only. A named register
of the JSON that is a field of `LCValue.Regs` evaluates to that field of `P135Value.regs<form>`,
closed by `rfl`: the register map (`LCValue.regsK` at the slots `k300`, `kq300`, `L300`, the
centre and the weight of the form) must agree with the DAG gate by gate, operand order included.
The JSON names `Dcar`, `Dcar2`, `Dcar3`, `kq3`, `qscale`, `shift` are the fields `Dc`, `Dc2`,
`Dc3`, `kq2`, `q3`, `Psi`. Every other gate (the unnamed ones, and `lam` and `corr` inside the
centres) evaluates to the expression of its children. The output node evaluates to
`P135Value.value<form>`.

The operand order of the JSON differs from `regsK` at up to three gates per form. There the lemma
states the `regsK` order and is closed by commutativity instead of `rw` alone:
  * the product `(q2 - Derr) * (Yk * Yk)` inside `Budget` (all five forms);
  * the weight gate `4 * S2` (the three forms of package 135; package 144 has `S2 * 64`);
  * `n * S` of 352/125, which has no centre: it is stated as `S * (n + 0)`.
The generator checks the shape of each such gate before it applies the exception.

Usage:
  py -I -X utf8 -B gen_literal135.py [--form 352|340|328|316|308]          write the Lean file(s)
  py -I -X utf8 -B gen_literal135.py [--form ...] --check   for each form: check the JSON pin;
      regenerate and compare byte for byte; parse every `def n<i>` of the file on disk back and
      compare it with JSON node i; check the DAG and the parsed literal numerically against the
      PROOF.md section 1 formulas modulo 2^127-1; check that the literal is none of the other four
      forms; run mutation controls.
Without `--form`, all five forms are processed.
"""
from pathlib import Path
import hashlib, importlib.util, json, random, sys

HERE = Path(__file__).resolve()
DC = HERE.parents[3]

_spec = importlib.util.spec_from_file_location(
    'gen_literal172', DC / 'research/p172-integer11/tools/gen_literal172.py')
g172 = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(g172)
need, VARS, PORTS, OPS, EVAL = g172.need, g172.VARS, g172.PORTS, g172.OPS, g172.EVAL
leaf_lean, parse_lean, compare = g172.leaf_lean, g172.parse_lean, g172.compare
PRIME, eval_dag = g172.PRIME, g172.eval_dag

P135 = 'con-zfc-diophantine-forms/135-cofinal-anchors-round17/scalar/'
P144 = 'con-zfc-diophantine-forms/144-shared-certificates-round18/scalar/'
FORMS = {
    '352': dict(
        json=P135 + 'free_cofactor11_none.json', package=135,
        sha='632f92bcabf691345329363faa704685d272636ec32c8a94685a92d06bc0df54',
        lean='Lean/DiophantineConsistency/P135/P135Syntax352.lean', module='P135Syntax352',
        tag='352/125', ops=125, counts=(80, 25, 20), output=148, degree=352, weight=4,
        centre='no centre', seed=135352125),
    '340': dict(
        json=P135 + 'free_cofactor11_simple.json', package=135,
        sha='31d1e1824512b20f6a73ce30e4eed5c2f6f00e156844137eab65f865190e9fc1',
        lean='Lean/DiophantineConsistency/P135/P135Syntax340.lean', module='P135Syntax340',
        tag='340/129', ops=129, counts=(83, 26, 20), output=152, degree=340, weight=4,
        centre='the centre `P135Value.psi340`', seed=135340129),
    '328': dict(
        json=P135 + 'free_cofactor11_sharp.json', package=135,
        sha='dff701474d8720a20e804cf52af7fa24d36a9293360f38868536482400b255fc',
        lean='Lean/DiophantineConsistency/P135/P135Syntax328.lean', module='P135Syntax328',
        tag='328/130', ops=130, counts=(83, 27, 20), output=153, degree=328, weight=4,
        centre='the centre `P135Value.psi328`', seed=135328130),
    '316': dict(
        json=P144 + 'free_whole_center11_c316.json', package=144,
        sha='c015b822e0e78a3ae81f706b62cc0a7131181effd3b273991ee4c8c1a12bc7d3',
        lean='Lean/DiophantineConsistency/P144/P144Syntax316.lean', module='P144Syntax316',
        tag='316/133', ops=133, counts=(85, 27, 21), output=158, degree=316, weight=64,
        centre='the centre `P135Value.psi316`', seed=144316133),
    '308': dict(
        json=P144 + 'free_whole_center11_c308.json', package=144,
        sha='0ae634d03f271c3667b30ce72932f17db1f1dd87b3046b3984fca25f172915f9',
        lean='Lean/DiophantineConsistency/P144/P144Syntax308.lean', module='P144Syntax308',
        tag='308/140', ops=140, counts=(90, 28, 22), output=165, degree=308, weight=64,
        centre='the centre `P135Value.psi308`', seed=144308140),
}
# JSON register names that are a differently named field of `LCValue.Regs`.
ALIAS = {'Dcar': 'Dc', 'Dcar2': 'Dc2', 'Dcar3': 'Dc3', 'kq3': 'kq2', 'qscale': 'q3',
         'shift': 'Psi'}
# The fields a named gate may be stated as. `lam` and `gamma` are fields of `Regs` too, but they
# are the registers of package 172's centres; the `lam` of these JSONs is another polynomial.
FIELDS = [x for x in g172.FIELDS if x not in ('lam', 'gamma')]
# Named gates that are not stated as fields: the registers inside the centres, and the output.
INLINE = ['lam', 'corr', 'output']


def gate_names(d):
    """Gate index -> the `Regs` field (or inline name) the JSON names it, after `ALIAS`."""
    nodes, names = d['nodes'], {}
    for name, i in sorted(d['named_registers'].items()):
        if nodes[i][0] not in OPS:
            continue
        field = ALIAS.get(name, name)
        need(field in FIELDS or field in INLINE, 'named gate is a Regs field or inlined: ' + name)
        need(names.setdefault(i, field) == field, f'node {i} has two different register names')
    return names


def load(f):
    raw = (DC / f['json']).read_bytes()
    need(hashlib.sha256(raw).hexdigest() == f['sha'], 'JSON SHA-256 pin: ' + f['json'])
    d = json.loads(raw)
    need(d['schema'] == 'integer-polynomial-dag-v1', 'schema')
    need(d['variables'] == VARS, 'variable order')
    need(d['output'] == len(d['nodes']) - 1 == f['output'], 'output node')
    mul, add, sub = f['counts']
    need(d['operation_counts'] == {'add': add, 'mul': mul, 'sub': sub} and d['operations'] == f['ops'],
         'operation counts')
    need(sum(1 for r in d['nodes'] if r[0] in OPS) == f['ops'], 'live gate count')
    need(d['exact_degree'] == f['degree'], 'degree')
    gate_names(d)
    return d


def shape(d, f):
    """The gates where the JSON operand order differs from `LCValue.regsK`, with their shapes
    checked: {node: 'swap' | 'zero'}. Also the indices the mutation controls use."""
    nodes, named = d['nodes'], d['named_registers']
    exc, idx = {}, {}
    # Budget = (Yk * Yk) * (q2 - Derr) - ...; the JSON has (q2 - Derr) * (Yk * Yk).
    bp = nodes[named['Budget']][1]
    need(nodes[named['Budget']][0] == 'sub' and nodes[bp][0] == 'mul', 'Budget = product - ...')
    a, b = nodes[bp][1], nodes[bp][2]
    need(nodes[a] == ['sub', named['q2'], named['Derr']], 'Budget: the factor q2 - Derr')
    need(nodes[b] == ['mul', named['Yk'], named['Yk']], 'Budget: the factor Yk * Yk')
    exc[bp] = 'swap'
    # pc = Cy * (Df * (B * (S2 * wt))); package 135 has 4 * S2.
    c1 = nodes[named['pc']]
    need(c1[0] == 'mul' and c1[1] == named['Cy'], 'pc = Cy * ...')
    c2 = nodes[c1[2]]
    need(c2[0] == 'mul' and c2[1] == named['Df'], 'pc = Cy * (Df * ...)')
    c3 = nodes[c2[2]]
    need(c3[0] == 'mul' and c3[1] == named['B'], 'pc = Cy * (Df * (B * ...))')
    wg = c3[2]
    wt = ['integer', f['weight']]
    if nodes[wg][0] == 'mul' and nodes[wg][2] == named['S2'] and nodes[nodes[wg][1]] == wt:
        exc[wg] = 'swap'
        idx['weight_leaf'] = nodes[wg][1]
    else:
        need(nodes[wg][0] == 'mul' and nodes[wg][1] == named['S2'] and nodes[nodes[wg][2]] == wt,
             'the weight gate S2 * wt')
        idx['weight_leaf'] = nodes[wg][2]
    idx['weight_gate'] = wg
    # Z = S * (n + Psi) - Ac; the form without a centre has n * S - Ac.
    z = nodes[named['Z']]
    need(z[0] == 'sub' and z[2] == named['Ac'], 'Z = ... - Ac')
    zs = nodes[z[1]]
    n = VARS.index('n')
    if 'shift' in named:
        need(zs[0] == 'mul' and zs[1] == named['S'], 'Z = S * ... - Ac')
        need(nodes[zs[2]] == ['add', n, named['shift']], 'Z = S * (n + shift) - Ac')
        idx['centre_add'] = zs[2]
    else:
        need(zs == ['mul', n, named['S']], 'Z = n * S - Ac')
        exc[z[1]] = 'zero'
    return exc, idx


def generate(f, d):
    nodes = d['nodes']
    named = gate_names(d)
    exc, _ = shape(d, f)
    form = f['tag'].split('/')[0]
    mod, regs, value = f['module'], 'regs' + form, 'value' + form
    gen = f'gen_literal135.py --form {form}'
    mul, add, sub = f['counts']
    out = []
    w = out.append
    w('import DiophantineConsistency.WeightedExpressionDegree')
    w('import DiophantineConsistency.P135.P135Value')
    w('import DiophantineConsistency.P138.P138Ports')
    w('')
    w(f"/-! # Package {f['package']}'s eleven-integer {f['tag']} equation, as a Lean literal")
    w('')
    w(f'Generated by `research/p135-integer11/tools/{gen}` from')
    w(f"`{f['json']}`")
    w(f'(SHA-256 `{f["sha"]}`): {len(nodes)} nodes, {f["ops"]} live operations')
    w(f'({mul} `mul`, {add} `add`, {sub} `sub`), variables `j C z h r v w T c n s`, output node '
      f'{d["output"]}. Node `nᵢ` is')
    w('the JSON node `i`; the six coefficient leaves are the integer constants `p 0 … p 5`')
    w('(`beta K0 MC MF cone_A cone_B`).')
    w('')
    w(f"The circuit is `LCValue.regsK` at the slots of package 172's 300/144 form, with {f['centre']}")
    w(f"and the radical weight `{f['weight']}`: `P135Value.{regs}`.")
    w('')
    w('The evaluation is proved gate by gate (`eᵢ`, from the two children only): a named register')
    w(f'that is a field of `LCValue.Regs` evaluates to that field of `P135Value.{regs}`, every other')
    w('gate to the expression of its children. Where the JSON orders the two operands of a product')
    w('the other way round than `regsK` does, the lemma states the `regsK` order and is closed by')
    w('commutativity. `evalRing_literal`: the literal evaluates to')
    w(f'`P135Value.{value}` in every commutative ring; `literal_zero_iff`: at the six ports, its zeros')
    w(f'in the ring of differences of a model of `𝗜𝚺₁` are the zeros of `{value} portsR`. The')
    w('correspondence with the JSON is checked by `gen_literal135.py --check` (byte-identical')
    w('regeneration, node-by-node parse, numeric agreement, mutation rejection). -/')
    w('set_option autoImplicit false')
    w('set_option maxRecDepth 8192')
    w('set_option linter.unusedVariables false')
    w('noncomputable section')
    w(f'namespace DiophantineConsistency.{mod}')
    w('open LCValue P135Value')
    w('')
    w('/-! ## The literal DAG -/')
    w('')
    for i, row in enumerate(nodes):
        if row[0] in OPS:
            body, com = f'n{row[1]} p {OPS[row[0]]} n{row[2]} p', ''
        else:
            body, com = leaf_lean(row)
        if i in named:
            com = f'  -- {named[i]}'
        w(f'def n{i} (p : Fin 6 → ℤ) : Expr (Fin 11) := {body}{com}')
    w('')
    w('/-- The literal polynomial at the integer ports `p`. -/')
    w(f'def literal (p : Fin 6 → ℤ) : Expr (Fin 11) := n{d["output"]} p')
    w('')
    w('/-! ## Gate-by-gate evaluation -/')
    w('')
    w('section Eval')
    w('variable {𝔸 : Type*} [CommRing 𝔸] (p : Fin 6 → ℤ) (x : Fin 11 → 𝔸)')
    w(f'local notation "𝓟" => {regs} (fun i => (p i : 𝔸)) x')
    w('')
    terms = []
    for i, row in enumerate(nodes):
        kind = row[0]
        if kind == 'variable':
            t = f'x {VARS.index(row[1])}'
            w(f'theorem e{i} : (n{i} p).evalRing x = {t} := rfl')
        elif kind == 'coefficient':
            t = f'(p {PORTS.index(row[1])} : 𝔸)'
            w(f'theorem e{i} : (n{i} p).evalRing x = {t} := rfl')
        elif kind == 'integer':
            t = f'({row[1]} : 𝔸)'
            cast = 'Int.cast_one' if row[1] == 1 else 'Int.cast_ofNat'
            w(f'theorem e{i} : (n{i} p).evalRing x = {t} := by')
            w(f'  rw [n{i}, Expr.evalRing_constant, {cast}]')
        else:
            a, b = row[1], row[2]
            rws = [f'n{i}', EVAL[kind], f'e{a}'] + ([f'e{b}'] if b != a else [])
            if i in exc:
                need(kind == 'mul' and a != b and i not in named and i != d['output'],
                     f'node {i}: an operand-order exception is an unnamed product')
                if exc[i] == 'swap':
                    t, close = f'({terms[b]} * {terms[a]})', '; exact mul_comm _ _'
                else:
                    t, close = f'({terms[b]} * ({terms[a]} + (0 : 𝔸)))', '; ring'
            elif i == d['output']:
                t, close = f'{value} (fun i => (p i : 𝔸)) x', '; rfl'
            elif i in named and named[i] in FIELDS:
                t, close = f'(𝓟).{named[i]}', '; rfl'
            else:
                t, close = f'({terms[a]} {OPS[kind]} {terms[b]})', ''
            w(f'theorem e{i} : (n{i} p).evalRing x = {t} := by')
            w(f'  rw [{", ".join(rws)}]' + close)
        terms.append(t)
    w('')
    w(f'/-- **The literal evaluates to `P135Value.{value}` in every commutative ring.** -/')
    w(f'theorem evalRing_literal : (literal p).evalRing x = {value} (fun i => (p i : 𝔸)) x :=')
    w(f'  e{d["output"]} p x')
    w('')
    w('end Eval')
    w('')
    w('section Model')
    w('open LO LO.FirstOrder LO.FirstOrder.Arithmetic')
    w('open scoped LO.FirstOrder LO.FirstOrder.Arithmetic')
    w('open ModelDifferenceRing P138Ports')
    w('variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]')
    w('')
    w(f'/-- At the six fixed ports, zeros of the literal in `DiffRing V` are zeros of `{value} portsR`. -/')
    w('theorem literal_zero_iff (x : Fin 11 → DiffRing V) :')
    w(f'    (literal (fun i => (ports6 i : ℤ))).evalRing x = 0 ↔ {value} portsR x = 0 := by')
    w('  rw [evalRing_literal]')
    w('  rfl')
    w('')
    w('end Model')
    w('')
    w(f'#print axioms DiophantineConsistency.{mod}.evalRing_literal')
    w(f'#print axioms DiophantineConsistency.{mod}.literal_zero_iff')
    w('')
    w(f'end DiophantineConsistency.{mod}')
    return '\n'.join(out) + '\n'


# ---------------------------------------------------------------- numeric gate (PROOF.md formulas)

def eval_proof_md(form, xs, ps):
    """Section 1 of the two packages' `scalar/PROOF.md` (the free-scale family), transcribed
    independently: `Z = S (n + Psi) - Ac`, `pc = wt S^2 B Df Cy`."""
    j, C, z, h, r, v, w, T, c, n, s = xs
    beta, K0, MC, MF, cA, cB = ps
    J = 6 * j + 1; q = beta * J + 1; W = 12 * w + 4
    X = q * W; Y = v; E = X * Y; ell = X * Y * Y
    a = E + Y; A = a + 2; H = 4 * a + 3; Delta = a * a + H
    F = (K0 + W) * C - z * (q - 1)
    R = (q * (q - F) - C) * (q * q - 1) + (MC + q * MF) * J
    k = R + 1 + h * E
    eta = c - Y * k
    Derr = (cA * F - q)**2 + (cB * C - q)**2
    B0 = k * k * (q * q - Derr) - 4 * q * q * eta * eta
    Budget = Y * Y * B0 - k * k * q**8
    Dt = 1 + ell * (ell + 1) * k * k; D = Budget - 4
    P = Dt * (1 + D * Dt * s * s)
    Dm = 1 + Delta * c * c; B = r * A * Dm; U = r * c * c * Dm
    I2 = c**4 * B
    Df = 1 + Delta * I2; Q = Delta**2 * I2; delta = Q - 1
    V = Df * (c - R + 4 * A * U * T) - c; Cy = Q * V * V - 1
    K = X * (3 * c - 2 * X) + 2; M = 2 * q**3; Dc = H * M; S = s * r * H * M**5
    zc = Dc * T + M * K + H * (v - q**3)
    Ac = (zc * zc + 3 * Dc * Dc) * (zc**3 - 19 * Dc**3)
    whole = ((8 * Delta + 4) * U - r * c**4) * V
    Psi = {'352': 0,
           '340': 2 * A * A * U * V,
           '328': (2 * Delta + 1) * U * V,
           '316': whole,
           '308': whole + 2 * U**3 * T * (c * c - 2)}[form]
    wt = {'352': 4, '340': 4, '328': 4, '316': 64, '308': 64}[form]
    Z = S * (n + Psi) - Ac
    pa = delta * Z * Z; pb = delta * S * S * P; pc = wt * S * S * B * Df * Cy
    return ((pa + pb - pc)**2 - 4 * pa * pb) % PRIME


def numeric_gate(form, nodes, out, seed, trials=40):
    rng = random.Random(seed)
    for _ in range(trials):
        xs = [rng.randrange(PRIME) for _ in VARS]
        ps = [rng.randrange(PRIME) for _ in PORTS]
        if eval_dag(nodes, out, xs, ps) != eval_proof_md(form, xs, ps):
            return False
    return True


def mutations(f, d):
    """Corrupted copies of the DAG: (name, nodes, output). Each must be rejected."""
    nodes, out = d['nodes'], d['output']
    named = d['named_registers']
    _, idx = shape(d, f)
    i19 = [i for i, r in enumerate(nodes) if r == ['integer', 19]]
    i3 = [i for i, r in enumerate(nodes) if r == ['integer', 3]]
    need(len(i19) == 1 and len(i3) == 1, 'the unique integer leaves 19 and 3')
    need(nodes[out][0] == 'sub', 'the output is the subtraction inner^2 - 4 pa pb')
    k = named['k']
    # the gate of `k` that holds h * E, i.e. the `mul` child of the last `add`
    hm = nodes[k][2]
    need(nodes[hm] == ['mul', VARS.index('h'), named['E']], 'k = (1 + R) + h * E')
    kq = named['kq3']
    need(nodes[kq] == ['mul', k, named['q3']], 'kq3 = k * q3')
    names = ['child', 'op', 'literal19', 'weight', 'variable', 'coefficient', 'modulus', 'budget']
    if 'centre_add' in idx:
        names.append('centre')
    cases = []
    for name in names:
        bad = [list(r) for r in nodes]
        if name == 'child':
            bad[out] = ['sub', bad[out][1], bad[out][1]]
        elif name == 'op':
            bad[out] = ['add'] + bad[out][1:]
        elif name == 'literal19':
            bad[i19[0]] = ['integer', 18]
        elif name == 'weight':
            # the weight leaf `4` is shared with other gates: rewire the weight gate to the leaf `3`
            wg = idx['weight_gate']
            bad[wg] = ['mul'] + [i3[0] if c == idx['weight_leaf'] else c for c in nodes[wg][1:]]
        elif name == 'variable':
            bad[0] = ['variable', 'C']
        elif name == 'coefficient':
            bad[15] = ['coefficient', 'cone_B']
        elif name == 'modulus':
            bad[hm] = ['mul', bad[hm][1], named['X']]
        elif name == 'budget':
            bad[kq] = ['mul', k, named['q2']]
        else:
            ca = idx['centre_add']
            bad[ca] = ['sub'] + bad[ca][1:]
        cases.append((name, bad, out))
    cases.append(('output', [list(r) for r in nodes], out - 1))
    return cases


def check(name, f, d):
    lean_path = DC / f['lean']
    text = generate(f, d)
    disk = lean_path.read_bytes().decode('utf-8')
    need(disk == text, f'{name}: Lean file is byte-identical to a fresh generation')
    parsed, out = parse_lean(disk)
    need(compare(parsed, out, d), f'{name}: parsed Lean literal = JSON DAG node for node')
    need(numeric_gate(name, parsed, out, f['seed'], trials=8), f'{name}: parsed literal = PROOF.md 1')
    for other in FORMS:
        if other != name:
            need(not numeric_gate(other, parsed, out, f['seed'], trials=2),
                 f'{name}: the literal is not the form {other}')
    controls = 0
    for mname, bad, bout in mutations(f, d):
        need(not compare(bad, bout, d), f'{name}: mutation detected by node comparison: {mname}')
        need(not numeric_gate(name, bad, bout, f['seed'], trials=2),
             f'{name}: mutation changes the value: {mname}')
        controls += 1
    print(f'OK {name} {f["tag"]}: {len(parsed)} nodes match JSON node for node; output {out}; '
          f'byte-identical regeneration; PROOF.md numeric gate; not one of the other '
          f'{len(FORMS) - 1} forms; {controls} mutation controls rejected')


def main():
    forms = list(FORMS)
    if '--form' in sys.argv:
        sel = sys.argv[sys.argv.index('--form') + 1]
        need(sel in FORMS, 'unknown form ' + sel)
        forms = [sel]
    for name in forms:
        f = FORMS[name]
        d = load(f)
        need(numeric_gate(name, d['nodes'], d['output'], f['seed']),
             f'{name}: JSON DAG = PROOF.md section 1 modulo 2^127-1')
        if '--check' in sys.argv:
            check(name, f, d)
        else:
            path = DC / f['lean']
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(generate(f, d), encoding='utf-8', newline='\n')
            print('wrote', path.relative_to(DC).as_posix())


if __name__ == '__main__':
    main()
