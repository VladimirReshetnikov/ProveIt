#!/usr/bin/env python3
"""Emit and check the Lean literals of package 125's two three-root equations:

  direct   488/118   Lean/DiophantineConsistency/P125/P125SyntaxDirect.lean
                     from con-zfc-diophantine-forms/125-unified-binomial-round15/norm/
                          integral_direct_paired.json
                     (147 nodes, 118 live operations: 74 mul, 23 add, 21 sub; output node 146)
  centered 464/119   Lean/DiophantineConsistency/P125/P125SyntaxCentered.lean
                     from con-zfc-diophantine-forms/125-unified-binomial-round15/norm/
                          integral_centered_paired.json
                     (148 nodes, 119 live operations: 74 mul, 24 add, 21 sub; output node 147)

Both JSON inputs are inert data with pinned SHA-256 (below).

Each Lean literal has one definition per JSON node, in JSON order:
  def n<i> (p : Fin 6 → ℤ) : Expr (Fin 11) := ...
with the eleven variables `j C z h r v w T c n s` as `.var 0 … .var 10`, the six coefficient leaves
`beta K0 MC MF cone_A cone_B` as `.constant (p 0) … .constant (p 5)`, integer leaves as
`.constant (k)`, and every gate as `n<a> p (+|-|*) n<b> p`.

Each node gets an evaluation lemma `e<i>`, proved from its two children only. A named register
(`named_registers` of the JSON) evaluates to a field of one of three Lean register records, or to
the linear slot:

  * the front registers, fields of `P138Value.regs` (the front of these circuits is the front of
    package 138's native form; `Eprod` is the field `E`);
  * the back-end registers, fields of `P125Value.back` at the native index `P138Value.kN`;
  * the radicands and the paired norm schedule, fields of `P125Value.tail` at the native index and
    the slot of the form;
  * `Z`, the slot `P125Value.zD` (direct) or `P125Value.zC` (centered).

The lemma is closed by `rfl`, i.e. the hand-written register maps must agree with the DAG gate by
gate, operand order included. There are two exceptions, where the DAG and package 138's record
associate a product differently and the lemma is closed by an explicit `show … ; ring` (`RING`
below): `Budget`, whose second term is `eta * (eta * (q2 * 4))` in the DAG and
`eta * (q2 * 4 * eta)` in Lean, and `L = k * (Y * E)` in the DAG and `E * (Y * k)` in Lean. The
named node `ell` has no Lean field (`INLINE` below) and evaluates, like all unnamed nodes, to the
expression of its children. The output node evaluates to `P125Value.valueD` (direct) or
`P125Value.valueC` (centered).

Usage:
  py -I -X utf8 -B gen_literal125.py [--form direct|centered]          write the Lean file(s)
  py -I -X utf8 -B gen_literal125.py [--form direct|centered] --check  for each form: check the JSON
      pin; regenerate and compare byte for byte; parse every `def n<i>` of the file on disk back
      and compare it with JSON node i; check the DAG and the parsed literal numerically against
      the formulas of the package's scalar/PROOF.md and norm/DEGREE_PROOF.md; run mutation
      controls. With both forms, also check numerically that the two DAGs share nodes 0–123 and
      the shear `centered(n − Q V) = direct(n)`.
Without `--form`, both forms are processed.
"""
from pathlib import Path
import hashlib, json, random, re, sys

HERE = Path(__file__).resolve()
DC = HERE.parents[3]
PKG = 'con-zfc-diophantine-forms/125-unified-binomial-round15/norm/'
FORMS = {
    'direct': dict(
        json=PKG + 'integral_direct_paired.json', name='integral_direct_paired',
        sha='3825390a058f023efedeaae7e35f11f25b2cb1cbe63461cee1e14a5377501928',
        lean='Lean/DiophantineConsistency/P125/P125SyntaxDirect.lean', module='P125SyntaxDirect',
        tag='488/118', ops=118, counts=(74, 23, 21), output=146, degree=488, center=False,
        slot='zD', value='valueD', gen='gen_literal125.py --form direct', seed=125488118),
    'centered': dict(
        json=PKG + 'integral_centered_paired.json', name='integral_centered_paired',
        sha='e1934d7614f0b2449ed8543f191c08f9af05b2053ec15eb824fb48f8f9d4ff73',
        lean='Lean/DiophantineConsistency/P125/P125SyntaxCentered.lean', module='P125SyntaxCentered',
        tag='464/119', ops=119, counts=(74, 24, 21), output=147, degree=464, center=True,
        slot='zC', value='valueC', gen='gen_literal125.py --form centered', seed=125464119),
}
VARS = ['j', 'C', 'z', 'h', 'r', 'v', 'w', 'T', 'c', 'n', 's']
PORTS = ['beta', 'K0', 'MC', 'MF', 'cone_A', 'cone_B']
OPS = {'add': '+', 'sub': '-', 'mul': '*'}
EVAL = {'add': 'Expr.evalRing_add', 'sub': 'Expr.evalRing_sub', 'mul': 'Expr.evalRing_mul'}
# JSON register name -> field of `P138Value.Regs` (front, record 𝓟).
FRONT = {n: n for n in ['J', 'qm', 'q', 'q2', 'q3', 'W', 'X', 'Y', 'a', 'H', 'Delta', 'F', 'R', 'k',
                        'c2', 'eta', 'Derr', 'Budget', 'L', 'Dt', 'K', 'H2', 'H3', 'S', 'zc', 'zc2',
                        'Ac']}
FRONT['Eprod'] = 'E'
# JSON register name -> field of `P125Value.Back` (back end, record 𝓑). `shift` is named only in
# the centered JSON (the same gate is node 101 of both).
BACK = {n: n for n in ['D81', 'Dg81', 'P81', 'I', 'strong', 'Df', 'Q', 'delta', 'b0', 'V', 'Cy',
                       'S2']}
BACK_CENTERED = {'shift': 'shift'}
# JSON register name -> field of `P125Value.Tail` (radicands and norm schedule, record 𝓣).
TAIL = {n: n for n in ['Z2', 'A', 'B', 'G', 'vnorm', 'left', 'right', 'ynorm']}
# The linear slot (record-free: `P125Value.zD` or `P125Value.zC`, notation 𝓩).
SLOT = 'Z'
# Named gates with no Lean field: evaluated like unnamed nodes.
INLINE = ['ell']
# Gates whose Lean field associates a product differently: JSON name -> Lean right-hand side.
RING = {
    'Budget': '(𝓟).k * (𝓟).k * ((𝓟).q2 - (𝓟).Derr) - (𝓟).eta * ((𝓟).q2 * 4 * (𝓟).eta)',
    'L': '(𝓟).E * ((𝓟).Y * (𝓟).k)',
}
SHARED = 124   # nodes 0 … 123 are common to the two DAGs


def need(ok, msg):
    if not ok:
        raise SystemExit('FAIL: ' + msg)


def mapped(f):
    names = list(FRONT) + list(BACK) + list(TAIL) + [SLOT] + INLINE
    return names + (list(BACK_CENTERED) if f['center'] else [])


def load(f):
    raw = (DC / f['json']).read_bytes()
    need(hashlib.sha256(raw).hexdigest() == f['sha'], 'JSON SHA-256 pin: ' + f['json'])
    d = json.loads(raw)
    need(d['schema'] == 'integer-polynomial-dag-v1', 'schema')
    need(d['name'] == f['name'], 'name')
    need(d['domain'] == 'unrestricted integers', 'domain')
    need(d['variables'] == VARS and d['variable_count'] == 11, 'variable order')
    need(d['output'] == len(d['nodes']) - 1 == f['output'], 'output node')
    mul, add, sub = f['counts']
    need(d['operation_counts'] == {'mul': mul, 'add': add, 'sub': sub} and d['operations'] == f['ops'],
         'operation counts')
    need(sum(1 for r in d['nodes'] if r[0] in OPS) == f['ops'], 'live gate count')
    need(d.get('syntactic_degree_bound') == 488, 'syntactic degree bound recorded by the package')
    need(d.get('exact_degree') == f['degree'], 'exact degree recorded by the package')
    need(d.get('coefficient_binding') == 'coefficients/BINDING.json', 'coefficient binding path')
    need(d.get('description') == {'center': f['center'], 'rational': False,
                                  'norm_schedule': 'paired'}, 'description')
    named = d['named_registers']
    need(len(set(named.values())) == len(named), 'register names are attached to distinct nodes')
    names = mapped(f)
    for name, i in named.items():
        if name in VARS:
            need(d['nodes'][i] == ['variable', name] and i == VARS.index(name), 'named leaf ' + name)
        elif name == 'output':
            need(i == d['output'], 'the name `output` is attached to the output node')
        else:
            need(d['nodes'][i][0] in OPS and name in names, 'named register is mapped: ' + name)
    need(sorted(n for n in named if n not in VARS and n != 'output') == sorted(names),
         'every mapped name occurs in the JSON')
    return d


def leaf_lean(row):
    kind = row[0]
    if kind == 'variable':
        return f'.var {VARS.index(row[1])}', f'  -- {row[1]}'
    if kind == 'coefficient':
        return f'.constant (p {PORTS.index(row[1])})', f'  -- {row[1]}'
    if kind == 'integer':
        need(type(row[1]) is int and row[1] > 0, 'positive integer leaf')
        return f'.constant ({row[1]})', ''
    raise SystemExit('FAIL: leaf kind ' + kind)


def generate(f, d):
    nodes = d['nodes']
    named = {i: n for n, i in d['named_registers'].items()}
    mod, value, slot = f['module'], f['value'], f['slot']
    back = dict(BACK, **(BACK_CENTERED if f['center'] else {}))
    mul, add, sub = f['counts']
    form = 'centered' if f['center'] else 'direct'
    out = []
    w = out.append
    w('import DiophantineConsistency.WeightedExpressionDegree')
    w('import DiophantineConsistency.P125.P125Value')
    w('import DiophantineConsistency.P138.P138Ports')
    w('')
    w(f"/-! # Package 125's {form} three-root {f['tag']} equation, as a Lean literal")
    w('')
    w(f"Generated by `research/p125-integer11/tools/{f['gen']}` from")
    w(f"`{f['json']}`")
    w(f'(SHA-256 `{f["sha"]}`): {len(nodes)} nodes, {f["ops"]} live operations')
    w(f'({mul} `mul`, {add} `add`, {sub} `sub`), variables `j C z h r v w T c n s`, output node '
      f'{d["output"]}. Node `nᵢ` is')
    w('the JSON node `i`; the six coefficient leaves are the integer constants `p 0 … p 5`')
    w('(`beta K0 MC MF cone_A cone_B`).')
    w('')
    w('The evaluation is proved gate by gate (`eᵢ`, from the two children only). A named front')
    w('register evaluates to a field of `P138Value.regs` (`Eprod` is the field `E`), a named')
    w('back-end register to the field of `P125Value.back` with the same name at the native index')
    w(f'`P138Value.kN`, the slot `Z` to `P125Value.{slot}`, and a radicand or a row of the norm')
    w('schedule to the field of `P125Value.tail` with the same name; all by `rfl`, except the two')
    w('gates `Budget` and `L`, where the DAG and the record of package 138 associate a product')
    w('differently and the proof ends with an explicit `show … ; ring`. The named node `ell` has no')
    w('Lean field and evaluates, like unnamed nodes, to the expression of its children.')
    w(f'`evalRing_literal`: the literal evaluates to `P125Value.{value}` in every commutative ring;')
    w('`literal_zero_iff`: at the six ports, its zeros in the ring of differences of a model of')
    w(f'`𝗜𝚺₁` are the zeros of `P125Value.{value} portsR`. The correspondence with the JSON is')
    w('checked by `gen_literal125.py --check` (byte-identical regeneration, node-by-node parse,')
    w('mutation rejection). -/')
    w('set_option autoImplicit false')
    w('set_option maxRecDepth 8192')
    w('set_option linter.unusedVariables false')
    w('noncomputable section')
    w(f'namespace DiophantineConsistency.{mod}')
    w('open P138Value')
    w('')
    w('/-! ## The literal DAG -/')
    w('')
    for i, row in enumerate(nodes):
        if row[0] in OPS:
            body, com = f'n{row[1]} p {OPS[row[0]]} n{row[2]} p', ''
        else:
            body, com = leaf_lean(row)
        if i in named and row[0] in OPS:
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
    w('local notation "𝓟" => regs (fun i => (p i : 𝔸)) x')
    w('local notation "𝓑" => P125Value.back (fun i => (p i : 𝔸)) x (kN (fun i => (p i : 𝔸)) x)')
    w(f'local notation "𝓩" => P125Value.{slot} (fun i => (p i : 𝔸)) x (kN (fun i => (p i : 𝔸)) x)')
    w('local notation "𝓣" => P125Value.tail (fun i => (p i : 𝔸)) x (kN (fun i => (p i : 𝔸)) x)')
    w(f'  (P125Value.{slot} (fun i => (p i : 𝔸)) x (kN (fun i => (p i : 𝔸)) x))')
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
            name = named.get(i)
            raw_term = f'{terms[a]} {OPS[kind]} {terms[b]}'
            close = '; rfl'
            if i == d['output']:
                t = f'P125Value.{value} (fun i => (p i : 𝔸)) x'
            elif name in FRONT:
                t = f'(𝓟).{FRONT[name]}'
            elif name in back:
                t = f'(𝓑).{back[name]}'
            elif name in TAIL:
                t = f'(𝓣).{TAIL[name]}'
            elif name == SLOT:
                t = '𝓩'
            else:
                t = f'({raw_term})'
                close = ''
            w(f'theorem e{i} : (n{i} p).evalRing x = {t} := by')
            if name in RING:
                w(f'  rw [{", ".join(rws)}]')
                w(f'  show {raw_term} = {RING[name]}')
                w('  ring')
            else:
                w(f'  rw [{", ".join(rws)}]' + close)
        terms.append(t)
    w('')
    w(f'/-- **The literal evaluates to `P125Value.{value}` in every commutative ring.** -/')
    w('theorem evalRing_literal :')
    w(f'    (literal p).evalRing x = P125Value.{value} (fun i => (p i : 𝔸)) x :=')
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
    w('/-- At the six fixed ports, zeros of the literal in `DiffRing V` are zeros of')
    w(f'`P125Value.{value} portsR`. -/')
    w('theorem literal_zero_iff (x : Fin 11 → DiffRing V) :')
    w(f'    (literal (fun i => (ports6 i : ℤ))).evalRing x = 0 ↔ P125Value.{value} portsR x = 0 := by')
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


DEF = re.compile(r'^def n(\d+) \(p : Fin 6 → ℤ\) : Expr \(Fin 11\) := (.*?)(  -- .*)?$')


def parse_lean(text):
    """Parse every `def n<i>` back into a JSON-shaped node, independently of `generate`."""
    nodes = {}
    for line in text.splitlines():
        m = DEF.match(line)
        if not m:
            continue
        i, body = int(m.group(1)), m.group(2).strip()
        need(i not in nodes, f'duplicate node {i}')
        if (mm := re.fullmatch(r'\.var (\d+)', body)):
            nodes[i] = ['variable', VARS[int(mm.group(1))]]
        elif (mm := re.fullmatch(r'\.constant \(p (\d)\)', body)):
            nodes[i] = ['coefficient', PORTS[int(mm.group(1))]]
        elif (mm := re.fullmatch(r'\.constant \((-?\d+)\)', body)):
            nodes[i] = ['integer', int(mm.group(1))]
        else:
            mm = re.fullmatch(r'n(\d+) p ([+*-]) n(\d+) p', body)
            need(mm is not None, f'unparsable node {i}: {body}')
            op = {'+': 'add', '-': 'sub', '*': 'mul'}[mm.group(2)]
            a, b = int(mm.group(1)), int(mm.group(3))
            need(a < i and b < i, f'node {i} is not topological')
            nodes[i] = [op, a, b]
    need(sorted(nodes) == list(range(len(nodes))), 'node numbering')
    lit = re.search(r'^def literal \(p : Fin 6 → ℤ\) : Expr \(Fin 11\) := n(\d+) p$', text, re.M)
    need(lit is not None, 'literal definition')
    return [nodes[i] for i in range(len(nodes))], int(lit.group(1))


def compare(parsed, out, d):
    return parsed == d['nodes'] and out == d['output']


# ------------------------------- numeric gate (scalar/PROOF.md and norm/DEGREE_PROOF.md formulas)

PRIME = 2**127 - 1


def eval_nodes(nodes, xs, ps):
    val = []
    for row in nodes:
        k = row[0]
        if k == 'variable':
            val.append(xs[VARS.index(row[1])])
        elif k == 'coefficient':
            val.append(ps[PORTS.index(row[1])])
        elif k == 'integer':
            val.append(row[1] % PRIME)
        else:
            a, b = val[row[1]], val[row[2]]
            val.append((a + b if k == 'add' else a - b if k == 'sub' else a * b) % PRIME)
    return val


def eval_dag(nodes, out, xs, ps):
    return eval_nodes(nodes, xs, ps)[out]


def eval_proof_md(center, xs, ps):
    """The register list of 125's scalar/PROOF.md and the paired norm of norm/DEGREE_PROOF.md,
    transcribed independently. Returns (output, Q V): `Z = S n − Ac` [direct],
    `Z = S (n + Q V) − Ac` [centered]."""
    j, C, z, h, r, v, w, T, c, n, s = xs
    beta, K0, MC, MF, cA, cB = ps
    J = 6 * j + 1; q = beta * J + 1; W = 12 * w + 4; X = q * W
    Y = (2 * v + 1) * q**3; E = X * Y; a = E + Y; H = 4 * a + 3; Delta = a * a + H
    F = (K0 + W) * C - z * (q - 1)
    R = (q * (q - F) - C) * (q * q - 1) + (MC + q * MF) * J
    k = R + 1 + h * E; eta = c - Y * k
    Derr = (cA * F - q)**2 + (cB * C - q)**2
    Budget = k * k * (q * q - Derr) - 4 * q * q * eta * eta
    D = 3 * Budget - 4; L = X * Y * Y * k; Dt = 1 + L * (L + k)
    Dg = 1 + D * Dt * s * s; Pg = Dt * Dg
    I = r * c * c; Df = 1 + Delta * I * I; Q = Delta**2 * I * I; delta = Q - 1
    V = Df * (c - R + 4 * I * T) - c; Cy = Q * V * V - 1
    K = X * (3 * c - 2 * X) + 2
    zc = H * T + K; Ac = (zc * zc + 3 * H * H) * (zc**3 - 19 * H**3)
    S = s * r * H
    Z = S * (n + Q * V) - Ac if center else S * n - Ac
    A = 9 * S * S * Df; B = S * S * delta * Cy; G = 81 * S * S * Pg
    N = ((Z * Z + A - B - G)**2 - 4 * (A * Z * Z + B * G))**2 - 64 * (A * Z * Z) * (B * G)
    return N % PRIME, Q * V % PRIME


def numeric_gate(center, nodes, out, seed, trials=40):
    rng = random.Random(seed)
    for _ in range(trials):
        xs = [rng.randrange(PRIME) for _ in VARS]
        ps = [rng.randrange(PRIME) for _ in PORTS]
        if eval_dag(nodes, out, xs, ps) != eval_proof_md(center, xs, ps)[0]:
            return False
    return True


def shear_gate(dd, dc, trials=40):
    """`P125Value.valueC_shift`: the centered DAG at n' = n − Q V equals the direct DAG at n; the
    shift `Q V` (node `shift` of the centered DAG) does not read n."""
    need(dd['nodes'][:SHARED] == dc['nodes'][:SHARED], 'the two DAGs share nodes 0 … 123')
    sh = dc['named_registers']['shift']
    need(sh < SHARED, 'the shift is a shared node')
    rng = random.Random(125)
    for _ in range(trials):
        xs = [rng.randrange(PRIME) for _ in VARS]
        ps = [rng.randrange(PRIME) for _ in PORTS]
        shift = eval_nodes(dc['nodes'], xs, ps)[sh]
        if shift != eval_proof_md(True, xs, ps)[1]:
            return False
        ys = list(xs)
        ys[9] = (xs[9] - shift) % PRIME
        if eval_nodes(dc['nodes'], ys, ps)[sh] != shift:
            return False
        if eval_dag(dc['nodes'], dc['output'], ys, ps) != eval_dag(dd['nodes'], dd['output'], xs, ps):
            return False
    return True


def mutations(f, d):
    """Corrupted copies of the DAG: (name, nodes, output). Each must be rejected."""
    nodes, out = d['nodes'], d['output']
    named = d['named_registers']
    i19 = [i for i, r in enumerate(nodes) if r == ['integer', 19]]
    i64 = [i for i, r in enumerate(nodes) if r == ['integer', 64]]
    need(len(i19) == 1 and len(i64) == 1, 'the unique integer leaves 19 and 64')
    vn = named['vnorm']
    need(nodes[vn] == ['sub', nodes[vn][1], named['G']], 'vnorm = (Z2 + A - B) - G')
    k = named['k']
    hm = nodes[k][2]
    need(nodes[hm] == ['mul', VARS.index('h'), named['Eprod']], 'k = (1 + R) + h * E')
    zn = named['Z']
    need(nodes[zn][0] == 'sub' and nodes[zn][2] == named['Ac'], 'Z = (slot) - Ac')
    lin = nodes[zn][1]
    if f['center']:
        slot = nodes[lin][2]                # Z = S * (n + shift) - Ac
        need(nodes[lin] == ['mul', named['S'], slot]
             and nodes[slot] == ['add', VARS.index('n'), named['shift']], 'the linear slot n + Q V')
        slot_bad = ['add', VARS.index('n'), named['V']]
    else:
        slot = lin                          # Z = n * S - Ac
        need(nodes[slot] == ['mul', VARS.index('n'), named['S']], 'the linear slot n * S')
        slot_bad = ['mul', VARS.index('T'), named['S']]
    cases = []
    for name in ('child', 'op', 'literal19', 'literal64', 'variable', 'coefficient', 'modulus',
                 'slot', 'order'):
        bad = [list(r) for r in nodes]
        if name == 'child':
            bad[out] = ['sub', nodes[out][1], nodes[out][1]]
        elif name == 'op':
            bad[vn] = ['add'] + bad[vn][1:]
        elif name == 'literal19':
            bad[i19[0]] = ['integer', 18]
        elif name == 'literal64':
            bad[i64[0]] = ['integer', 63]
        elif name == 'variable':
            bad[0] = ['variable', 'C']
        elif name == 'coefficient':
            bad[15] = ['coefficient', 'cone_B']
        elif name == 'modulus':
            bad[hm] = ['mul', VARS.index('h'), named['X']]
        elif name == 'slot':
            bad[slot] = slot_bad
        else:
            bad[out] = ['sub', nodes[out][2], nodes[out][1]]
        cases.append((name, bad, out))
    cases.append(('output', [list(r) for r in nodes], out - 1))
    return cases


def check(name, f, d):
    lean_path = DC / f['lean']
    text = generate(f, d)
    disk = lean_path.read_text(encoding='utf-8')
    need(disk == text, f'{name}: Lean file is byte-identical to a fresh generation')
    parsed, out = parse_lean(disk)
    need(compare(parsed, out, d), f'{name}: parsed Lean literal = JSON DAG node for node')
    need(numeric_gate(f['center'], parsed, out, f['seed'], trials=8),
         f'{name}: parsed literal = PROOF.md formulas')
    controls = 0
    for mname, bad, bout in mutations(f, d):
        need(not compare(bad, bout, d), f'{name}: mutation detected by node comparison: {mname}')
        need(not numeric_gate(f['center'], bad, bout, f['seed'], trials=2),
             f'{name}: mutation changes the value: {mname}')
        controls += 1
    print(f'OK {name} {f["tag"]}: {len(parsed)} nodes match JSON node for node; output {out}; '
          f'byte-identical regeneration; PROOF.md numeric gate; {controls} mutation controls rejected')


def main():
    forms = list(FORMS)
    if '--form' in sys.argv:
        sel = sys.argv[sys.argv.index('--form') + 1]
        need(sel in FORMS, 'unknown form ' + sel)
        forms = [sel]
    data = {}
    for name in forms:
        f = FORMS[name]
        d = load(f)
        need(numeric_gate(f['center'], d['nodes'], d['output'], f['seed']),
             f'{name}: JSON DAG = PROOF.md formulas modulo 2^127-1')
        data[name] = d
        if '--check' in sys.argv:
            check(name, f, d)
        else:
            path = DC / f['lean']
            path.write_text(generate(f, d), encoding='utf-8', newline='\n')
            print('wrote', path)
    if '--check' in sys.argv and len(data) == 2:
        need(shear_gate(data['direct'], data['centered']),
             'shear: centered(n - Q V) = direct(n) modulo 2^127-1')
        print('OK shear: nodes 0-123 shared; centered value at n - Q V = direct value at n '
              '(40 points mod 2^127-1)')


if __name__ == '__main__':
    main()
