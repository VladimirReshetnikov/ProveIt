#!/usr/bin/env python3
"""Emit and check package 138's two Lean literals:

  native 924/107   Lean/DiophantineConsistency/P138/P138Syntax.lean
                   from con-zfc-diophantine-forms/138-semantic-signs/integer11/parity_saturated11_native.json
                   (131 nodes, 107 live operations: 66 mul, 24 add, 17 sub; output node 130)
  short  840/108   Lean/DiophantineConsistency/P138/P138ShortSyntax.lean
                   from con-zfc-diophantine-forms/138-semantic-signs/integer11/parity_saturated11_short.json
                   (132 nodes, 108 live operations: 67 mul, 24 add, 17 sub; output node 131)

Both JSON inputs are inert data with pinned SHA-256 (below).

Each Lean literal has one definition per JSON node, in JSON order:
  def n<i> (p : Fin 6 → ℤ) : Expr (Fin 11) := ...
with the eleven variables `j C z h r v w T c n s` as `.var 0 … .var 10`, the six coefficient leaves
`beta K0 MC MF cone_A cone_B` as `.constant (p 0) … .constant (p 5)`, integer leaves as
`.constant (k)`, and every gate as `n<a> p (+|-|*) n<b> p`.

Each node gets an evaluation lemma `e<i>`, proved from its two children only: a named register
(`named_registers` of the JSON) evaluates to the field of the same name of `P138Value.regs`
(native) or `P138Value.regsS` (short), closed by `rfl`, i.e. the hand-written register map of
`P138Value` must agree with the DAG gate by gate, operand order included; an unnamed node evaluates
to the expression of its children. The output node evaluates to `P138Value.value` (native) or
`P138Value.valueS` (short).

Usage:
  py -I -X utf8 -B gen_literal.py [--form native|short]          write the Lean file(s)
  py -I -X utf8 -B gen_literal.py [--form native|short] --check  for each form: check the JSON pin;
      regenerate and compare byte for byte; parse every `def n<i>` of the file on disk back and
      compare it with JSON node i; check the DAG and the parsed literal numerically against the
      PROOF.md formulas; run mutation controls. With both forms, also check the completeness
      transfer `short(h (3w+1)(2v+1)) = native(h)` numerically.
Without `--form`, both forms are processed.
"""
from pathlib import Path
import hashlib, json, random, re, sys

HERE = Path(__file__).resolve()
DC = HERE.parents[3]
PKG = 'con-zfc-diophantine-forms/138-semantic-signs/integer11/'
FORMS = {
    'native': dict(
        json=PKG + 'parity_saturated11_native.json',
        sha='ae109bcc44bd2d6c7102875eb79e562366bbf46ce1e350d0cfa8cc026add4195',
        lean='Lean/DiophantineConsistency/P138/P138Syntax.lean', module='P138Syntax',
        tag='924/107', ops=107, counts=(66, 24, 17), output=130,
        regs='regs', value='value', gen='gen_literal.py', seed=138924107),
    'short': dict(
        json=PKG + 'parity_saturated11_short.json',
        sha='286116717dcd19faaec9f27e2a88e36a704a1a644385c1a3a9116c564994cfe7',
        lean='Lean/DiophantineConsistency/P138/P138ShortSyntax.lean', module='P138ShortSyntax',
        tag='840/108', ops=108, counts=(67, 24, 17), output=131,
        regs='regsS', value='valueS', gen='gen_literal.py --form short', seed=138840108),
}
VARS = ['j', 'C', 'z', 'h', 'r', 'v', 'w', 'T', 'c', 'n', 's']
PORTS = ['beta', 'K0', 'MC', 'MF', 'cone_A', 'cone_B']
OPS = {'add': '+', 'sub': '-', 'mul': '*'}
EVAL = {'add': 'Expr.evalRing_add', 'sub': 'Expr.evalRing_sub', 'mul': 'Expr.evalRing_mul'}
# Registers the Lean structure `P138Value.Regs` has (the leaves are not fields).
FIELDS = ['J', 'qm', 'q', 'q2', 'q3', 'W', 'X', 'Y', 'E', 'a', 'H', 'Delta', 'A', 'F', 'R', 'q24', 'k',
          'Yk', 'eta', 'Derr', 'Budget', 'L', 'Dt', 'D4', 'Pg', 'P', 'c2', 'Dm', 'BP', 'U', 'UBP',
          'strong', 'Df', 'Q', 'V', 'K', 'H2', 'H3', 'zc', 'zc2', 'Ac', 'S', 'Z', 'RG', 'Z2', 'V2']


def need(ok, msg):
    if not ok:
        raise SystemExit('FAIL: ' + msg)


def load(f):
    raw = (DC / f['json']).read_bytes()
    need(hashlib.sha256(raw).hexdigest() == f['sha'], 'JSON SHA-256 pin: ' + f['json'])
    d = json.loads(raw)
    need(d['schema'] == 'integer-polynomial-dag-v1', 'schema')
    need(d['variables'] == VARS, 'variable order')
    need(d['output'] == len(d['nodes']) - 1 == f['output'], 'output node')
    mul, add, sub = f['counts']
    need(d['operation_counts'] == {'mul': mul, 'add': add, 'sub': sub} and d['operations'] == f['ops'],
         'operation counts')
    need(sum(1 for r in d['nodes'] if r[0] in OPS) == f['ops'], 'live gate count')
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
    mod, regs, value = f['module'], f['regs'], f['value']
    mul, add, sub = f['counts']
    out = []
    w = out.append
    w('import DiophantineConsistency.WeightedExpressionDegree')
    w('import DiophantineConsistency.P138.P138Value')
    w('import DiophantineConsistency.P138.P138Ports')
    w('')
    w(f"/-! # Package 138's {f['tag']} equation, as a Lean literal")
    w('')
    w(f"Generated by `research/p138-integer11/tools/{f['gen']}` from")
    w(f"`{f['json']}`")
    w(f'(SHA-256 `{f["sha"]}`): {len(nodes)} nodes, {f["ops"]} live operations')
    w(f'({mul} `mul`, {add} `add`, {sub} `sub`), variables `j C z h r v w T c n s`, output node '
      f'{d["output"]}. Node `nᵢ` is')
    w('the JSON node `i`; the six coefficient leaves are the integer constants `p 0 … p 5`')
    w('(`beta K0 MC MF cone_A cone_B`).')
    w('')
    w('The evaluation is proved gate by gate (`eᵢ`, from the two children only): a named register')
    w(f'evaluates to the field of `P138Value.{regs}` with the same name, an unnamed node to the')
    w(f'expression of its children. `evalRing_literal`: the literal evaluates to `P138Value.{value}` in')
    w('every commutative ring; `literal_zero_iff`: at the six ports, its zeros in the ring of')
    w(f'differences of a model of `𝗜𝚺₁` are the zeros of `{value} portsR`. The correspondence with the')
    w('JSON is checked by `gen_literal.py --check` (byte-identical regeneration, node-by-node parse,')
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
            if i == d['output']:
                t = f'{value} (fun i => (p i : 𝔸)) x'
                close = True
            elif i in named:
                need(named[i] in FIELDS, 'named register is a Regs field: ' + named[i])
                t = f'(𝓟).{named[i]}'
                close = True
            else:
                t = f'({terms[a]} {OPS[kind]} {terms[b]})'
                close = False
            w(f'theorem e{i} : (n{i} p).evalRing x = {t} := by')
            w(f'  rw [{", ".join(rws)}]' + ('; rfl' if close else ''))
        terms.append(t)
    w('')
    w(f'/-- **The literal evaluates to `P138Value.{value}` in every commutative ring.** -/')
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


# ---------------------------------------------------------------- numeric gate (PROOF.md formulas)

PRIME = 2**127 - 1


def eval_dag(nodes, out, xs, ps):
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
    return val[out]


def eval_proof_md(form, xs, ps):
    """Section 'Literal definition' of 138's PROOF.md, transcribed independently.
    `M_index = E` [native], `M_index = 4q^4` [short]."""
    j, C, z, h, r, v, w, T, c, n, s = xs
    beta, K0, MC, MF, cA, cB = ps
    J = 6 * j + 1; q = beta * J + 1; W = 12 * w + 4
    X = q * W; Y = (2 * v + 1) * q**3; E = X * Y
    a = E + Y; A = a + 2; H = 4 * a + 3; Delta = a * a + H
    F = (K0 + W) * C - z * (q - 1)
    R = (q * (q - F) - C) * (q * q - 1) + (MC + q * MF) * J
    M_index = {'native': E, 'short': 4 * q**4}[form]
    k = R + 1 + h * M_index; eta = c - Y * k
    Derr = (cA * F - q)**2 + (cB * C - q)**2
    Budget = k * k * (q * q - Derr) - 4 * q * q * eta * eta
    L = X * Y * Y * k; Dt = 1 + L * (L + k); D = Budget - 4
    P = Dt + D * (Dt * s)**2
    Dm = 1 + Delta * c * c; BP = Dm * P; U = A * r * c * c
    Df = 1 + Delta * U * U * BP; Q = Delta**2 * U * U * BP
    V = Df * (c - R + 4 * U * BP * T) - c
    K = X * (3 * c - 2 * X) + 2
    S = s * r * H; zc = H * T + K
    Ac = (zc * zc + 3 * H * H) * (zc**3 - 19 * H**3); Z = S * n - Ac
    RG = S * S * BP * Df
    return (Q * (Z * Z - RG * V * V) + (RG - Z * Z)) % PRIME


def numeric_gate(form, nodes, out, seed, trials=40):
    rng = random.Random(seed)
    for _ in range(trials):
        xs = [rng.randrange(PRIME) for _ in VARS]
        ps = [rng.randrange(PRIME) for _ in PORTS]
        if eval_dag(nodes, out, xs, ps) != eval_proof_md(form, xs, ps):
            return False
    return True


def transfer_gate(dn, ds, trials=40):
    """`P138Value.valueS_update`: short at h' = h (3w+1)(2v+1) equals native at h."""
    rng = random.Random(138)
    for _ in range(trials):
        xs = [rng.randrange(PRIME) for _ in VARS]
        ps = [rng.randrange(PRIME) for _ in PORTS]
        h, v, w = xs[3], xs[5], xs[6]
        ys = list(xs)
        ys[3] = h * (3 * w + 1) * (2 * v + 1) % PRIME
        if eval_dag(ds['nodes'], ds['output'], ys, ps) != eval_dag(dn['nodes'], dn['output'], xs, ps):
            return False
    return True


def mutations(form, d):
    """Corrupted copies of the DAG: (name, nodes, output). Each must be rejected."""
    nodes, out = d['nodes'], d['output']
    named = d['named_registers']
    i19 = [i for i, r in enumerate(nodes) if r == ['integer', 19]]
    need(len(i19) == 1, 'the unique integer leaf 19')
    need(nodes[out - 3][0] == 'sub', 'node out-3 is the subtraction Z2 - RG V2')
    k = named['k']
    # the gate of `k` that holds h * M_index, i.e. the `mul` child of the last `add`
    hm = nodes[k][2]
    need(nodes[hm][0] == 'mul' and nodes[hm][1] == VARS.index('h'), 'k = (1 + R) + h * M_index')
    mindex = nodes[hm][2]
    # the other form's index modulus: `E = X * Y` for the short DAG; for the native DAG (where `E`
    # precedes `q24`), the `h * M_index` gate becomes `h * q24 = h * 4 q^2`
    target, alt = (mindex, [named['X'], named['Y']]) if form == 'short' else (hm, [3, named['q24']])
    cases = []
    for name in ('child', 'op', 'literal', 'variable', 'coefficient', 'modulus'):
        bad = [list(r) for r in nodes]
        if name == 'child':
            bad[out] = ['add', out - 2, out - 2]
        elif name == 'op':
            bad[out - 3] = ['add'] + bad[out - 3][1:]
        elif name == 'literal':
            bad[i19[0]] = ['integer', 18]
        elif name == 'variable':
            bad[0] = ['variable', 'C']
        elif name == 'coefficient':
            bad[15] = ['coefficient', 'cone_B']
        else:
            bad[target] = ['mul'] + alt
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
    need(numeric_gate(name, parsed, out, f['seed'], trials=8), f'{name}: parsed literal = PROOF.md (1)')
    controls = 0
    for mname, bad, bout in mutations(name, d):
        need(not compare(bad, bout, d), f'{name}: mutation detected by node comparison: {mname}')
        need(not numeric_gate(name, bad, bout, f['seed'], trials=2),
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
        need(numeric_gate(name, d['nodes'], d['output'], f['seed']),
             f'{name}: JSON DAG = PROOF.md formula (1) modulo 2^127-1')
        data[name] = d
        if '--check' in sys.argv:
            check(name, f, d)
        else:
            path = DC / f['lean']
            path.write_text(generate(f, d), encoding='utf-8', newline='\n')
            print('wrote', path)
    if '--check' in sys.argv and len(data) == 2:
        need(transfer_gate(data['native'], data['short']),
             'transfer: short(h (3w+1)(2v+1)) = native(h) modulo 2^127-1')
        print('OK transfer: short value at h(3w+1)(2v+1) = native value at h (40 points mod 2^127-1)')


if __name__ == '__main__':
    main()
