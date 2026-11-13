#!/usr/bin/env python3
"""Emit and check package 172's two eleven-integer Lean literals:

  298/146   Lean/DiophantineConsistency/P172/P172Syntax.lean
            from …/scalar/integer11/integer11_degree298_ops146.json
            (173 nodes, 146 live operations: 94 mul, 29 add, 23 sub; output node 172)
  300/144   Lean/DiophantineConsistency/P172/P172Syntax300.lean
            from …/scalar/integer11/integer11_degree300_ops144.json
            (170 nodes, 144 live operations: 92 mul, 29 add, 23 sub; output node 169)

Both JSON inputs are inert data with pinned SHA-256 (below).

Each Lean literal has one definition per JSON node, in JSON order:
  def n<i> (p : Fin 6 → ℤ) : Expr (Fin 11) := ...
with the eleven variables `j C z h r v w T c n s` as `.var 0 … .var 10`, the six coefficient leaves
`beta K0 MC MF cone_A cone_B` as `.constant (p 0) … .constant (p 5)`, integer leaves as
`.constant (k)`, and every gate as `n<a> p (+|-|*) n<b> p`.

Each node gets an evaluation lemma `e<i>`, proved from its two children only: a named register
(`named_registers` of the JSON) that is a field of `LCValue.Regs` evaluates to the field of the
same name of `LCValue.regs298` or `LCValue.regs300`, closed by `rfl`, i.e. the hand-written
register map of `LCValue` (the slot-generic circuit `regsK` at the slot fillers of the form) must
agree with the DAG gate by gate, operand order included; every other gate (the unnamed ones, and
the registers `AD`, `residual`, `corr`, `core` inside the two centers, which are not fields)
evaluates to the expression of its children. The output node evaluates to `LCValue.value298` or
`LCValue.value300`.

Usage:
  py -I -X utf8 -B gen_literal172.py [--form 298|300]          write the Lean file(s)
  py -I -X utf8 -B gen_literal172.py [--form 298|300] --check  for each form: check the JSON pin;
      regenerate and compare byte for byte; parse every `def n<i>` of the file on disk back and
      compare it with JSON node i; check the DAG and the parsed literal numerically against the
      PROOF.md section 1 formulas modulo 2^127-1; run mutation controls.
Without `--form`, both forms are processed.
"""
from pathlib import Path
import hashlib, json, random, re, sys

HERE = Path(__file__).resolve()
DC = HERE.parents[3]
PKG = ('con-zfc-diophantine-forms/172-pooled-powers-round21/part2/'
       'ConZFC_Pooled_Powers_Round21_2026-10-25/scalar/integer11/')
FORMS = {
    '298': dict(
        json=PKG + 'integer11_degree298_ops146.json',
        sha='b03239019cd6d6be7226635627e6d3ec7b03639d132f62fa8254750b2192b5e2',
        lean='Lean/DiophantineConsistency/P172/P172Syntax.lean', module='P172Syntax',
        tag='298/146', ops=146, counts=(94, 29, 23), output=172, degree=298, budget=6,
        regs='regs298', value='value298', gen='gen_literal172.py --form 298', seed=172298146),
    '300': dict(
        json=PKG + 'integer11_degree300_ops144.json',
        sha='d71707fd2cee0d2119da6cda150b4d143f9fe95aafb1501f1c406421b15d22be',
        lean='Lean/DiophantineConsistency/P172/P172Syntax300.lean', module='P172Syntax300',
        tag='300/144', ops=144, counts=(92, 29, 23), output=169, degree=300, budget=8,
        regs='regs300', value='value300', gen='gen_literal172.py --form 300', seed=172300144),
}
VARS = ['j', 'C', 'z', 'h', 'r', 'v', 'w', 'T', 'c', 'n', 's']
PORTS = ['beta', 'K0', 'MC', 'MF', 'cone_A', 'cone_B']
OPS = {'add': '+', 'sub': '-', 'mul': '*'}
EVAL = {'add': 'Expr.evalRing_add', 'sub': 'Expr.evalRing_sub', 'mul': 'Expr.evalRing_mul'}
# Registers the Lean structure `LCValue.Regs` has (the leaves are not fields; `Y` is the leaf `v`).
FIELDS = ['J', 'qm', 'q', 'q2', 'W', 'X', 'E', 'ell', 'a', 'H', 'Delta', 'A', 'F', 'R', 'k', 'c2',
          'Yk', 'eta', 'Derr', 'q3', 'Yeta', 'kq2', 'Budget', 'L', 'Dt', 'Dguard', 'Pg', 'P', 'Dm',
          'rDm', 'B', 'U', 'AU', 'strong', 'Df', 'Q', 'delta', 'b', 'V', 'Cy', 'K', 'M', 'Dc', 'M2',
          'M4', 'Dc2', 'Dc3', 'S', 'S2', 'zc', 'zc2', 'Ac', 'c4', 'rc4', 'U2', 'UT', 'cm2', 'gamma',
          'lam', 'Psi', 'Z', 'Z2', 'pa', 'pb', 'pc', 'inner']
# Named gates that are not fields: the registers inside the two centers, and the output.
INLINE = ['AD', 'residual', 'corr', 'core', 'output']


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
    need(d['operation_counts'] == {'add': add, 'mul': mul, 'sub': sub} and d['operations'] == f['ops'],
         'operation counts')
    need(sum(1 for r in d['nodes'] if r[0] in OPS) == f['ops'], 'live gate count')
    need(d['exact_degree'] == f['degree'] and d['budget_q_exponent'] == f['budget'],
         'degree and budget exponent')
    for name, i in d['named_registers'].items():
        if d['nodes'][i][0] in OPS:
            need(name in FIELDS or name in INLINE, 'named gate is a Regs field or inlined: ' + name)
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
    named = {i: n for n, i in d['named_registers'].items() if nodes[i][0] in OPS}
    mod, regs, value = f['module'], f['regs'], f['value']
    mul, add, sub = f['counts']
    out = []
    w = out.append
    w('import DiophantineConsistency.WeightedExpressionDegree')
    w('import DiophantineConsistency.LinCof.LCValue')
    w('import DiophantineConsistency.P138.P138Ports')
    w('')
    w(f"/-! # Package 172's eleven-integer {f['tag']} equation, as a Lean literal")
    w('')
    w(f"Generated by `research/p172-integer11/tools/{f['gen']}` from")
    w(f"`{f['json']}`")
    w(f'(SHA-256 `{f["sha"]}`): {len(nodes)} nodes, {f["ops"]} live operations')
    w(f'({mul} `mul`, {add} `add`, {sub} `sub`), variables `j C z h r v w T c n s`, output node '
      f'{d["output"]}. Node `nᵢ` is')
    w('the JSON node `i`; the six coefficient leaves are the integer constants `p 0 … p 5`')
    w('(`beta K0 MC MF cone_A cone_B`).')
    w('')
    w('The evaluation is proved gate by gate (`eᵢ`, from the two children only): a named register')
    w(f'that is a field of `LCValue.Regs` evaluates to that field of `LCValue.{regs}`, every other')
    w('gate to the expression of its children. `evalRing_literal`: the literal evaluates to')
    w(f'`LCValue.{value}` in every commutative ring; `literal_zero_iff`: at the six ports, its zeros')
    w(f'in the ring of differences of a model of `𝗜𝚺₁` are the zeros of `{value} portsR`. The')
    w('correspondence with the JSON is checked by `gen_literal172.py --check` (byte-identical')
    w('regeneration, node-by-node parse, numeric agreement, mutation rejection). -/')
    w('set_option autoImplicit false')
    w('set_option maxRecDepth 8192')
    w('set_option linter.unusedVariables false')
    w('noncomputable section')
    w(f'namespace DiophantineConsistency.{mod}')
    w('open LCValue')
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
            if i == d['output']:
                t = f'{value} (fun i => (p i : 𝔸)) x'
                close = True
            elif i in named and named[i] in FIELDS:
                t = f'(𝓟).{named[i]}'
                close = True
            else:
                t = f'({terms[a]} {OPS[kind]} {terms[b]})'
                close = False
            w(f'theorem e{i} : (n{i} p).evalRing x = {t} := by')
            w(f'  rw [{", ".join(rws)}]' + ('; rfl' if close else ''))
        terms.append(t)
    w('')
    w(f'/-- **The literal evaluates to `LCValue.{value}` in every commutative ring.** -/')
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
    """Section 1 of 172's integer11 PROOF.md, transcribed independently.
    Index modulus `ell = X Y^2` and budget power `q^6` [298]; `E = X Y` and `q^8` [300]."""
    j, C, z, h, r, v, w, T, c, n, s = xs
    beta, K0, MC, MF, cA, cB = ps
    J = 6 * j + 1; q = beta * J + 1; W = 12 * w + 4
    X = q * W; Y = v; E = X * Y; ell = X * Y * Y
    a = E + Y; A = a + 2; H = 4 * a + 3; Delta = a * a + H
    F = (K0 + W) * C - z * (q - 1)
    R = (q * (q - F) - C) * (q * q - 1) + (MC + q * MF) * J
    k = R + 1 + h * {'298': ell, '300': E}[form]
    eta = c - Y * k
    Derr = (cA * F - q)**2 + (cB * C - q)**2
    B0 = k * k * (q * q - Derr) - 4 * q * q * eta * eta
    Budget = Y * Y * B0 - k * k * q**{'298': 6, '300': 8}[form]
    Dt = 1 + ell * (ell + 1) * k * k; D = Budget - 4
    P = Dt * (1 + D * Dt * s * s)
    Dm = 1 + Delta * c * c; B = r * A * Dm; U = r * c * c * Dm
    I2 = c**4 * B
    Df = 1 + Delta * I2; Q = Delta**2 * I2; delta = Q - 1
    V = Df * (c - R + 4 * A * U * T) - c; Cy = Q * V * V - 1
    K = X * (3 * c - 2 * X) + 2; M = 2 * q**3; Dc = H * M; S = s * r * H * M**5
    zc = Dc * T + M * K + H * (v - q**3)
    Ac = (zc * zc + 3 * Dc * Dc) * (zc**3 - 19 * Dc**3)
    gamma = 8 * Delta + 4; lam = 4 * (gamma * U - r * c**4)
    if form == '298':
        Psi = lam * V + U * U * T * (r * c**4 * (gamma * (c * c - 2) - c * c) + 64 * A * Delta)
    else:
        Psi = lam * V + U * U * T * ((gamma - 1) * (r * c**4 * (c * c - 2) + 8 * A))
    Z = S * (n + Psi) - Ac
    pa = delta * Z * Z; pb = delta * S * S * P; pc = 1024 * S * S * B * Df * Cy
    return ((pa + pb - pc)**2 - 4 * pa * pb) % PRIME


def numeric_gate(form, nodes, out, seed, trials=40):
    rng = random.Random(seed)
    for _ in range(trials):
        xs = [rng.randrange(PRIME) for _ in VARS]
        ps = [rng.randrange(PRIME) for _ in PORTS]
        if eval_dag(nodes, out, xs, ps) != eval_proof_md(form, xs, ps):
            return False
    return True


def mutations(form, d):
    """Corrupted copies of the DAG: (name, nodes, output). Each must be rejected."""
    nodes, out = d['nodes'], d['output']
    named = d['named_registers']
    i19 = [i for i, r in enumerate(nodes) if r == ['integer', 19]]
    i1024 = [i for i, r in enumerate(nodes) if r == ['integer', 1024]]
    need(len(i19) == 1 and len(i1024) == 1, 'the unique integer leaves 19 and 1024')
    need(nodes[out][0] == 'sub', 'the output is the subtraction inner^2 - 4 pa pb')
    k = named['k']
    # the gate of `k` that holds h * M_index, i.e. the `mul` child of the last `add`
    hm = nodes[k][2]
    need(nodes[hm][0] == 'mul' and nodes[hm][1] == VARS.index('h'), 'k = (1 + R) + h * M_index')
    # the other form's index modulus (`E` for 298, whose own is `ell`; `X` for 300, whose own is `E`)
    other = named['E'] if form == '298' else named['X']
    need(nodes[hm][2] != other, 'the index modulus of this form')
    # the other form's budget power: `kq2 = q3 * k` for 298 (own `q2 * k`), `k * q2` for 300
    kq = named['kq2']
    alt = ['mul', named['q3'], k] if form == '298' else ['mul', k, named['q2']]
    need(nodes[kq] != alt, 'the budget power of this form')
    cases = []
    for name in ('child', 'op', 'literal19', 'literal1024', 'variable', 'coefficient', 'modulus',
                 'budget'):
        bad = [list(r) for r in nodes]
        if name == 'child':
            bad[out] = ['sub', bad[out][1], bad[out][1]]
        elif name == 'op':
            bad[out] = ['add'] + bad[out][1:]
        elif name == 'literal19':
            bad[i19[0]] = ['integer', 18]
        elif name == 'literal1024':
            bad[i1024[0]] = ['integer', 1023]
        elif name == 'variable':
            bad[0] = ['variable', 'C']
        elif name == 'coefficient':
            bad[15] = ['coefficient', 'cone_B']
        elif name == 'modulus':
            bad[hm] = ['mul', bad[hm][1], other]
        else:
            bad[kq] = alt
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
    other = [g for g in FORMS if g != name][0]
    need(not numeric_gate(other, parsed, out, f['seed'], trials=2),
         f'{name}: the literal is not the other form')
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
