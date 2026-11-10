#!/usr/bin/env python3
"""Emit and check the Lean literal of package 131's two-root equation:

  810/112   Lean/DiophantineConsistency/P131/P131Syntax.lean
            from con-zfc-diophantine-forms/131-shared-pell-caps-round16/scalar/two_root/
                 two_root11_degree810.json
            (136 nodes, 112 live operations: 70 mul, 22 add, 20 sub; output node 135)

The JSON input is inert data with a pinned SHA-256 (below).

The Lean literal has one definition per JSON node, in JSON order:
  def n<i> (p : Fin 6 → ℤ) : Expr (Fin 11) := ...
with the eleven variables `j C z h r v w T c n s` as `.var 0 … .var 10`, the six coefficient leaves
`beta K0 MC MF cone_A cone_B` as `.constant (p 0) … .constant (p 5)`, integer leaves as
`.constant (k)`, and every gate as `n<a> p (+|-|*) n<b> p`.

Each node gets an evaluation lemma `e<i>`, proved from its two children only. A named register
(`named_registers` of the JSON) evaluates to a field of one of two Lean register records:

  * the front registers, fields of `P138Value.regsS` (the front of this circuit is the front of
    package 138's short form), with the renamings `FRONT` below;
  * the back-end registers, fields of `P131Value.backK` at the short index `P138Value.kS`.

The lemma is closed by `rfl`, i.e. the hand-written register maps must agree with the DAG gate by
gate, operand order included. There are two exceptions, where the DAG and the Lean record
associate a product differently and the lemma is closed by an explicit `show … ; ring` (`RING`
below): node 76, `L = k * (Y * E)` in the DAG and `E * (Y * k)` in Lean, and node 84,
`P = Dt + D * (Pg * Pg)` in the DAG and `Dt + Pg * (D * Pg)` in Lean. The four named nodes with
no Lean field (`INLINE` below) and all unnamed nodes evaluate to the expression of their
children. The output node evaluates to `P131Value.value`.

Usage:
  py -I -X utf8 -B gen_literal131.py           write the Lean file
  py -I -X utf8 -B gen_literal131.py --check   check the JSON pin; regenerate and compare byte for
      byte; parse every `def n<i>` of the file on disk back and compare it with JSON node i; check
      the DAG and the parsed literal numerically against formula (1) of TWO_ROOT_PROOF.md; check
      the completeness transfer `value(h (3w+1)(2v+1)) = native-index value(h)` numerically; run
      mutation controls.
"""
from pathlib import Path
import hashlib, json, random, re, sys

HERE = Path(__file__).resolve()
DC = HERE.parents[3]
JSON = ('con-zfc-diophantine-forms/131-shared-pell-caps-round16/scalar/two_root/'
        'two_root11_degree810.json')
SHA = '4b2eb90c2ce445bc450e4080699d70780da4a86efef5f658696c0caaf84b9fd3'
LEAN = 'Lean/DiophantineConsistency/P131/P131Syntax.lean'
MODULE = 'P131Syntax'
OPS_TOTAL, COUNTS, OUTPUT, NODES, DEGREE = 112, (70, 22, 20), 135, 136, 810
SEED = 131810112

VARS = ['j', 'C', 'z', 'h', 'r', 'v', 'w', 'T', 'c', 'n', 's']
PORTS = ['beta', 'K0', 'MC', 'MF', 'cone_A', 'cone_B']
OPS = {'add': '+', 'sub': '-', 'mul': '*'}
EVAL = {'add': 'Expr.evalRing_add', 'sub': 'Expr.evalRing_sub', 'mul': 'Expr.evalRing_mul'}
# JSON register name -> field of `P138Value.Regs` (front, record 𝓟).
FRONT = {n: n for n in ['J', 'qm', 'q', 'q2', 'q3', 'W', 'X', 'Y', 'E', 'a', 'H', 'Delta', 'F', 'R',
                        'k', 'c2', 'eta', 'Derr', 'Budget', 'L', 'Dt', 'P', 'K', 'H2', 'H3', 'S',
                        'zc', 'zc2', 'Ac']}
FRONT.update({'q2four': 'q24', 'D': 'D4', 'guard_scale': 'Pg'})
# JSON register name -> field of `P131Value.Back` (back end, record 𝓑).
BACK = {n: n for n in ['U', 'UP', 'strong', 'Df', 'Q', 'delta', 'b', 'V', 'Cy', 'S2', 'Z', 'Aux',
                       'Guard', 'Inner']}
# Named gates with no Lean field: evaluated like unnamed nodes.
INLINE = ['index_modulus', 'coneF', 'coneC', 'ell']
# Named leaves (variables): not gates.
LEAF_NAMES = {'c': 'c', 's2': 's'}
# Gates whose Lean field associates the product differently: JSON name -> Lean right-hand side.
RING = {
    'L': '(𝓟).E * ((𝓟).Y * (𝓟).k)',
    'P': '(𝓟).Dt + (𝓟).Pg * ((𝓟).D4 * (𝓟).Pg)',
}


def need(ok, msg):
    if not ok:
        raise SystemExit('FAIL: ' + msg)


def load():
    raw = (DC / JSON).read_bytes()
    need(hashlib.sha256(raw).hexdigest() == SHA, 'JSON SHA-256 pin: ' + JSON)
    d = json.loads(raw)
    need(d['schema'] == 'integer-polynomial-dag-v1', 'schema')
    need(d['variables'] == VARS, 'variable order')
    need(len(d['nodes']) == NODES and d['output'] == NODES - 1 == OUTPUT, 'output node')
    mul, add, sub = COUNTS
    need(d['operation_counts'] == {'mul': mul, 'add': add, 'sub': sub}
         and d['operations'] == OPS_TOTAL, 'operation counts')
    need(sum(1 for r in d['nodes'] if r[0] in OPS) == OPS_TOTAL, 'live gate count')
    need(d.get('exact_degree') == DEGREE, 'exact degree recorded by the package')
    need(d.get('short_index') is True, 'short index')
    need(d.get('coefficient_binding') == '../coefficients/BINDING.json', 'coefficient binding path')
    named = d['named_registers']
    need(len(set(named.values())) == len(named), 'register names are attached to distinct nodes')
    for name, i in named.items():
        gate = d['nodes'][i][0] in OPS
        if name in LEAF_NAMES:
            need(d['nodes'][i] == ['variable', LEAF_NAMES[name]], 'named leaf ' + name)
        elif name == 'output':
            need(i == d['output'], 'the name `output` is attached to the output node')
        else:
            need(gate and (name in FRONT or name in BACK or name in INLINE),
                 'named register is mapped: ' + name)
    need(sorted(n for n in named if n not in LEAF_NAMES and n != 'output')
         == sorted(list(FRONT) + list(BACK) + INLINE), 'every mapped name occurs in the JSON')
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


def generate(d):
    nodes = d['nodes']
    named = {i: n for n, i in d['named_registers'].items()}
    mul, add, sub = COUNTS
    out = []
    w = out.append
    w('import DiophantineConsistency.WeightedExpressionDegree')
    w('import DiophantineConsistency.P131.P131Value')
    w('import DiophantineConsistency.P138.P138Ports')
    w('')
    w("/-! # Package 131's two-root 810/112 equation, as a Lean literal")
    w('')
    w('Generated by `research/p131-integer11/tools/gen_literal131.py` from')
    w(f'`{JSON}`')
    w(f'(SHA-256 `{SHA}`): {len(nodes)} nodes, {OPS_TOTAL} live operations')
    w(f'({mul} `mul`, {add} `add`, {sub} `sub`), variables `j C z h r v w T c n s`, output node '
      f'{d["output"]}. Node `nᵢ` is')
    w('the JSON node `i`; the six coefficient leaves are the integer constants `p 0 … p 5`')
    w('(`beta K0 MC MF cone_A cone_B`).')
    w('')
    w('The evaluation is proved gate by gate (`eᵢ`, from the two children only). A named front')
    w('register evaluates to a field of `P138Value.regsS` (`q2four`, `D`, `guard_scale` are the')
    w('fields `q24`, `D4`, `Pg`), a named back-end register to the field of `P131Value.backK` with')
    w('the same name at the short index `P138Value.kS`; both by `rfl`, except the two gates `L` and')
    w('`P`, where the DAG and the Lean record associate a product differently and the proof ends')
    w('with an explicit `show … ; ring`. The named nodes `index_modulus`, `coneF`, `coneC`, `ell`')
    w('have no Lean field and evaluate, like unnamed nodes, to the expression of their children.')
    w('`evalRing_literal`: the literal evaluates to `P131Value.value` in every commutative ring;')
    w('`literal_zero_iff`: at the six ports, its zeros in the ring of differences of a model of')
    w('`𝗜𝚺₁` are the zeros of `P131Value.value portsR`. The correspondence with the JSON is checked')
    w('by `gen_literal131.py --check` (byte-identical regeneration, node-by-node parse, mutation')
    w('rejection). -/')
    w('set_option autoImplicit false')
    w('set_option maxRecDepth 8192')
    w('set_option linter.unusedVariables false')
    w('noncomputable section')
    w(f'namespace DiophantineConsistency.{MODULE}')
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
    w('local notation "𝓟" => regsS (fun i => (p i : 𝔸)) x')
    w('local notation "𝓑" => P131Value.backK (fun i => (p i : 𝔸)) x (kS (fun i => (p i : 𝔸)) x)')
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
                t = 'P131Value.value (fun i => (p i : 𝔸)) x'
            elif name in FRONT:
                t = f'(𝓟).{FRONT[name]}'
            elif name in BACK:
                t = f'(𝓑).{BACK[name]}'
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
    w('/-- **The literal evaluates to `P131Value.value` in every commutative ring.** -/')
    w('theorem evalRing_literal :')
    w('    (literal p).evalRing x = P131Value.value (fun i => (p i : 𝔸)) x :=')
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
    w('`P131Value.value portsR`. -/')
    w('theorem literal_zero_iff (x : Fin 11 → DiffRing V) :')
    w('    (literal (fun i => (ports6 i : ℤ))).evalRing x = 0 ↔ P131Value.value portsR x = 0 := by')
    w('  rw [evalRing_literal]')
    w('  rfl')
    w('')
    w('end Model')
    w('')
    w(f'#print axioms DiophantineConsistency.{MODULE}.evalRing_literal')
    w(f'#print axioms DiophantineConsistency.{MODULE}.literal_zero_iff')
    w('')
    w(f'end DiophantineConsistency.{MODULE}')
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


# ------------------------------------------------------ numeric gate (TWO_ROOT_PROOF.md formulas)

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


def eval_proof_md(index, xs, ps):
    """Section 1 of 131's TWO_ROOT_PROOF.md, cubic scale, transcribed independently.
    `index_modulus = 4q^4` ['short', the degree-810 equation]; `index_modulus = XY` ['native',
    the degree-906 comparison form, used here only for the completeness transfer]."""
    j, C, z, h, r, v, w, T, c, n, s = xs
    beta, K0, MC, MF, cA, cB = ps
    J = 6 * j + 1; q = beta * J + 1; W = 12 * w + 4; X = q * W
    F = (K0 + W) * C - z * (q - 1)
    R = (q * (q - F) - C) * (q * q - 1) + (MC + q * MF) * J
    Y = (2 * v + 1) * q**3
    M_index = {'short': 4 * q**4, 'native': X * Y}[index]
    E = X * Y; a = E + Y; H = 4 * a + 3; Delta = a * a + H
    k = R + 1 + h * M_index; eta = c - Y * k
    Derr = (cA * F - q)**2 + (cB * C - q)**2
    Budget = k * k * (q * q - Derr) - 4 * q * q * eta * eta; D = Budget - 4
    ell = X * Y * Y; Dt = 1 + ell * (ell + 1) * k * k
    Dg = 1 + D * Dt * s * s; P = Dt * Dg
    U = r * c * c; Df = 1 + Delta * U * U * P
    Q = Delta**2 * U * U * P; delta = Q - 1
    b = c - R + 4 * U * P * T; V = Df * b - c; Cy = Q * V * V - 1
    K = X * (3 * c - 2 * X) + 2
    S = s * r * H; zc = H * T + K
    Ac = (zc * zc + 3 * H * H) * (zc**3 - 19 * H**3)
    Z = S * (n + V) - Ac; Aux = S * S * Cy; Guard = S * S * P * Df
    Inner = delta * (Z * Z - Guard) - Aux
    return (Inner * Inner - 4 * delta * Aux * Guard) % PRIME


def numeric_gate(nodes, out, seed, trials=40):
    rng = random.Random(seed)
    for _ in range(trials):
        xs = [rng.randrange(PRIME) for _ in VARS]
        ps = [rng.randrange(PRIME) for _ in PORTS]
        if eval_dag(nodes, out, xs, ps) != eval_proof_md('short', xs, ps):
            return False
    return True


def transfer_gate(d, trials=40):
    """`P131Complete.value_update`: the DAG at h' = h (3w+1)(2v+1) equals the native-index value
    at h."""
    rng = random.Random(131)
    for _ in range(trials):
        xs = [rng.randrange(PRIME) for _ in VARS]
        ps = [rng.randrange(PRIME) for _ in PORTS]
        h, v, w = xs[3], xs[5], xs[6]
        ys = list(xs)
        ys[3] = h * (3 * w + 1) * (2 * v + 1) % PRIME
        if eval_dag(d['nodes'], d['output'], ys, ps) != eval_proof_md('native', xs, ps):
            return False
    return True


def mutations(d):
    """Corrupted copies of the DAG: (name, nodes, output). Each must be rejected."""
    nodes, out = d['nodes'], d['output']
    named = d['named_registers']
    i19 = [i for i, r in enumerate(nodes) if r == ['integer', 19]]
    need(len(i19) == 1, 'the unique integer leaf 19')
    inner = named['Inner']
    zg = nodes[nodes[inner][1]][2]          # Inner = delta * (Z*Z - Guard) - Aux
    need(nodes[zg][0] == 'sub' and nodes[zg][2] == named['Guard'], 'the gate Z*Z - Guard')
    k = named['k']
    hm = nodes[k][2]
    need(nodes[hm][0] == 'mul' and nodes[hm][1] == VARS.index('h')
         and nodes[hm][2] == named['index_modulus'], 'k = (1 + R) + h * index_modulus')
    slot = nodes[nodes[named['Z']][1]][2]   # Z = S * (n + V) - Ac
    need(nodes[slot] == ['add', VARS.index('n'), named['V']], 'the linear slot n + V')
    cases = []
    for name in ('child', 'op', 'literal', 'variable', 'coefficient', 'modulus', 'slot', 'order'):
        bad = [list(r) for r in nodes]
        if name == 'child':
            bad[out] = ['sub', nodes[out][1], nodes[out][1]]
        elif name == 'op':
            bad[zg] = ['add'] + bad[zg][1:]
        elif name == 'literal':
            bad[i19[0]] = ['integer', 18]
        elif name == 'variable':
            bad[0] = ['variable', 'C']
        elif name == 'coefficient':
            bad[15] = ['coefficient', 'cone_B']
        elif name == 'modulus':
            bad[named['index_modulus']] = ['mul', named['X'], named['Y']]
        elif name == 'slot':
            bad[slot] = ['add', VARS.index('n'), named['b']]
        else:
            bad[out] = ['sub', nodes[out][2], nodes[out][1]]
        cases.append((name, bad, out))
    cases.append(('output', [list(r) for r in nodes], out - 1))
    return cases


def check(d):
    lean_path = DC / LEAN
    text = generate(d)
    disk = lean_path.read_text(encoding='utf-8')
    need(disk == text, 'Lean file is byte-identical to a fresh generation')
    parsed, out = parse_lean(disk)
    need(compare(parsed, out, d), 'parsed Lean literal = JSON DAG node for node')
    need(numeric_gate(parsed, out, SEED, trials=8), 'parsed literal = TWO_ROOT_PROOF.md (1)')
    controls = 0
    for mname, bad, bout in mutations(d):
        need(not compare(bad, bout, d), f'mutation detected by node comparison: {mname}')
        need(not numeric_gate(bad, bout, SEED, trials=2), f'mutation changes the value: {mname}')
        controls += 1
    need(transfer_gate(d), 'transfer: value(h (3w+1)(2v+1)) = native-index value(h) modulo 2^127-1')
    print(f'OK 810/112: {len(parsed)} nodes match JSON node for node; output {out}; '
          f'byte-identical regeneration; TWO_ROOT_PROOF.md numeric gate; '
          f'{controls} mutation controls rejected')
    print('OK transfer: value at h(3w+1)(2v+1) = native-index value at h (40 points mod 2^127-1)')


def main():
    d = load()
    need(numeric_gate(d['nodes'], d['output'], SEED),
         'JSON DAG = TWO_ROOT_PROOF.md formula (1) modulo 2^127-1')
    if '--check' in sys.argv:
        check(d)
    else:
        path = DC / LEAN
        path.write_text(generate(d), encoding='utf-8', newline='\n')
        print('wrote', path)


if __name__ == '__main__':
    main()
