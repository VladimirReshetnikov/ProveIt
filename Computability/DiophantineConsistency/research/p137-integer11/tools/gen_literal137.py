#!/usr/bin/env python3
"""Emit and check the Lean literal of package 137's weak product equation:

  648/115   Lean/DiophantineConsistency/P137/P137Syntax.lean
            from con-zfc-diophantine-forms/137-odd-helpers-saturated-carriers/integer/
                 weak_product11_none.json
            (140 nodes, 115 live operations: 73 mul, 23 add, 19 sub; output node 139)

The JSON input is inert data with a pinned SHA-256 (below).

The Lean literal has one definition per JSON node, in JSON order:
  def n<i> (p : Fin 6 → ℤ) : Expr (Fin 11) := ...
with the eleven variables `j C z h r v w T c n s` as `.var 0 … .var 10`, the six coefficient leaves
`beta K0 MC MF cone_A cone_B` as `.constant (p 0) … .constant (p 5)`, integer leaves as
`.constant (k)`, and every gate as `n<a> p (+|-|*) n<b> p`.

Each node gets an evaluation lemma `e<i>`, proved from its two children only. A named register
(`named_registers` of the JSON) evaluates to a field of one of two Lean register records:

  * the front and carrier registers, fields of `P137Front.front` (`FRONT` below);
  * the back-end registers, fields of `P137Value.back` (`BACK` below).

Every such lemma is closed by `rfl`: the hand-written register maps agree with the DAG gate by
gate, operand order included. Unnamed nodes evaluate to the expression of their children. The
output node evaluates to `P137Value.value`.

One node carries two names: node 23 is both `q2` and `qscale` (the weak scale is `q^2`). Both
names are mapped to the field `q2`; no other node has two names.

Usage:
  py -I -X utf8 -B gen_literal137.py           write the Lean file
  py -I -X utf8 -B gen_literal137.py --check   check the JSON pin; regenerate and compare byte for
      byte; parse every `def n<i>` of the file on disk back and compare it with JSON node i; check
      the DAG and the parsed literal numerically against formula (1) of PROOF.md; check the scale
      transfer `value(v = (1 + 2 v') q^2) = cubic-scale value(v')` numerically; run mutation
      controls.
"""
from pathlib import Path
import hashlib, json, random, re, sys

HERE = Path(__file__).resolve()
DC = HERE.parents[3]
JSON = ('con-zfc-diophantine-forms/137-odd-helpers-saturated-carriers/integer/'
        'weak_product11_none.json')
SHA = '63023b059a84ced728fae1dddfcc334a5b8c401abc77a0012266d77a28b4f963'
LEAN = 'Lean/DiophantineConsistency/P137/P137Syntax.lean'
MODULE = 'P137Syntax'
OPS_TOTAL, COUNTS, OUTPUT, NODES, DEGREE = 115, (73, 23, 19), 139, 140, 648
SEED = 137648115

VARS = ['j', 'C', 'z', 'h', 'r', 'v', 'w', 'T', 'c', 'n', 's']
PORTS = ['beta', 'K0', 'MC', 'MF', 'cone_A', 'cone_B']
OPS = {'add': '+', 'sub': '-', 'mul': '*'}
EVAL = {'add': 'Expr.evalRing_add', 'sub': 'Expr.evalRing_sub', 'mul': 'Expr.evalRing_mul'}
# JSON register name -> field of `P137Front.Front` (front and carrier, record 𝓕).
FRONT = {n: n for n in ['J', 'qm', 'q', 'q2', 'W', 'X', 'Y', 'E', 'a', 'H', 'Delta', 'A', 'F', 'R',
                        'k', 'c2', 'Yk', 'eta', 'Derr', 'Budget', 'L', 'Dt', 'Dm', 'K', 'M', 'Dcar',
                        'M2', 'M4', 'Dcar2', 'Dcar3', 'S', 'S2', 'zc', 'zc2', 'Ac', 'Z']}
FRONT['qscale'] = 'q2'
# JSON register name -> field of `P137Value.Back` (back end, record 𝓑).
BACK = {n: n for n in ['D4', 'Pg', 'P', 'BP', 'Ub', 'U', 'UBP', 'strong', 'Df', 'Q', 'delta', 'b',
                       'V', 'Cy']}
# The only node with two names.
DOUBLE = ('q2', 'qscale')


def need(ok, msg):
    if not ok:
        raise SystemExit('FAIL: ' + msg)


def names_by_node(d):
    """node index -> sorted list of its register names."""
    inv = {}
    for name, i in d['named_registers'].items():
        inv.setdefault(i, []).append(name)
    return {i: sorted(ns) for i, ns in inv.items()}


def load():
    raw = (DC / JSON).read_bytes()
    need(hashlib.sha256(raw).hexdigest() == SHA, 'JSON SHA-256 pin: ' + JSON)
    d = json.loads(raw)
    need(d['schema'] == 'integer-polynomial-dag-v1', 'schema')
    need(d['name'] == 'weak_product11_none', 'name')
    need(d['domain'] == 'unrestricted integers', 'domain')
    need(d['variables'] == VARS and d['variable_count'] == len(VARS), 'variable order')
    need(len(d['nodes']) == NODES and d['output'] == NODES - 1 == OUTPUT, 'output node')
    mul, add, sub = COUNTS
    need(d['operation_counts'] == {'mul': mul, 'add': add, 'sub': sub}
         and d['operations'] == OPS_TOTAL, 'operation counts')
    need(sum(1 for r in d['nodes'] if r[0] in OPS) == OPS_TOTAL, 'live gate count')
    need(d.get('exact_degree') == DEGREE and d.get('syntactic_degree_bound') == DEGREE,
         'exact degree recorded by the package')
    need(d.get('center') == 'none' and d.get('free_y') is False, 'direct weak form')
    need(d.get('coefficient_binding') == 'coefficients/BINDING.json', 'coefficient binding path')
    named = d['named_registers']
    inv = names_by_node(d)
    multi = {i: ns for i, ns in inv.items() if len(ns) > 1}
    need(list(multi.values()) == [sorted(DOUBLE)], 'exactly one node has two names: q2 and qscale')
    for name, i in named.items():
        row = d['nodes'][i]
        if name in VARS:
            need(row == ['variable', name], 'named leaf ' + name)
        elif name == 'output':
            need(i == d['output'], 'the name `output` is attached to the output node')
        else:
            need(row[0] in OPS and (name in FRONT) != (name in BACK),
                 'named register is mapped to exactly one record: ' + name)
    need(sorted(n for n in named if n not in VARS and n != 'output')
         == sorted(list(FRONT) + list(BACK)), 'every mapped name occurs in the JSON')
    need(all(v in named for v in VARS), 'every variable is a named register')
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
    inv = names_by_node(d)
    mul, add, sub = COUNTS
    out = []
    w = out.append
    w('import DiophantineConsistency.WeightedExpressionDegree')
    w('import DiophantineConsistency.P137.P137Value')
    w('import DiophantineConsistency.P138.P138Ports')
    w('')
    w("/-! # Package 137's weak product 648/115 equation, as a Lean literal")
    w('')
    w('Generated by `research/p137-integer11/tools/gen_literal137.py` from')
    w(f'`{JSON}`')
    w(f'(SHA-256 `{SHA}`): {len(nodes)} nodes, {OPS_TOTAL} live operations')
    w(f'({mul} `mul`, {add} `add`, {sub} `sub`), variables `j C z h r v w T c n s`, output node '
      f'{d["output"]}. Node `nᵢ` is')
    w('the JSON node `i`; the six coefficient leaves are the integer constants `p 0 … p 5`')
    w('(`beta K0 MC MF cone_A cone_B`).')
    w('')
    w('The evaluation is proved gate by gate (`eᵢ`, from the two children only). A named front or')
    w('carrier register evaluates to the field of `P137Front.front` with the same name, a named')
    w('back-end register to the field of `P137Value.back` with the same name; every one by `rfl`,')
    w('so the hand-written records agree with the DAG in operand order. Node 23 has two names,')
    w('`q2` and `qscale` (the weak scale is `q²`); both are the field `q2`. Unnamed nodes evaluate')
    w('to the expression of their children.')
    w('`evalRing_literal`: the literal evaluates to `P137Value.value` in every commutative ring;')
    w('`literal_zero_iff`: at the six ports, its zeros in the ring of differences of a model of')
    w('`𝗜𝚺₁` are the zeros of `P137Value.value portsR`. The correspondence with the JSON is checked')
    w('by `gen_literal137.py --check` (byte-identical regeneration, node-by-node parse, mutation')
    w('rejection). -/')
    w('set_option autoImplicit false')
    w('set_option maxRecDepth 8192')
    w('set_option linter.unusedVariables false')
    w('noncomputable section')
    w(f'namespace DiophantineConsistency.{MODULE}')
    w('')
    w('/-! ## The literal DAG -/')
    w('')
    for i, row in enumerate(nodes):
        if row[0] in OPS:
            body, com = f'n{row[1]} p {OPS[row[0]]} n{row[2]} p', ''
            if i in inv:
                com = '  -- ' + ', '.join(inv[i])
        else:
            body, com = leaf_lean(row)
        w(f'def n{i} (p : Fin 6 → ℤ) : Expr (Fin 11) := {body}{com}')
    w('')
    w('/-- The literal polynomial at the integer ports `p`. -/')
    w(f'def literal (p : Fin 6 → ℤ) : Expr (Fin 11) := n{d["output"]} p')
    w('')
    w('/-! ## Gate-by-gate evaluation -/')
    w('')
    w('section Eval')
    w('variable {𝔸 : Type*} [CommRing 𝔸] (p : Fin 6 → ℤ) (x : Fin 11 → 𝔸)')
    w('local notation "𝓕" => P137Front.front (fun i => (p i : 𝔸)) x')
    w('local notation "𝓑" => P137Value.back (fun i => (p i : 𝔸)) x')
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
            names = [n for n in inv.get(i, []) if n != 'output']
            raw_term = f'{terms[a]} {OPS[kind]} {terms[b]}'
            close = '; rfl'
            if i == d['output']:
                t = 'P137Value.value (fun i => (p i : 𝔸)) x'
            elif names and names[0] in FRONT:
                t = f'(𝓕).{FRONT[names[0]]}'
            elif names and names[0] in BACK:
                t = f'(𝓑).{BACK[names[0]]}'
            else:
                t = f'({raw_term})'
                close = ''
            w(f'theorem e{i} : (n{i} p).evalRing x = {t} := by')
            w(f'  rw [{", ".join(rws)}]' + close)
        terms.append(t)
    w('')
    w('/-- **The literal evaluates to `P137Value.value` in every commutative ring.** -/')
    w('theorem evalRing_literal :')
    w('    (literal p).evalRing x = P137Value.value (fun i => (p i : 𝔸)) x :=')
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
    w('`P137Value.value portsR`. -/')
    w('theorem literal_zero_iff (x : Fin 11 → DiffRing V) :')
    w('    (literal (fun i => (ports6 i : ℤ))).evalRing x = 0 ↔ P137Value.value portsR x = 0 := by')
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


# ------------------------------------------------------------- numeric gate (PROOF.md formulas)

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


def eval_proof_md(scale, xs, ps):
    """Section 1 of 137's PROOF.md, direct form (centre `none`), transcribed independently.
    `scale = 'weak'`: `Y = q v`, `qscale = q^2` [the degree-648 equation]. `scale = 'cubic'`: the
    scale variable is the old `v'`, `Y = (2 v' + 1) q^3` and the carrier's scale term
    `v - qscale` is `2 q^2 v'` [used here only for the scale transfer]."""
    j, C, z, h, r, v, w, T, c, n, s = xs
    beta, K0, MC, MF, cA, cB = ps
    J = 6 * j + 1; q = beta * J + 1; W = 12 * w + 4; X = q * W
    Y, shift = {'weak': (q * v, v - q * q),
                'cubic': ((2 * v + 1) * q**3, 2 * q * q * v)}[scale]
    E = X * Y; a = E + Y; A = a + 2; H = 4 * a + 3; Delta = a * a + H
    F = (K0 + W) * C - z * (q - 1)
    R = (q * (q - F) - C) * (q * q - 1) + (MC + q * MF) * J
    k = R + 1 + h * E; eta = c - Y * k
    Derr = (cA * F - q)**2 + (cB * C - q)**2
    Budget = k * k * (q * q - Derr) - 4 * q * q * eta * eta
    ell = X * Y * Y; L = ell * k; Dt = 1 + L * (L + k)
    D = 3 * Budget - 4; Dg = 1 + 4 * D * Dt * s * s; P = Dt * Dg
    Dm = 1 + Delta * c * c; BP = Dm * P
    Ub = r * c * c; U = A * Ub
    Df = 1 + Delta * U * U * BP; Q = Delta**2 * U * U * BP; delta = Q - 1
    V = Df * (c - R + 4 * U * BP * T) - c; Cy = Q * V * V - 1
    K = X * (3 * c - 2 * X) + 2
    M = 2 * q * q; Dc = H * M; zc = Dc * T + M * K + H * shift
    Ac = (zc * zc + 3 * Dc * Dc) * (zc**3 - 19 * Dc**3)
    S = s * r * H * M**5; Z = S * n - Ac
    return (delta * Z * Z - S * S * BP * Df * Cy) % PRIME


def numeric_gate(nodes, out, seed, trials=40):
    rng = random.Random(seed)
    for _ in range(trials):
        xs = [rng.randrange(PRIME) for _ in VARS]
        ps = [rng.randrange(PRIME) for _ in PORTS]
        if eval_dag(nodes, out, xs, ps) != eval_proof_md('weak', xs, ps):
            return False
    return True


def transfer_gate(d, trials=40):
    """The substitution of `P137Bootstrap.recover` and `P137Complete.weak_regs`: the DAG at
    `v = (1 + 2 v') q^2` equals the cubic-scale value at `v'`."""
    rng = random.Random(137)
    for _ in range(trials):
        xs = [rng.randrange(PRIME) for _ in VARS]
        ps = [rng.randrange(PRIME) for _ in PORTS]
        q = (ps[0] * (6 * xs[0] + 1) + 1) % PRIME
        ys = list(xs)
        ys[5] = (1 + 2 * xs[5]) * q * q % PRIME
        if eval_dag(d['nodes'], d['output'], ys, ps) != eval_proof_md('cubic', xs, ps):
            return False
    return True


def mutations(d):
    """Corrupted copies of the DAG: (name, nodes, output). Each must be rejected."""
    nodes, out = d['nodes'], d['output']
    named = d['named_registers']
    i19 = [i for i, r in enumerate(nodes) if r == ['integer', 19]]
    i16 = [i for i, r in enumerate(nodes) if r == ['integer', 16]]
    need(len(i19) == 1 and len(i16) == 1, 'the unique integer leaves 19 and 16')
    y, z = named['Y'], named['Z']
    need(nodes[y] == ['mul', VARS.index('v'), named['q']], 'the weak scale Y = v * q')
    slot = nodes[z][1]
    need(nodes[z][0] == 'sub' and nodes[z][2] == named['Ac']
         and nodes[slot] == ['mul', VARS.index('n'), named['S']], 'the direct slot Z = n * S - Ac')
    need(nodes[named['D4']] == ['sub', nodes[named['D4']][1], i16[0]], 'the guard D4 = 12 Budget - 16')
    cases = []
    for name in ('child', 'op', 'literal', 'variable', 'coefficient', 'scale', 'slot', 'guard',
                 'order'):
        bad = [list(r) for r in nodes]
        if name == 'child':
            bad[out] = ['sub', nodes[out][1], nodes[out][1]]
        elif name == 'op':
            bad[z] = ['add'] + bad[z][1:]
        elif name == 'literal':
            bad[i19[0]] = ['integer', 18]
        elif name == 'variable':
            bad[0] = ['variable', 'C']
        elif name == 'coefficient':
            bad[15] = ['coefficient', 'cone_B']
        elif name == 'scale':
            bad[y] = ['mul', VARS.index('v'), named['q2']]
        elif name == 'slot':
            bad[slot] = ['mul', VARS.index('n'), named['S2']]
        elif name == 'guard':
            bad[i16[0]] = ['integer', 4]
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
    need(numeric_gate(parsed, out, SEED, trials=8), 'parsed literal = PROOF.md (1)')
    controls = 0
    for mname, bad, bout in mutations(d):
        need(not compare(bad, bout, d), f'mutation detected by node comparison: {mname}')
        need(not numeric_gate(bad, bout, SEED, trials=2), f'mutation changes the value: {mname}')
        controls += 1
    need(transfer_gate(d), 'transfer: value(v = (1 + 2 v\') q^2) = cubic-scale value(v\')')
    print(f'OK 648/115: {len(parsed)} nodes match JSON node for node; output {out}; '
          f'byte-identical regeneration; PROOF.md numeric gate; '
          f'{controls} mutation controls rejected')
    print("OK transfer: value at v = (1 + 2 v') q^2 = cubic-scale value at v' "
          '(40 points mod 2^127-1)')


def main():
    d = load()
    need(numeric_gate(d['nodes'], d['output'], SEED),
         'JSON DAG = PROOF.md formula (1) modulo 2^127-1')
    if '--check' in sys.argv:
        check(d)
    else:
        path = DC / LEAN
        path.write_text(generate(d), encoding='utf-8', newline='\n')
        print('wrote', path)


if __name__ == '__main__':
    main()
