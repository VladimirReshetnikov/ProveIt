#!/usr/bin/env python3
"""Emit and check the Lean literal of package 113's twelve-integer equation.

  Lean/DiophantineConsistency/P113/P113Syntax.lean
  from con-zfc-diophantine-forms/113-saturated-pell/integer12_saturated/rational.json
  (153 nodes, 123 live operations: 75 mul, 25 add, 23 sub; output node 152).

The JSON input is inert data with a pinned SHA-256 (below).

The Lean literal has one definition per JSON node, in JSON order,
  def n<i> (p : Fin 6 → ℤ) : Expr (Fin 12) := ...
with the twelve variables `j C z h r v w T c n t s` as `.var 0 … .var 11`, the six coefficient
leaves `beta K0 MC MF cone_A cone_B` as `.constant (p 0) … .constant (p 5)`, integer leaves as
`.constant (k)`, and every gate as `n<a> p (+|-|*) n<b> p`.

Every node gets an evaluation lemma `e<i>`, proved from its two children only: a named register
evaluates to the field of `P113Value.regs (pc p) w` (by its `_def` lemma and `ring`), every other
node to the expression of its children, and the output to `P113Value.value (pc p) w`.

Before writing, every register is checked numerically against the JSON DAG and against an
independent model of `P113Value` (exact integers modulo a 127-bit prime at random points).

Usage:
  py -I -X utf8 -B gen_literal113.py           write the Lean file
  py -I -X utf8 -B gen_literal113.py --check   check the pin, the numerics, and that the file on disk
                                               is byte-identical to the regeneration
"""
from pathlib import Path
import argparse, hashlib, json, random

HERE = Path(__file__).resolve()
DC = HERE.parents[3]
SRC = DC / 'con-zfc-diophantine-forms/113-saturated-pell/integer12_saturated/rational.json'
PIN = '4afd94ea0580a4527b5b9320528e3c198539ad2698f7d3e453e76e8e2667ba50'
LEAN = DC / 'Lean/DiophantineConsistency/P113/P113Syntax.lean'
VARS = ['j', 'C', 'z', 'h', 'r', 'v', 'w', 'T', 'c', 'n', 't', 's']
PORTS = ['beta', 'K0', 'MC', 'MF', 'cone_A', 'cone_B']
PRIME = (1 << 127) - 1
OPS = {'add': '+', 'sub': '-', 'mul': '*'}
EVAL = {'add': 'Expr.evalRing_add', 'sub': 'Expr.evalRing_sub', 'mul': 'Expr.evalRing_mul'}
R = '(regs (pc p) w)'
# JSON register name -> (field of `P113Value.Regs`, extra definitions to unfold after the `_def`)
REG = {n: (n, '') for n in ['J', 'q', 'W0', 'X', 'Y', 'a', 'H', 'Delta', 'F', 'R', 'k', 'eta',
                            'zeta', 'G', 'Pair', 'Dg81', 'ell', 'U', 'Df', 'Q', 'delta', 'b', 'V',
                            'Cy', 'K', 'S', 'zc', 'Ac', 'fs', 'fa', 'fb', 'fc', 'Pe']}
REG.update({'Dt': ('E', ''), 'center': ('Z', ''), 'F': ('F', 'P113Value.q_def')})
# named nodes with no Lean field: evaluated like unnamed nodes
INLINE = {'qm', 'q2', 'q3', 'XY', 'coneU', 'coneV', 'Peta', 'err', 'ellk', 'c2', 'UDt', 'strong',
          'H2', 'H3', 'H5', 'S2', 'zc2', 'zc3', 'G2', 'scale', 'sum', 'ab', 'Po', 'sc', 'aXb', 'scab',
          'product'}
LEAVES = set(VARS) | set(PORTS) | {'output'}


def need(ok, msg):
    if not ok:
        raise SystemExit('FAIL: ' + msg)


def load():
    raw = SRC.read_bytes()
    need(hashlib.sha256(raw).hexdigest() == PIN, 'rational.json pin')
    d = json.loads(raw)
    need(d['variables'] == VARS, 'variable order')
    need(d['output'] == len(d['nodes']) - 1 == 152, 'output node')
    need(d['operation_counts'] == {'add': 25, 'mul': 75, 'sub': 23}, 'operation counts')
    need(sum(1 for n in d['nodes'] if n[0] in OPS) == 123, 'counted operations')
    for nm in d['named_registers']:
        need(nm in REG or nm in INLINE or nm in LEAVES, f'unclassified named node {nm}')
    return d


def dag_eval(d, vals, ports):
    out = []
    for nd in d['nodes']:
        k = nd[0]
        if k == 'variable':
            out.append(vals[VARS.index(nd[1])] % PRIME)
        elif k == 'coefficient':
            out.append(ports[PORTS.index(nd[1])] % PRIME)
        elif k == 'integer':
            out.append(nd[1] % PRIME)
        else:
            a, b = out[nd[1]], out[nd[2]]
            out.append((a + b if k == 'add' else a - b if k == 'sub' else a * b) % PRIME)
    return out


def model(x, p):
    """An independent model of `P113Value.regs` and `P113Value.value`."""
    j, C, z, h, r, v, w, T, c, n, t, s = x
    beta, K0, MC, MF, cA, cB = p
    J = 6 * j + 1; q = beta * J + 1; W0 = 12 * w + 4; X = q * W0; Y = (2 * v + 1) * q ** 3
    a = (X + 1) * Y; H = 4 * a + 3; Delta = a * a + H; F = (K0 + W0) * C - z * (q - 1)
    R = (q * (q - F) - C) * (q * q - 1) + (MC + q * MF) * J
    k = R + 1 + h * X * Y; eta = c - Y * k; zeta = k - eta
    G = (cA * F) * (cB * C) - (q - cA * F - cB * C) ** 2
    Pair = G * eta * zeta - (t * t - G - eta * zeta + 1) ** 2
    Dg81 = (243 * Pair - 324) * s * s + 81; ell = X * Y * Y; E = 1 + ell * (ell + 1) * k * k
    U = s * r * c * c; Df = 1 + Delta * U * U * E; Q = Delta ** 2 * U * U * E; delta = Q - 1
    b = c - R + 4 * U * E * T; V = Df * b - c; Cy = Q * V * V - 1; K = X * (X + 2 * a * c) - 1
    S = U * H ** 5; zc = H * T + K; Ac = (zc * zc + 3 * H * H) * (zc ** 3 - 19 * H ** 3)
    Z = S * (n + V) - Ac
    fs = delta * Z * Z; fa = 9 * delta * S * S * E * Df; fb = delta * S * S * Dg81; fc = S * S * Cy
    Pe = (fs + fc - fa - fb) ** 2 - 4 * (fs * fc + fa * fb); value = Pe * Pe - 64 * fs * fc * fa * fb
    regs = dict(J=J, q=q, W0=W0, X=X, Y=Y, a=a, H=H, Delta=Delta, F=F, R=R, k=k, eta=eta,
                zeta=zeta, G=G, Pair=Pair, Dg81=Dg81, ell=ell, E=E, U=U, Df=Df, Q=Q, delta=delta,
                b=b, V=V, Cy=Cy, K=K, S=S, zc=zc, Ac=Ac, Z=Z, fs=fs, fa=fa, fb=fb, fc=fc, Pe=Pe)
    return {k2: v2 % PRIME for k2, v2 in regs.items()}, value % PRIME


def numeric_checks(d):
    rng = random.Random(113123)
    for _ in range(4):
        vals = [rng.randrange(PRIME) for _ in VARS]
        ports = [rng.randrange(PRIME) for _ in PORTS]
        ev = dag_eval(d, vals, ports)
        regs, value = model(vals, ports)
        for nm, i in d['named_registers'].items():
            if nm in REG:
                need(ev[i] == regs[REG[nm][0]], f'register {nm} (node {i})')
        need(ev[d['output']] == value, 'output = P113Value.value')


def node_def(nd, i):
    k = nd[0]
    if k == 'variable':
        body, tag = f'.var {VARS.index(nd[1])}', f'  -- {nd[1]}'
    elif k == 'coefficient':
        body, tag = f'.constant (p {PORTS.index(nd[1])})', f'  -- {nd[1]}'
    elif k == 'integer':
        body, tag = f'.constant ({nd[1]})', ''
    else:
        body, tag = f'n{nd[1]} p {OPS[k]} n{nd[2]} p', ''
    return f'def n{i} (p : Fin 6 → ℤ) : Expr (Fin 12) := {body}{tag}'


def lemmas(d):
    ns = d['nodes']
    named = {i: nm for nm, i in d['named_registers'].items() if nm not in LEAVES}
    rhs = [None] * len(ns)
    out = []
    for i, nd in enumerate(ns):
        k = nd[0]
        if k == 'variable':
            rhs[i] = f'w {VARS.index(nd[1])}'
            out.append(f'theorem e{i} : (n{i} p).evalRing w = {rhs[i]} := rfl')
            continue
        if k == 'coefficient':
            rhs[i] = f'pc p {PORTS.index(nd[1])}'
            out.append(f'theorem e{i} : (n{i} p).evalRing w = {rhs[i]} := rfl')
            continue
        if k == 'integer':
            rhs[i] = f'({nd[1]} : R)'
            out.append(f'theorem e{i} : (n{i} p).evalRing w = {rhs[i]} := by\n  norm_num [n{i}]')
            continue
        l, r = nd[1], nd[2]
        rws = f'n{i}, {EVAL[k]}, e{l}' + (f', e{r}' if r != l else '')
        nm = named.get(i)
        if i == len(ns) - 1:
            rhs[i] = 'value (pc p) w'
            out.append(f'theorem e{i} : (n{i} p).evalRing w = {rhs[i]} := by\n  rw [{rws}]\n'
                       f'  rw [P113Value.value_def]\n  try ring')
        elif nm in REG:
            field, unf = REG[nm]
            rhs[i] = f'{R}.{field}'
            extra = f', {unf}' if unf else ''
            out.append(f'theorem e{i} : (n{i} p).evalRing w = {rhs[i]} := by\n  rw [{rws}]\n'
                       f'  try (rw [P113Value.{field}_def{extra}]; try ring)')
        else:
            rhs[i] = f'(({rhs[l]}) {OPS[k]} ({rhs[r]}))'
            out.append(f'theorem e{i} : (n{i} p).evalRing w = {rhs[i]} := by\n  rw [{rws}]')
    return out


HEADER = f'''import DiophantineConsistency.WeightedExpressionDegree
import DiophantineConsistency.P113.P113Value

/-! # Package 113's twelve-integer 1084/123 equation, as a Lean literal

Generated by `research/p113-integer12/tools/gen_literal113.py` from
`con-zfc-diophantine-forms/113-saturated-pell/integer12_saturated/rational.json`
(SHA-256 `{PIN}`): 153 nodes, 123 live operations (75 `mul`, 25 `add`, 23 `sub`), variables
`j C z h r v w T c n t s`, output node 152. Node `nᵢ` is the JSON node `i`; the six coefficient
leaves are the integer constants `p 0 … p 5` (`beta K0 MC MF cone_A cone_B`).

The evaluation is proved gate by gate (`eᵢ`, from the two children only): a named register
evaluates to the field of `P113Value.regs (pc p) w` (the JSON's `Dt` is the field `E`, its
`center` the field `Z`), every other node to the expression of its children, and the output to
`P113Value.value (pc p) w` (`evalRing_literal`). The correspondence with the JSON is checked by
`gen_literal113.py --check` (pin, numeric model, byte-identical regeneration). -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
set_option linter.unusedVariables false
noncomputable section
namespace DiophantineConsistency.P113Syntax
open P113Value

/-! ## The literal DAG -/

'''


def render(d):
    defs = '\n'.join(node_def(nd, i) for i, nd in enumerate(d['nodes']))
    return (HEADER + defs + '''

/-- The literal: the output node. -/
def literal (p : Fin 6 → ℤ) : Expr (Fin 12) := n152 p

/-- The ports in a commutative ring. -/
def pc {R : Type*} [CommRing R] (p : Fin 6 → ℤ) : Fin 6 → R := fun j => (p j : R)

section Eval
variable {R : Type*} [CommRing R] (p : Fin 6 → ℤ) (w : Fin 12 → R)

''' + '\n\n'.join(lemmas(d)) + '''

/-- **The literal evaluates to `P113Value.value` in every commutative ring.** -/
theorem evalRing_literal : (literal p).evalRing w = value (pc p) w := e152 p w

end Eval

end DiophantineConsistency.P113Syntax

#print axioms DiophantineConsistency.P113Syntax.evalRing_literal
''')


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--check', action='store_true')
    args = ap.parse_args()
    d = load()
    numeric_checks(d)
    text = render(d)
    if args.check:
        need(LEAN.read_text(encoding='utf-8') == text, 'generated file differs: ' + LEAN.name)
    else:
        with open(LEAN, 'w', encoding='utf-8', newline='\n') as f:
            f.write(text)
    print(json.dumps({'status': 'PASS' if args.check else 'GENERATED', 'nodes': len(d['nodes']),
                      'pin': PIN}))


if __name__ == '__main__':
    main()
