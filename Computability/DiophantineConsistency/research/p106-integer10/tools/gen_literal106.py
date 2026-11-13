#!/usr/bin/env python3
"""Emit and check the Lean literals of package 106's four ten-integer equations.

  polar    Lean/DiophantineConsistency/Z10/Z10SyntaxPolar.lean    from integer10_polar.json
  linear   Lean/DiophantineConsistency/Z10/Z10SyntaxLinear.lean   from integer10_linear.json
  cubic    Lean/DiophantineConsistency/Z10/Z10SyntaxCubic.lean    from integer10_cubic.json
  sixterm  Lean/DiophantineConsistency/Z10/Z10SyntaxSixterm.lean  from integer10_sixterm.json

(all under con-zfc-diophantine-forms/106-compact-certificates-round13/norm/). The JSON inputs are
inert data with pinned SHA-256 values (below).

The Lean literal has one definition per JSON node, in JSON order,
  def n<i> (p : Fin 4 → ℤ) : Expr (Fin 10) := ...
with the ten variables `t g0 c0 k0 l w x y z m` as `.var 0 … .var 9`, integer leaves as
`.constant (k)`, the two scales as the irreducible `Z10Regs.radix`, `Z10Regs.threshold`, and the ten
coefficient leaves `c000`–`c009` as their port polynomials (`fixed_recipes`, ports `β K0 MC MF`).

Every node gets an evaluation lemma `e<i>`, proved from its two children only (no proof unfolds the
DAG as a tree), in one of four shapes:

  * closed forms: a node depending only on the code base `𝔅 = Bc b` (node `base`), integer leaves
    and coefficient leaves evaluates to an explicit polynomial in `𝔅` and the ports (`ring`);
  * prefix functions: the named prefix nodes evaluate to the `Z10Regs` prefix definitions
    (`ell`, `AT`, `ker0/1/2`, `N0`, `NN`, `word`, `coded`, `mask`, `Tc + 2`, `AT + 2 coded`, `Sc`);
    the four sums are expanded from their layout tables (`N105Layout.weights/targets/pos*`,
    `N101Layout.c0/c1/c2`);
  * registers: a named register node evaluates to the field of `Z10Regs.regs (pc p) w` (`rfl` when
    the DAG and the record agree gate by gate, else the field's `_def` lemma and `ring`);
  * every other node evaluates to the expression of its children.

The output node evaluates to `Z10Regs.value` (polar) or `Z10Regs.valueS σ` (variants).

Before writing, every closed form, prefix function and register is checked numerically against the
JSON DAG and against an independent model of `Z10Regs` (exact integers modulo a 127-bit prime at
random points).

Usage:
  py -I -X utf8 -B gen_literal106.py FORM            write the Lean file
  py -I -X utf8 -B gen_literal106.py FORM --check    check the pin, the numerics, and that the file
                                                     on disk is byte-identical to the regeneration
"""
from pathlib import Path
import argparse, hashlib, importlib.util, json, random

HERE = Path(__file__).resolve()
DC = HERE.parents[3]
NORM = DC / 'con-zfc-diophantine-forms/106-compact-certificates-round13/norm'
FORMS = {
    'polar': ('integer10_polar.json', '63f5d72c36d03343b2ee3250e23099aaffd892ff3dec318f84137ae2ce1324eb',
              'Z10SyntaxPolar', 467),
    'linear': ('integer10_linear.json', '3d027fa1bab12e81c441c6cd23dd57e239e4ddeaf1eb0f8f6a90b2374706589f',
               'Z10SyntaxLinear', 470),
    'cubic': ('integer10_cubic.json', 'ef1fb28fa0dc65f18f41d84a80a0b881fd16046afe5fb14f52c83ef85386e3fa',
              'Z10SyntaxCubic', 473),
    'sixterm': ('integer10_sixterm.json', '408fcc66d4854360c3635341aec236ab73427211b860e63f7a9efb6ae0991aff',
                'Z10SyntaxSixterm', 507),
}
VARS = ['t', 'g0', 'c0', 'k0', 'l', 'w', 'x', 'y', 'z', 'm']
PRIME = (1 << 127) - 1
RADIX_EXP, THRESHOLD_EXP = 2134940, 34159017
OPS = {'add': '+', 'sub': '-', 'mul': '*'}
EVAL = {'add': 'Expr.evalRing_add', 'sub': 'Expr.evalRing_sub', 'mul': 'Expr.evalRing_mul'}
R = '(regs (pc p) w)'
B = 'Bc (regs (pc p) w).b'

# named register nodes -> (field of `Z10Regs.Regs`, extra definitions to unfold after the `_def`)
REG = {
    'b': ('b', ''), 'g': ('g', ''), 'twice_k': ('k2', ''), 'X': ('X', 'Z10Regs.Xc, Z10Regs.NN'),
    'Y': ('Y', 'Z10Regs.Yc'), 'cap': ('cap', 'Z10Regs.cap'), 'L': ('L', ''), 'halfU': ('halfU', ''),
    'U': ('U', ''), 'V': ('V', ''), 'W': ('W', ''), 'uv': ('uv', ''), 'halfA': ('halfA', ''),
    'A': ('A', ''), 'B1': ('B1', ''), 'C': ('C', ''), 'Phalf': ('Phalf', ''), 'K': ('K', 'Z10Regs.X_def, Z10Regs.Xc, Z10Regs.NN'),
    'S': ('S', ''), 'T': ('T', ''), 'Q': ('Q', ''), 'Delta': ('Delta', ''), 'xi': ('xi', ''),
    'D': ('D', ''), 'E0': ('E0', ''), 'E': ('E', ''), 'E2': ('E2', ''), 'F': ('F', ''),
    'G': ('G', 'Z10Regs.F_def'), 'Omega': ('Omega', ''), 'H': ('H', ''), 'I': ('I', ''), 'rho': ('rho', ''),
    'Theta': ('Theta', ''), 'r': ('r', ''), 'guard': ('a0', ''), 'lucas': ('a1', ''),
    'Sigma_new': ('Sigma', ''),
}
# named prefix nodes -> (Lean right-hand side, how to close)
PREFIX = {
    'ell': (f'ell {R}.b', ('table', 'Z10Regs.ell, N105Layout.weights')),
    'targets': (f'AT {R}.b', ('table', 'Z10Regs.AT, N105Layout.targets')),
    'Dcode0': (f'ker0 (pc p) {R}.b', ('table', 'Z10Regs.ker0, N101Layout.c0, N105Layout.pos0, pc')),
    'Dcode1': (f'ker1 (pc p) {R}.b', ('table', 'Z10Regs.ker1, N101Layout.c1, N105Layout.pos1, pc')),
    'Dcode2': (f'ker2 (pc p) {R}.b', ('table', 'Z10Regs.ker2, N101Layout.c2, N105Layout.pos2, pc')),
    'word': (f'word {R}.b {R}.g', ('unfold', 'Z10Regs.word')),
    'coded': (f'coded (pc p) {R}.b {R}.g', ('unfold', 'Z10Regs.coded')),
    'mask': (f'mask {R}.b', ('unfold', 'Z10Regs.mask, Z10Regs.N0')),
    'tc_original': (f'Tc {R}.b + 2', ('unfold', 'Z10Regs.Tc, Z10Regs.N0')),
    'jc': (f'AT {R}.b + 2 * coded (pc p) {R}.b {R}.g', ('ring', '')),
    'sc': (f'Sc (pc p) {R}.b {R}.g', ('unfold', 'Z10Regs.Sc, Z10Regs.N0')),
}
# the shear of a variant: Lean definition and the definitions to unfold
SHEAR = {
    'linear': ('shearLin', 'Z10Regs.shearLin'),
    'cubic': ('shearCub', 'Z10Regs.shearCub'),
    'sixterm': ('shearSix', 'Z10Regs.shearSix, Z10Regs.sixT, Z10Regs.sixA, Z10Regs.sixB'),
}
# named nodes with no Lean field or prefix function: evaluated like unnamed nodes
INLINE = {'base', 'CKL', 'Fm1', 'shifted_center', 'Theta_new', 'n0', 'nn'}


def need(ok, msg):
    if not ok:
        raise SystemExit('FAIL: ' + msg)


def load(form):
    name, pin, module, ops = FORMS[form]
    raw = (NORM / name).read_bytes()
    need(hashlib.sha256(raw).hexdigest() == pin, f'{name} pin')
    d = json.loads(raw)
    need(d['variables'] == VARS, 'variable order')
    need(d['output'] == len(d['nodes']) - 1, 'output node is last')
    need(d['total_operations'] == ops, 'operation count')
    need(sum(1 for n in d['nodes'] if n['kind'] in OPS) == ops, 'counted operations')
    for nm in d['named_nodes']:
        need(nm in REG or nm in PREFIX or nm in INLINE or (nm == 'shear' and form in SHEAR),
             f'unclassified named node {nm}')
    need(('shear' in d['named_nodes']) == (form in SHEAR), 'shear node exactly in the variants')
    return d


def recipe(d, name):
    out = {}
    for t in d['fixed_recipes'][name]:
        m = tuple(t['powers'])
        need(len(m) == 4 and m not in out, 'recipe ' + name)
        out[m] = t['coefficient']
    return out


# ---------------------------------------------------------------- closed forms {(eB, ports): c}
def cf_add(a, b, s=1):
    out = dict(a)
    for k, v in b.items():
        out[k] = out.get(k, 0) + s * v
    return {k: v for k, v in out.items() if v}


def cf_mul(a, b):
    out = {}
    for (ea, ma), ca in a.items():
        for (eb, mb), cb in b.items():
            k = (ea + eb, tuple(x + y for x, y in zip(ma, mb)))
            out[k] = out.get(k, 0) + ca * cb
    return {k: v for k, v in out.items() if v}


def cf_lean(cf):
    if not cf:
        return '(0 : R)'
    terms = []
    for (e, m), c in sorted(cf.items()):
        parts = [f'(p {j} : R)' + (f' ^ {x}' if x > 1 else '') for j, x in enumerate(m) if x]
        if e == 1:
            parts.append(B)
        elif e > 1:
            parts.append(f'{B} ^ {e}')
        body = ' * '.join(parts)
        if not body:
            terms.append(f'({c} : R)')
        elif c == 1:
            terms.append(body)
        else:
            terms.append(f'({c} : R) * {body}')
    return ' + '.join(terms)


def int_poly(poly):
    terms = []
    for m, c in sorted(poly.items()):
        mono = ' * '.join(f'p {j}' + (f' ^ {e}' if e > 1 else '') for j, e in enumerate(m) if e)
        terms.append(f'({c})' if not mono else (mono if c == 1 else f'({c}) * {mono}'))
    return ' + '.join(terms)


def analyse(d):
    ns = d['nodes']
    named = {}
    for nm, i in d['named_nodes'].items():
        if nm == 'Theta_new':
            continue
        need(i not in named, f'node {i} named twice')
        named[i] = nm
    base = d['named_nodes']['base']
    bnode = d['named_nodes']['b']
    need(ns[base]['kind'] == 'mul', 'base is a product')
    need(ns[ns[base]['left']] == {'kind': 'fixed', 'name': 'radix'}, 'base = radix * _')
    bb = ns[base]['right']
    need(ns[bb] == {'kind': 'mul', 'left': bnode, 'right': bnode}, 'base = radix * (b * b)')
    cf = [None] * len(ns)
    for i, nd in enumerate(ns):
        k = nd['kind']
        if k == 'literal':
            cf[i] = {(0, (0, 0, 0, 0)): nd['value']} if nd['value'] else {}
        elif k == 'fixed' and nd['name'] not in ('radix', 'threshold'):
            cf[i] = {(0, m): c for m, c in recipe(d, nd['name']).items()}
        elif i == base:
            cf[i] = {(1, (0, 0, 0, 0)): 1}
        elif k in OPS and named.get(i) not in REG:
            l, r = nd['left'], nd['right']
            if (cf[l] is not None and cf[r] is not None and named.get(l) not in PREFIX
                    and named.get(r) not in PREFIX):
                cf[i] = cf_add(cf[l], cf[r]) if k == 'add' else cf_add(cf[l], cf[r], -1) if k == 'sub' \
                    else cf_mul(cf[l], cf[r])
    for i, nm in named.items():
        if nm in PREFIX and PREFIX[nm][1][0] == 'table':
            need(cf[i] is not None, f'table node {nm} is a closed form')
    return named, cf, base


# ---------------------------------------------------------------- numerics
def layout():
    spec = importlib.util.spec_from_file_location(
        'gen105', DC / 'research/nine-positive-p105-456-endpoint/tools/generate_n105_layout.py')
    gen = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(gen)
    dd = gen.analyse()
    return dd['w'], dd['E'], dd['pos'], dd['coef']


def pval(poly, ports):
    s = 0
    for m, c in poly.items():
        t = c
        for j, e in enumerate(m):
            t *= pow(ports[j], e, PRIME)
        s += t
    return s % PRIME


def dag_eval(d, vals, ports):
    out = []
    for nd in d['nodes']:
        k = nd['kind']
        if k == 'variable':
            out.append(vals[VARS.index(nd['name'])] % PRIME)
        elif k == 'literal':
            out.append(nd['value'] % PRIME)
        elif k == 'fixed':
            if nd['name'] == 'radix':
                out.append(pow(2, RADIX_EXP, PRIME))
            elif nd['name'] == 'threshold':
                out.append(pow(2, THRESHOLD_EXP, PRIME))
            else:
                out.append(pval(recipe(d, nd['name']), ports))
        else:
            a, b = out[nd['left']], out[nd['right']]
            out.append((a + b if k == 'add' else a - b if k == 'sub' else a * b) % PRIME)
    return out


def model(vals, ports, lay):
    """An independent model of `Z10Regs` (prefix, registers, polar value), modulo PRIME."""
    P = PRIME
    Wt, Et, pos, coef = lay
    t, g0, c0, k0, l, w, xx, y, z, m = vals
    b = 6 * t + 4; g = b * g0; k2 = b * (6 * k0 + 4)
    Bc = pow(2, RADIX_EXP, P) * b * b % P
    ker = [sum(pval(coef[q][i], ports) * pow(Bc, pos[q][i], P) for i in range(len(pos[q]))) % P
           for q in range(3)]
    ell = sum(pow(Bc, e, P) for e in Wt) % P
    AT = sum(pow(Bc, e, P) for e in Et) % P
    word = ell + g; coded = ker[0] + word * (ker[1] + word * ker[2])
    N0 = pow(Bc, 117, P); NN = pow(Bc, 1986, P)
    mask = N0 - 1 - ell * (b - 1); Tc = mask + N0 * (AT * (Bc - 2)) - 2
    Sc = g + N0 * (AT + 2 * coded); X = NN * (Sc + Tc + 1) - Sc - 1
    Y = b * (pow(2, THRESHOLD_EXP, P) * pow(Bc, 2109, P)); cap = b * pow(Bc, 116, P)
    L = l * Y; halfU = L * X; U = 2 * halfU; V = 4 * g * w * Y; W = b * w; uv = halfU * V
    halfA = halfU + uv; A = 2 * halfA; B1 = 2 * X + 1; C = 6 * c0 - 1; Phalf = U * uv
    K = X + 1 + k2 * (Phalf - 1); S = 2 * A - 5; T = 3 * W * C - 2 * (W * W - 1)
    Q = (Phalf * Phalf - 1) * (K * K) + 1
    Delta = g * (cap - g) * (K * K) - cap * cap * ((C - K * L) * (C - K * L)); xi = z * xx
    D = (A * A - 4) * (C * C) + 4; E0 = C * C * xi; E = D * E0; E2 = E0 * E
    F = 4 * (A * A - 4) * E2 + 1; G = (halfA - 1) * (F - 1) - 1; Omega = 16 * E
    H = C + F * (B1 - C + Omega * y); I = (G * G - 1) * (H * H) + 1; rho = T + S * y
    Sigma = xi * S ** 5; Theta = (rho ** 3 - rho * S ** 2 - S ** 3) * (rho ** 2 + 23 * S ** 2)
    r = b * Q; a0 = r + (9 * Delta - 3) * (r * z) ** 2; a1 = D * F * I
    sixA = 6 + C * C * (2 * (halfA * halfA) - 11)
    sixB = 48 + ((8 * halfA ** 4 - 52 * (halfA * halfA) + 143) * (C * C) ** 2 +
                 C * C * (32 * (halfA * halfA) - 176))
    sixT = 3 * y + (sixA * (xi * (B1 - C)) + sixB * (y * (xi * (E0 * 16))))
    shears = {'polar': 0, 'linear': G * H * (2 * A * E),
              'cubic': G * H * ((D - 2 * (C * C)) * (2 * A * E0)),
              'sixterm': ((halfA - 1) * sixT - 2 * y) * (halfA ** 9 * (E0 ** 4 * (32768 * (C * C) ** 3)))}
    values = {}
    for f, sh in shears.items():
        th = Sigma * (m + sh) - Theta
        values[f] = ((th ** 2 - Sigma ** 2 * (a0 + a1)) ** 2 - 4 * Sigma ** 4 * a0 * a1) % P
    value = values
    regs = dict(b=b, g=g, k2=k2, X=X, Y=Y, cap=cap, L=L, halfU=halfU, U=U, V=V, W=W, uv=uv,
                halfA=halfA, A=A, B1=B1, C=C, Phalf=Phalf, K=K, S=S, T=T, Q=Q, Delta=Delta, xi=xi,
                D=D, E0=E0, E=E, E2=E2, F=F, G=G, Omega=Omega, H=H, I=I, rho=rho, Theta=Theta, r=r,
                a0=a0, a1=a1, Sigma=Sigma)
    pre = {'ell': ell, 'targets': AT, 'Dcode0': ker[0], 'Dcode1': ker[1], 'Dcode2': ker[2],
           'word': word, 'coded': coded, 'mask': mask, 'tc_original': Tc + 2,
           'jc': AT + 2 * coded, 'sc': Sc}
    return ({k: v % P for k, v in regs.items()}, {k: v % P for k, v in pre.items()}, Bc,
            value, {f: s % P for f, s in shears.items()})


def numeric_checks(form, d, named, cf):
    lay = layout()
    rng = random.Random(106467 + len(form))
    for _ in range(4):
        vals = [rng.randrange(PRIME) for _ in VARS]
        ports = [rng.randrange(PRIME) for _ in range(4)]
        ev = dag_eval(d, vals, ports)
        regs, pre, Bc, value, shears = model(vals, ports, lay)
        for i, c in enumerate(cf):
            if c is not None:
                s = 0
                for (e, m), co in c.items():
                    t = co * pow(Bc, e, PRIME)
                    for j, x in enumerate(m):
                        t *= pow(ports[j], x, PRIME)
                    s += t
                need(s % PRIME == ev[i], f'closed form of node {i}')
        for i, nm in named.items():
            if nm in REG:
                need(ev[i] == regs[REG[nm][0]], f'register {nm} (node {i})')
            elif nm in PREFIX:
                need(ev[i] == pre[nm], f'prefix node {nm} (node {i})')
            elif nm == 'shear':
                need(ev[i] == shears[form], f'shear (node {i})')
        need(ev[d['output']] == value[form], f'output = Z10Regs value of {form}')


# ---------------------------------------------------------------- Lean rendering
def node_def(d, i):
    nd = d['nodes'][i]
    k = nd['kind']
    if k == 'variable':
        body = f'.var {VARS.index(nd["name"])}'
    elif k == 'literal':
        body = f'.constant ({nd["value"]})'
    elif k == 'fixed':
        if nd['name'] in ('radix', 'threshold'):
            body = f'.constant {nd["name"]}'
        else:
            body = f'.constant ({int_poly(recipe(d, nd["name"]))})'
    else:
        body = f'n{nd["left"]} p {OPS[k]} n{nd["right"]} p'
    tag = f'  -- {nd["name"]}' if k in ('variable', 'fixed') else ''
    return f'def n{i} (p : Fin 4 → ℤ) : Expr (Fin 10) := {body}{tag}'


def lemmas(d, named, cf, base, output_rhs, output_tail, shear=None):
    ns = d['nodes']
    rhs = [None] * len(ns)
    out = []
    for i, nd in enumerate(ns):
        k = nd['kind']
        nm = named.get(i)
        if k == 'variable':
            rhs[i] = f'w {VARS.index(nd["name"])}'
            out.append(f'theorem e{i} : (n{i} p).evalRing w = {rhs[i]} := rfl')
            continue
        if k == 'fixed' and nd['name'] in ('radix', 'threshold'):
            rhs[i] = f'(({nd["name"]} : ℤ) : R)'
            out.append(f'theorem e{i} : (n{i} p).evalRing w = {rhs[i]} := rfl')
            continue
        if k in ('literal', 'fixed'):
            rhs[i] = cf_lean(cf[i])
            out.append(f'theorem e{i} : (n{i} p).evalRing w = {rhs[i]} := by\n  norm_num [n{i}]')
            continue
        l, r = nd['left'], nd['right']
        rws = f'n{i}, {EVAL[k]}, e{l}' + (f', e{r}' if r != l else '')
        if i == base:
            rhs[i] = B
            out.append(f'theorem e{i} : (n{i} p).evalRing w = {B} := by\n  rw [{rws}]\n  try rfl')
        elif nm in REG:
            field, unf = REG[nm]
            rhs[i] = f'{R}.{field}'
            extra = f', {unf}' if unf else ''
            out.append(f'theorem e{i} : (n{i} p).evalRing w = {rhs[i]} := by\n  rw [{rws}]\n'
                       f'  try (rw [Z10Regs.{field}_def{extra}]; try ring)')
        elif nm == 'shear':
            sname, unf = shear
            rhs[i] = f'{sname} {R} (w 7)'
            out.append(f'theorem e{i} : (n{i} p).evalRing w = {rhs[i]} := by\n  rw [{rws}]\n'
                       f'  simp only [{unf}]\n  try ring')
        elif nm in PREFIX:
            rhs[i], (how, defs) = PREFIX[nm]
            if how == 'table':
                tail = (f'  simp only [{defs}, Fin.sum_univ_succ, Fin.sum_univ_zero,\n'
                        f'    Matrix.cons_val_zero, Matrix.cons_val_succ]\n  ring')
            elif how == 'unfold':
                tail = f'  try (rw [{defs}]; try ring)'
            else:
                tail = '  try ring'
            out.append(f'theorem e{i} : (n{i} p).evalRing w = {rhs[i]} := by\n  rw [{rws}]\n{tail}')
        elif cf[i] is not None:
            rhs[i] = cf_lean(cf[i])
            out.append(f'theorem e{i} : (n{i} p).evalRing w = {rhs[i]} := by\n  rw [{rws}]; try ring')
        elif i == len(ns) - 1:
            rhs[i] = output_rhs
            out.append(f'theorem e{i} : (n{i} p).evalRing w = {rhs[i]} := by\n  rw [{rws}]\n'
                       f'{output_tail}')
        else:
            rhs[i] = f'(({rhs[l]}) {OPS[k]} ({rhs[r]}))'
            out.append(f'theorem e{i} : (n{i} p).evalRing w = {rhs[i]} := by\n  rw [{rws}]')
    return out


HEADER = '''import DiophantineConsistency.WeightedExpressionDegree
import DiophantineConsistency.Z10.Z10Regs
import DiophantineConsistency.Nine121.Source31Facts
import DiophantineConsistency.Mixed121.Mixed121Ports

/-! # Package 106's {ops}-operation ten-integer {form} equation, as a Lean literal

Generated by `research/p106-integer10/tools/gen_literal106.py {form}` from
`con-zfc-diophantine-forms/106-compact-certificates-round13/norm/{json}`
(SHA-256 `{pin}`): {nodes} nodes, {ops} live operations, variables `t g0 c0 k0 l w x y z m`,
output node {out}. Node `nᵢ` is the JSON node `i`; the fixed leaves are `Z10Regs.radix = 2^2134940`,
`Z10Regs.threshold = 2^34159017` (irreducible) and the ten coefficient leaves `c000`–`c009` as port
polynomials in `p = (β, K0, MC, MF)`.

The evaluation is proved gate by gate (`eᵢ`, from the two children only): closed forms in the code
base `𝔅 = Bc b`, the `Z10Regs` prefix definitions (the four sums expanded from their layout
tables), the fields of `Z10Regs.regs (pc p) w`, and the expressions of the remaining nodes.
`evalRing_literal`: the literal evaluates to {target} in every commutative ring;
`literal_zero_iff`: at the ports of the 121x8801 machine, its zeros in the ring of differences of a
model of `𝗜𝚺₁` are the zeros of {target_short}. The correspondence with the JSON is checked by
`gen_literal106.py {form} --check` (pin, numeric model, byte-identical regeneration). -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
set_option linter.unusedVariables false
noncomputable section
namespace DiophantineConsistency.{module}
open Nine121 Z10Regs

/-! ## The literal DAG -/

'''


def render(form, d, named, cf, base):
    name, pin, module, ops = FORMS[form]
    ns = d['nodes']
    outn = len(ns) - 1
    if form == 'polar':
        target = '`Z10Regs.value (pc p) w`'
        target_short = '`Z10Regs.value pR`'
        out_rhs = 'value (pc p) w'
        out_tail = '  rw [value_def]\n  unfold Nine121.N9Norm.norm2\n  ring'
        lit_stmt = 'value (pc p) w'
        zero_stmt = 'value pR x'
    else:
        sname = SHEAR[form][0]
        target = f'`Z10Regs.valueS Z10Regs.{sname} (pc p) w`'
        target_short = f'`Z10Regs.valueS Z10Regs.{sname} pR`'
        out_rhs = f'valueS {sname} (pc p) w'
        out_tail = '  unfold Z10Regs.valueS Z10Regs.out Nine121.N9Norm.norm2\n  ring'
        lit_stmt = out_rhs
        zero_stmt = f'valueS {sname} pR x'
    head = HEADER.format(ops=ops, form=form, json=name, pin=pin, nodes=len(ns), out=outn,
                         target=target, target_short=target_short, module=module)
    defs = '\n'.join(node_def(d, i) for i in range(len(ns)))
    lem = lemmas(d, named, cf, base, out_rhs, out_tail, SHEAR.get(form))
    body = (head + defs + f'''

/-- The literal: the output node. -/
def literal (p : Fin 4 → ℤ) : Expr (Fin 10) := n{outn} p

/-- The ports in a commutative ring. -/
def pc {{R : Type*}} [CommRing R] (p : Fin 4 → ℤ) : Fin 4 → R := fun j => (p j : R)

section Eval
variable {{R : Type*}} [CommRing R] (p : Fin 4 → ℤ) (w : Fin 10 → R)

''' + '\n\n'.join(lem) + f'''

/-- **The literal evaluates to {target} in every commutative ring.** -/
theorem evalRing_literal : (literal p).evalRing w = {lit_stmt} := e{outn} p w

end Eval

section Model
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open ModelDifferenceRing
variable {{V : Type}} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

attribute [local irreducible] Mixed121Ports.ports

/-- The ports in the ring of differences. -/
local notation "pR" => Source31Facts.portsR (V := V) Mixed121Ports.ports

/-- At the ports of the 121x8801 machine, the zeros of the literal in `DiffRing V` are the
zeros of {target_short}. -/
theorem literal_zero_iff (x : Fin 10 → DiffRing V) :
    (literal (fun j => (Mixed121Ports.ports j : ℤ))).evalRing x = 0 ↔ {zero_stmt} = 0 := by
  rw [evalRing_literal]
  rfl

end Model

end DiophantineConsistency.{module}

#print axioms DiophantineConsistency.{module}.evalRing_literal
#print axioms DiophantineConsistency.{module}.literal_zero_iff
''')
    return module, body


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('form', choices=sorted(FORMS))
    ap.add_argument('--check', action='store_true')
    args = ap.parse_args()
    d = load(args.form)
    named, cf, base = analyse(d)
    numeric_checks(args.form, d, named, cf)
    module, text = render(args.form, d, named, cf, base)
    path = DC / f'Lean/DiophantineConsistency/Z10/{module}.lean'
    if args.check:
        need(path.read_text(encoding='utf-8') == text, f'generated file differs: {path.name}')
    else:
        with open(path, 'w', encoding='utf-8', newline='\n') as f:
            f.write(text)
    print(json.dumps({'form': args.form, 'status': 'PASS' if args.check else 'GENERATED',
                      'nodes': len(d['nodes']), 'closed_forms': sum(c is not None for c in cf),
                      'pin': FORMS[args.form][1]}))


if __name__ == '__main__':
    main()
