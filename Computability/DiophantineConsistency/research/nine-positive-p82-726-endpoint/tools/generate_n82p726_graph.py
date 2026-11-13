#!/usr/bin/env python3
"""Emit Nine121/N82p726Graph.lean: package 82's 726-operation nine-positive DAG as a Lean literal.

Input (inert JSON, SHA-256 pinned below):
  82-pell-congruences/nine_full_radical/laurent9_positive.json (861 nodes, output 860).
Nodes 0..408 are package 71's source65 prefix (base B = node 13), the ratio registers follow, the
Pell registers D (425), E (430), F (433), Lambda (454), G (456), Z (439), H (441), I (504); node 844 is
the Laurent majorant T, 846 the scale S = 2^18 C^7, 850 the radicand a1 = DFI S^2, 860 the output.

The Lean literal has one definition per node: `n<i> (p : Fin 4 → ℤ) : Expr (Fin 9)` in the JSON order,
with variables `b g h s w C i j n`, literals as integer constants, the two scales as the irreducible
`N101Prefix.baseScale` / `N82Prefix.thresholdScale82`, and the eleven fixed coefficient leaves as
their port polynomials (from `coefficient_recipes`, ports `β K MC MF`).

Evaluation lemmas are gate-local, so no proof ever unfolds the DAG as a tree:
  * every node depending only on `B` (node 13), literals and coefficient leaves gets its exact
    closed form (a polynomial in `Bq (w 0)` and the ports), proved from its two children by `ring`;
  * the prefix registers (kernels, ell, T*, U*, G*, M0, T_c, S*, L, N, R, t) are identified with the
    `N82Prefix` definitions;
  * the finalizer registers are stated over the evaluations of other register nodes (atoms) and fed
    to `value_regs`, which is `N82Finalizer.value` with its lets named; the majorant register `r844`
    is `N82Majorant.TR` (the block `N82Majorant.tBlock`), proved by unfolding its cone and `rfl`.

Before writing, every closed form and register formula is checked numerically against the JSON DAG
(exact integers modulo 2^127 - 1, at random points), and the output is checked against an
independent Python model of `N82Finalizer.value` composed with the prefix (T evaluated as 4 T0 from
the 654-term `laurent_candidate.json`).

Use --check to compare with the file on disk instead of writing it.
"""
from pathlib import Path
import argparse, hashlib, importlib.util, json, random, re

HERE = Path(__file__).resolve()
DC = HERE.parents[3]
LEAN = DC / 'Lean/DiophantineConsistency/Nine121/N82p726Graph.lean'
PKG = DC / 'con-zfc-diophantine-forms/82-pell-congruences/nine_full_radical'
SRC = PKG / 'laurent9_positive.json'
PIN = '56e8629e1590157e608d5ffafcf3943b925562578fba4854c81d443ed2e54f93'
OUTN = 860
BNODE = 13
VARS = ['b', 'g', 'h', 's', 'w', 'C', 'i', 'j', 'n']
PRIME = (1 << 127) - 1
KAPPA, THETA = 2134939, 17079501


def need(ok, msg):
    if not ok:
        raise SystemExit('FAIL: ' + msg)


def load():
    raw = SRC.read_bytes()
    need(hashlib.sha256(raw).hexdigest() == PIN, 'laurent9_positive.json pin')
    d = json.loads(raw)
    need(d['variables'] == VARS, 'variable order')
    need(d['output'] == len(d['nodes']) - 1 == OUTN, 'output node')
    need(d['base_scale_exponent'] == KAPPA and d['threshold_scale_exponent'] == THETA, 'scales')
    need(d['total_operations'] == 726, 'operation count')
    ops = sum(1 for n in d['nodes'] if n['kind'] in ('add', 'sub', 'mul'))
    need(ops == 726, 'counted operations')
    ns = d['nodes']
    need(ns[BNODE] == {'kind': 'mul', 'left': 11, 'right': 12}, 'node 13 is B')
    need(ns[11] == {'kind': 'fixed', 'name': 'base_scale'} and ns[12] == {'kind': 'mul', 'left': 1, 'right': 1},
         'B = base_scale * (b * b)')
    return d


def recipe(d, name):
    for r in d['coefficient_recipes']:
        if r['name'] == name:
            out = {}
            for t in r['terms']:
                m = tuple(t['powers'])
                need(len(m) == 4 and m not in out, 'recipe ' + name)
                out[m] = t['coefficient']
            return out
    raise SystemExit('FAIL: no recipe ' + name)


def port_mono(m):
    return [f'(p {j} : R)' + (f' ^ {e}' if e > 1 else '') for j, e in enumerate(m) if e]


def int_poly(poly):
    terms = []
    for m, c in sorted(poly.items()):
        mono = ' * '.join(f'p {j}' + (f' ^ {e}' if e > 1 else '') for j, e in enumerate(m) if e)
        if not mono:
            terms.append(f'({c})')
        elif c == 1:
            terms.append(mono)
        else:
            terms.append(f'({c}) * {mono}')
    return ' + '.join(terms)


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
        return '0'
    terms = []
    for (e, m), c in sorted(cf.items(), key=lambda kv: (kv[0][0], kv[0][1])):
        parts = port_mono(m)
        if e == 1:
            parts.append('Bq (w 0)')
        elif e > 1:
            parts.append(f'Bq (w 0) ^ {e}')
        body = ' * '.join(parts)
        if not body:
            terms.append(f'({c} : R)')
        elif c == 1:
            terms.append(body)
        else:
            terms.append(f'({c} : R) * {body}')
    return ' + '.join(terms)


# ---------------------------------------------------------------- registers
# prefix registers: node -> (Lean RHS, definitions to unfold before ring)
PREFIX = {
    201: ('ker0 (pc p) (w 0)', None),
    285: ('ker1 (pc p) (w 0)', None),
    365: ('ker2 (pc p) (w 0)', None),
    133: ('ell (w 0)', None),
    180: ('Tst (w 0)', None),
    202: ('Ust (w 0) (w 1)', 'Ust'),
    369: ('Gs (pc p) (w 0) (w 1)', 'Gs'),
    136: ('maskq (w 0)', 'maskq, N0'),
    184: ('Tcq (w 0)', 'Tcq, N0'),
    373: ('Scq (pc p) (w 0) (w 1)', 'Scq, N0'),
    102: ('Lq (w 0)', 'Lq'),
    383: ('Nq (w 0)', 'Nq'),
    378: ('Rq (pc p) (w 0) (w 1)', 'Rq'),
    408: ('tq (w 0)', 'tq'),
}
KERNELS = {201: ('ker0', 'c0, pos0'), 285: ('ker1', 'c1, pos1'), 365: ('ker2', 'c2, pos2'),
           133: ('ell', 'weights'), 180: ('Tst', 'targets')}
# finalizer registers, in the order of the lets of `N82Finalizer.value`
FINAL = [
    (387, 'U', 'E383 ^ 2 * w 4'),
    (385, 'Y', 'E383 ^ 2 * w 3'),
    (386, 'M', 'E378 * E385'),
    (402, 'P', '2 * E386 ^ 2 * E387'),
    (406, 'K', 'E378 + 1 + w 2 * (E402 - 1)'),
    (389, 'Am', 'E386 * (E387 + 1)'),
    (435, 'B1', '2 * E378 + 1'),
    (3, 'W1', 'w 0 * w 4'),
    (393, 'J', '4 * E389 - 5'),
    (10, 'Qr', '3 * E3 * w 5 - 2 * (E3 ^ 2 - 1)'),
    (418, 'm', 'E406 ^ 2 * (4 * E408 - w 1) - 16 * E408 * (w 5 - E406 * E385) ^ 2'),
    (419, 'Om', 'E393 * E418'),
    (398, 'E0', 'E393 * (w 8 + E3 ^ 2) + E10'),
    (420, 'V0', 'E402 * E406'),
    (499, 'a0', '(E402 ^ 2 - 1) * E406 ^ 2 + 1'),
    (425, 'D', '(E389 ^ 2 - 1) * w 5 ^ 2 + 1'),
    (430, 'E', 'w 6 * E393 * w 5 ^ 2 * E425'),
    (433, 'F', '(E389 ^ 2 - 1) * E430 ^ 2 + 1'),
    (454, 'Lam', 'w 5 * E425 + 1 - E389'),
    (456, 'G', 'E389 + E433 * E454'),
    (439, 'Z', 'E435 + (w 7 - 1) * w 5'),
    (441, 'H1', 'w 5 + E433 * E439'),
    (504, 'I', '(E456 ^ 2 - 1) * E441 ^ 2 + 1'),
    (846, 'S', '262144 * w 5 ^ 7'),
    (850, 'a1', 'E425 * E433 * E504 * (E846 * E846)'),
    (844, 'V1', 'N82Majorant.TR E389 (w 5) (w 6) E439'),
]
OUTPUT = 'N9Norm.norm2 (E398 - E419 * (E420 + E844)) E419 E499 E850'
T_NODE = 844
T_ATOMS = {389, 4, 426, 439}
FINAL_INPUTS = {383, 378, 408}
EXTRA_RW = {499: ['r420']}


def atom(i):
    return f'((n{i} p).evalRing w)'


def subst_atoms(text):
    return re.sub(r'E(\d+)', lambda m: atom(int(m.group(1))), text)


def internal(ns, root, boundary):
    seen, stack, inner, edge = set(), [root], [], set()
    while stack:
        i = stack.pop()
        if i in seen:
            continue
        seen.add(i)
        if i != root and i in boundary:
            edge.add(i)
            continue
        inner.append(i)
        nd = ns[i]
        if nd['kind'] in ('add', 'sub', 'mul'):
            stack += [nd['left'], nd['right']]
    return sorted(inner), sorted(edge)


def analyse(d):
    ns = d['nodes']
    cf = [None] * len(ns)
    for i, nd in enumerate(ns):
        k = nd['kind']
        if k == 'literal':
            cf[i] = {(0, (0, 0, 0, 0)): nd['value']} if nd['value'] else {}
        elif k == 'fixed' and nd['name'].startswith('c'):
            cf[i] = {(0, m): c for m, c in recipe(d, nd['name']).items()}
        elif i == BNODE:
            cf[i] = {(1, (0, 0, 0, 0)): 1}
        elif (k in ('add', 'sub', 'mul') and cf[nd['left']] is not None and cf[nd['right']] is not None
              and nd['left'] not in PREFIX and nd['right'] not in PREFIX):
            l, r = cf[nd['left']], cf[nd['right']]
            cf[i] = cf_add(l, r) if k == 'add' else cf_add(l, r, -1) if k == 'sub' else cf_mul(l, r)
    return cf


# ---------------------------------------------------------------- numeric model
def mod_eval(d, vals, ports):
    ns = d['nodes']
    base = pow(2, KAPPA, PRIME)
    thr = pow(2, THETA, PRIME)
    out = []
    for nd in ns:
        k = nd['kind']
        if k == 'variable':
            out.append(vals[VARS.index(nd['name'])] % PRIME)
        elif k == 'literal':
            out.append(nd['value'] % PRIME)
        elif k == 'fixed':
            if nd['name'] == 'base_scale':
                out.append(base)
            elif nd['name'] == 'threshold_scale':
                out.append(thr)
            else:
                s = 0
                for m, c in recipe(d, nd['name']).items():
                    t = c
                    for j, e in enumerate(m):
                        t *= pow(ports[j], e, PRIME)
                    s += t
                out.append(s % PRIME)
        else:
            a, b = out[nd['left']], out[nd['right']]
            out.append((a + b if k == 'add' else a - b if k == 'sub' else a * b) % PRIME)
    return out


def t0_mod(a, c, i, t):
    cand = json.loads((PKG / 'laurent_candidate.json').read_bytes())
    s = 0
    for m, co in cand['majorant']:
        s += int(co) * pow(a, m[0], PRIME) * pow(c, m[1], PRIME) * pow(i, m[2], PRIME) * pow(t, m[3], PRIME)
    return s % PRIME


def model(vals, ports, layout):
    """Independent model: N82Prefix definitions and N82Finalizer.value, modulo PRIME."""
    P = PRIME
    b, g, h, s, w, C, i, j, n = (v % P for v in vals)
    B = pow(2, KAPPA, P) * b * b % P
    W, E, pos, coef = layout

    def cval(poly):
        t = 0
        for m, c in poly.items():
            u = c
            for k2, e in enumerate(m):
                u *= pow(ports[k2], e, P)
            t += u
        return t % P
    ker = [sum(cval(coef[dd][q]) * pow(B, pos[dd][q], P) for q in range(len(pos[dd]))) % P for dd in range(3)]
    ell = sum(pow(B, x, P) for x in W) % P
    Tst = sum(pow(B, x, P) for x in E) % P
    U = (g + ell) % P
    G = (ker[0] + U * (ker[1] + U * ker[2])) % P
    N0 = pow(B, 117, P)
    mask = (N0 - 1 - ell * (b - 1)) % P
    Tc = (mask + N0 * (Tst * (B - 2))) % P
    Sc = (g + N0 * (Tst + 2 * G)) % P
    L = b * pow(B, 1991, P) % P
    R = (L * (1 + (Tc + Sc)) - Sc - 1) % P
    N = pow(2, THETA, P) * b * pow(B, 1057, P) % P
    t = b * pow(B, 116, P) % P
    Uf = N * N * w; Y = N * N * s; M = R * Y; Pp = 2 * M * M * Uf
    K = R + 1 + h * (Pp - 1); Am = M * (Uf + 1); B1 = 2 * R + 1; W1 = b * w
    J = 4 * Am - 5; Qr = 3 * W1 * C - 2 * (W1 * W1 - 1)
    m = K * K * (4 * t - g) - 16 * t * (C - K * Y) ** 2
    Om = J * m; E0 = J * (n + W1 * W1) + Qr; V0 = Pp * K; a0 = (Pp * Pp - 1) * K * K + 1
    D = (Am * Am - 1) * C * C + 1; Ee = i * J * C * C * D; F = (Am * Am - 1) * Ee * Ee + 1
    Lam = C * D + 1 - Am; Gf = Am + F * Lam; Z = B1 + (j - 1) * C; H1 = C + F * Z
    I = (Gf * Gf - 1) * H1 * H1 + 1
    S = 262144 * pow(C, 7, P)
    a1 = D * F * I * (S * S)
    V1 = 4 * t0_mod(Am % P, C, i, Z % P)
    th = E0 - Om * (V0 + V1)
    val = (th * th - Om * Om * (a0 + a1)) ** 2 - 4 * Om ** 4 * a0 * a1
    regs = dict(ker0=ker[0], ker1=ker[1], ker2=ker[2], ell=ell, Tst=Tst, U=U, G=G, mask=mask, Tc=Tc,
                Sc=Sc, L=L, N=N, R=R, t=t, T=V1, value=val)
    return {k: v % P for k, v in regs.items()}


def layout_data():
    spec = importlib.util.spec_from_file_location('gen82', HERE.parent / 'generate_n82_layout.py')
    gen = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(gen)
    dd = gen.analyse()
    return dd['w'], dd['E'], dd['pos'], dd['coef']


def numeric_checks(d, cf, layout):
    rng = random.Random(20261109)
    ns = d['nodes']
    for trial in range(4):
        vals = [rng.randrange(1, PRIME) for _ in VARS]
        ports = [rng.randrange(1, PRIME) for _ in range(4)]
        ev = mod_eval(d, vals, ports)
        B = pow(2, KAPPA, PRIME) * vals[0] * vals[0] % PRIME
        for i, c in enumerate(cf):
            if c is None:
                continue
            s = 0
            for (e, m), co in c.items():
                t = co * pow(B, e, PRIME)
                for j, x in enumerate(m):
                    t *= pow(ports[j], x, PRIME)
                s += t
            need(s % PRIME == ev[i], f'closed form of node {i}')
        mdl = model(vals, ports, layout)
        for node, key in [(201, 'ker0'), (285, 'ker1'), (365, 'ker2'), (133, 'ell'), (180, 'Tst'),
                          (202, 'U'), (369, 'G'), (136, 'mask'), (184, 'Tc'), (373, 'Sc'), (102, 'L'),
                          (383, 'N'), (378, 'R'), (408, 't'), (844, 'T')]:
            need(ev[node] == mdl[key], f'prefix register {key} (node {node})')
        need(ev[OUTN] == mdl['value'], 'output = value(prefix)')
        env = {f'E{k}': ev[k] for k in range(len(ns))}
        w = vals
        for node, name, formula in FINAL:
            if node == T_NODE:
                need(4 * t0_mod(ev[389], w[5], w[6], ev[439]) % PRIME == ev[node], 'majorant register T')
                continue
            expr = formula.replace('^', '**')
            expr = re.sub(r'w (\d)', r'w[\1]', expr)
            got = eval(expr, {'w': w, **env}) % PRIME
            need(got == ev[node], f'finalizer register {name} (node {node})')


# ---------------------------------------------------------------- Lean rendering
def node_def(d, i):
    nd = d['nodes'][i]
    k = nd['kind']
    if k == 'variable':
        body = f'.var {VARS.index(nd["name"])}'
    elif k == 'literal':
        body = f'.constant ({nd["value"]})'
    elif k == 'fixed':
        if nd['name'] == 'base_scale':
            body = '.constant baseScale'
        elif nd['name'] == 'threshold_scale':
            body = '.constant thresholdScale82'
        else:
            body = f'.constant ({int_poly(recipe(d, nd["name"]))})'
    else:
        op = {'add': '+', 'sub': '-', 'mul': '*'}[k]
        body = f'n{nd["left"]} p {op} n{nd["right"]} p'
    tag = f'  -- {nd["name"]}' if k in ('variable', 'fixed') else ''
    return f'def n{i} (p : Fin 4 → ℤ) : Expr (Fin 9) := {body}{tag}'


EV = 'Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul'


def render(d, cf):
    ns = d['nodes']
    regs = {node for node, _, _ in FINAL}
    defs = '\n'.join(node_def(d, i) for i in range(len(ns)))
    lem = []
    for i, nd in enumerate(ns):
        k = nd['kind']
        if k == 'variable':
            lem.append(f'theorem e{i} : (n{i} p).evalRing w = w {VARS.index(nd["name"])} := rfl')
        elif i == 11:
            lem.append('theorem e11 : (n11 p).evalRing w = (baseScale : R) := rfl')
        elif i == 381:
            lem.append('theorem e381 : (n381 p).evalRing w = (thresholdScale82 : R) := rfl')
        elif i == 12:
            lem.append('theorem e12 : (n12 p).evalRing w = w 0 * w 0 := rfl')
        elif i == BNODE:
            lem.append(f'theorem e{BNODE} : (n{BNODE} p).evalRing w = Bq (w 0) := rfl')
        elif cf[i] is not None and k in ('literal', 'fixed'):
            lem.append(f'theorem e{i} : (n{i} p).evalRing w = {cf_lean(cf[i])} := by\n  norm_num [n{i}]')
        elif cf[i] is not None:
            l, r = nd['left'], nd['right']
            ev = {'add': 'Expr.evalRing_add', 'sub': 'Expr.evalRing_sub', 'mul': 'Expr.evalRing_mul'}[k]
            rws = [f'e{l}'] + ([f'e{r}'] if r != l else [])
            lem.append(f'theorem e{i} : (n{i} p).evalRing w = {cf_lean(cf[i])} := by\n'
                       f'  rw [n{i}, {ev}, {", ".join(rws)}]; try ring')
        if i in PREFIX:
            rhs, unf = PREFIX[i]
            if i in KERNELS:
                dname, extra = KERNELS[i]
                lem.append(f'theorem s{i} : (n{i} p).evalRing w = {rhs} := by\n'
                           f'  rw [e{i}]\n'
                           f'  simp only [{dname}, Fin.sum_univ_succ, Fin.sum_univ_zero, {extra}, pc,\n'
                           f'    Matrix.cons_val_zero, Matrix.cons_val_succ]\n'
                           f'  ring')
            else:
                boundary = set(i2 for i2 in range(len(ns)) if cf[i2] is not None or ns[i2]['kind'] in
                               ('variable', 'literal', 'fixed') or i2 in (12, BNODE)) | (set(PREFIX) - {i})
                inner, edge = internal(ns, i, boundary)
                rw = [f's{x}' if x in PREFIX else f'e{x}' for x in edge]
                unfold = ', '.join(f'n{x}' for x in inner)
                tail = f'\n  unfold {unf.replace(",", "")}' if unf else ''
                lem.append(f'theorem s{i} : (n{i} p).evalRing w = {rhs} := by\n'
                           f'  simp only [{unfold}, {EV}, {", ".join(rw)}]{tail}\n'
                           f'  try ring')
    fbound = regs | FINAL_INPUTS
    for node, name, formula in FINAL:
        if node == T_NODE:
            boundary = T_ATOMS
            inner, edge = internal(ns, node, boundary)
            need(set(edge) == T_ATOMS, 'T cone edge')
            lem.append(f'/-- `{name}`: the block `N82Majorant.tBlock` -/\n'
                       f'theorem r{node} : (n{node} p).evalRing w = {subst_atoms(formula)} := by\n'
                       f'  simp only [{", ".join(f"n{x}" for x in inner)}, {EV}, Expr.evalRing_constant, e4, e426]\n'
                       f'  rfl')
            continue
        boundary = set(i2 for i2 in range(len(ns)) if ns[i2]['kind'] in ('variable', 'literal', 'fixed')
                       or cf[i2] is not None) | (fbound - {node})
        inner, edge = internal(ns, node, boundary)
        need(all(x > 378 or x in (3, 6, 7, 8, 9, 10) for x in inner), f'finalizer register {name} reaches the prefix')
        rw = [f'e{x}' for x in edge if x not in fbound]
        rw += EXTRA_RW.get(node, [])
        unfold = ', '.join(f'n{x}' for x in inner)
        lem.append(f'/-- `{name}` -/\ntheorem r{node} : (n{node} p).evalRing w = {subst_atoms(formula)} := by\n'
                   f'  simp only [{unfold}, {EV}' + (', ' + ', '.join(rw) if rw else '') + ']\n'
                   f'  try ring')
    boundary = set(i2 for i2 in range(len(ns)) if ns[i2]['kind'] in ('variable', 'literal', 'fixed')
                   or cf[i2] is not None) | regs | FINAL_INPUTS
    inner, edge = internal(ns, OUTN, boundary)
    rw = [f'e{x}' for x in edge if x not in regs and x not in FINAL_INPUTS]
    out_inner = ', '.join(f'n{x}' for x in inner)
    reg_args = ' '.join(f'(r{node} p w)' for node, _, _ in FINAL)
    out = f'''theorem output_norm : (n{OUTN} p).evalRing w = {subst_atoms(OUTPUT)} := by
  simp only [{out_inner}, {EV}''' + (', ' + ', '.join(rw) if rw else '') + f''']
  unfold N9Norm.norm2
  ring

/-- **The graph computes the finalizer at the prefix.** -/
theorem output_eval : (n{OUTN} p).evalRing w =
    N82Finalizer.value (Rq (pc p) (w 0) (w 1)) (Nq (w 0)) (w 0) (w 1) (tq (w 0)) (w 2) (w 3) (w 4)
      (w 5) (w 6) (w 7) (w 8) := by
  rw [← s378, ← s383, ← s408, output_norm, value_regs {reg_args}]'''
    return defs, '\n\n'.join(lem), out


HEADER = '''import DiophantineConsistency.WeightedExpressionDegree
import DiophantineConsistency.Nine121.N82Prefix
import DiophantineConsistency.Nine121.N82Finalizer

/-! # Package 82's 726-operation nine-positive equation, as a Lean literal

Generated by `research/nine-positive-p82-726-endpoint/tools/generate_n82p726_graph.py` from
`82-pell-congruences/nine_full_radical/laurent9_positive.json` (SHA-256 `{pin}`):
861 nodes (726 live operations), variables `b g h s w C i j n`, output node 860. Node `nᵢ` is the JSON
node `i`; the fixed leaves are `baseScale = 2^2134939`, `thresholdScale82 = 2^17079501` (kept
irreducible) and the eleven coefficient leaves as port polynomials in `p = (β, K, MC, MF)`.

The evaluation is proved gate by gate: closed forms in `Bq b` for the nodes that depend on the base
only (`eᵢ`), the prefix registers of `N82Prefix` (`sᵢ`), and the 26 finalizer registers over the
evaluations of other register nodes (`rᵢ`; `r844` is the majorant `N82Majorant.TR`, the cone of node
844). `output_eval` is the evaluation of the whole DAG: `N82Finalizer.value` at `R = Rq`, `N = Nq`,
`t = tq`. The correspondence with the JSON is checked by `tools/check_graph.py` (byte-identical
regeneration, gate-by-gate parse, mutation rejection). -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
set_option linter.unusedVariables false
noncomputable section
namespace Nine121.N82p726Graph
open DiophantineConsistency N82Layout N82Prefix
open N101Prefix (Bq baseScale)

'''


def full(d, cf):
    defs, lem, out = render(d, cf)
    hyps = ' '.join(['U', 'Y', 'M', 'P', 'K', 'Am', 'B1', 'W1', 'J', 'Qr', 'm', 'Ω', 'E0', 'V0', 'a0', 'D', 'E',
                     'F', 'Λ', 'G', 'Z', 'H1', 'I', 'S', 'a1', 'V1'])
    return (HEADER.replace('{pin}', PIN) + '/-! ## The literal DAG -/\n\n' + defs + '\n\n' +
            '''/-- The ports in a commutative ring. -/
def pc {R : Type*} [CommRing R] (p : Fin 4 → ℤ) : Fin 4 → R := fun j => (p j : R)

/-- `N82Finalizer.value` with its lets named. -/
theorem value_regs {A : Type*} [CommRing A] {R N b g t h s w C i j n ''' + hyps + ''' : A}
    (hU : U = N ^ 2 * w) (hY : Y = N ^ 2 * s) (hM : M = R * Y) (hP : P = 2 * M ^ 2 * U)
    (hK : K = R + 1 + h * (P - 1)) (hAm : Am = M * (U + 1)) (hB1 : B1 = 2 * R + 1)
    (hW1 : W1 = b * w) (hJ : J = 4 * Am - 5) (hQr : Qr = 3 * W1 * C - 2 * (W1 ^ 2 - 1))
    (hm : m = K ^ 2 * (4 * t - g) - 16 * t * (C - K * Y) ^ 2) (hΩ : Ω = J * m)
    (hE0 : E0 = J * (n + W1 ^ 2) + Qr) (hV0 : V0 = P * K) (ha0 : a0 = (P ^ 2 - 1) * K ^ 2 + 1)
    (hD : D = (Am ^ 2 - 1) * C ^ 2 + 1) (hE : E = i * J * C ^ 2 * D) (hF : F = (Am ^ 2 - 1) * E ^ 2 + 1)
    (hΛ : Λ = C * D + 1 - Am) (hG : G = Am + F * Λ) (hZ : Z = B1 + (j - 1) * C)
    (hH1 : H1 = C + F * Z) (hI : I = (G ^ 2 - 1) * H1 ^ 2 + 1) (hS : S = 262144 * C ^ 7)
    (ha1 : a1 = D * F * I * (S * S)) (hV1 : V1 = N82Majorant.TR Am C i Z) :
    N9Norm.norm2 (E0 - Ω * (V0 + V1)) Ω a0 a1 = N82Finalizer.value R N b g t h s w C i j n := by
  subst hV1 ha1 hS hI hH1 hZ hG hΛ hF hE hD ha0 hV0 hE0 hΩ hm hQr hJ hW1 hB1 hAm hK hP hM hY hU
  rfl

section Eval
variable {R : Type*} [CommRing R] (p : Fin 4 → ℤ) (w : Fin 9 → R)

''' + lem + '\n\n' + out + '\n\nend Eval\n\nend Nine121.N82p726Graph\n\n#print axioms Nine121.N82p726Graph.output_eval\n')


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--check', action='store_true')
    args = ap.parse_args()
    d = load()
    cf = analyse(d)
    layout = layout_data()
    numeric_checks(d, cf, layout)
    text = full(d, cf)
    if args.check:
        need(LEAN.read_text(encoding='utf-8') == text, 'generated file differs: ' + LEAN.name)
    else:
        LEAN.write_text(text, encoding='utf-8', newline='\n')
    print(json.dumps({'status': 'PASS' if args.check else 'GENERATED', 'nodes': len(d['nodes']),
                      'closed_forms': sum(c is not None for c in cf), 'pin': PIN}))


if __name__ == '__main__':
    main()
