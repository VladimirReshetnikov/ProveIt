#!/usr/bin/env python3
"""Emit Nine121/N101p1057Graph.lean: package 101's 1,057-operation boundary_complete DAG as a Lean literal.

Input (inert JSON, SHA-256 pinned below):
  101-constructive-reductions/nine/equations/boundary_complete.json (1,386 nodes, output 1385).
Nodes 0..434 are those of boundary_simple.json (prefix and the saturated registers); nodes
435..1367 evaluate the complete-radical majorant Pi(A, C, i, Z) in Horner form, 1369 is
sigma = 1024 C^5 i and 1371 is a1 = DFI * sigma^2.

The Lean literal has one definition per node: `n<i> (p : Fin 4 → ℤ) : Expr (Fin 9)` in the JSON order,
with variables `b g h s w C i j n`, literals as integer constants, the two scales as the irreducible
`N101Prefix.baseScale` / `N101Prefix.thresholdScale`, and the ten fixed coefficient leaves as their
port polynomials (from `coefficient_recipes`, ports `β K MC MF`).

Evaluation lemmas are gate-local, so no proof ever unfolds the DAG as a tree:
  * every node depending only on `B` (node 12), literals and coefficient leaves gets its exact
    closed form (a polynomial in `Bq (w 0)` and the ports), proved from its two children by `ring`;
  * the prefix registers (U*, G*, M0, T_c, S*, L, N, R + 1, R, t) are identified with the
    `N101Prefix` definitions, the kernels with `ker0/1/2`, `ℓ` with `ell`, `T*` with `Tst`;
  * the 26 finalizer registers are stated over the evaluations of other register nodes (atoms) and
    fed to `value_regs`, which is `N1057Finalizer.value` with its lets named; the majorant register
    `r1367` is `N1057Majorant.PiR` (the generic Horner block of `N1057Majorant.piBlock`), proved by
    unfolding the 933 block nodes (literals as integer constants) and `rfl`.

Before writing, every closed form and register formula is checked numerically against the JSON DAG
(exact integers modulo a 127-bit prime, at random points), and the output is checked against an
independent Python model of `N1057Finalizer.value` composed with the prefix.

Use --check to compare with the file on disk instead of writing it.
"""
from pathlib import Path
import argparse, hashlib, json, random, sys

HERE = Path(__file__).resolve()
DC = HERE.parents[3]
LEAN = DC / 'Lean/DiophantineConsistency/Nine121/N101p1057Graph.lean'
SRC = DC / 'con-zfc-diophantine-forms/101-constructive-reductions/nine/equations/boundary_complete.json'
PIN = '3f5f4f92feebd9bd1392af21e3faccf674f1d1e96ac2637cc22a22c73fcfc3bc'
OUTN = 1385
VARS = ['b', 'g', 'h', 's', 'w', 'C', 'i', 'j', 'n']
PRIME = (1 << 127) - 1


def need(ok, msg):
    if not ok:
        raise SystemExit('FAIL: ' + msg)


def load():
    raw = SRC.read_bytes()
    need(hashlib.sha256(raw).hexdigest() == PIN, 'boundary_complete.json pin')
    d = json.loads(raw)
    need(d['variables'] == VARS, 'variable order')
    need(d['output'] == len(d['nodes']) - 1 == OUTN, 'output node')
    need(d['base_scale_exponent'] == 2134939 and d['threshold_scale_exponent'] == 16012032, 'scales')
    need(d['total_operations'] == 1057, 'operation count')
    ops = sum(1 for n in d['nodes'] if n['kind'] in ('add', 'sub', 'mul'))
    need(ops == 1057, 'counted operations')
    return d


# ---------------------------------------------------------------- port polynomials
def recipe(d, name):
    """Port polynomial {(e0,e1,e2,e3): c} of a fixed coefficient leaf."""
    out = {}
    for t in d['coefficient_recipes'][name]:
        m = tuple(t['powers'])
        need(len(m) == 4 and m not in out, 'recipe ' + name)
        out[m] = t['coefficient']
    return out


def port_mono(m):
    parts = []
    for j, e in enumerate(m):
        if e:
            parts.append(f'(p {j} : R)' + (f' ^ {e}' if e > 1 else ''))
    return parts


def int_poly(poly):
    """The integer port polynomial as a Lean ℤ term in `p`."""
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


# ---------------------------------------------------------------- closed forms in B and ports
# a closed form is {(eB, (e0,e1,e2,e3)): c}
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


def analyse(d):
    ns = d['nodes']
    n = len(ns)
    cf = [None] * n          # closed forms of regime-A nodes
    for i, nd in enumerate(ns):
        k = nd['kind']
        if k == 'literal':
            cf[i] = {(0, (0, 0, 0, 0)): nd['value']} if nd['value'] else {}
        elif k == 'fixed' and nd['name'].startswith('c'):
            cf[i] = {(0, m): c for m, c in recipe(d, nd['name']).items()}
        elif i == 12:
            need(nd == {'kind': 'mul', 'left': 9, 'right': 11}, 'node 12 is B')
            need(ns[11] == {'kind': 'mul', 'left': 0, 'right': 0}, 'node 11 is b*b')
            need(ns[9] == {'kind': 'fixed', 'name': 'base_scale'}, 'node 9 is base_scale')
            cf[i] = {(1, (0, 0, 0, 0)): 1}
        elif (k in ('add', 'sub', 'mul') and cf[nd['left']] is not None and cf[nd['right']] is not None
              and nd['left'] not in PREFIX and nd['right'] not in PREFIX):
            l, r = cf[nd['left']], cf[nd['right']]
            cf[i] = cf_add(l, r) if k == 'add' else cf_add(l, r, -1) if k == 'sub' else cf_mul(l, r)
    return cf


# ---------------------------------------------------------------- registers
NN = dict(d=None)
# prefix registers: node -> (Lean RHS, definitions to unfold before ring)
PREFIX = {
    76: ('ker0 (pc p) (w 0)', None),
    168: ('ker1 (pc p) (w 0)', None),
    256: ('ker2 (pc p) (w 0)', None),
    291: ('ell (w 0)', None),
    334: ('Tst (w 0)', None),
    335: ('Ust (w 0) (w 1)', 'Ust'),
    339: ('Gs (pc p) (w 0) (w 1)', 'Gs'),
    343: ('maskq (w 0)', 'maskq, N0'),
    347: ('Tcq (w 0)', 'Tcq, N0'),
    351: ('Scq (pc p) (w 0) (w 1)', 'Scq, N0'),
    354: ('Lq (w 0)', 'Lq'),
    356: ('Nq (w 0)', 'Nq'),
    360: ('Rq (pc p) (w 0) (w 1) + 1', 'Rq'),
    361: ('Rq (pc p) (w 0) (w 1)', None),
    362: ('tq (w 0)', 'tq'),
}
# finalizer registers: node -> (name, formula over register atoms E<i> and variables)
FINAL = [
    (364, 'U', 'E356 ^ 2 * w 4'),
    (365, 'Y', 'E356 ^ 2 * w 3'),
    (366, 'M', 'E361 * E365'),
    (369, 'P', '2 * E366 ^ 2 * E364'),
    (372, 'K', 'E361 + 1 + w 2 * (E369 - 1)'),
    (373, 'Am', 'E366 * (E364 + 1)'),
    (375, 'B1', '2 * E361 + 1'),
    (376, 'W1', 'w 0 * w 4'),
    (380, 'J', '4 * E373 - 5'),
    (386, 'Qr', '3 * E376 * w 5 - 2 * (E376 ^ 2 - 1)'),
    (401, 'm', 'E372 ^ 2 * (4 * E362 - w 1) - 16 * E362 * (w 5 - E372 * E365) ^ 2'),
    (402, 'Om', 'E380 * E401'),
    (406, 'E0', 'E380 * (w 8 + E376 ^ 2) + E386'),
    (387, 'V0', 'E369 * E372'),
    (391, 'a0', '(E369 ^ 2 - 1) * E372 ^ 2 + 1'),
    (411, 'D', '(E373 ^ 2 - 1) * w 5 ^ 2 + 1'),
    (418, 'F', '(E373 ^ 2 - 1) * E411 * (w 6 * E380 * w 5 ^ 2) ^ 2 + 1'),
    (420, 'Lam', 'w 5 * E411 + 1 - E373'),
    (422, 'G', 'E373 + E418 * E420'),
    (425, 'Z', 'E375 + (w 7 - 1) * w 5'),
    (427, 'H1', 'w 5 + E418 * E425'),
    (432, 'I', '(E422 ^ 2 - 1) * E427 ^ 2 + 1'),
    (434, 'R1', 'E411 * E418 * E432'),
    (1367, 'V1', 'N1057Majorant.PiR E373 (w 5) (w 6) E425'),
    (1369, 'sg', '1024 * w 5 ^ 5 * w 6'),
    (1371, 'a1', 'E434 * (E1369 * E1369)'),
]
OUTPUT = 'N9Norm.norm2 (E406 - E402 * (E387 + E1367)) E402 E391 E1371'
PI_NODE, PI_LO = 1367, 435
FINAL_INPUTS = {356, 361, 362}


def atom(i):
    return f'((n{i} p).evalRing w)'


# finalizer registers whose graph cone uses another register's value as a product: the defining
# lemma of that register is rewritten in (a₀ squares V₀ = PK)
EXTRA_RW = {391: ['r387']}


def subst_atoms(text):
    import re
    return re.sub(r'E(\d+)', lambda m: atom(int(m.group(1))), text)


def internal(ns, root, boundary):
    """Nodes strictly inside the cone of `root` above `boundary` (root included)."""
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


# ---------------------------------------------------------------- numeric model
def mod_eval(d, vals, ports):
    """Evaluate every node modulo PRIME."""
    ns = d['nodes']
    base = pow(2, 2134939, PRIME)
    thr = pow(2, 16012032, PRIME)
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


def model(d, vals, ports, layout):
    """Independent model: N101Prefix definitions and N9Finalizer.value, modulo PRIME."""
    P = PRIME
    b, g, h, s, w, C, i, j, n = (v % P for v in vals)
    B = pow(2, 2134939, P) * b * b % P
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
    N0 = pow(B, 116, P)
    mask = (N0 - 1 - ell * (b - 1)) % P
    Tc = (mask + N0 * (Tst * (B - 2))) % P
    Sc = (g + N0 * (Tst + 2 * G)) % P
    L = 2 * b * pow(B, 1983, P) % P
    R = (L * (1 + (Tc + Sc)) - Sc - 1) % P
    N = pow(2, 16012032, P) * pow(B, 1053, P) % P
    t = b * pow(B, 115, P) % P
    Uf = N * N * w; Y = N * N * s; M = R * Y; Pp = 2 * M * M * Uf
    K = R + 1 + h * (Pp - 1); Am = M * (Uf + 1); B1 = 2 * R + 1; W1 = b * w
    J = 4 * Am - 5; Qr = 3 * W1 * C - 2 * (W1 * W1 - 1)
    m = K * K * (4 * t - g) - 16 * t * (C - K * Y) ** 2
    Om = J * m; E0 = J * (n + W1 * W1) + Qr; V0 = Pp * K; a0 = (Pp * Pp - 1) * K * K + 1
    D = (Am * Am - 1) * C * C + 1; r0 = i * J * C * C; F = (Am * Am - 1) * D * r0 * r0 + 1
    Lam = C * D + 1 - Am; Gf = Am + F * Lam; Z = B1 + (j - 1) * C; H1 = C + F * Z
    I = (Gf * Gf - 1) * H1 * H1 + 1
    sg = 1024 * C ** 5 * i
    a1 = D * F * I * (sg * sg); V1 = pi_mod(d, Am, C, i, Z)
    th = E0 - Om * (V0 + V1)
    val = (th * th - Om * Om * (a0 + a1)) ** 2 - 4 * Om ** 4 * a0 * a1
    regs = dict(ker0=ker[0], ker1=ker[1], ker2=ker[2], ell=ell, Tst=Tst, U=U, G=G, mask=mask, Tc=Tc,
                Sc=Sc, L=L, N=N, R=R, t=t, value=val)
    return {k: v % P for k, v in regs.items()}


def pi_mod(d, a, c, i, z):
    """An independent evaluation of Pi: the 333-term saturated_corrected_P.json, modulo PRIME."""
    P = json.loads((SRC.parents[1] / 'data/saturated_corrected_P.json').read_bytes())
    need(P['symbols'] == ['A', 'C', 'i', 'Z'] and len(P['terms']) == 333, 'saturated_corrected_P.json')
    s = 0
    for t in P['terms']:
        e = t['powers']
        s += t['coefficient'] * pow(a, e[0], PRIME) * pow(c, e[1], PRIME) * pow(i, e[2], PRIME) * pow(z, e[3], PRIME)
    return s % PRIME


def layout_data():
    spec = __import__('importlib.util').util.spec_from_file_location(
        'gen', HERE.parents[2] / 'nine-positive-p101-420-endpoint/tools/generate_n101_layout.py')
    gen = __import__('importlib.util').util.module_from_spec(spec)
    spec.loader.exec_module(gen)
    dd = gen.analyse()
    return dd['w'], dd['E'], dd['pos'], dd['coef']


def numeric_checks(d, cf, layout):
    rng = random.Random(20261108)
    ns = d['nodes']
    for trial in range(4):
        vals = [rng.randrange(1, PRIME) for _ in VARS]
        ports = [rng.randrange(1, PRIME) for _ in range(4)]
        ev = mod_eval(d, vals, ports)
        B = pow(2, 2134939, PRIME) * vals[0] * vals[0] % PRIME
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
        mdl = model(d, vals, ports, layout)
        for node, key in [(76, 'ker0'), (168, 'ker1'), (256, 'ker2'), (291, 'ell'), (334, 'Tst'),
                          (335, 'U'), (339, 'G'), (343, 'mask'), (347, 'Tc'), (351, 'Sc'), (354, 'L'),
                          (356, 'N'), (361, 'R'), (362, 't')]:
            need(ev[node] == mdl[key], f'prefix register {key} (node {node})')
        need((ev[360] - ev[361] - 1) % PRIME == 0, 'R + 1 register')
        need(ev[OUTN] == mdl['value'], 'output = value(prefix)')
        # finalizer register formulas over the register atoms
        env = {f'E{k}': ev[k] for k in range(len(ns))}
        w = vals
        for node, name, formula in FINAL:
            if node == PI_NODE:
                need(pi_mod(d, ev[373], w[5], w[6], ev[425]) == ev[node], 'majorant register Pi (node 1367)')
                continue
            expr = formula.replace('^', '**')
            import re
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
            body = '.constant thresholdScale'
        else:
            body = f'.constant ({int_poly(recipe(d, nd["name"]))})'
    else:
        op = {'add': '+', 'sub': '-', 'mul': '*'}[k]
        body = f'n{nd["left"]} p {op} n{nd["right"]} p'
    tag = f'  -- {nd["name"]}' if k in ('variable', 'fixed') else ''
    return f'def n{i} (p : Fin 4 → ℤ) : Expr (Fin 9) := {body}{tag}'


EV = 'Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul'


def lemma_name(i, cf):
    if i in PREFIX:
        return f's{i}'
    if cf[i] is not None or i == 12:
        return f'e{i}'
    return None


def render(d, cf):
    ns = d['nodes']
    regs = {node for node, _, _ in FINAL}
    defs = '\n'.join(node_def(d, i) for i in range(len(ns)))
    lem = []
    # leaves and regime-A nodes
    for i, nd in enumerate(ns):
        k = nd['kind']
        if k == 'variable':
            lem.append(f'theorem e{i} : (n{i} p).evalRing w = w {VARS.index(nd["name"])} := rfl')
        elif i == 9:
            lem.append(f'theorem e9 : (n9 p).evalRing w = (baseScale : R) := rfl')
        elif i == 355:
            lem.append(f'theorem e355 : (n355 p).evalRing w = (thresholdScale : R) := rfl')
        elif i == 11:
            lem.append(f'theorem e11 : (n11 p).evalRing w = w 0 * w 0 := rfl')
        elif i == 12:
            lem.append(f'theorem e12 : (n12 p).evalRing w = Bq (w 0) := rfl')
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
            if i in (76, 168, 256, 291, 334):
                dname = {76: 'ker0', 168: 'ker1', 256: 'ker2', 291: 'ell', 334: 'Tst'}[i]
                extra = {76: 'c0, pos0', 168: 'c1, pos1', 256: 'c2, pos2', 291: 'weights', 334: 'targets'}[i]
                lem.append(f'theorem s{i} : (n{i} p).evalRing w = {rhs} := by\n'
                           f'  rw [e{i}]\n'
                           f'  simp only [{dname}, Fin.sum_univ_succ, Fin.sum_univ_zero, {extra}, pc,\n'
                           f'    Matrix.cons_val_zero, Matrix.cons_val_succ]\n'
                           f'  ring')
            else:
                boundary = set(i2 for i2 in range(len(ns)) if cf[i2] is not None or ns[i2]['kind'] in
                               ('variable', 'literal', 'fixed') or i2 in (11, 12)) | (set(PREFIX) - {i})
                inner, edge = internal(ns, i, boundary)
                rw = []
                for x in edge:
                    rw.append(f's{x}' if x in PREFIX else f'e{x}')
                unfold = ', '.join(f'n{x}' for x in inner)
                tail = f'\n  unfold {unf.replace(",", "")}' if unf else ''
                lem.append(f'theorem s{i} : (n{i} p).evalRing w = {rhs} := by\n'
                           f'  simp only [{unfold}, {EV}, {", ".join(rw)}]{tail}\n'
                           f'  try ring')
    lem.append('theorem e360_361 : (n360 p).evalRing w = (n361 p).evalRing w + 1 := by\n'
               '  rw [s360, s361]')
    # finalizer registers
    fbound = regs | FINAL_INPUTS | {360}
    for node, name, formula in FINAL:
        if node == PI_NODE:
            inner = [409] + list(range(PI_LO, PI_NODE + 1))
            lem.append(f'/-- `{name}`: the Horner block of `N1057Majorant.piBlock` -/\n'
                       f'theorem r{node} : (n{node} p).evalRing w = {subst_atoms(formula)} := by\n'
                       f'  simp only [{", ".join(f"n{x}" for x in inner)}, {EV}, Expr.evalRing_constant, e5, e6]\n'
                       f'  rfl')
            continue
        boundary = set(i2 for i2 in range(len(ns)) if ns[i2]['kind'] in ('variable', 'literal', 'fixed')
                       or cf[i2] is not None) | (fbound - {node})
        inner, edge = internal(ns, node, boundary)
        need(all(x >= 363 for x in inner), f'finalizer register {name} reaches the prefix')
        need(all(x <= 434 or x >= PI_LO for x in inner), f'finalizer register {name}')
        rw = [f'e{x}' for x in edge if x not in fbound]
        if 360 in edge:
            rw.append('e360_361')
        rw += EXTRA_RW.get(node, [])
        unfold = ', '.join(f'n{x}' for x in inner)
        lem.append(f'/-- `{name}` -/\ntheorem r{node} : (n{node} p).evalRing w = {subst_atoms(formula)} := by\n'
                   f'  simp only [{unfold}, {EV}' + (', ' + ', '.join(rw) if rw else '') + ']\n'
                   f'  try ring')
    # output
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
    N1057Finalizer.value (Rq (pc p) (w 0) (w 1)) (Nq (w 0)) (w 0) (w 1) (tq (w 0)) (w 2) (w 3) (w 4)
      (w 5) (w 6) (w 7) (w 8) := by
  rw [← s361, ← s356, ← s362, output_norm, value_regs {reg_args}]'''
    return defs, '\n\n'.join(lem), out


HEADER = '''import DiophantineConsistency.WeightedExpressionDegree
import DiophantineConsistency.Nine121.N101Prefix
import DiophantineConsistency.Nine121.N1057Finalizer

/-! # Package 101's 1,057-operation nine-positive equation, as a Lean literal

Generated by `research/nine-positive-p101-1057-endpoint/tools/generate_n101p1057_graph.py` from
`101-constructive-reductions/nine/equations/boundary_complete.json` (SHA-256 `{pin}`):
1,386 nodes (1,057 live operations), variables `b g h s w C i j n`, output node 1385. Node `nᵢ` is the
JSON node `i`; the fixed leaves are `baseScale = 2^2134939`, `thresholdScale = 2^16012032` (kept
irreducible) and the ten coefficient leaves `c000`–`c009` as port polynomials in `p = (β, K, MC, MF)`.

The evaluation is proved gate by gate: closed forms in `Bq b` for the nodes that depend on the base
only (`eᵢ`), the prefix registers of `N101Prefix` (`sᵢ`), and the 26 finalizer registers over the
evaluations of other register nodes (`rᵢ`; `r1367` is the majorant `N1057Majorant.PiR`, the Horner
block of nodes 435–1367). `output_eval` is the evaluation of the whole DAG:
`N1057Finalizer.value` at `R = Rq`, `N = Nq`, `t = tq`. The correspondence with the JSON is checked by
`tools/check_graph.py` (byte-identical regeneration, gate-by-gate parse, mutation rejection). -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
set_option linter.unusedVariables false
noncomputable section
namespace Nine121.N101p1057Graph
open DiophantineConsistency N101Layout N101Prefix

'''


def full(d, cf):
    defs, lem, out = render(d, cf)
    pin = PIN
    return (HEADER.replace('{pin}', pin) + '/-! ## The literal DAG -/\n\n' + defs + '\n\n' +
            '''/-- The ports in a commutative ring. -/
def pc {R : Type*} [CommRing R] (p : Fin 4 → ℤ) : Fin 4 → R := fun j => (p j : R)

/-- `N1057Finalizer.value` with its lets named. -/
theorem value_regs {A : Type*} [CommRing A] {R N b g t h s w C i j n U Y M P K Am B1 W1 J Qr m Ω E0
    V0 a0 D F Λ G Z H1 I R1 V1 σ a1 : A}
    (hU : U = N ^ 2 * w) (hY : Y = N ^ 2 * s) (hM : M = R * Y) (hP : P = 2 * M ^ 2 * U)
    (hK : K = R + 1 + h * (P - 1)) (hAm : Am = M * (U + 1)) (hB1 : B1 = 2 * R + 1)
    (hW1 : W1 = b * w) (hJ : J = 4 * Am - 5) (hQr : Qr = 3 * W1 * C - 2 * (W1 ^ 2 - 1))
    (hm : m = K ^ 2 * (4 * t - g) - 16 * t * (C - K * Y) ^ 2) (hΩ : Ω = J * m)
    (hE0 : E0 = J * (n + W1 ^ 2) + Qr) (hV0 : V0 = P * K) (ha0 : a0 = (P ^ 2 - 1) * K ^ 2 + 1)
    (hD : D = (Am ^ 2 - 1) * C ^ 2 + 1) (hF : F = (Am ^ 2 - 1) * D * (i * J * C ^ 2) ^ 2 + 1)
    (hΛ : Λ = C * D + 1 - Am) (hG : G = Am + F * Λ) (hZ : Z = B1 + (j - 1) * C)
    (hH1 : H1 = C + F * Z) (hI : I = (G ^ 2 - 1) * H1 ^ 2 + 1) (hR1 : R1 = D * F * I)
    (hV1 : V1 = N1057Majorant.PiR Am C i Z) (hσ : σ = 1024 * C ^ 5 * i) (ha1 : a1 = R1 * (σ * σ)) :
    N9Norm.norm2 (E0 - Ω * (V0 + V1)) Ω a0 a1 = N1057Finalizer.value R N b g t h s w C i j n := by
  subst ha1 hσ hV1 hR1 hI hH1 hZ hG hΛ hF hD ha0 hV0 hE0 hΩ hm hQr hJ hW1 hB1 hAm hK hP hM hY hU
  rfl

section Eval
variable {R : Type*} [CommRing R] (p : Fin 4 → ℤ) (w : Fin 9 → R)

''' + lem + '\n\n' + out + '\n\nend Eval\n\nend Nine121.N101p1057Graph\n\n#print axioms Nine121.N101p1057Graph.output_eval\n')


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
