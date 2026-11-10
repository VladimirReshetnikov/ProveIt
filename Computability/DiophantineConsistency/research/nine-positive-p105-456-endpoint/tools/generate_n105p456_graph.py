#!/usr/bin/env python3
"""Emit Nine121/N105p456Graph.lean: package 105's 456-operation h1868 DAG as a Lean literal.

Input (inert JSON, SHA-256 pinned below):
  105-bootstrap-certificates/nine/equations/h1868.json (488 nodes, output 487).

The Lean literal has one definition per node: `n<i> (p : Fin 4 → ℤ) : Expr (Fin 9)` in the JSON order,
with variables `b g h s w c i j n`, literals as integer constants, the two scales as the irreducible
`N101Prefix.baseScale` / `N101Prefix.thresholdScale`, and the ten fixed coefficient leaves as their
port polynomials (from `coefficient_recipes`, ports `β K MC MF`).

Evaluation lemmas are gate-local, so no proof ever unfolds the DAG as a tree:
  * every node depending only on `B` (node 3), literals and coefficient leaves gets its exact
    closed form (a polynomial in `Bq (w 0)` and the ports), proved from its two children by `ring`;
  * the prefix registers (U*, G*, M0, T_c, S*, L, N, R + 1, R, t) are identified with the
    `N105Prefix` definitions, the kernels with `ker0/1/2`, `ℓ` with `ell`, `T*` with `Tst`;
  * the 25 finalizer registers (including the successor `C = c + 1`) are stated over the
    evaluations of other register nodes (atoms) and fed to `value_regs`, which is
    `N105Finalizer.value` with its lets named.

Before writing, every closed form and register formula is checked numerically against the JSON DAG
(exact integers modulo a 127-bit prime, at random points), and the output is checked against an
independent Python model of `N105Finalizer.value` composed with the prefix.

Use --check to compare with the file on disk instead of writing it.
"""
from pathlib import Path
import argparse, hashlib, importlib.util, json, random, re

HERE = Path(__file__).resolve()
DC = HERE.parents[3]
LEAN = DC / 'Lean/DiophantineConsistency/Nine121/N105p456Graph.lean'
SRC = DC / 'con-zfc-diophantine-forms/105-bootstrap-certificates/nine/equations/h1868.json'
PIN = '9c3d4b0b6e9a31d148f07a1bd453ea5cd5b5e1a8f0ebfd1b39bdc4fa17b96d6b'
VARS = ['b', 'g', 'h', 's', 'w', 'c', 'i', 'j', 'n']
PRIME = (1 << 127) - 1
BASENODE, BBNODE, BNODE, THRNODE, OUTNODE = 0, 2, 3, 383, 487
RPLUS1, RNODE = 380, 381


def need(ok, msg):
    if not ok:
        raise SystemExit('FAIL: ' + msg)


def load(path=SRC, pin=PIN):
    raw = path.read_bytes()
    need(hashlib.sha256(raw).hexdigest() == pin, 'h1868.json pin')
    d = json.loads(raw)
    need(d['variables'] == VARS, 'variable order')
    need(d['output'] == len(d['nodes']) - 1 == OUTNODE, 'output node')
    need(d['source_parameters']['base_exp'] == 2134939 and d['source_parameters']['threshold_exp'] == 16012032,
         'scales')
    need(d['total_operations'] == 456, 'operation count')
    ops = sum(1 for n in d['nodes'] if n['kind'] in ('add', 'sub', 'mul'))
    need(ops == 456, 'counted operations')
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


# ---------------------------------------------------------------- registers
# prefix registers: node -> (Lean RHS, definitions to unfold before ring)
PREFIX = {
    197: ('ker0 (pc p) (w 0)', None),
    285: ('ker1 (pc p) (w 0)', None),
    368: ('ker2 (pc p) (w 0)', None),
    114: ('ell (w 0)', None),
    174: ('Tst (w 0)', None),
    198: ('Ust (w 0) (w 1)', 'Ust'),
    372: ('Gs (pc p) (w 0) (w 1)', 'Gs'),
    117: ('maskq (w 0)', 'maskq, N0'),
    178: ('Tcq (w 0)', 'Tcq, N0'),
    376: ('Scq (pc p) (w 0) (w 1)', 'Scq, N0'),
    51: ('Lq (w 0)', 'Lq'),
    384: ('Nq (w 0)', 'Nq'),
    380: ('Rq (pc p) (w 0) (w 1) + 1', 'Rq'),
    381: ('Rq (pc p) (w 0) (w 1)', None),
    411: ('tq (w 0)', 'tq'),
}
# closed-form prefix registers: node -> (definition, tables to unfold)
TABLES = {
    197: ('ker0', 'N101Layout.c0, N105Layout.pos0'),
    285: ('ker1', 'N101Layout.c1, N105Layout.pos1'),
    368: ('ker2', 'N101Layout.c2, N105Layout.pos2'),
    114: ('ell', 'N105Layout.weights'),
    174: ('Tst', 'N105Layout.targets'),
}
# finalizer registers: node -> (name, formula over register atoms E<i> and variables)
FINAL = [
    (395, 'C', 'w 5 + 1'),
    (389, 'U', 'E384 ^ 2 * w 4'),
    (386, 'Y', 'E384 ^ 2 * w 3'),
    (387, 'M', 'E381 * E386'),
    (401, 'P', '2 * E387 ^ 2 * E389'),
    (405, 'K', 'E381 + 1 + w 2 * (E401 - 1)'),
    (391, 'Am', 'E387 * (E389 + 1)'),
    (393, 'B1', '2 * E381 + 1'),
    (423, 'W1', 'w 0 * w 4'),
    (399, 'J', '4 * E391 - 5'),
    (429, 'Qr', '3 * E423 * E395 - 2 * (E423 ^ 2 - 1)'),
    (421, 'm', 'E405 ^ 2 * (4 * E411 - w 1) - 16 * E411 * (E395 - E405 * E386) ^ 2'),
    (422, 'Om', 'E399 * E421'),
    (434, 'E0', 'E399 * (w 8 + E423 ^ 2) + E429'),
    (406, 'V0', 'E401 * E405'),
    (410, 'a0', '(E401 ^ 2 - 1) * E405 ^ 2 + 1'),
    (441, 'D', '(E391 ^ 2 - 1) * E395 ^ 2 + 1'),
    (447, 'F', '(E391 ^ 2 - 1) * E441 * (w 6 * E399 * E395 ^ 2) ^ 2 + 1'),
    (450, 'Lam', 'E395 * E441 + 1 - E391'),
    (452, 'G', 'E391 + E447 * E450'),
    (455, 'Z', 'E393 + (w 7 - 1) * E395'),
    (457, 'H1', 'E395 + E447 * E455'),
    (462, 'I', '(E452 ^ 2 - 1) * E457 ^ 2 + 1'),
    (465, 'a1', '4 * (E441 * E447 * E462)'),
    (474, 'V1', 'w 6 * E395 ^ 2 * (E391 * E399 * (2 * E441 - E395 ^ 2) + (3 * E395 ^ 2 - 4)) * E452 * E457'),
]
# the arguments of `value_regs`, in its hypothesis order (the successor register C is not one)
REG_ORDER = ['U', 'Y', 'M', 'P', 'K', 'Am', 'B1', 'W1', 'J', 'Qr', 'm', 'Om', 'E0', 'V0', 'a0', 'D', 'F',
             'Lam', 'G', 'Z', 'H1', 'I', 'a1', 'V1']
OUTPUT = 'N9Norm.norm2 (E434 - E422 * (E406 + E474)) E422 E410 E465'
FINAL_INPUTS = {384, 381, 411}
# finalizer registers whose graph cone uses another register's value as a product: the defining
# lemma of that register is rewritten in (a₀ squares V₀ = PK)
EXTRA_RW = {410: ['r406']}


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
        elif i == BNODE:
            need(nd == {'kind': 'mul', 'left': BASENODE, 'right': BBNODE}, 'node 3 is B')
            need(ns[BBNODE] == {'kind': 'mul', 'left': 1, 'right': 1}, 'node 2 is b*b')
            need(ns[1] == {'kind': 'variable', 'name': 'b'}, 'node 1 is b')
            need(ns[BASENODE] == {'kind': 'fixed', 'name': 'base_scale'}, 'node 0 is base_scale')
            cf[i] = {(1, (0, 0, 0, 0)): 1}
        elif (k in ('add', 'sub', 'mul') and cf[nd['left']] is not None and cf[nd['right']] is not None
              and nd['left'] not in PREFIX and nd['right'] not in PREFIX):
            l, r = cf[nd['left']], cf[nd['right']]
            cf[i] = cf_add(l, r) if k == 'add' else cf_add(l, r, -1) if k == 'sub' else cf_mul(l, r)
    need(ns[THRNODE] == {'kind': 'fixed', 'name': 'threshold_scale'}, 'node 383 is threshold_scale')
    for node in TABLES:
        need(cf[node] is not None, f'prefix table register {node} is a closed form')
    return cf


def atom(i):
    return f'((n{i} p).evalRing w)'


def subst_atoms(text):
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


def model(vals, ports, layout):
    """Independent model: N105Prefix definitions and N105Finalizer.value at C = c + 1, modulo PRIME."""
    P = PRIME
    b, g, h, s, w, c, i, j, n = (v % P for v in vals)
    C = c + 1
    B = pow(2, 2134939, P) * b * b % P
    W, E, pos, coef = layout

    def cval(poly):
        t = 0
        for m, cc in poly.items():
            u = cc
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
    L = 2 * b * pow(B, 1986, P) % P
    R = (L * (1 + (Tc + Sc)) - Sc - 1) % P
    N = pow(2, 16012032, P) * pow(B, 1055, P) % P
    t = b * pow(B, 116, P) % P
    Uf = N * N * w; Y = N * N * s; M = R * Y; Pp = 2 * M * M * Uf
    K = R + 1 + h * (Pp - 1); Am = M * (Uf + 1); B1 = 2 * R + 1; W1 = b * w
    J = 4 * Am - 5; Qr = 3 * W1 * C - 2 * (W1 * W1 - 1)
    m = K * K * (4 * t - g) - 16 * t * (C - K * Y) ** 2
    Om = J * m; E0 = J * (n + W1 * W1) + Qr; V0 = Pp * K; a0 = (Pp * Pp - 1) * K * K + 1
    D = (Am * Am - 1) * C * C + 1; r0 = i * J * C * C; F = (Am * Am - 1) * D * r0 * r0 + 1
    Lam = C * D + 1 - Am; Gf = Am + F * Lam; Z = B1 + (j - 1) * C; H1 = C + F * Z
    I = (Gf * Gf - 1) * H1 * H1 + 1; a1 = 4 * (D * F * I)
    T = i * C * C * (Am * J * (2 * D - C * C) + (3 * C * C - 4)); V1 = T * Gf * H1
    th = E0 - Om * (V0 + V1)
    val = (th * th - Om * Om * (a0 + a1)) ** 2 - 4 * Om ** 4 * a0 * a1
    regs = dict(ker0=ker[0], ker1=ker[1], ker2=ker[2], ell=ell, Tst=Tst, U=U, G=G, mask=mask, Tc=Tc,
                Sc=Sc, L=L, N=N, R=R, t=t, value=val)
    return {k: v % P for k, v in regs.items()}


def layout_data():
    spec = importlib.util.spec_from_file_location('gen105', HERE.parent / 'generate_n105_layout.py')
    gen = importlib.util.module_from_spec(spec)
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
        mdl = model(vals, ports, layout)
        for node, key in [(197, 'ker0'), (285, 'ker1'), (368, 'ker2'), (114, 'ell'), (174, 'Tst'),
                          (198, 'U'), (372, 'G'), (117, 'mask'), (178, 'Tc'), (376, 'Sc'), (51, 'L'),
                          (384, 'N'), (381, 'R'), (411, 't')]:
            need(ev[node] == mdl[key], f'prefix register {key} (node {node})')
        need((ev[RPLUS1] - ev[RNODE] - 1) % PRIME == 0, 'R + 1 register')
        need(ev[OUTNODE] == mdl['value'], 'output = value(prefix)')
        # finalizer register formulas over the register atoms
        env = {f'E{k}': ev[k] for k in range(len(ns))}
        for node, name, formula in FINAL:
            expr = re.sub(r'w (\d)', r'w[\1]', formula.replace('^', '**'))
            got = eval(expr, {'w': vals, **env}) % PRIME
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
        elif i == BASENODE:
            lem.append(f'theorem e{i} : (n{i} p).evalRing w = (baseScale : R) := rfl')
        elif i == THRNODE:
            lem.append(f'theorem e{i} : (n{i} p).evalRing w = (thresholdScale : R) := rfl')
        elif i == BBNODE:
            lem.append(f'theorem e{i} : (n{i} p).evalRing w = w 0 * w 0 := rfl')
        elif i == BNODE:
            lem.append(f'theorem e{i} : (n{i} p).evalRing w = Bq (w 0) := rfl')
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
            if i in TABLES:
                dname, extra = TABLES[i]
                lem.append(f'theorem s{i} : (n{i} p).evalRing w = {rhs} := by\n'
                           f'  rw [e{i}]\n'
                           f'  simp only [{dname}, Fin.sum_univ_succ, Fin.sum_univ_zero, {extra}, pc,\n'
                           f'    Matrix.cons_val_zero, Matrix.cons_val_succ]\n'
                           f'  ring')
            else:
                boundary = set(i2 for i2 in range(len(ns)) if cf[i2] is not None or ns[i2]['kind'] in
                               ('variable', 'literal', 'fixed') or i2 in (BBNODE, BNODE)) | (set(PREFIX) - {i})
                inner, edge = internal(ns, i, boundary)
                rw = []
                for x in edge:
                    rw.append(f's{x}' if x in PREFIX else f'e{x}')
                unfold = ', '.join(f'n{x}' for x in inner)
                tail = f'\n  unfold {unf.replace(",", "")}' if unf else ''
                lem.append(f'theorem s{i} : (n{i} p).evalRing w = {rhs} := by\n'
                           f'  simp only [{unfold}, {EV}, {", ".join(rw)}]{tail}\n'
                           f'  try ring')
    lem.append(f'theorem e{RPLUS1}_{RNODE} : (n{RPLUS1} p).evalRing w = (n{RNODE} p).evalRing w + 1 := by\n'
               f'  rw [s{RPLUS1}, s{RNODE}]')
    # finalizer registers
    fbound = regs | FINAL_INPUTS | {RPLUS1}
    for node, name, formula in FINAL:
        boundary = set(i2 for i2 in range(len(ns)) if ns[i2]['kind'] in ('variable', 'literal', 'fixed')
                       or cf[i2] is not None) | (fbound - {node})
        inner, edge = internal(ns, node, boundary)
        need(all(x > RNODE for x in inner), f'finalizer register {name} reaches the prefix')
        rw = [f'e{x}' for x in edge if x not in fbound]
        if RPLUS1 in edge:
            rw.append(f'e{RPLUS1}_{RNODE}')
        rw += EXTRA_RW.get(node, [])
        unfold = ', '.join(f'n{x}' for x in inner)
        lem.append(f'/-- `{name}` -/\ntheorem r{node} : (n{node} p).evalRing w = {subst_atoms(formula)} := by\n'
                   f'  simp only [{unfold}, {EV}' + (', ' + ', '.join(rw) if rw else '') + ']\n'
                   f'  try ring')
    # output
    boundary = set(i2 for i2 in range(len(ns)) if ns[i2]['kind'] in ('variable', 'literal', 'fixed')
                   or cf[i2] is not None) | regs | FINAL_INPUTS
    inner, edge = internal(ns, OUTNODE, boundary)
    rw = [f'e{x}' for x in edge if x not in regs and x not in FINAL_INPUTS]
    out_inner = ', '.join(f'n{x}' for x in inner)
    byname = {name: node for node, name, _ in FINAL}
    reg_args = ' '.join(f'(r{byname[nm]} p w)' for nm in REG_ORDER)
    out = f'''theorem output_norm : (n{OUTNODE} p).evalRing w = {subst_atoms(OUTPUT)} := by
  simp only [{out_inner}, {EV}''' + (', ' + ', '.join(rw) if rw else '') + f''']
  unfold N9Norm.norm2
  ring

/-- **The graph computes the finalizer at the prefix**, with the successor `C = c + 1`. -/
theorem output_eval : (n{OUTNODE} p).evalRing w =
    N105Finalizer.value (Rq (pc p) (w 0) (w 1)) (Nq (w 0)) (w 0) (w 1) (tq (w 0)) (w 2) (w 3) (w 4)
      (w 5 + 1) (w 6) (w 7) (w 8) := by
  rw [← s{RNODE}, ← s384, ← s411, output_norm, value_regs {reg_args}, r{byname['C']}]'''
    return defs, '\n\n'.join(lem), out


HEADER = '''import DiophantineConsistency.WeightedExpressionDegree
import DiophantineConsistency.Nine121.N105Prefix
import DiophantineConsistency.Nine121.N105Finalizer

/-! # Package 105's 456-operation nine-positive equation, as a Lean literal

Generated by `research/nine-positive-p105-456-endpoint/tools/generate_n105p456_graph.py` from
`105-bootstrap-certificates/nine/equations/h1868.json` (SHA-256 `{pin}`):
488 nodes (456 live operations), variables `b g h s w c i j n`, output node 487. Node `nᵢ` is the
JSON node `i`; the fixed leaves are `baseScale = 2^2134939`, `thresholdScale = 2^16012032` (kept
irreducible) and the ten coefficient leaves `c000`–`c009` as port polynomials in `p = (β, K, MC, MF)`.

The evaluation is proved gate by gate: closed forms in `Bq b` for the nodes that depend on the base
only (`eᵢ`), the prefix registers of `N105Prefix` (`sᵢ`), and the 25 finalizer registers over the
evaluations of other register nodes (`rᵢ`; `r395` is the successor `C = c + 1`). `output_eval` is
the evaluation of the whole DAG: `N105Finalizer.value` at `R = Rq`, `N = Nq`, `t = tq`, `C = c + 1`.
The correspondence with the JSON is checked by `tools/check_graph.py` (byte-identical
regeneration, gate-by-gate parse, mutation rejection). -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
set_option linter.unusedVariables false
noncomputable section
namespace Nine121.N105p456Graph
open DiophantineConsistency N105Layout N105Prefix
open N101Prefix (Bq baseScale thresholdScale)

'''


def full(d, cf):
    defs, lem, out = render(d, cf)
    return (HEADER.replace('{pin}', PIN) + '/-! ## The literal DAG -/\n\n' + defs + '\n\n' +
            '''/-- The ports in a commutative ring. -/
def pc {R : Type*} [CommRing R] (p : Fin 4 → ℤ) : Fin 4 → R := fun j => (p j : R)

/-- `N105Finalizer.value` with its lets named. -/
theorem value_regs {A : Type*} [CommRing A] {R N b g t h s w C i j n U Y M P K Am B1 W1 J Qr m Ω E0
    V0 a0 D F Λ G Z H1 I a1 V1 : A}
    (hU : U = N ^ 2 * w) (hY : Y = N ^ 2 * s) (hM : M = R * Y) (hP : P = 2 * M ^ 2 * U)
    (hK : K = R + 1 + h * (P - 1)) (hAm : Am = M * (U + 1)) (hB1 : B1 = 2 * R + 1)
    (hW1 : W1 = b * w) (hJ : J = 4 * Am - 5) (hQr : Qr = 3 * W1 * C - 2 * (W1 ^ 2 - 1))
    (hm : m = K ^ 2 * (4 * t - g) - 16 * t * (C - K * Y) ^ 2) (hΩ : Ω = J * m)
    (hE0 : E0 = J * (n + W1 ^ 2) + Qr) (hV0 : V0 = P * K) (ha0 : a0 = (P ^ 2 - 1) * K ^ 2 + 1)
    (hD : D = (Am ^ 2 - 1) * C ^ 2 + 1) (hF : F = (Am ^ 2 - 1) * D * (i * J * C ^ 2) ^ 2 + 1)
    (hΛ : Λ = C * D + 1 - Am) (hG : G = Am + F * Λ) (hZ : Z = B1 + (j - 1) * C)
    (hH1 : H1 = C + F * Z) (hI : I = (G ^ 2 - 1) * H1 ^ 2 + 1) (ha1 : a1 = 4 * (D * F * I))
    (hV1 : V1 = i * C ^ 2 * (Am * J * (2 * D - C ^ 2) + (3 * C ^ 2 - 4)) * G * H1) :
    N9Norm.norm2 (E0 - Ω * (V0 + V1)) Ω a0 a1 = N105Finalizer.value R N b g t h s w C i j n := by
  subst hV1 ha1 hI hH1 hZ hG hΛ hF hD ha0 hV0 hE0 hΩ hm hQr hJ hW1 hB1 hAm hK hP hM hY hU
  rfl

section Eval
variable {R : Type*} [CommRing R] (p : Fin 4 → ℤ) (w : Fin 9 → R)

''' + lem + '\n\n' + out + '\n\nend Eval\n\nend Nine121.N105p456Graph\n\n#print axioms Nine121.N105p456Graph.output_eval\n')


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
