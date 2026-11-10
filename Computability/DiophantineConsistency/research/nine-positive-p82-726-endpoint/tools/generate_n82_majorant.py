#!/usr/bin/env python3
"""Emit Nine121/N82Majorant.lean: package 82's full-radical Laurent majorant and its certificate.

Inputs (inert JSON, SHA-256 pinned below), under 82-pell-congruences/nine_full_radical/:
  * laurent9_positive.json      the 726-operation equation (861 nodes, output 860);
  * laurent_candidate.json      T0 (654 terms), the radicand DFI (5,011) and Delta0 (3,781);
  * laurent_cone_certificate.json  the package's translated positivity certificate (checked here only).

The JSON nodes in the cone of `Laurent_T` (node 844) above the register nodes A (389), C (4), i (426)
and t (439) are emitted as `tBlock add sub mul lit a c i t` over arbitrary operations (one `let` per
node, JSON order, JSON operand order). Over a commutative ring this is `TR`, the value the graph
computes (`N82p726Graph.r844`).

Three Kronecker identity checks (`Kron4`, `decide +kernel`):
  * idT: TR = 4 T0                                           (the package's evaluator rewrite);
  * idD: T0^2 - 2^32 C^14 D F I = A^22 t^2 P + rest           (P = the 19 terms of Delta0 at A^22 t^2);
  * idQ: P - kappa C^42 i^10 = Q(C - 1, i - 1)               (Q a Horner form with nonnegative literals),
and three Boolean certificates:
  * T0 is dominated by its top term A^23 C^31 i^5 t (SP4.posCheck, M = 2^20);
  * every term of `rest` divides A^22 C^42 i^10 t^2 with a negative coefficient only at A-degree < 22 or
    t-degree < 2, and kappa 2^20 + nu > 0 (TopDom.pos_split);
  * Q is a sum of products of nonnegative literals and C - 1, i - 1 (TopDom.NN).
Hence for A, t >= 2^20, C, i >= 1: T = 4 T0 > 0, T^2 - (2^18 C^7)^2 D F I = 16 Delta0 > 0 and T > A D.

The package certifies Delta0 > 0 by its translate (32,637 positive coefficients); the generator checks
that translate and the T0 translate (9,216) against laurent_cone_certificate.json, but Lean uses the
domination form above (it needs A, t >= 2^20, which the prefix guarantees).

Use --check to compare with the file on disk instead of writing it.
"""
from pathlib import Path
from collections import defaultdict
import argparse, hashlib, json, math, sys

HERE = Path(__file__).resolve()
DC = HERE.parents[3]
LEAN = DC / 'Lean/DiophantineConsistency/Nine121/N82Majorant.lean'
PKG = DC / 'con-zfc-diophantine-forms/82-pell-congruences/nine_full_radical'
PINS = {
    'equation': (PKG / 'laurent9_positive.json', '56e8629e1590157e608d5ffafcf3943b925562578fba4854c81d443ed2e54f93'),
    'candidate': (PKG / 'laurent_candidate.json', '894ebc7687d764e3eab0cd4e5ffe2f853eb9592731aec37f7918e26fea9ac4f5'),
    'cone': (PKG / 'laurent_cone_certificate.json', 'f3e277a6d0a02c2596bcd0d73dc877bebc95ff7c58a0a8c1afe1d6ff98570b43'),
}
ATOMS = {389: 'a', 4: 'c', 426: 'i', 439: 't'}
ROOT = 844
M_BOUND = 1 << 20
TOP_T0 = (23, 31, 5, 1)
TOP_D = (22, 42, 10, 2)
PRIME = (1 << 127) - 1


def need(ok, msg):
    if not ok:
        raise SystemExit('FAIL: ' + msg)


def load():
    docs, pins = {}, {}
    for key, (path, pin) in PINS.items():
        raw = path.read_bytes()
        pins[key] = hashlib.sha256(raw).hexdigest()
        need(pins[key] == pin, 'pin ' + key)
        docs[key] = json.loads(raw)
    return docs, pins


# ---------------------------------------------------------------- dict polynomials in (a, c, i, t)
def clean(p): return {m: c for m, c in p.items() if c}


def padd(p, q, f=1):
    out = dict(p)
    for m, c in q.items():
        out[m] = out.get(m, 0) + f * c
    return clean(out)


def pmul(p, q):
    out = defaultdict(int)
    for m, c in p.items():
        for n, d in q.items():
            out[(m[0] + n[0], m[1] + n[1], m[2] + n[2], m[3] + n[3])] += c * d
    return clean(out)


def pnum(c): return {(0, 0, 0, 0): c} if c else {}
def pvar(k): return {tuple(int(j == k) for j in range(4)): 1}


def table(raw): return {tuple(m): int(c) for m, c in raw}


def translate(p, shifts):
    for axis, value in enumerate(shifts):
        out = defaultdict(int)
        for m, c in p.items():
            for k in range(m[axis] + 1):
                n = list(m); n[axis] = k
                out[tuple(n)] += c * math.comb(m[axis], k) * value ** (m[axis] - k)
        p = clean(out)
    return p


# ---------------------------------------------------------------- a Python mirror of Kron.ZE
class Z:
    __slots__ = ('op', 'a', 'b')

    def __init__(self, op, a=None, b=None):
        self.op, self.a, self.b = op, a, b


def pw(k, n): return Z('pw', k, n)
def lit(n): return Z('lit', n)
def add(x, y): return Z('add', x, y)
def sub(x, y): return Z('sub', x, y)
def mul(x, y): return Z('mul', x, y)
def terms(name, tl): return Z('terms', name, tl)
def zref(name, target): return Z('ref', name, target)


def zpoly(e, memo):
    """Exact polynomial of a ZE."""
    k = id(e)
    if k in memo:
        return memo[k]
    if e.op == 'ref':
        r = zpoly(e.b, memo)
    elif e.op == 'pw':
        r = {tuple(e.b if j == e.a else 0 for j in range(4)): 1}
    elif e.op == 'lit':
        r = pnum(e.a)
    elif e.op == 'terms':
        r = clean(dict(e.b))
    else:
        x, y = zpoly(e.a, memo), zpoly(e.b, memo)
        r = padd(x, y) if e.op == 'add' else padd(x, y, -1) if e.op == 'sub' else pmul(x, y)
    memo[k] = r
    return r


def mx(u, v): return tuple(max(x, y) for x, y in zip(u, v))
def ad(u, v): return tuple(x + y for x, y in zip(u, v))


def zsplit(e, pt, memo, mod=None):
    """(pos, neg, pdeg, ndeg) of Kron.split e at the point pt (exact model of the Lean recursion)."""
    k = id(e)
    if k in memo:
        return memo[k]
    red = (lambda v: v % mod) if mod else (lambda v: v)
    z4 = (0, 0, 0, 0)
    if e.op == 'ref':
        r = zsplit(e.b, pt, memo, mod)
    elif e.op == 'pw':
        r = (red(pt[e.a] ** e.b) if not mod else pow(pt[e.a], e.b, mod), 0,
             tuple(e.b if j == e.a else 0 for j in range(4)), z4)
    elif e.op == 'lit':
        r = (max(e.a, 0), max(-e.a, 0), z4, z4)
    elif e.op == 'terms':
        pos = neg = 0
        dp = dn = z4
        for m, c in e.b:
            v = 1
            for j in range(4):
                v = v * (pow(pt[j], m[j], mod) if mod else pt[j] ** m[j])
            pos += max(c, 0) * v
            neg += max(-c, 0) * v
            dp = mx(dp, m); dn = mx(dn, m)
        r = (red(pos), red(neg), dp, dn)
    else:
        x, y = zsplit(e.a, pt, memo, mod), zsplit(e.b, pt, memo, mod)
        if e.op == 'add':
            r = (red(x[0] + y[0]), red(x[1] + y[1]), mx(x[2], y[2]), mx(x[3], y[3]))
        elif e.op == 'sub':
            r = (red(x[0] + y[1]), red(x[1] + y[0]), mx(x[2], y[3]), mx(x[3], y[2]))
        else:
            r = (red(x[0] * y[0] + x[1] * y[1]), red(x[0] * y[1] + x[1] * y[0]),
                 mx(ad(x[2], y[2]), ad(x[3], y[3])), mx(ad(x[2], y[3]), ad(x[3], y[2])))
    memo[k] = r
    return r


def kron_params(e, name):
    """Degree box and K with an exact model of Kron.kcheckK; a modular Kronecker check."""
    v = zsplit(e, (1, 1, 1, 1), {})
    box = tuple(max(x, y) + 1 for x, y in zip(v[2], v[3]))
    K = max(v[0], v[1]).bit_length() + 1
    X0 = 1 << K
    need(v[0] < X0 and v[1] < X0, name + ' coefficient bound')
    pt = (X0, X0 ** box[0], X0 ** (box[0] * box[1]), X0 ** (box[0] * box[1] * box[2]))
    ptm = tuple(p % PRIME for p in pt)
    w = zsplit(e, ptm, {}, mod=PRIME)
    need(w[0] == w[1], name + ' Kronecker evaluation modulo 2^127 - 1')
    return box, K


# ---------------------------------------------------------------- the T block
def cone(ns):
    seen, inner, st = set(), [], [ROOT]
    while st:
        k = st.pop()
        if k in seen:
            continue
        seen.add(k)
        if k in ATOMS:
            continue
        inner.append(k)
        nd = ns[k]
        if nd['kind'] in ('add', 'sub', 'mul'):
            st += [nd['left'], nd['right']]
        else:
            need(nd['kind'] == 'literal', f'node {k} in the T cone is a {nd["kind"]}')
    return sorted(inner)


def block(ns, inner, add_, sub_, mul_, lit_, a, c, i, t):
    val = {389: a, 4: c, 426: i, 439: t}
    for k in inner:
        nd = ns[k]
        if nd['kind'] == 'literal':
            val[k] = lit_(nd['value'])
        else:
            f = {'add': add_, 'sub': sub_, 'mul': mul_}[nd['kind']]
            val[k] = f(val[nd['left']], val[nd['right']])
    return val[ROOT]


def registers(pa, pc, pi, pt_, add_, sub_, mul_, lit_):
    one = lit_(1)
    D = add_(mul_(sub_(mul_(pa, pa), one), mul_(pc, pc)), one)
    E = mul_(mul_(mul_(pi, sub_(mul_(lit_(4), pa), lit_(5))), mul_(pc, pc)), D)
    F = add_(mul_(sub_(mul_(pa, pa), one), mul_(E, E)), one)
    G = add_(pa, mul_(F, sub_(add_(mul_(pc, D), one), pa)))
    H = add_(pc, mul_(F, pt_))
    I = add_(mul_(sub_(mul_(G, G), one), mul_(H, H)), one)
    return D, E, F, G, H, I


def horner(q):
    """Q(y, z) = sum q[a, b] y^a z^b as a ZE in y = c - 1, z = i - 1 (Horner in z, then y)."""
    y = sub(pw(1, 1), lit(1))
    z = sub(pw(2, 1), lit(1))
    A = max(a for a, _ in q); Bm = max(b for _, b in q)

    def row(b):
        h = lit(q.get((A, b), 0))
        for a in range(A - 1, -1, -1):
            h = add(mul(h, y), lit(q.get((a, b), 0)))
        return h
    rows = [zref(f'Qrow{b}', row(b)) for b in range(Bm + 1)]
    h = rows[Bm]
    for b in range(Bm - 1, -1, -1):
        h = add(mul(h, z), rows[b])
    return h, rows


def analyse():
    docs, pins = load()
    eq, cand, conecert = docs['equation'], docs['candidate'], docs['cone']
    ns = eq['nodes']
    need(eq['output'] == len(ns) - 1 == 860 and eq['total_operations'] == 726, 'equation shape')
    nn = eq['named_nodes']
    need(nn['A'] == 389 and nn['C'] == 4 and nn['Laurent_t'] == 439 and nn['Laurent_T'] == ROOT, 'named registers')
    need(ns[426] == {'kind': 'variable', 'name': 'i'} and ns[4] == {'kind': 'variable', 'name': 'C'}, 'variables')
    inner = cone(ns)
    T0 = table(cand['majorant'])
    need(len(T0) == 654, 'T0 terms')
    need(cand['scale_integer'] == 65536 and cand['scale_powers'] == [0, 7, 0, 0], 'scale 2^16 C^7')
    # (1) the evaluator block is 4 T0
    X = [pvar(k) for k in range(4)]
    Tpoly = block(ns, inner, padd, lambda p, q: padd(p, q, -1), pmul, pnum, *X)
    need(Tpoly == {m: 4 * c for m, c in T0.items()}, 'block = 4 T0')
    # (2) the radicand and the defect
    D, E, F, G, H, I = registers(*X, padd, lambda p, q: padd(p, q, -1), pmul, pnum)
    rad = pmul(pmul(D, F), I)
    need(rad == table(cand['radicand']), 'radicand = laurent_candidate radicand')
    defect = padd(pmul(T0, T0), pmul({(0, 14, 0, 0): 1 << 32}, rad), -1)
    need(defect == table(cand['defect']) and len(defect) == 3781, 'Delta0 = laurent_candidate defect')
    # the package's cone certificate (translate by 3, 1, 1, 3): checked, not used in Lean
    for key, p in (('majorant', T0), ('defect', defect)):
        cc = conecert[key]
        need(cc['shifts'] == [3, 1, 1, 3], 'cone shifts')
        sh = translate(p, (3, 1, 1, 3))
        need(sh == table(cc['coefficients']) and min(sh.values()) > 0, 'cone certificate ' + key)
    # (3) top group, rest, kappa, Q
    P = {(0, m[1], m[2], 0): c for m, c in defect.items() if m[0] == TOP_D[0] and m[3] == TOP_D[3]}
    rest = {m: c for m, c in defect.items() if not (m[0] == TOP_D[0] and m[3] == TOP_D[3])}
    need(len(P) == 19 and len(rest) == 3762, 'top group / rest sizes')
    need(all(all(m[k] <= TOP_D[k] for k in range(4)) for m in rest), 'rest divides the top')
    need(all(c > 0 or m[0] < TOP_D[0] or m[3] < TOP_D[3] for m, c in rest.items()), 'rest negatives')
    nu = sum(c for c in rest.values() if c < 0)
    Pt = translate({(m[1], m[2], 0, 0): c for m, c in P.items()}, (1, 1, 0, 0))
    kappa = min(Pt.get((x, y, 0, 0), 0) // (math.comb(TOP_D[1], x) * math.comb(TOP_D[2], y))
                for x in range(TOP_D[1] + 1) for y in range(TOP_D[2] + 1))
    need(kappa == P[(0, 42, 10, 0)] == 141664530202624, 'kappa = the leading coefficient')
    q = {}
    for x in range(TOP_D[1] + 1):
        for y in range(TOP_D[2] + 1):
            q[(x, y)] = Pt.get((x, y, 0, 0), 0) - kappa * math.comb(TOP_D[1], x) * math.comb(TOP_D[2], y)
    need(min(q.values()) >= 0, 'Q nonnegative')
    need(kappa * M_BOUND + nu > 0, 'kappa M + nu > 0')
    # T0 domination
    kap0 = T0[TOP_T0]
    nu0 = sum(c for m, c in T0.items() if c < 0)
    need(all(all(m[k] <= TOP_T0[k] for k in range(4)) for m in T0), 'T0 divides its top')
    need(all(c > 0 or m[0] < TOP_T0[0] for m, c in T0.items() if m != TOP_T0), 'T0 negatives below top')
    need(kap0 * M_BOUND + nu0 > 0, 'T0 domination')
    # (4) the three ZE identities, exactly as polynomials, and their Kronecker parameters
    aZ, cZ, iZ, tZ = (pw(k, 1) for k in range(4))
    TRz = block(ns, inner, add, sub, mul, lit, aZ, cZ, iZ, tZ)
    T0l = sorted(T0.items(), key=kron_order)
    Pl = sorted(P.items(), key=kron_order)
    Rl = sorted(rest.items(), key=kron_order)
    T0z = terms('T0T', T0l)
    PTz = terms('PT', Pl)
    RTz = terms('restT', Rl)
    DZ, EZ, FZ, GZ, HZ, IZ = registers(aZ, cZ, iZ, tZ, add, sub, mul, lit)
    QhZ, _ = horner(q)
    idT = sub(TRz, mul(lit(4), T0z))
    idD = sub(sub(mul(T0z, T0z), mul(mul(lit(1 << 32), pw(1, 14)), mul(mul(DZ, FZ), IZ))),
              add(mul(mul(pw(0, 22), pw(3, 2)), PTz), RTz))
    idQ = sub(sub(PTz, mul(lit(kappa), mul(pw(1, 42), pw(2, 10)))), QhZ)
    for e, name in ((idT, 'idT'), (idD, 'idD'), (idQ, 'idQ')):
        need(zpoly(e, {}) == {}, name + ' is a polynomial identity')
    kp = {name: kron_params(e, name) for e, name in ((idT, 'idT'), (idD, 'idD'), (idQ, 'idQ'))}
    stats = dict(block_nodes=len(inner), T0_terms=len(T0), defect_terms=len(defect), top_group=len(P),
                 rest_terms=len(rest), kappa=kappa, nu=nu, nu_bits=abs(nu).bit_length(), T0_top=kap0,
                 T0_nu=nu0, Q_terms=len(q), Q_zero=sum(1 for v in q.values() if v == 0),
                 kron={k: {'box': list(v[0]), 'K': v[1]} for k, v in kp.items()},
                 cone_terms={'majorant': len(conecert['majorant']['coefficients']),
                             'defect': len(conecert['defect']['coefficients'])})
    return dict(pins=pins, ns=ns, inner=inner, T0l=T0l, Pl=Pl, Rl=Rl, q=q, kappa=kappa, kp=kp,
                stats=stats)


def kron_order(t):
    m = t[0]
    return (m[3], m[2], m[1], m[0])


# ---------------------------------------------------------------- Lean rendering
def tree_text(items):
    if len(items) == 1:
        return items[0]
    h = len(items) // 2
    return f'(.node {tree_text(items[:h])}\n  {tree_text(items[h:])})'


def tt_defs(base, tl, doc, size=256):
    out, names = [], []
    for j in range(0, len(tl), size):
        leaves = [f'(.leaf (Mon.mk {m[0]} {m[1]} {m[2]} {m[3]}) ({c}))' for m, c in tl[j:j + size]]
        name = f'{base}{j // size}'
        names.append(name)
        out.append(f'def {name} : TT :=\n  {tree_text(leaves)}')
    if len(names) == 1:
        return f'/-- {doc} -/\ndef {base} : TT :=\n  {tree_text([l for l in leaves])}\n'
    return '\n\n'.join(out) + f'\n\n/-- {doc} -/\ndef {base} : TT :=\n  {tree_text(names)}\n'


def ze_text(e):
    """Lean text of a ZE built by `horner` (no sharing needed: Horner chains are linear)."""
    if e.op == 'ref':
        return e.a
    if e.op == 'pw':
        return f'(.pw {e.a} {e.b})'
    if e.op == 'lit':
        return f'(.lit ({e.a}))'
    return f'(.{e.op} {ze_text(e.a)} {ze_text(e.b)})'


def ref(k):
    return ATOMS.get(k, f'x{k}')


def render(d):
    ns, inner = d['ns'], d['inner']
    lines = []
    for k in inner:
        nd = ns[k]
        if nd['kind'] == 'literal':
            lines.append(f'  let x{k} := lit ({nd["value"]})')
        else:
            lines.append(f'  let x{k} := {nd["kind"]} {ref(nd["left"])} {ref(nd["right"])}')
    lines.append(f'  x{ROOT}')
    body = '\n'.join(lines)
    sys.setrecursionlimit(100000)
    qtop, qrows = horner(d['q'])
    qh = ze_text(qtop)
    qrows_text = '\n'.join(f'def {r.a} : ZE :=\n  {ze_text(r.b)}' for r in qrows)
    kp = d['kp']

    def box(name):
        b, K = kp[name]
        return ' '.join(map(str, b)) + f' {K}'
    lit_text = (tt_defs('T0T', d['T0l'], 'The 654-term majorant `T₀` (`laurent_candidate.json`, key `majorant`).') + '\n' +
                tt_defs('PT', d['Pl'], 'The 19 terms of `Δ₀` at `A²² t²`, as a polynomial in `C, i`.') + '\n' +
                tt_defs('restT', d['Rl'], 'The other 3,762 terms of `Δ₀`.'))
    return (HEADER.replace('@PIN@', d['pins']['equation']).replace('@PINC@', d['pins']['candidate']) +
            f'''/-- The JSON cone of `Laurent_T` (node 844) over arbitrary operations: `a, c, i, t` are the
register nodes `A` (389), `C` (4), `i` (426) and `t = B₁ + (j − 1)C` (439). -/
def tBlock {{T : Type*}} (add sub mul : T → T → T) (lit : ℤ → T) (a c i t : T) : T :=
{body}

''' + TAIL.replace('@LIT@', lit_text).replace('@QH@', qh).replace('@QROWS@', qrows_text).replace('@BT@', box('idT'))
            .replace('@BD@', box('idD')).replace('@BQ@', box('idQ'))
            .replace('@KAPPA@', str(d['kappa'])))


HEADER = '''import DiophantineConsistency.Nine121.TopDom

/-! # Package 82's full-radical Laurent majorant and its positivity certificate

Generated by `research/nine-positive-p82-726-endpoint/tools/generate_n82_majorant.py` from
`82-pell-congruences/nine_full_radical/laurent9_positive.json` (SHA-256 `@PIN@`) and
`laurent_candidate.json` (SHA-256 `@PINC@`).

`tBlock` is the JSON circuit of `T` (the cone of node 844 above the registers `A, C, i, t`) over
arbitrary operations, and `TR` its value in a commutative ring:
`T = 64C⁷H(T₇ − 640i − 4096) − Corr(J, C, i, t, D)`. The Pell registers are Jones's:
`D = (a² − 1)c² + 1`, `E = i(4a − 5)c²D`, `F = (a² − 1)E² + 1`, `G = a + F(cD + 1 − a)`,
`H = c + Ft`, `I = (G² − 1)H² + 1`, and the scale is `S = 2¹⁸c⁷`.

`majorant`: for `a, t ≥ 2²⁰` and `c, i ≥ 1` in an ordered commutative ring,
`0 < T`, `S²DFI < T²` and `aD < T`. The proof is three Kronecker identity checks
(`Kron.kcheckK`): `T = 4T₀` (the 654-term `T₀` of `laurent_candidate.json`),
`T₀² − 2³²c¹⁴DFI = a²²t²P + rest` (the 3,781-term `Δ₀`, split into its 19 terms at `a²²t²` and the
rest), `P − κc⁴²i¹⁰ = Q(c − 1, i − 1)` with `κ = 141664530202624` and `Q` a Horner form with
nonnegative coefficients; then `SP4.pos_of_check` for `T₀` (top `a²³c³¹i⁵t`) and
`TopDom.pos_split` for `Δ₀` (top `a²²c⁴²i¹⁰t²`, `κ·2²⁰ + ν > 0`). The package's own certificate
(the translate by `a = x + 3, c = y + 1, i = u + 1, t = v + 3`, 32,637 + 9,216 positive
coefficients) is checked by the generator, not used in Lean. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Nine121.N82Majorant
open SP4

'''

TAIL = '''/-- `T` in a commutative ring. -/
def TR {R : Type*} [CommRing R] (a c i t : R) : R :=
  tBlock (fun x y => x + y) (fun x y => x - y) (fun x y => x * y) (fun k => (k : R)) a c i t

section Ring
variable {R : Type*} [CommRing R]

/-- Jones's Pell registers of the radicand, and the scale. -/
def Dr (a c : R) : R := (a ^ 2 - 1) * c ^ 2 + 1
def Er (a c i : R) : R := i * (4 * a - 5) * c ^ 2 * Dr a c
def Fr (a c i : R) : R := (a ^ 2 - 1) * Er a c i ^ 2 + 1
def Gr (a c i : R) : R := a + Fr a c i * (c * Dr a c + 1 - a)
def Hr (a c i t : R) : R := c + Fr a c i * t
def Ir (a c i t : R) : R := (Gr a c i ^ 2 - 1) * Hr a c i t ^ 2 + 1
def Sr (c : R) : R := 262144 * c ^ 7

end Ring

/-! ## The literal polynomials and the identities -/

open Kron

@LIT@
def aZ : ZE := .pw 0 1
def cZ : ZE := .pw 1 1
def iZ : ZE := .pw 2 1
def tZ : ZE := .pw 3 1
def oneZ : ZE := .lit 1
def TRz : ZE := tBlock ZE.add ZE.sub ZE.mul ZE.lit aZ cZ iZ tZ
def T0z : ZE := .terms T0T
def DZ : ZE := .add (.mul (.sub (.mul aZ aZ) oneZ) (.mul cZ cZ)) oneZ
def EZ : ZE := .mul (.mul (.mul iZ (.sub (.mul (.lit 4) aZ) (.lit 5))) (.mul cZ cZ)) DZ
def FZ : ZE := .add (.mul (.sub (.mul aZ aZ) oneZ) (.mul EZ EZ)) oneZ
def GZ : ZE := .add aZ (.mul FZ (.sub (.add (.mul cZ DZ) oneZ) aZ))
def HZ : ZE := .add cZ (.mul FZ tZ)
def IZ : ZE := .add (.mul (.sub (.mul GZ GZ) oneZ) (.mul HZ HZ)) oneZ

/-- The rows of `Q`: Horner forms in `c − 1` with nonnegative literals. -/
@QROWS@

/-- `Q(c − 1, i − 1)`, Horner form in `i − 1` over the rows. -/
def QhZ : ZE :=
  @QH@

/-- `T − 4T₀`. -/
def idT : ZE := .sub TRz (.mul (.lit 4) T0z)
/-- `T₀² − 2³²c¹⁴DFI − (a²²t²P + rest)`. -/
def idD : ZE := .sub (.sub (.mul T0z T0z) (.mul (.mul (.lit 4294967296) (.pw 1 14)) (.mul (.mul DZ FZ) IZ)))
  (.add (.mul (.mul (.pw 0 22) (.pw 3 2)) (.terms PT)) (.terms restT))
/-- `P − κc⁴²i¹⁰ − Q(c − 1, i − 1)`. -/
def idQ : ZE := .sub (.sub (.terms PT) (.mul (.lit @KAPPA@) (.mul (.pw 1 42) (.pw 2 10)))) QhZ

theorem idT_check : kcheckK @BT@ (split idT).1 (split idT).2 = true := by decide +kernel
theorem idD_check : kcheckK @BD@ (split idD).1 (split idD).2 = true := by decide +kernel
theorem idQ_check : kcheckK @BQ@ (split idQ).1 (split idQ).2 = true := by decide +kernel

theorem T0_check : posCheckT ⟨23, 31, 5, 1⟩ 1048576 T0T = true := by decide +kernel
theorem rest_check : restT.all (TopDom.restOk ⟨22, 42, 10, 2⟩) = true := by decide +kernel
theorem rest_neg : 0 < ((@KAPPA@ : ℕ) : ℤ) * ((1048576 : ℕ) : ℤ) + TopDom.negAll restT := by
  decide +kernel
theorem Q_check : TopDom.NN QhZ = true := by decide +kernel

section Ring
variable {R : Type*} [CommRing R] (a c i t : R)

theorem zeval_TRz : TRz.eval a c i t = TR a c i t := by
  simp only [TRz, TR, tBlock, aZ, cZ, iZ, tZ, zeval_add, zeval_sub, zeval_mul, zeval_lit, zeval_pw, sel,
    pow_one]

theorem zeval_DZ : DZ.eval a c i t = Dr a c := by
  simp only [DZ, oneZ, aZ, cZ, Dr, zeval_add, zeval_sub, zeval_mul, zeval_lit, zeval_pw, sel, pow_one,
    Int.cast_one]; ring

theorem zeval_EZ : EZ.eval a c i t = Er a c i := by
  simp only [EZ, aZ, cZ, iZ, Er, zeval_sub, zeval_mul, zeval_lit, zeval_pw, sel, pow_one, zeval_DZ,
    Int.cast_ofNat]; ring

theorem zeval_FZ : FZ.eval a c i t = Fr a c i := by
  simp only [FZ, oneZ, aZ, Fr, zeval_add, zeval_sub, zeval_mul, zeval_lit, zeval_pw, sel, pow_one,
    zeval_EZ, Int.cast_one]; ring

theorem zeval_GZ : GZ.eval a c i t = Gr a c i := by
  simp only [GZ, oneZ, aZ, cZ, Gr, zeval_add, zeval_sub, zeval_mul, zeval_lit, zeval_pw, sel, pow_one,
    zeval_DZ, zeval_FZ, Int.cast_one]

theorem zeval_HZ : HZ.eval a c i t = Hr a c i t := by
  simp only [HZ, cZ, tZ, Hr, zeval_add, zeval_mul, zeval_pw, sel, pow_one, zeval_FZ]

theorem zeval_IZ : IZ.eval a c i t = Ir a c i t := by
  simp only [IZ, oneZ, Ir, zeval_add, zeval_sub, zeval_mul, zeval_lit, zeval_GZ, zeval_HZ,
    Int.cast_one]; ring

/-- **The evaluator rewrite** `T = 4T₀`. -/
theorem T_eq : TR a c i t = 4 * evL a c i t T0T.toList := by
  have h := zero_of_kcheckK @BT@ idT idT_check a c i t
  simp only [idT, T0z, zeval_sub, zeval_mul, zeval_lit, zeval_terms, zeval_TRz, Int.cast_ofNat] at h
  linear_combination h

/-- **The defect identity** `T₀² − 2³²c¹⁴DFI = a²²t²P + rest`. -/
theorem defect_eq : evL a c i t T0T.toList ^ 2 - 4294967296 * c ^ 14 * (Dr a c * Fr a c i * Ir a c i t) =
    a ^ 22 * t ^ 2 * evL a c i t PT.toList + evL a c i t restT.toList := by
  have h := zero_of_kcheckK @BD@ idD idD_check a c i t
  simp only [idD, T0z, zeval_sub, zeval_mul, zeval_add, zeval_lit, zeval_pw, sel, zeval_terms,
    zeval_DZ, zeval_FZ, zeval_IZ, Int.cast_ofNat] at h
  linear_combination h

/-- **The top group** `P = κc⁴²i¹⁰ + Q(c − 1, i − 1)`. -/
theorem P_eq : evL a c i t PT.toList = ((@KAPPA@ : ℕ) : R) * (c ^ 42 * i ^ 10) + QhZ.eval a c i t := by
  have h := zero_of_kcheckK @BQ@ idQ idQ_check a c i t
  simp only [idQ, zeval_sub, zeval_mul, zeval_lit, zeval_pw, sel, zeval_terms, Int.cast_ofNat] at h
  rw [Nat.cast_ofNat]
  linear_combination h

end Ring

/-- **The full-radical Laurent majorant**: for `a, t ≥ 2²⁰` and `c, i ≥ 1`,
`0 < T`, `S²DFI < T²` and `aD < T`. -/
theorem majorant {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R] {a c i t : R}
    (ha : 1048576 ≤ a) (ht : 1048576 ≤ t) (hc : 1 ≤ c) (hi : 1 ≤ i) :
    0 < TR a c i t ∧ Dr a c * Fr a c i * Ir a c i t * Sr c ^ 2 < TR a c i t ^ 2 ∧
      a * Dr a c < TR a c i t := by
  have haM : ((1048576 : ℕ) : R) ≤ a := by rw [Nat.cast_ofNat]; exact ha
  have htM : ((1048576 : ℕ) : R) ≤ t := by rw [Nat.cast_ofNat]; exact ht
  have ha1 : (1 : R) ≤ a := le_trans (by norm_num) ha
  have ht1 : (1 : R) ≤ t := le_trans (by norm_num) ht
  -- `T₀ > 0`
  have h0 := pos_of_check _ _ ⟨T0T.toList⟩ (by rw [← posCheckT_eq]; exact T0_check) haM ha1 hc hi ht1
  unfold ev at h0
  have hT : 0 < TR a c i t := by rw [T_eq]; linarith
  -- `Δ₀ > 0`
  have hQ := TopDom.NN_nonneg ha1 hc hi ht1 QhZ Q_check
  have hP : ((@KAPPA@ : ℕ) : R) * (c ^ (⟨22, 42, 10, 2⟩ : Mon).e1 * i ^ (⟨22, 42, 10, 2⟩ : Mon).e2) ≤
      evL a c i t PT.toList := by
    show ((@KAPPA@ : ℕ) : R) * (c ^ 42 * i ^ 10) ≤ _
    rw [P_eq a c i t]; linarith
  have hΔ := TopDom.pos_split ⟨22, 42, 10, 2⟩ 1048576 @KAPPA@ restT rest_check rest_neg haM htM ha1 hc hi ht1 hP
  have hΔ' : 0 < a ^ 22 * t ^ 2 * evL a c i t PT.toList + evL a c i t restT.toList := hΔ
  rw [← defect_eq] at hΔ'
  have hS : Sr c ^ 2 = 68719476736 * c ^ 14 := by unfold Sr; ring
  have hmaj : Dr a c * Fr a c i * Ir a c i t * Sr c ^ 2 < TR a c i t ^ 2 := by
    rw [hS, T_eq]
    nlinarith [hΔ']
  refine ⟨hT, hmaj, ?_⟩
  -- `aD < T`: `S²DFI ≥ DF ≥ a²D²`
  have hc2 : (1 : R) ≤ c ^ 2 := one_le_pow₀ hc
  have ha2 : (1048576 : R) ≤ a ^ 2 := by nlinarith
  have hd1 : a ^ 2 ≤ Dr a c := by
    unfold Dr
    have := mul_nonneg (by linarith : (0 : R) ≤ a ^ 2 - 1) (by linarith : (0 : R) ≤ c ^ 2 - 1)
    nlinarith
  have hd0 : (1 : R) ≤ Dr a c := by linarith
  have hJ : (1 : R) ≤ i * (4 * a - 5) * c ^ 2 := by
    have h1 : (1 : R) ≤ 4 * a - 5 := by linarith
    have h2 : (1 : R) ≤ i * (4 * a - 5) := one_le_mul_of_one_le_of_one_le hi h1
    exact one_le_mul_of_one_le_of_one_le h2 hc2
  have he : Dr a c ≤ Er a c i := by
    unfold Er
    exact le_mul_of_one_le_left (by linarith) hJ
  have hf : a ^ 2 * Dr a c ≤ Fr a c i := by
    unfold Fr
    have hee : Dr a c ^ 2 ≤ Er a c i ^ 2 := pow_le_pow_left₀ (by linarith) he 2
    have h1 : (a ^ 2 - 1) * Dr a c ^ 2 ≤ (a ^ 2 - 1) * Er a c i ^ 2 :=
      mul_le_mul_of_nonneg_left hee (by linarith)
    have h2 : 0 ≤ (Dr a c - 1) * ((a ^ 2 - 1) * Dr a c - 1) := by
      apply mul_nonneg (by linarith)
      nlinarith
    nlinarith
  have hL : 0 ≤ c * Dr a c + 1 - a := by
    have : Dr a c ≤ c * Dr a c := le_mul_of_one_le_left (by linarith) hc
    nlinarith
  have hf0 : 0 ≤ Fr a c i := le_trans (mul_nonneg (sq_nonneg a) (by linarith)) hf
  have hg : (1 : R) ≤ Gr a c i := by
    unfold Gr
    have : 0 ≤ Fr a c i * (c * Dr a c + 1 - a) := mul_nonneg hf0 hL
    linarith
  have hI : (1 : R) ≤ Ir a c i t := by
    unfold Ir
    have hg2 : (1 : R) ≤ Gr a c i ^ 2 := one_le_pow₀ hg
    have : 0 ≤ (Gr a c i ^ 2 - 1) * Hr a c i t ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
    linarith
  have hS1 : (1 : R) ≤ Sr c ^ 2 := by
    rw [hS]
    have : (1 : R) ≤ c ^ 14 := one_le_pow₀ hc
    nlinarith
  have hDF : (a * Dr a c) ^ 2 ≤ Dr a c * Fr a c i * Ir a c i t * Sr c ^ 2 := by
    have h1 : (a * Dr a c) ^ 2 ≤ Dr a c * Fr a c i := by
      have := mul_le_mul_of_nonneg_left hf (by linarith : (0 : R) ≤ Dr a c)
      nlinarith
    have h2 : Dr a c * Fr a c i ≤ Dr a c * Fr a c i * Ir a c i t :=
      le_mul_of_one_le_right (mul_nonneg (by linarith) hf0) hI
    have h3 : Dr a c * Fr a c i * Ir a c i t ≤ Dr a c * Fr a c i * Ir a c i t * Sr c ^ 2 :=
      le_mul_of_one_le_right (mul_nonneg (mul_nonneg (by linarith) hf0) (by linarith)) hS1
    linarith
  have had0 : 0 ≤ a * Dr a c := mul_nonneg (by linarith) (by linarith)
  by_contra hn
  have hle : TR a c i t ≤ a * Dr a c := not_lt.mp hn
  have : TR a c i t ^ 2 ≤ (a * Dr a c) ^ 2 := pow_le_pow_left₀ hT.le hle 2
  linarith

end Nine121.N82Majorant

#print axioms Nine121.N82Majorant.majorant
'''


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--check', action='store_true')
    args = ap.parse_args()
    d = analyse()
    text = render(d)
    if args.check:
        need(LEAN.read_text(encoding='utf-8') == text, 'generated file differs: ' + LEAN.name)
    else:
        LEAN.write_text(text, encoding='utf-8', newline='\n')
    print(json.dumps({'status': 'PASS' if args.check else 'GENERATED', 'pins': d['pins'], **d['stats']}))


if __name__ == '__main__':
    main()
