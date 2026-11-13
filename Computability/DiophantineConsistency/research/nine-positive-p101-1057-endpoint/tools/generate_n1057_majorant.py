#!/usr/bin/env python3
"""Emit Nine121/N1057Majorant.lean: package 101's complete-radical majorant and its certificate.

Input (inert JSON, SHA-256 pinned below):
  101-constructive-reductions/nine/equations/boundary_complete.json (1,386 nodes, output 1385).

The JSON nodes 435..1367 evaluate the 333-term majorant Pi(A, C, i, Z) in Horner form from the
register nodes A (373), C (5), i (6), Z (425) and C^2 (409 = C*C). The generator emits that block as
`piBlock add mul lit a c i z` over arbitrary operations (one `let` per node, in JSON order and with
the JSON operand order), so the same text is
  * `PiR` over a commutative ring (the value the graph computes; `N101p1057Graph.r1367`), and
  * `PiS` over `SP4.Poly` (the kernel computes its 333 terms).
Then two kernel checks (`decide +kernel`) prove, for a >= 2^20 and c, i, z >= 1,
  Pi^2 - sigma^2 D F I > 0   (sigma = 1024 C^5 i)    and    Pi - A D > 0,
by recomputing both polynomials from the register formulas and certifying their domination
structure (`SP4.pos_of_check`).

Before writing, the generator checks with an exact Python model of the Lean algorithm that
  * the block evaluates to the 333-term `data/saturated_corrected_P.json`,
  * Pi^2 - sigma^2 D F I is the package's defect polynomial, whose translate by
    A = x+3, C = y+1, i = u+1, Z = v+1 is the package's 36,309-term certificate
    `data/saturated_corrected_certificate.json` (exact equality),
  * both posCheck conditions hold.

Use --check to compare with the file on disk instead of writing it.
"""
from pathlib import Path
import argparse, hashlib, json, math

HERE = Path(__file__).resolve()
DC = HERE.parents[3]
LEAN = DC / 'Lean/DiophantineConsistency/Nine121/N1057Majorant.lean'
PKG = DC / 'con-zfc-diophantine-forms/101-constructive-reductions/nine'
SRC = PKG / 'equations/boundary_complete.json'
PIN = '3f5f4f92feebd9bd1392af21e3faccf674f1d1e96ac2637cc22a22c73fcfc3bc'
LEAVES = {373: 'a', 5: 'c', 6: 'i', 425: 'z', 409: 'x409'}
LO, HI = 435, 1367
M_BOUND = 1 << 20
TOP_DEF = (18, 48, 12, 2)
TOP_GAP = (18, 24, 6, 1)


def need(ok, msg):
    if not ok:
        raise SystemExit('FAIL: ' + msg)


def load(path=SRC, pin=None):
    raw = path.read_bytes()
    if pin is not None:
        need(hashlib.sha256(raw).hexdigest() == pin, 'boundary_complete.json pin')
    d = json.loads(raw)
    ns = d['nodes']
    need(d['output'] == len(ns) - 1 == 1385, 'output node')
    need(d['majorant'] == 'complete', 'majorant kind')
    need(ns[409] == {'kind': 'mul', 'left': 5, 'right': 5}, 'node 409 is C*C')
    need(ns[5] == {'kind': 'variable', 'name': 'C'} and ns[6] == {'kind': 'variable', 'name': 'i'},
         'variables C, i')
    need(d['named_nodes']['A'] == 373 and d['named_nodes']['Z'] == 425 and d['named_nodes']['V1'] == HI,
         'named registers A, Z, V1')
    for k in range(LO, HI + 1):
        nd = ns[k]
        if nd['kind'] == 'literal':
            continue
        need(nd['kind'] in ('add', 'mul'), f'node {k} kind')
        for ch in (nd['left'], nd['right']):
            need(LO <= ch < k or ch in LEAVES, f'node {k} child {ch} outside the block')
    return d


# ---------------------------------------------------------------- exact model of SP4
def merge(p, q):
    out, i, j = [], 0, 0
    while i < len(p) and j < len(q):
        (m, c), (m2, c2) = p[i], q[j]
        if m < m2:
            out.append(p[i]); i += 1
        elif m2 < m:
            out.append(q[j]); j += 1
        else:
            if c + c2:
                out.append((m, c + c2))
            i += 1; j += 1
    return out + p[i:] + q[j:]


def p_add(p, q): return merge(p, q)
def p_neg(p): return [(m, -c) for m, c in p]
def p_sub(p, q): return merge(p, p_neg(q))


def p_mul(p, q):
    acc = []
    for (m, c) in reversed(p):
        acc = merge([(tuple(x + y for x, y in zip(m, m2)), c * c2) for m2, c2 in q], acc)
    return acc


def p_lit(k): return [] if k == 0 else [((0, 0, 0, 0), k)]


X = [[((1, 0, 0, 0), 1)], [((0, 1, 0, 0), 1)], [((0, 0, 1, 0), 1)], [((0, 0, 0, 1), 1)]]


def block(d, add, mul, lit, a, c, i, z):
    ns = d['nodes']
    val = {373: a, 5: c, 6: i, 425: z}
    val[409] = mul(c, c)
    for k in range(LO, HI + 1):
        nd = ns[k]
        val[k] = lit(nd['value']) if nd['kind'] == 'literal' else (
            add if nd['kind'] == 'add' else mul)(val[nd['left']], val[nd['right']])
    return val[HI]


def registers():
    A, C, I_, Z = X
    one = p_lit(1)
    a2 = p_sub(p_mul(A, A), one)
    D = p_add(p_mul(a2, p_mul(C, C)), one)
    J = p_sub(p_mul(p_lit(4), A), p_lit(5))
    r = p_mul(p_mul(I_, J), p_mul(C, C))
    F = p_add(p_mul(p_mul(a2, D), p_mul(r, r)), one)
    Lam = p_sub(p_add(p_mul(C, D), one), A)
    G = p_add(A, p_mul(F, Lam))
    H = p_add(C, p_mul(F, Z))
    I = p_add(p_mul(p_sub(p_mul(G, G), one), p_mul(H, H)), one)
    C2 = p_mul(C, C)
    sig = p_mul(p_mul(p_lit(1024), p_mul(C, p_mul(C2, C2))), I_)
    return D, F, I, sig


def pos_check(p, top):
    if top[0] < 1:
        return False
    kappa = nu = 0
    for m, c in p:
        if any(m[k] > top[k] for k in range(4)):
            return False
        if m == top:
            kappa += c
        elif c < 0:
            if not m[0] < top[0]:
                return False
            nu += c
    return kappa * M_BOUND + nu > 0


def shift(p):
    """Translate A = x+3, C = y+1, i = u+1, Z = v+1 (dict form)."""
    cur = dict(p)
    for k, s in enumerate((3, 1, 1, 1)):
        nxt = {}
        for e, c in cur.items():
            for j in range(e[k] + 1):
                e2 = list(e); e2[k] = j; e2 = tuple(e2)
                nxt[e2] = nxt.get(e2, 0) + c * math.comb(e[k], j) * s ** (e[k] - j)
        cur = {e: c for e, c in nxt.items() if c}
    return cur


def terms_of(path):
    t = json.loads(path.read_bytes())
    need(t['symbols'] == ['A', 'C', 'i', 'Z'], path.name + ' symbols')
    return {tuple(x['powers']): x['coefficient'] for x in t['terms']}


def model_checks(d):
    Pi = block(d, p_add, p_mul, p_lit, *X)
    need(dict(Pi) == terms_of(PKG / 'data/saturated_corrected_P.json') and len(Pi) == 333,
         'block = saturated_corrected_P.json (333 terms)')
    D, F, I, sig = registers()
    defect = p_sub(p_mul(Pi, Pi), p_mul(p_mul(sig, sig), p_mul(p_mul(D, F), I)))
    gap = p_sub(Pi, p_mul(X[0], D))
    need(pos_check(defect, TOP_DEF), 'posCheck defect')
    need(pos_check(gap, TOP_GAP), 'posCheck gap')
    cert = terms_of(PKG / 'data/saturated_corrected_certificate.json')
    need(shift(defect) == cert and len(cert) == 36309 and min(cert.values()) > 0,
         'translated defect = the 36,309-term positive certificate')
    kb = kron_bounds(d, defect)
    return defect, dict(pi_terms=len(Pi), defect_terms=len(defect), gap_terms=len(gap),
                        certificate_terms=len(cert), **kb)


# ---------------------------------------------------------------- exact model of Kron.split
# A value is (pos, neg, pdeg, ndeg): the values at a point of split(e) and their syntactic degrees.
def z_pw(k, n, pt):
    return (pt[k] ** n, 0, tuple(n if j == k else 0 for j in range(4)), (0, 0, 0, 0))


def z_lit(n):
    return (max(n, 0), max(-n, 0), (0, 0, 0, 0), (0, 0, 0, 0))


def mx(u, v): return tuple(max(x, y) for x, y in zip(u, v))
def ad(u, v): return tuple(x + y for x, y in zip(u, v))


def z_add(x, y): return (x[0] + y[0], x[1] + y[1], mx(x[2], y[2]), mx(x[3], y[3]))
def z_sub(x, y): return (x[0] + y[1], x[1] + y[0], mx(x[2], y[3]), mx(x[3], y[2]))


def z_mul(x, y):
    return (x[0] * y[0] + x[1] * y[1], x[0] * y[1] + x[1] * y[0],
            mx(ad(x[2], y[2]), ad(x[3], y[3])), mx(ad(x[2], y[3]), ad(x[3], y[2])))


def z_terms(l, pt):
    pos = neg = 0
    dg = (0, 0, 0, 0)
    for m, c in l:
        v = pt[0] ** m[0] * pt[1] ** m[1] * pt[2] ** m[2] * pt[3] ** m[3]
        pos += max(c, 0) * v
        neg += max(-c, 0) * v
        dg = mx(dg, m)
    return (pos, neg, dg, dg)


def id_value(d, defect, pt):
    a, c, i, z = (z_pw(k, 1, pt) for k in range(4))
    one = z_lit(1)
    Pi = block(d, z_add, z_mul, z_lit, a, c, i, z)
    a2 = z_sub(z_mul(a, a), one)
    D = z_add(z_mul(a2, z_mul(c, c)), one)
    r = z_mul(z_mul(i, z_sub(z_mul(z_lit(4), a), z_lit(5))), z_mul(c, c))
    F = z_add(z_mul(z_mul(a2, D), z_mul(r, r)), one)
    G = z_add(a, z_mul(F, z_sub(z_add(z_mul(c, D), one), a)))
    H = z_add(c, z_mul(F, z))
    I = z_add(z_mul(z_sub(z_mul(G, G), one), z_mul(H, H)), one)
    c2 = z_mul(c, c)
    sig = z_mul(z_mul(z_lit(1024), z_mul(c, z_mul(c2, c2))), i)
    rad = z_mul(z_mul(z_mul(D, F), I), z_mul(sig, sig))
    return z_sub(z_sub(z_mul(Pi, Pi), rad), z_terms(defect, pt))


BOX = (37, 49, 13, 3)


def kron_bounds(d, defect):
    v = id_value(d, defect, (1, 1, 1, 1))
    need(all(x < b for x, b in zip(v[2], BOX)) and all(x < b for x, b in zip(v[3], BOX)), 'degree box')
    k = max(v[0], v[1]).bit_length() + 1
    X0 = 1 << k
    need(v[0] < X0 and v[1] < X0, 'coefficient bound')
    pt = (X0, X0 ** BOX[0], X0 ** (BOX[0] * BOX[1]), X0 ** (BOX[0] * BOX[1] * BOX[2]))
    w = id_value(d, defect, pt)
    need(w[0] == w[1], 'Kronecker evaluation: pos = neg')
    return dict(kron_bits=k, pos_at_one_bits=v[0].bit_length(), neg_at_one_bits=v[1].bit_length(),
                pos_degrees=list(v[2]), neg_degrees=list(v[3]), kron_value_bits=w[0].bit_length())


# ---------------------------------------------------------------- Lean rendering
def ref(k):
    return LEAVES.get(k, f'x{k}')


def tree_text(items):
    """Balanced `TT` literal over leaf texts / subtree names."""
    if len(items) == 1:
        return items[0]
    h = len(items) // 2
    return f'(.node {tree_text(items[:h])}\n  {tree_text(items[h:])})'


def lit_chunks(defect, size=256):
    """The defect as a balanced term tree over the terms sorted by Kronecker index."""
    srt = sorted(defect, key=lambda t: (t[0][3], t[0][2], t[0][1], t[0][0]))
    out, names = [], []
    for j in range(0, len(srt), size):
        leaves = [f'(.leaf (Mon.mk {m[0]} {m[1]} {m[2]} {m[3]}) ({c}))' for m, c in srt[j:j + size]]
        name = f'defT{j // size}'
        names.append(name)
        out.append(f'def {name} : TT :=\n  {tree_text(leaves)}')
    return ('\n\n'.join(out) + '\n\n/-- The 2,599-term defect `Π² − σ²DFI` as a balanced term tree '
            '(terms sorted by Kronecker index). -/\ndef defT : TT :=\n  ' + tree_text(names) + '\n')


def render(d, pin, defect, kbits):
    ns = d['nodes']
    lines = ['  let x409 := mul c c']
    for k in range(LO, HI + 1):
        nd = ns[k]
        if nd['kind'] == 'literal':
            lines.append(f'  let x{k} := lit ({nd["value"]})')
        else:
            lines.append(f'  let x{k} := {nd["kind"]} {ref(nd["left"])} {ref(nd["right"])}')
    lines.append(f'  x{HI}')
    body = '\n'.join(lines)
    return HEADER.replace('@PIN@', pin) + f'''/-- The JSON nodes 435–1367 (`V₁ = Π(A, C, i, Z)` in Horner form) over arbitrary operations:
`a, c, i, z` are the register nodes `A` (373), `C` (5), `i` (6), `Z` (425), and `x409 = c·c`. -/
def piBlock {{T : Type*}} (add mul : T → T → T) (lit : ℤ → T) (a c i z : T) : T :=
{body}

''' + TAIL.replace('@LIT@', lit_chunks(defect)).replace('@K@', str(kbits))


HEADER = '''import DiophantineConsistency.Nine121.Kron4

/-! # Package 101's complete-radical majorant and its positivity certificate

Generated by `research/nine-positive-p101-1057-endpoint/tools/generate_n1057_majorant.py` from
`101-constructive-reductions/nine/equations/boundary_complete.json` (SHA-256 `@PIN@`).

`piBlock` is the JSON circuit of `V₁ = Π(A, C, i, Z)` (nodes 435–1367, Horner form) over arbitrary
operations; `PiR` is its value in a commutative ring and `PiS` its sparse polynomial (333 terms,
equal to the package's `data/saturated_corrected_P.json`; checked by the generator).

`majorant`: for `a ≥ 2²⁰` and `c, i, z ≥ 1` in an ordered commutative ring,
`D F I σ² < Π²` with `σ = 1024c⁵i`, `D = (a² − 1)c² + 1`, `F = (a² − 1)D(i(4a − 5)c²)² + 1`,
`G = a + F(cD + 1 − a)`, `H = c + Fz`, `I = (G² − 1)H² + 1`, and `aD < Π`.

The proof is a kernel computation: `defS = Π² − σ²DFI` (2,599 terms) and `gapS = Π − aD` are
recomputed from these formulas by `SP4` arithmetic and certified by `SP4.posCheck` (every monomial
divides `a¹⁸c⁴⁸i¹²z²`, resp. `a¹⁸c²⁴i⁶z`, negative coefficients sit below the top `a`-degree, and
`κ·2²⁰ + ν > 0`). The package certifies the same defect differently: its translate by
`a = x + 3, c = y + 1, i = u + 1, z = v + 1` is the 36,309-term positive certificate
`data/saturated_corrected_certificate.json` (that equality is checked by the generator, not
in Lean; Lean only uses the domination form, which needs `a ≥ 2²⁰`). -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Nine121.N1057Majorant
open SP4

'''

TAIL = '''/-- `Π` in a commutative ring. -/
def PiR {R : Type*} [CommRing R] (a c i z : R) : R :=
  piBlock (fun x y => x + y) (fun x y => x * y) (fun k => (k : R)) a c i z

/-- `Π` as a sparse polynomial. -/
def PiS : Poly := piBlock Poly.add Poly.mul Poly.lit X0 X1 X2 X3

section Ring
variable {R : Type*} [CommRing R]

/-- The saturated registers of the radicand. -/
def Dr (a c : R) : R := (a ^ 2 - 1) * c ^ 2 + 1
def Fr (a c i : R) : R := (a ^ 2 - 1) * Dr a c * (i * (4 * a - 5) * c ^ 2) ^ 2 + 1
def Gr (a c i : R) : R := a + Fr a c i * (c * Dr a c + 1 - a)
def Hr (a c i z : R) : R := c + Fr a c i * z
def Ir (a c i z : R) : R := (Gr a c i ^ 2 - 1) * Hr a c i z ^ 2 + 1
def sig (c i : R) : R := 1024 * c ^ 5 * i

theorem ev_PiS (a c i z : R) : ev a c i z PiS = PiR a c i z := by
  simp only [PiS, PiR, piBlock, ev_add, ev_mul, ev_lit, ev_X0, ev_X1, ev_X2, ev_X3]

end Ring

def one : Poly := Poly.lit 1
def DS : Poly := (((X0.mul X0).sub one).mul (X1.mul X1)).add one

/-- `Π − aD`. -/
def gapS : Poly := PiS.sub (X0.mul DS)

theorem gapS_check : posCheck ⟨18, 24, 6, 1⟩ 1048576 gapS = true := by decide +kernel

/-! ## The defect identity, by one Kronecker evaluation -/

open Kron

@LIT@
def aZ : ZE := .pw 0 1
def cZ : ZE := .pw 1 1
def iZ : ZE := .pw 2 1
def zZ : ZE := .pw 3 1
def oneZ : ZE := .lit 1
def PiZ : ZE := piBlock ZE.add ZE.mul ZE.lit aZ cZ iZ zZ
def DZ : ZE := .add (.mul (.sub (.mul aZ aZ) oneZ) (.mul cZ cZ)) oneZ
def rZ : ZE := .mul (.mul iZ (.sub (.mul (.lit 4) aZ) (.lit 5))) (.mul cZ cZ)
def FZ : ZE := .add (.mul (.mul (.sub (.mul aZ aZ) oneZ) DZ) (.mul rZ rZ)) oneZ
def GZ : ZE := .add aZ (.mul FZ (.sub (.add (.mul cZ DZ) oneZ) aZ))
def HZ : ZE := .add cZ (.mul FZ zZ)
def IZ : ZE := .add (.mul (.sub (.mul GZ GZ) oneZ) (.mul HZ HZ)) oneZ
def sigZ : ZE := .mul (.mul (.lit 1024) (.mul cZ (.mul (.mul cZ cZ) (.mul cZ cZ)))) iZ
/-- `Π² − DFIσ² − defect`. -/
def idZ : ZE := .sub (.sub (.mul PiZ PiZ) (.mul (.mul (.mul DZ FZ) IZ) (.mul sigZ sigZ))) (.terms defT)

/-- The Kronecker check in the box `37 × 49 × 13 × 3` at `X = 2^@K@`. -/
theorem id_check : kcheckK 37 49 13 3 @K@ (split idZ).1 (split idZ).2 = true := by
  decide +kernel

/-- The defect is dominated by its top term `a¹⁸c⁴⁸i¹²z²` for `a ≥ 2²⁰`. -/
theorem def_check : posCheckT ⟨18, 48, 12, 2⟩ 1048576 defT = true := by decide +kernel

section Ring
variable {R : Type*} [CommRing R] (a c i z : R)

theorem ev_DS : ev a c i z DS = Dr a c := by
  simp only [DS, one, Dr, ev_add, ev_sub, ev_mul, ev_lit, ev_X0, ev_X1, Int.cast_one]; ring

theorem ev_gapS : ev a c i z gapS = PiR a c i z - a * Dr a c := by
  simp only [gapS, ev_sub, ev_mul, ev_PiS, ev_DS, ev_X0]

theorem zeval_PiZ : PiZ.eval a c i z = PiR a c i z := by
  simp only [PiZ, PiR, piBlock, aZ, cZ, iZ, zZ, zeval_add, zeval_mul, zeval_lit, zeval_pw, sel, pow_one]

theorem zeval_DZ : DZ.eval a c i z = Dr a c := by
  simp only [DZ, oneZ, aZ, cZ, Dr, zeval_add, zeval_sub, zeval_mul, zeval_lit, zeval_pw, sel, pow_one,
    Int.cast_one]; ring

theorem zeval_FZ : FZ.eval a c i z = Fr a c i := by
  simp only [FZ, rZ, oneZ, aZ, cZ, iZ, Fr, zeval_add, zeval_sub, zeval_mul, zeval_lit, zeval_pw, sel,
    pow_one, zeval_DZ, Int.cast_one, Int.cast_ofNat]; ring

theorem zeval_GZ : GZ.eval a c i z = Gr a c i := by
  simp only [GZ, oneZ, aZ, cZ, Gr, zeval_add, zeval_sub, zeval_mul, zeval_lit, zeval_pw, sel, pow_one,
    zeval_DZ, zeval_FZ, Int.cast_one]

theorem zeval_HZ : HZ.eval a c i z = Hr a c i z := by
  simp only [HZ, cZ, zZ, Hr, zeval_add, zeval_mul, zeval_pw, sel, pow_one, zeval_FZ]

theorem zeval_IZ : IZ.eval a c i z = Ir a c i z := by
  simp only [IZ, oneZ, Ir, zeval_add, zeval_sub, zeval_mul, zeval_lit, zeval_GZ, zeval_HZ,
    Int.cast_one]; ring

theorem zeval_sigZ : sigZ.eval a c i z = sig c i := by
  simp only [sigZ, cZ, iZ, sig, zeval_mul, zeval_lit, zeval_pw, sel, pow_one, Int.cast_ofNat]; ring

/-- **The defect identity** `Π² − DFIσ² = defect` in every commutative ring. -/
theorem defect_eq : PiR a c i z ^ 2 - Dr a c * Fr a c i * Ir a c i z * sig c i ^ 2 =
    ev a c i z ⟨defT.toList⟩ := by
  have h := zero_of_kcheckK 37 49 13 3 @K@ idZ id_check a c i z
  simp only [idZ, zeval_sub, zeval_mul, zeval_terms, zeval_PiZ, zeval_DZ, zeval_FZ, zeval_IZ,
    zeval_sigZ] at h
  unfold ev
  linear_combination h

end Ring

/-- **The complete-radical majorant**: `DFIσ² < Π²` and `aD < Π` for `a ≥ 2²⁰`, `c, i, z ≥ 1`. -/
theorem majorant {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R] {a c i z : R}
    (ha : 1048576 ≤ a) (hc : 1 ≤ c) (hi : 1 ≤ i) (hz : 1 ≤ z) :
    Dr a c * Fr a c i * Ir a c i z * sig c i ^ 2 < PiR a c i z ^ 2 ∧ a * Dr a c < PiR a c i z := by
  have haM : ((1048576 : ℕ) : R) ≤ a := by rw [Nat.cast_ofNat]; exact ha
  have ha1 : (1 : R) ≤ a := le_trans (by norm_num) ha
  have h1 := pos_of_check _ _ ⟨defT.toList⟩ (by rw [← posCheckT_eq]; exact def_check) haM ha1 hc hi hz
  have h2 := pos_of_check _ _ gapS gapS_check haM ha1 hc hi hz
  rw [← defect_eq] at h1
  rw [ev_gapS] at h2
  exact ⟨by linarith, by linarith⟩

end Nine121.N1057Majorant

#print axioms Nine121.N1057Majorant.majorant
'''


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--check', action='store_true')
    args = ap.parse_args()
    pin = PIN
    d = load(SRC, pin)
    defect, stats = model_checks(d)
    text = render(d, pin, defect, stats['kron_bits'])
    if args.check:
        need(LEAN.read_text(encoding='utf-8') == text, 'generated file differs: ' + LEAN.name)
    else:
        LEAN.write_text(text, encoding='utf-8', newline='\n')
    print(json.dumps({'status': 'PASS' if args.check else 'GENERATED', 'pin': pin, **stats}))


if __name__ == '__main__':
    main()
