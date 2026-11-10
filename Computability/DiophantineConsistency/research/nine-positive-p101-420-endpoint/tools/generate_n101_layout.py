#!/usr/bin/env python3
"""Emit the Lean layout modules of package 101's translated original31 (gapN86) source.

Inputs (inert JSON, SHA-256 pinned below):
  * 66-gap-congruence/source/gapN86_source.json      the 22-row, 31-input positive source;
  * candidates/gap2082-compact54/data/parent_source.json   its parent (package-31 parent);
  * 101-constructive-reductions/nine/data/code.json  the translated weights and targets;
  * 101-constructive-reductions/nine/data/kernels.json  the three translated kernels.

Checks performed before anything is written (all exact integer polynomial arithmetic):
  1. every gapN86 row equals the parent row system after the recorded row operations
     (0-based rho13 = r13 + r1, rho14 = r14 + r2) composed with the affine coordinate map
     P_old = P + eta + zeta, N_old = N + 1;
  2. the weights are distinct, include 0, are at most 115; the targets are distinct;
  3. every quadratic pair is isolated, linear/quadratic spans and cross conditions hold;
  4. the kernels recomputed from the rows, weights and targets equal kernels.json exactly.

Outputs (Lean, generic in a commutative ring R; ports stay parameters):
  Nine121/N101Source.lean, Nine121/N101Geometry.lean, Nine121/N101Certificate.lean.
Use --check to compare with the files on disk instead of writing them.
"""
from collections import defaultdict
from itertools import combinations_with_replacement
from pathlib import Path
import argparse, hashlib, json, sys

HERE = Path(__file__).resolve()
DC = HERE.parents[3]          # Computability/DiophantineConsistency
LEAN = DC / 'Lean/DiophantineConsistency/Nine121'
FORMS = DC / 'con-zfc-diophantine-forms'
INPUTS = {
    'source': (FORMS / '66-gap-congruence/source/gapN86_source.json', None),
    'parent': (DC / 'candidates/gap2082-compact54/data/parent_source.json',
               '1c336ba0b3c9827ffddcf7ce895cad9dca2907f907cde7484c7f387bb2cb1287'),
    'code': (FORMS / '101-constructive-reductions/nine/data/code.json', None),
    'kernels': (FORMS / '101-constructive-reductions/nine/data/kernels.json', None),
}


def need(ok, msg):
    if not ok:
        raise SystemExit('FAIL: ' + msg)


def load():
    docs, pins = {}, {}
    for key, (path, pin) in INPUTS.items():
        raw = path.read_bytes()
        h = hashlib.sha256(raw).hexdigest()
        if pin is not None:
            need(h == pin, 'pin ' + key)
        pins[key] = h
        docs[key] = json.loads(raw)
    return docs, pins


def poly_of(eq, order, names):
    idx = [names.index(v) for v in order]
    out = {}
    for t in eq['terms']:
        m = [0] * len(names)
        for k, e in zip(idx, t['powers']):
            m[k] += e
        m = tuple(m)
        need(m not in out, 'duplicate monomial')
        out[m] = t['coefficient']
    return {m: c for m, c in out.items() if c}


def add(a, b, s=1):
    out = dict(a)
    for m, c in b.items():
        out[m] = out.get(m, 0) + s * c
    return {m: c for m, c in out.items() if c}


def mul(a, b):
    out = defaultdict(int)
    for ma, ca in a.items():
        for mb, cb in b.items():
            out[tuple(x + y for x, y in zip(ma, mb))] += ca * cb
    return {m: c for m, c in out.items() if c}


def power(p, e, n):
    out = {(0,) * n: 1}
    for _ in range(e):
        out = mul(out, p)
    return out


def substitute(poly, images, n):
    out = {}
    for m, c in poly.items():
        term = {(0,) * n: c}
        for i, e in enumerate(m):
            if e:
                term = mul(term, power(images[i], e, n))
        out = add(out, term)
    return out


def var(i, n):
    return {tuple(int(j == i) for j in range(n)): 1}


def grouping(poly):
    result = defaultdict(dict)
    for m, c in sorted(poly.items()):
        result[m[:31]][m[31:]] = c
    return dict(result)


def monomial(m, atom):
    return ' * '.join(atom(i) + (f' ^ {e}' if e > 1 else '') for i, e in enumerate(m) if e) or '1'


def coefficient(poly):
    terms = []
    for m, c in sorted(poly.items()):
        term = monomial(m, lambda i: f'ports {i}')
        if term == '1':
            term = f'({c})'
        elif c == -1:
            term = f'(-({term}))'
        elif c != 1:
            term = f'({c}) * {term}'
        terms.append(term)
    return '(' + ' + '.join(terms) + ')' if terms else '0'


def expression(poly):
    terms = []
    for m, p in sorted(grouping(poly).items()):
        coeff = coefficient(p)
        term = monomial(m, lambda i: f'x {i}')
        if term == '1':
            terms.append(coeff)
        else:
            terms.append(f'{coeff} * ({term})')
    return '(' + ' + '.join(terms) + ')' if terms else '0'


def vec(values):
    return '![' + ',\n    '.join(values) + ']'


def fset(values):
    return '{' + ', '.join(map(str, values)) + '}' if values else '∅'


def pairlit(pair):
    return f'⟨({pair[0]}, {pair[1]}), by decide⟩'


def function(entries, v='i'):
    return '(fun ' + v + ' => ' + ''.join(f'if {v} = {k} then {val} else ' for k, val in entries) + '0)'


def analyse():
    docs, pins = load()
    source, parent, code, kernels = docs['source'], docs['parent'], docs['code'], docs['kernels']
    names = source['variables'] + source['constants']
    need(len(source['variables']) == 31 and source['constants'] == ['beta', 'K0', 'MC', 'MF'], 'source order')
    need(parent['variables'] == source['variables'] and parent['constants'] == source['constants'], 'parent order')
    need(kernels['variables'] == source['variables'], 'kernel variable order')
    n = len(names)
    rows = []
    for i, eq in enumerate(source['equations']):
        need(eq['number'] == i + 1, 'source numbering')
        rows.append(poly_of(eq, names, names))
    porder = parent['sparse_term_coordinate_order']
    need(sorted(porder) == sorted(names), 'parent coordinates')
    prows = [poly_of(eq, porder, names) for eq in parent['equations']]
    need(len(rows) == 22 and len(prows) == 22, 'row counts')
    # (1) affine map and row operations
    ix = {v: names.index(v) for v in names}
    images = [var(i, n) for i in range(n)]
    images[ix['P']] = add(add(var(ix['P'], n), var(ix['eta'], n)), var(ix['zeta'], n))
    images[ix['N']] = add(var(ix['N'], n), {(0,) * n: 1})
    trans = [dict(r) for r in prows]
    trans[13] = add(prows[13], prows[1])
    trans[14] = add(prows[14], prows[2])
    for k in range(22):
        need(substitute(trans[k], images, n) == rows[k], f'row identity {k}')
    # (2) layout
    w = code['weights']
    E = code['targets_by_row']
    need(len(w) == 31 and len(set(w)) == 31 and min(w) == 0 and max(w) == 115, 'weights')
    need(len(E) == 22 and len(set(E)) == 22 and max(E) == 1834, 'targets')
    need(code['row_orientations'] == [1] * 22, 'orientations')
    # (3) kernels as authoritative sparse records
    ker = {}
    for ch in kernels['kernels']:
        recs = sorted((t['exponent'], {tuple(v['powers']): v['coefficient'] for v in t['coefficient']})
                      for t in ch['terms'])
        need(len({e for e, _ in recs}) == len(recs), 'kernel positions distinct')
        ker[ch['degree']] = recs
    need(sorted(ker) == [0, 1, 2], 'three kernels')
    pos = {d: [e for e, _ in ker[d]] for d in ker}
    coef = {d: [p for _, p in ker[d]] for d in ker}
    # (4) target sets and the exact extraction identity (polynomials in x and ports)
    S2 = [[(i, j, p) for i in range(31) for j in range(31) for p in range(len(pos[2]))
           if w[i] + w[j] + pos[2][p] == E[k]] for k in range(22)]
    S1 = [[(i, p) for i in range(31) for p in range(len(pos[1])) if w[i] + pos[1][p] == E[k]]
          for k in range(22)]
    S0 = [[p for p in range(len(pos[0])) if pos[0][p] == E[k]] for k in range(22)]

    def lift(portpoly):
        return {(0,) * 31 + m: c for m, c in portpoly.items()}

    for k in range(22):
        total = {}
        for (i, j, p) in S2[k]:
            total = add(total, mul(mul(var(i, n), var(j, n)), lift(coef[2][p])))
        for (i, p) in S1[k]:
            total = add(total, mul(var(i, n), lift(coef[1][p])))
        for p in S0[k]:
            total = add(total, lift(coef[0][p]))
        need(total == {m: 2 * c for m, c in rows[k].items()}, f'extraction identity at target {k}')
    # (5) heights: every exponent below 1867; the leading quadratic coefficient is 1
    need(max(w) * 2 + max(pos[2]) == 1866 and max(w) + max(pos[1]) <= 1866 and max(pos[0]) <= 1866,
         'height 1866')
    need(coef[2][-1] == {(0, 0, 0, 0): 1}, 'leading quadratic coefficient')
    return dict(pins=pins, rows=rows, w=w, E=E, pos=pos, coef=coef, S2=S2, S1=S1, S0=S0,
                counts=tuple(len(pos[d]) for d in range(3)))

HEADER = '''set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
set_option synthInstance.maxSize 512
'''


def render(d):
    pins = d['pins']
    rows_txt = vec([expression(r) for r in d['rows']])
    src = f'''import DiophantineConsistency.Nine121.Source31Rows
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.Basic

/-! # Package 101's original31 source `gapN86` and its parent

Generated by `research/nine-positive-p101-420-endpoint/tools/generate_n101_layout.py`
from `66-gap-congruence/source/gapN86_source.json` (SHA-256 `{pins['source']}`).
`rows` is the 22-row positive source in the order
`J F α z f h i o j s w τ η ζ y γ N E P c a X D C2 L F2 V g I Baux Δ`, ports `β K MC MF`.
It is the parent (`Source31Rows.rows`) after the row operations `ρ₁₃ = r₁₃ + r₁`,
`ρ₁₄ = r₁₄ + r₂` and the affine map `P_old = P + η + ζ`, `N_old = N + 1`
(`row_identity`). All ports are parameters. -/
{HEADER}namespace Nine121.N101Source

variable {{R : Type*}} [CommRing R]

/-- The literal gapN86 rows. -/
def rows (ports : Fin 4 → R) (x : Fin 31 → R) : Fin 22 → R :=
  {rows_txt}

/-- The affine map to the parent coordinates. -/
def toOld (x : Fin 31 → R) : Fin 31 → R := fun i =>
  if i = 18 then x 18 + x 12 + x 13 else if i = 16 then x 16 + 1 else x i

/-- The parent rows after the two recorded row operations. -/
def transformed (ports : Fin 4 → R) (x : Fin 31 → R) (k : Fin 22) : R :=
  Source31Rows.rows ports x k + (if k = 13 then Source31Rows.rows ports x 1 else 0) +
    (if k = 14 then Source31Rows.rows ports x 2 else 0)

theorem row_identity (ports : Fin 4 → R) (x : Fin 31 → R) (k : Fin 22) :
    rows ports x k = transformed ports (toOld x) k := by
  fin_cases k <;> simp [rows, transformed, Source31Rows.rows, toOld] <;> ring

theorem zero_iff (ports : Fin 4 → R) (x : Fin 31 → R) :
    (∀ k, rows ports x k = 0) ↔ ∀ k, Source31Rows.rows ports (toOld x) k = 0 := by
  constructor
  · intro h k
    have e1 : Source31Rows.rows ports (toOld x) 1 = 0 := by
      have := h 1; rw [row_identity] at this; simpa [transformed] using this
    have e2 : Source31Rows.rows ports (toOld x) 2 = 0 := by
      have := h 2; rw [row_identity] at this; simpa [transformed] using this
    have hk := h k
    rw [row_identity] at hk
    unfold transformed at hk
    split_ifs at hk with h13 h14 <;> simp_all
  · intro h k
    rw [row_identity]
    unfold transformed
    rw [h k, h 1, h 2]
    simp

end Nine121.N101Source
'''
    w, E, pos, coef = d['w'], d['E'], d['pos'], d['coef']
    m0, m1, m2 = (len(pos[k]) for k in range(3))
    def tr(t):
        return '(' + ', '.join(str(v) for v in t) + ')'
    def lst(items):
        return '[' + ', '.join(items) + ']'
    S2 = vec([lst([tr(t) for t in s]) for s in d['S2']])
    S1 = vec([lst([tr(t) for t in s]) for s in d['S1']])
    S0 = vec([lst([str(p) for p in s]) for s in d['S0']])
    mask2 = sum(1 << p for p in set(pos[2]))
    mask1 = sum(1 << p for p in set(pos[1]))
    chk2 = '\n\n'.join(
        f'theorem chk2_ok_{k} : chkI (targets {k}) mask2 wL ((S2 {k}).map pairOf) 0 wL = true := by\n'
        f'  decide +kernel' for k in range(22))
    exacts2 = ', '.join(f'chk2_ok_{k}' for k in range(22))
    lay = f'''import DiophantineConsistency.Nine121.SparseCheck
import DiophantineConsistency.Nine121.N101Source
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/-! # Package 101's translated original31 layout and its coefficient extraction

Generated by `research/nine-positive-p101-420-endpoint/tools/generate_n101_layout.py`
from `101-constructive-reductions/nine/data/code.json` (SHA-256 `{pins['code']}`) and
`data/kernels.json` (SHA-256 `{pins['kernels']}`). The weights are the original31
weights translated down by one (so `J` sits at radix position zero), the
targets are translated down by two, and the three kernels are the literal
{m0}+{m1}+{m2} sparse records, with the four ports as parameters.

`S2 k`, `S1 k`, `S0 k` list every quadratic, linear and constant interaction
landing on the `k`-th target, including those of positions shared between rows;
`coeff_target` is the extraction identity `[T^{{q_k}}](K₂U² + K₁U + K₀) = 2ρ_k`
for the gapN86 rows in any commutative ring.

Completeness of the index lists is certified by `SparseCheck`: a pair loop over the
weights with one bit test of the position masks `mask2`, `mask1` per pair (`chk2_ok_k`,
`chk1_ok`), turned into the exact characterisations `hS2`, `hS1` by `quad_iff`/`lin_iff`. -/
{HEADER}namespace Nine121.N101Layout
open Polynomial SparseExtraction SparseCheck

def weights : Fin 31 → ℕ := {vec(list(map(str, w)))}

def targets : Fin 22 → ℕ := {vec(list(map(str, E)))}

def pos0 : Fin {m0} → ℕ := {vec(list(map(str, pos[0])))}

def pos1 : Fin {m1} → ℕ := {vec(list(map(str, pos[1])))}

def pos2 : Fin {m2} → ℕ := {vec(list(map(str, pos[2])))}

theorem weights_injective : Function.Injective weights := by decide +kernel
theorem pos0_injective : Function.Injective pos0 := by decide +kernel
theorem pos1_injective : Function.Injective pos1 := by decide +kernel
theorem pos2_injective : Function.Injective pos2 := by decide +kernel
theorem weights_le : ∀ i, weights i ≤ 115 := by decide +kernel
theorem pos0_le : ∀ p, pos0 p ≤ 1406 := by decide +kernel
theorem pos1_le : ∀ p, pos1 p ≤ 1726 := by decide +kernel
theorem pos2_le : ∀ p, pos2 p ≤ 1636 := by decide +kernel
theorem pos2_top : ∀ p : Fin {m2}, p ≠ ⟨{m2 - 1}, by decide⟩ → pos2 p ≤ 1635 := by decide +kernel
theorem pos2_last : pos2 ⟨{m2 - 1}, by decide⟩ = 1636 := by decide +kernel
theorem targets_injective : Function.Injective targets := by decide +kernel
theorem targets_le : ∀ k, targets k ≤ 1834 := by decide +kernel

section Coefficients
variable {{R : Type*}} [CommRing R]

def c0 (ports : Fin 4 → R) : Fin {m0} → R := {vec([coefficient(p) for p in coef[0]])}

def c1 (ports : Fin 4 → R) : Fin {m1} → R := {vec([coefficient(p) for p in coef[1]])}

def c2 (ports : Fin 4 → R) : Fin {m2} → R := {vec([coefficient(p) for p in coef[2]])}

theorem c2_last (ports : Fin 4 → R) : c2 ports ⟨{m2 - 1}, by decide⟩ = 1 := by
  simp [c2]

/-- The translated source polynomial `K₂U² + K₁U + K₀`. -/
noncomputable def sourcePoly (ports : Fin 4 → R) (x : Fin 31 → R) : R[X] :=
  wordPoly weights x ^ 2 * kernelPoly pos2 (c2 ports) + wordPoly weights x * kernelPoly pos1 (c1 ports) +
    kernelPoly pos0 (c0 ports)

end Coefficients

def wL : List ℕ := {lst(list(map(str, w)))}

/-- Bit `e` is set iff `e` is a quadratic-kernel position. -/
def mask2 : ℕ := {mask2}

/-- Bit `e` is set iff `e` is a linear-kernel position. -/
def mask1 : ℕ := {mask1}

theorem weights_getD : ∀ i : Fin 31, weights i = wL.getD i 0 := by decide +kernel
theorem mask2_bits : ∀ p, Nat.testBit mask2 (pos2 p) = true := by decide +kernel
theorem mask1_bits : ∀ p, Nat.testBit mask1 (pos1 p) = true := by decide +kernel

def S2 : Fin 22 → List (Fin 31 × Fin 31 × Fin {m2}) :=
  {S2}

def S1 : Fin 22 → List (Fin 31 × Fin {m1}) :=
  {S1}

def S0 : Fin 22 → List (Fin {m0}) :=
  {S0}

/-- The first two coordinates of a quadratic index, as naturals. -/
def pairOf (t : Fin 31 × Fin 31 × Fin {m2}) : ℕ × ℕ := ((t.1 : ℕ), (t.2.1 : ℕ))

-- `List.all` keeps the decision procedure on the listed indices; a binder `∀ t ∈ S2 k` would
-- be decided through the `Fintype` instance over every triple.
theorem S2_all : ∀ k, ((S2 k).all fun t => weights t.1 + weights t.2.1 + pos2 t.2.2 == targets k) = true := by
  decide +kernel
theorem S1_all : ∀ k, ((S1 k).all fun t => weights t.1 + pos1 t.2 == targets k) = true := by
  decide +kernel

theorem S2_mem (k : Fin 22) : ∀ t ∈ S2 k, weights t.1 + weights t.2.1 + pos2 t.2.2 = targets k := by
  intro t ht
  simpa using List.all_eq_true.1 (S2_all k) t ht

theorem S1_mem (k : Fin 22) : ∀ t ∈ S1 k, weights t.1 + pos1 t.2 = targets k := by
  intro t ht
  simpa using List.all_eq_true.1 (S1_all k) t ht
theorem S2_nodup : ∀ k, (S2 k).Nodup := by decide +kernel
theorem S1_nodup : ∀ k, (S1 k).Nodup := by decide +kernel
theorem S0_nodup : ∀ k, (S0 k).Nodup := by decide +kernel

{chk2}

theorem chk2_ok (k : Fin 22) : chkI (targets k) mask2 wL ((S2 k).map pairOf) 0 wL = true := by
  fin_cases k
  exacts [{exacts2}]

theorem chk1_ok : ∀ k : Fin 22, chk1 (targets k) mask1 ((S1 k).map fun t => (t.1 : ℕ)) 0 wL = true := by
  decide +kernel

theorem hS2 (k : Fin 22) : ∀ t, weights t.1 + weights t.2.1 + pos2 t.2.2 = targets k ↔ t ∈ S2 k :=
  quad_iff weights pos2 pos2_injective wL weights_getD rfl mask2 mask2_bits (targets k) (S2 k)
    (S2_mem k) (chk2_ok k)

theorem hS1 (k : Fin 22) : ∀ t, weights t.1 + pos1 t.2 = targets k ↔ t ∈ S1 k :=
  lin_iff weights pos1 pos1_injective wL weights_getD rfl mask1 mask1_bits (targets k) (S1 k)
    (S1_mem k) (chk1_ok k)

theorem hS0 : ∀ k p, pos0 p = targets k ↔ p ∈ S0 k := by decide +kernel

theorem coeff_target {{R : Type*}} [CommRing R] (ports : Fin 4 → R) (x : Fin 31 → R) (k : Fin 22) :
    (sourcePoly ports x).coeff (targets k) = 2 * N101Source.rows ports x k := by
  rw [sourcePoly, coeff_add, coeff_add, quad_expand, lin_expand, kernelPoly,
    coeff_sum_monomial_list _ _ _ _ (S2_nodup k) (hS2 k),
    coeff_sum_monomial_list _ _ _ _ (S1_nodup k) (hS1 k),
    coeff_sum_monomial_list _ _ _ _ (S0_nodup k) (hS0 k)]
  fin_cases k <;> simp [S2, S1, S0, c2, c1, c0, N101Source.rows] <;> ring

end Nine121.N101Layout

#print axioms Nine121.N101Layout.coeff_target
'''
    return {'N101Source.lean': src, 'N101Layout.lean': lay}


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--check', action='store_true')
    args = ap.parse_args()
    d = analyse()
    out = render(d)
    for name, text in out.items():
        path = LEAN / name
        if args.check:
            need(path.read_text(encoding='utf-8') == text, 'generated file differs: ' + name)
        else:
            path.write_text(text, encoding='utf-8', newline='\n')
    print(json.dumps({'status': 'PASS' if args.check else 'GENERATED', 'records': d['counts'],
                      'interactions': [sum(map(len, d[s])) for s in ('S2', 'S1', 'S0')], 'pins': d['pins']}, sort_keys=True))


if __name__ == '__main__':
    main()
