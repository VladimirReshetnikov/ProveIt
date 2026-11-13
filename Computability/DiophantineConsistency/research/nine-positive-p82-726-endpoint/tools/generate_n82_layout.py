#!/usr/bin/env python3
"""Emit Nine121/N82Layout.lean: package 65's shared-tap layout of the package-31 parent source,
the source of package 71's source65 prefix used by package 82's nine-positive equation.

Inputs (inert JSON, SHA-256 pinned below):
  * candidates/gap2082-compact54/data/parent_source.json   the package-31 parent (22 rows, 31 inputs),
    pinned in ../../nine-positive-p101-420-endpoint/tools/generate_n101_layout.py;
  * 65-shared-taps/nine/data/layout.json                   weights and targets (source65 layout);
  * 65-shared-taps/nine/data/kernels.json                  the three shared-tap kernels.

Checks performed before anything is written (exact integer polynomial arithmetic):
  1. the kernels' source hash is the parent's and their variable order is the parent's;
  2. the source rows are the parent rows after the row operations (0-based)
     rho13 = r13 + r1, rho14 = r14 + r2 (layout.json `source_row_operations`, 1-based), with no
     coordinate map (the "unshifted transport source");
  3. the weights are distinct, between 1 and 116, the targets distinct, the largest 1841, the height
     max(2W + deg D2, W + deg D1, deg D0) = 1873, the quadratic leading coefficient 1;
  4. the 22 extraction identities [T^{q_k}](K2 U^2 + K1 U + K0) = 2 rho_k hold coefficient by
     coefficient (all 1 + 31 + 496 coefficients of each row, absent monomials included).

Output: Nine121/N82Layout.lean (literal tables, a SparseCheck completeness certificate and the
extraction identity for `N101Source.transformed`).  Use --check to compare with the file on disk.
"""
from pathlib import Path
import argparse, hashlib, importlib.util, json

HERE = Path(__file__).resolve()
DC = HERE.parents[3]          # Computability/DiophantineConsistency
LEAN = DC / 'Lean/DiophantineConsistency/Nine121/N82Layout.lean'
FORMS = DC / 'con-zfc-diophantine-forms'
P65 = FORMS / '65-shared-taps/nine/data'
PINS = {
    'layout': (P65 / 'layout.json', '0edbd3e778f9f55834ab6dd13a85d72d828f59d74914bcb5a8a469af909c001a'),
    'kernels': (P65 / 'kernels.json', '0d694f61e7217bf0d9742ad7befe24d5854fbed32da35623472ac7bd4a6933ca'),
}
GEN101 = DC / 'research/nine-positive-p101-420-endpoint/tools/generate_n101_layout.py'
PARENT_SHA = '1c336ba0b3c9827ffddcf7ce895cad9dca2907f907cde7484c7f387bb2cb1287'


def need(ok, msg):
    if not ok:
        raise SystemExit('FAIL: ' + msg)


def gen101():
    spec = importlib.util.spec_from_file_location('gen101', GEN101)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def load():
    docs, pins = {}, {}
    for key, (path, pin) in PINS.items():
        raw = path.read_bytes()
        h = hashlib.sha256(raw).hexdigest()
        need(h == pin, 'pin ' + key)
        pins[key] = h
        docs[key] = json.loads(raw)
    return docs, pins


def parent_rows(g):
    """The parent rows, re-read through the 101 generator (which pins the parent's SHA-256)."""
    docs, pins = g.load()
    need(pins['parent'] == PARENT_SHA, 'parent pin')
    parent = docs['parent']
    names = parent['variables'] + parent['constants']
    need(len(parent['variables']) == 31 and parent['constants'] == ['beta', 'K0', 'MC', 'MF'], 'parent order')
    porder = parent['sparse_term_coordinate_order']
    prows = [g.poly_of(eq, porder, names) for eq in parent['equations']]
    need(len(prows) == 22, 'row count')
    return parent, names, prows


def transformed(g, prows, ops):
    rows = [dict(r) for r in prows]
    for tgt, src, mult in ops:          # 1-based (target, source, multiplier)
        need(mult == 1, 'row operation multiplier')
        rows[tgt - 1] = g.add(rows[tgt - 1], prows[src - 1])
    return rows


def kernel_records(kernels):
    ker = {}
    for ch in kernels['kernels']:
        recs = sorted((t['exponent'], {tuple(v['powers']): v['coefficient'] for v in t['coefficient']})
                      for t in ch['terms'])
        need(len({e for e, _ in recs}) == len(recs), 'kernel positions distinct')
        ker[ch['degree']] = recs
    need(sorted(ker) == [0, 1, 2], 'three kernels')
    return ker


def extraction_holds(g, w, E, pos, coef, rows):
    n = 35

    def lift(pp):
        return {(0,) * 31 + m: c for m, c in pp.items()}
    for k in range(22):
        total = {}
        for i in range(31):
            for j in range(31):
                for p in range(len(pos[2])):
                    if w[i] + w[j] + pos[2][p] == E[k]:
                        total = g.add(total, g.mul(g.mul(g.var(i, n), g.var(j, n)), lift(coef[2][p])))
        for i in range(31):
            for p in range(len(pos[1])):
                if w[i] + pos[1][p] == E[k]:
                    total = g.add(total, g.mul(g.var(i, n), lift(coef[1][p])))
        for p in range(len(pos[0])):
            if pos[0][p] == E[k]:
                total = g.add(total, lift(coef[0][p]))
        if total != {m: 2 * c for m, c in rows[k].items()}:
            return False
    return True


def analyse():
    g = gen101()
    docs, pins = load()
    layout, kernels = docs['layout'], docs['kernels']
    parent, names, prows = parent_rows(g)
    need(kernels['source_sha256'] == PARENT_SHA, 'kernel source hash')
    need(kernels['variables'] == parent['variables'], 'kernel variable order')
    need(kernels['ports'] == ['beta', 'K0', 'MC', 'MF'], 'kernel ports')
    ops = layout['source_row_operations']
    need(ops == [[14, 2, 1], [15, 3, 1]], 'row operations')
    rows = transformed(g, prows, ops)
    w = layout['weights']
    need(len(w) == 31 and len(set(w)) == 31 and min(w) == 1 and max(w) == 116 == layout['max_weight'], 'weights')
    order = layout['order']
    need(sorted(order) == list(range(1, 23)), 'target order')
    E = [None] * 22
    for q, r in zip(layout['targets'], order):
        E[r - 1] = q
    need(len(set(E)) == 22 and max(E) == 1841 == layout['maximum_target'], 'targets')
    ker = kernel_records(kernels)
    pos = {d: [e for e, _ in ker[d]] for d in ker}
    coef = {d: [p for _, p in ker[d]] for d in ker}
    need([max(pos[d]) for d in range(3)] == layout['kernel_degrees'] == [1384, 1739, 1641], 'kernel degrees')
    need(max(2 * 116 + 1641, 116 + 1739, 1384) == 1873 == layout['convolution_height'], 'height 1873')
    need(coef[2][-1] == {(0, 0, 0, 0): 1} and pos[2][-1] == 1641, 'leading quadratic coefficient')
    need(all(c for p in coef.values() for c in p), 'nonzero kernel coefficients')
    need(extraction_holds(g, w, E, pos, coef, rows), 'extraction identities')
    S2 = [[(i, j, p) for i in range(31) for j in range(31) for p in range(len(pos[2]))
           if w[i] + w[j] + pos[2][p] == E[k]] for k in range(22)]
    S1 = [[(i, p) for i in range(31) for p in range(len(pos[1])) if w[i] + pos[1][p] == E[k]]
          for k in range(22)]
    S0 = [[p for p in range(len(pos[0])) if pos[0][p] == E[k]] for k in range(22)]
    return dict(g=g, pins=pins, rows=rows, prows=prows, w=w, E=E, pos=pos, coef=coef, S2=S2, S1=S1,
                S0=S0, counts=tuple(len(pos[d]) for d in range(3)))


HEADER = '''set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
set_option synthInstance.maxSize 512
'''


def render(d):
    g = d['g']
    pins = d['pins']
    vec, coefficient = g.vec, g.coefficient
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
    top2 = max(pos[2][:-1])
    return f'''import DiophantineConsistency.Nine121.SparseCheck
import DiophantineConsistency.Nine121.N101Source
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/-! # Package 65's shared-tap layout of the package-31 parent and its coefficient extraction

Generated by `research/nine-positive-p82-726-endpoint/tools/generate_n82_layout.py` from
`65-shared-taps/nine/data/layout.json` (SHA-256 `{pins['layout']}`) and
`kernels.json` (SHA-256 `{pins['kernels']}`). This is the source65 layout of package 71's
prefix, which package 82's nine-positive equation keeps unchanged.

The source is the package-31 parent itself (`Source31Rows.rows`, no coordinate map) after the
row operations `ρ₁₃ = r₁₃ + r₁`, `ρ₁₄ = r₁₄ + r₂`, i.e. `N101Source.transformed`. The weights are
`1 … 116` in the parent order, the targets are listed by row, and the three kernels are the
literal {m0}+{m1}+{m2} shared-tap records (a position serves every row whose complete coefficient
requirement there agrees), with the four ports as parameters.

`S2 k`, `S1 k`, `S0 k` list every quadratic, linear and constant interaction landing on the
`k`-th target; completeness is certified by `SparseCheck` (pair loop with a bit test of the
position masks), and `coeff_target` is the extraction identity
`[T^{{q_k}}](K₂U² + K₁U + K₀) = 2ρ_k` in any commutative ring. -/
{HEADER}namespace Nine121.N82Layout
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
theorem weights_le : ∀ i, weights i ≤ 116 := by decide +kernel
theorem pos0_le : ∀ p, pos0 p ≤ {max(pos[0])} := by decide +kernel
theorem pos1_le : ∀ p, pos1 p ≤ {max(pos[1])} := by decide +kernel
theorem pos2_le : ∀ p, pos2 p ≤ {max(pos[2])} := by decide +kernel
theorem pos2_top : ∀ p : Fin {m2}, p ≠ ⟨{m2 - 1}, by decide⟩ → pos2 p ≤ {max(pos[2]) - 1} := by decide +kernel
theorem pos2_last : pos2 ⟨{m2 - 1}, by decide⟩ = {pos[2][-1]} := by decide +kernel
theorem targets_injective : Function.Injective targets := by decide +kernel
theorem targets_le : ∀ k, targets k ≤ {max(E)} := by decide +kernel

section Coefficients
variable {{R : Type*}} [CommRing R]

def c0 (ports : Fin 4 → R) : Fin {m0} → R := {vec([coefficient(p) for p in coef[0]])}

def c1 (ports : Fin 4 → R) : Fin {m1} → R := {vec([coefficient(p) for p in coef[1]])}

def c2 (ports : Fin 4 → R) : Fin {m2} → R := {vec([coefficient(p) for p in coef[2]])}

theorem c2_last (ports : Fin 4 → R) : c2 ports ⟨{m2 - 1}, by decide⟩ = 1 := by
  simp [c2]

/-- The source polynomial `K₂U² + K₁U + K₀`. -/
noncomputable def sourcePoly (ports : Fin 4 → R) (x : Fin 31 → R) : R[X] :=
  wordPoly weights x ^ 2 * kernelPoly pos2 (c2 ports) + wordPoly weights x * kernelPoly pos1 (c1 ports) +
    kernelPoly pos0 (c0 ports)

/-- The transformed parent rows vanish exactly at the parent's zeros. -/
theorem transformed_zero_iff (ports : Fin 4 → R) (x : Fin 31 → R) :
    (∀ k, N101Source.transformed ports x k = 0) ↔ ∀ k, Source31Rows.rows ports x k = 0 := by
  constructor
  · intro h k
    have e1 : Source31Rows.rows ports x 1 = 0 := by
      simpa [N101Source.transformed] using h 1
    have e2 : Source31Rows.rows ports x 2 = 0 := by
      simpa [N101Source.transformed] using h 2
    have hk := h k
    unfold N101Source.transformed at hk
    split_ifs at hk with h13 h14 <;> simp_all
  · intro h k
    unfold N101Source.transformed
    rw [h k, h 1, h 2]
    simp

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

/-- **The extraction identity** for the source65 layout. -/
theorem coeff_target {{R : Type*}} [CommRing R] (ports : Fin 4 → R) (x : Fin 31 → R) (k : Fin 22) :
    (sourcePoly ports x).coeff (targets k) = 2 * N101Source.transformed ports x k := by
  rw [sourcePoly, coeff_add, coeff_add, quad_expand, lin_expand, kernelPoly,
    coeff_sum_monomial_list _ _ _ _ (S2_nodup k) (hS2 k),
    coeff_sum_monomial_list _ _ _ _ (S1_nodup k) (hS1 k),
    coeff_sum_monomial_list _ _ _ _ (S0_nodup k) (hS0 k)]
  fin_cases k <;> simp [S2, S1, S0, c2, c1, c0, N101Source.transformed, Source31Rows.rows] <;> ring

end Nine121.N82Layout

#print axioms Nine121.N82Layout.coeff_target
'''


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--check', action='store_true')
    args = ap.parse_args()
    d = analyse()
    text = render(d)
    if args.check:
        need(LEAN.read_text(encoding='utf-8') == text, 'generated file differs: N82Layout.lean')
    else:
        LEAN.write_text(text, encoding='utf-8', newline='\n')
    print(json.dumps({'status': 'PASS' if args.check else 'GENERATED', 'records': d['counts'],
                      'interactions': [sum(map(len, d[s])) for s in ('S2', 'S1', 'S0')],
                      'pins': d['pins'], 'top2': max(d['pos'][2][:-1])}, sort_keys=True))


if __name__ == '__main__':
    main()
