#!/usr/bin/env python3
"""Emit Nine121/N105Layout.lean: package 105's H1868 layout of the original31 (gapN86) source.

Inputs (inert JSON, SHA-256 pinned below):
  * 105-bootstrap-certificates/nine/source/h1868/code.json     weights and targets;
  * 105-bootstrap-certificates/nine/source/h1868/kernels.json  the three kernels;
  * through ../../nine-positive-p101-420-endpoint/tools/generate_n101_layout.py: the gapN86 rows
    (re-derived there from the package-31 parent) and package 101's translated layout.

Checks performed before anything is written (exact integer polynomial arithmetic):
  1. the variable order of 105's kernels is the gapN86/101 order;
  2. 105's weights are 101's plus one, 105's targets are 101's plus two, and 105's kernel
     records are 101's with positions shifted by 2, 1, 0 (constant, linear, quadratic kernel)
     and identical port-polynomial coefficients;
  3. independently of (2), the 22 extraction identities [T^{q_k}](K2 U^2 + K1 U + K0) = 2 rho_k
     hold for 105's own weights, targets and kernels;
  4. the weights are distinct, between 1 and 116; the height is 1868; the largest target is 1836.

Output: Nine121/N105Layout.lean (literal tables, the shift identities proved by `decide`, and the
extraction identity deduced from N101Layout.coeff_target through `sourcePoly = X^2 * sourcePoly_101`).
Use --check to compare with the file on disk instead of writing it.
"""
from pathlib import Path
import argparse, hashlib, importlib.util, json

HERE = Path(__file__).resolve()
DC = HERE.parents[3]          # Computability/DiophantineConsistency
LEAN = DC / 'Lean/DiophantineConsistency/Nine121/N105Layout.lean'
FORMS = DC / 'con-zfc-diophantine-forms'
SRC105 = FORMS / '105-bootstrap-certificates/nine/source/h1868'
PINS = {
    'code': (SRC105 / 'code.json', 'd8e94d2a9d5b5e35f32bbc8805916497bfcd9a3bfe9deb7afaeca6a24e324574'),
    'kernels': (SRC105 / 'kernels.json', '8e45487cc7accac8a429b9afc8f089677753d71b558d68f0e25b98dc9ecea1c2'),
}
GEN101 = DC / 'research/nine-positive-p101-420-endpoint/tools/generate_n101_layout.py'
SHIFT = {0: 2, 1: 1, 2: 0}


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
    d101 = g.analyse()                      # re-derives the gapN86 rows from the parent
    docs, pins = load()
    code, kernels = docs['code'], docs['kernels']
    names101 = json.loads((FORMS / '101-constructive-reductions/nine/data/kernels.json').read_text())['variables']
    need(kernels['variables'] == names101, 'kernel variable order')
    w = code['weights']
    E = code['targets_by_row']
    need(w == [x + 1 for x in d101['w']], 'weights = 101 weights + 1')
    need(E == [x + 2 for x in d101['E']], 'targets = 101 targets + 2')
    need(len(set(w)) == 31 and min(w) == 1 and max(w) == 116, 'weights')
    need(len(set(E)) == 22 and max(E) == 1836, 'targets')
    need(code['row_orientations'] == [1] * 22, 'orientations')
    ker = kernel_records(kernels)
    pos = {dd: [e for e, _ in ker[dd]] for dd in ker}
    coef = {dd: [p for _, p in ker[dd]] for dd in ker}
    for dd in range(3):
        need(pos[dd] == [e + SHIFT[dd] for e in d101['pos'][dd]], f'kernel {dd} positions shifted')
        need(coef[dd] == d101['coef'][dd], f'kernel {dd} coefficients')
    need(max(w) * 2 + max(pos[2]) == 1868 and max(w) + max(pos[1]) <= 1868 and max(pos[0]) <= 1868,
         'height 1868')
    need(extraction_holds(g, w, E, pos, coef, d101['rows']), 'extraction identities (105 layout)')
    return dict(pins=pins, w=w, E=E, pos=pos, coef=coef, counts=tuple(len(pos[dd]) for dd in range(3)))


def vec(values):
    return '![' + ', '.join(values) + ']'


def render(d):
    pins = d['pins']
    w, E, pos = d['w'], d['E'], d['pos']
    m0, m1, m2 = d['counts']
    return f'''import DiophantineConsistency.Nine121.N101Layout

/-! # Package 105's H1868 layout of the original31 source and its coefficient extraction

Generated by `research/nine-positive-p105-456-endpoint/tools/generate_n105_layout.py` from
`105-bootstrap-certificates/nine/source/h1868/code.json` (SHA-256 `{pins['code']}`) and
`kernels.json` (SHA-256 `{pins['kernels']}`).

The H1868 layout is the untranslated original31 layout: its weights are package 101's plus one
(`weights_shift`), its targets 101's plus two (`targets_shift`), its constant and linear kernel
positions 101's plus two and plus one, its quadratic positions 101's (`pos0_shift`, `pos1_shift`,
`pos2_shift`), with the same {m0}+{m1}+{m2} port-polynomial coefficients `N101Layout.c0/c1/c2`. Hence
`sourcePoly = X² · N101Layout.sourcePoly` (`sourcePoly_shift`), and the extraction identity
`coeff_target : [T^{{q_k}}](K₂U² + K₁U + K₀) = 2ρ_k` for the gapN86 rows follows from
`N101Layout.coeff_target` without a second sparse certificate. -/
set_option autoImplicit false
namespace Nine121.N105Layout
open Polynomial SparseExtraction

def weights : Fin 31 → ℕ := {vec(list(map(str, w)))}

def targets : Fin 22 → ℕ := {vec(list(map(str, E)))}

def pos0 : Fin {m0} → ℕ := {vec(list(map(str, pos[0])))}

def pos1 : Fin {m1} → ℕ := {vec(list(map(str, pos[1])))}

def pos2 : Fin {m2} → ℕ := {vec(list(map(str, pos[2])))}

theorem weights_shift : ∀ i, weights i = N101Layout.weights i + 1 := by decide +kernel
theorem targets_shift : ∀ k, targets k = N101Layout.targets k + 2 := by decide +kernel
theorem pos0_shift : ∀ p, pos0 p = N101Layout.pos0 p + 2 := by decide +kernel
theorem pos1_shift : ∀ p, pos1 p = N101Layout.pos1 p + 1 := by decide +kernel
theorem pos2_shift : ∀ p, pos2 p = N101Layout.pos2 p := by decide +kernel

theorem weights_injective : Function.Injective weights := fun a b h =>
  N101Layout.weights_injective (by rw [weights_shift, weights_shift] at h; omega)
theorem targets_injective : Function.Injective targets := fun a b h =>
  N101Layout.targets_injective (by rw [targets_shift, targets_shift] at h; omega)
theorem pos0_injective : Function.Injective pos0 := fun a b h =>
  N101Layout.pos0_injective (by rw [pos0_shift, pos0_shift] at h; omega)
theorem pos1_injective : Function.Injective pos1 := fun a b h =>
  N101Layout.pos1_injective (by rw [pos1_shift, pos1_shift] at h; omega)
theorem pos2_injective : Function.Injective pos2 := fun a b h =>
  N101Layout.pos2_injective (by rw [pos2_shift, pos2_shift] at h; exact h)

theorem weights_le : ∀ i, weights i ≤ 116 := by decide +kernel
theorem pos0_le : ∀ p, pos0 p ≤ 1408 := by decide +kernel
theorem pos1_le : ∀ p, pos1 p ≤ 1727 := by decide +kernel
theorem pos2_le : ∀ p, pos2 p ≤ 1636 := by decide +kernel
theorem pos2_top : ∀ p : Fin {m2}, p ≠ ⟨{m2 - 1}, by decide⟩ → pos2 p ≤ 1635 := by decide +kernel
theorem pos2_last : pos2 ⟨{m2 - 1}, by decide⟩ = 1636 := by decide +kernel
theorem targets_le : ∀ k, targets k ≤ 1836 := by decide +kernel

section Coefficients
variable {{R : Type*}} [CommRing R]

/-- The H1868 source polynomial `K₂U² + K₁U + K₀`. -/
noncomputable def sourcePoly (ports : Fin 4 → R) (x : Fin 31 → R) : R[X] :=
  wordPoly weights x ^ 2 * kernelPoly pos2 (N101Layout.c2 ports) +
    wordPoly weights x * kernelPoly pos1 (N101Layout.c1 ports) + kernelPoly pos0 (N101Layout.c0 ports)

theorem wordPoly_shift (x : Fin 31 → R) : wordPoly weights x = X * wordPoly N101Layout.weights x := by
  simp only [wordPoly, Finset.mul_sum, X_mul_monomial, weights_shift]

theorem kernelPoly1_shift (c : Fin {m1} → R) : kernelPoly pos1 c = X * kernelPoly N101Layout.pos1 c := by
  simp only [kernelPoly, Finset.mul_sum, X_mul_monomial, pos1_shift]

theorem kernelPoly0_shift (c : Fin {m0} → R) : kernelPoly pos0 c = X ^ 2 * kernelPoly N101Layout.pos0 c := by
  simp only [kernelPoly, Finset.mul_sum, X_pow_mul_monomial, pos0_shift]

theorem kernelPoly2_shift (c : Fin {m2} → R) : kernelPoly pos2 c = kernelPoly N101Layout.pos2 c := by
  simp only [kernelPoly, pos2_shift]

theorem sourcePoly_shift (ports : Fin 4 → R) (x : Fin 31 → R) :
    sourcePoly ports x = X ^ 2 * N101Layout.sourcePoly ports x := by
  rw [sourcePoly, N101Layout.sourcePoly, wordPoly_shift, kernelPoly1_shift, kernelPoly0_shift,
    kernelPoly2_shift]
  ring

/-- **The extraction identity** for the H1868 layout. -/
theorem coeff_target (ports : Fin 4 → R) (x : Fin 31 → R) (k : Fin 22) :
    (sourcePoly ports x).coeff (targets k) = 2 * N101Source.rows ports x k := by
  rw [sourcePoly_shift, targets_shift, coeff_X_pow_mul, N101Layout.coeff_target]

end Coefficients

end Nine121.N105Layout

#print axioms Nine121.N105Layout.coeff_target
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
    print(json.dumps({'status': 'PASS' if args.check else 'GENERATED', 'records': d['counts'],
                      'pins': d['pins']}, sort_keys=True))


if __name__ == '__main__':
    main()
