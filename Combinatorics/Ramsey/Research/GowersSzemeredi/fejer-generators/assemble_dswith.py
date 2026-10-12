"""Proofs16DenseSelectionWith: dense induced selection and Lemma 16.7 with (θ₁, ζ) parameters."""
import re
from pathlib import Path

GS = Path(r'C:\ProveIt\.claude\worktrees\q-fabius-deformations-merge-9bc27b\Combinatorics\Ramsey\Lean\GowersSzemeredi')
LEFT = re.compile(r'section16ThetaOne|section16Zeta|\btheta\b|\bgamma\b')


def block(path, start, end_marker):
    s = (GS / path).read_text(encoding='utf-8')
    i = s.index(start)
    j = s.index(end_marker, i + len(start))
    return s[i:j]


def sub(t, pairs):
    for a, b in pairs:
        assert a in t, ('missing', a[:80])
        t = t.replace(a, b)
    return t


ds = block('Proofs16DenseSelection.lean',
           'theorem section16_dense_induced_selection_of_arrangements',
           '/-- One family of actual Bohr-model selections for a structured pair. -/')
ds = sub(ds, [
    ('theorem section16_dense_induced_selection_of_arrangements',
     'theorem section16_dense_induced_selection_with'),
    ('    (hprime : N.Prime) (theta gamma : Real) (B : Finset (Point N (k + 1)))',
     '    (hprime : N.Prime) (t1 zeta : Real) (B : Finset (Point N (k + 1)))'),
    ('    (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1)\n',
     '    (ha0 : 0 < t1 / 4) (haS : t1 / 4 ≤ 1 / 36)\n'
     '    (hzeta : ∀ alpha : Real, t1 / 4 ≤ alpha → alpha ≤ 1 / 6 → zeta ≤ section10Zeta alpha)\n'
     '    (hz0 : 0 < zeta)\n'),
    ('    section16_good_sidelengths_of_arrangements theta gamma B phi ht hg hB\n',
     '    section16_good_sidelengths_with t1 B phi (by linarith) hB\n'),
    ('section16_selected_side_model theta gamma B phi h ht ht1 hg hg1',
     'section16_selected_side_model_with t1 zeta B phi h ha0 haS hzeta'),
    ('    (by unfold section16Zeta; positivity) (fun h hh => (hY h hh).2)',
     '    hz0 (fun h hh => (hY h hh).2)'),
])
ds = ds.replace('section16ThetaOne theta gamma k', 't1').replace('section16Zeta theta gamma k', 'zeta')
assert not LEFT.search(ds), [l for l in ds.split('\n') if LEFT.search(l)]

l7 = block('Proofs16CommonBase.lean', 'theorem lemma_16_7_holds : lemma_16_7 := by',
           'end LeanProofs.GowersSzemeredi')
l7 = sub(l7, [
    ('theorem lemma_16_7_holds : lemma_16_7 := by\n  classical\n  unfold lemma_16_7\n'
     '  intro N k _ theta gamma B phi H1 Y phiPrime\n  dsimp only\n  intro hH hX hY hselection\n'
     '  let theta1 := section16ThetaOne theta gamma k\n'
     '  have htheta1 : 0 ≤ theta1 := by\n    dsimp only [theta1, section16ThetaOne]\n'
     '    exact (Nat.even_pow.mpr ⟨even_two, by positivity⟩).pow_nonneg _\n',
     '''theorem lemma_16_7_with {N k : Nat} [NeZero N] (t1 zeta : Real) (ht1 : 0 ≤ t1)
    (B : Finset (Point N (k + 1))) (phi : Point N (k + 1) → ZMod N)
    (H1 : Finset (Point N k)) (Y : (h : Point N k) → Finset (Section16CubeElement B h))
    (phiPrime : Point N k → ZMod N → ZMod N)
    (hH : t1 / 8 * (N : Real) ^ k ≤ H1.card)
    (hX : ∀ h, h ∈ H1 → t1 / 4 * (N : Real) ^ (k + 1) ≤ (section16CubeDomain B h).card)
    (hY : ∀ h, h ∈ H1 →
      (2 : Real) ^ (-(27 : Real)) * t1 ^ 6 * (section16CubeDomain B h).card ≤ (Y h).card)
    (hselection : Section16InducedSelection B phi H1 Y
      (fun h => section16LargeSpectrum B h (section16Delta t1)) zeta phiPrime) :
    ∃ x0 : Point N k,
      section16ThetaTwo t1 * (N : Real) ^ (k + 1) ≤ section16GoodInducedPairCount B H1 Y x0 ∧
      ∀ z, Section16GoodInducedPair B H1 Y x0 z →
        phiPrime z.1 z.2 = section16CubeValueAtBase phi x0 z.1 z.2 := by
  classical
  let theta1 := t1
  have htheta1 : 0 ≤ theta1 := ht1
'''),
])
assert not LEFT.search(l7), [l for l in l7.split('\n') if LEFT.search(l)]
# the private helpers of Lemma 16.7 (Proofs16CommonBase lines 22-231), renamed
cb = (GS / 'Proofs16CommonBase.lean').read_text(encoding='utf-8').split('\n')
helpers = '\n'.join(cb[21:231])
assert helpers.lstrip().startswith('private abbrev Lemma167Witness'), helpers[:60]
assert 'theorem lemma_16_7_holds' not in helpers
helpers = helpers.replace('lemma167', 'lemma167w').replace('Lemma167', 'Lemma167w')
l7 = l7.replace('lemma167', 'lemma167w').replace('Lemma167', 'Lemma167w')
ds = ds.replace('    hz0 (fun h hh => (hY h hh).2)', '    hz0.le (fun h hh => (hY h hh).2)')

HEADER = '''import GowersSzemeredi.Proofs16Lemma5With
import GowersSzemeredi.Proofs16DenseSelection
import GowersSzemeredi.Proofs16CommonBase

/-! **The dense induced selection and Lemma 16.7 with `(θ₁, ζ)` as
parameters** (Notes L.16d).

* `section16_dense_induced_selection_with`: the corpus's
  `section16_dense_induced_selection_of_arrangements` with
  `section16ThetaOne θ γ k ↦ t1` and `section16Zeta θ γ k ↦ zeta`. It
  assumes `0 < t1/4 ≤ 1/36`, `ζ ≤ section10Zeta α` for `t1/4 ≤ α ≤ 1/6`, and
  `0 < ζ`, and runs through `Proofs16Lemma5With`.
* `lemma_16_7_with`: Lemma 16.7 for any `t1 ≥ 0` and any `zeta`. The
  corpus proof never uses the printed formulas beyond `θ₁ ≥ 0`.

Both proofs are generated from the corpus proofs by a script with a guard
that no printed parameter survives. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

'''
out = HEADER + ds + '\n' + helpers + '\n\n' + l7 + '\nend LeanProofs.GowersSzemeredi\n'
(GS / 'Proofs16DenseSelectionWith.lean').write_text(out, encoding='utf-8', newline='\n')
print('wrote', len(out.splitlines()))
