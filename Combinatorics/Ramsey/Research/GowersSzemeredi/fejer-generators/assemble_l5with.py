"""Proofs16Lemma5With: Lemma 16.5's two proof steps with (θ₁, ζ) as parameters."""
import re
from pathlib import Path

GS = Path(r'C:\ProveIt\.claude\worktrees\q-fabius-deformations-merge-9bc27b\Combinatorics\Ramsey\Lean\GowersSzemeredi')


def block(path, start, end_marker):
    s = (GS / path).read_text(encoding='utf-8')
    i = s.index(start)
    j = s.index(end_marker, i + len(start))
    return s[i:j]


def sub(t, pairs):
    for a, b in pairs:
        assert a in t, ('missing', a[:70])
        t = t.replace(a, b)
    return t


sel = block('Proofs16ArrangementSelection.lean',
            'theorem section16_good_sidelengths_of_arrangements',
            '/-- The averaging part of Lemma 16.5 for a structured pair. -/')
sel = sub(sel, [
    ('theorem section16_good_sidelengths_of_arrangements', 'theorem section16_good_sidelengths_with'),
    ('    (theta gamma : Real) (B : Finset (Point N (k + 1)))', '    (t1 : Real) (B : Finset (Point N (k + 1)))'),
    ('    (htheta : 0 < theta) (hgamma : 0 < gamma)\n', '    (ht1 : 0 ≤ t1)\n'),
    ('  have ht : 0 ≤ t := by dsimp [t, section16ThetaOne]; positivity\n',
     '  have ht : 0 ≤ t := by dsimp [t]; exact mul_nonneg (div_nonneg ht1 (by norm_num)) (by positivity)\n'),
])
sel = sel.replace('section16ThetaOne theta gamma k', 't1')
LEFT = re.compile(r'section16ThetaOne|section16Zeta|\btheta\b')
assert not LEFT.search(sel), [l for l in sel.split('\n') if LEFT.search(l)]

mod = block('Proofs16Lemma5.lean',
            'theorem section16_selected_side_model',
            '/-- Exact companion for Lemma 16.5. -/')
mod = sub(mod, [
    ('theorem section16_selected_side_model', 'theorem section16_selected_side_model_with'),
    ('    (theta gamma : Real) (B : Finset (Point N (k + 1)))', '    (t1 zeta : Real) (B : Finset (Point N (k + 1)))'),
    ('    (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1)\n',
     '    (ha0 : 0 < t1 / 4) (haS : t1 / 4 ≤ 1 / 36)\n'
     '    (hzeta : ∀ alpha : Real, t1 / 4 ≤ alpha → alpha ≤ 1 / 6 → zeta ≤ section10Zeta alpha)\n'),
    ('  obtain ⟨ha, haSmall⟩ := section16_density_parameter_bounds k ht ht1 hg hg1\n',
     '  have ha : 0 < a := ha0\n  have haSmall : a ≤ 1 / 36 := haS\n'),
    ('  have htheta1 : 0 ≤ section16ThetaOne theta gamma k := by\n    unfold section16ThetaOne; positivity\n',
     '  have htheta1 : 0 ≤ t1 := by linarith\n'),
    ('(section16_zeta_le_section10Zeta k ht ht1 hg hg1 halpha halpha1)', '(hzeta alpha halpha halpha1)'),
])
mod = mod.replace('section16ThetaOne theta gamma k', 't1').replace('section16Zeta theta gamma k', 'zeta')
assert not LEFT.search(mod), [l for l in mod.split('\n') if LEFT.search(l)]

HEADER = '''import GowersSzemeredi.Proofs16Lemma5
import GowersSzemeredi.Proofs16TightRadius

/-! **Lemma 16.5 with the arrangement density and the Bohr radius as
parameters** (Notes L.16d).

The proof of Lemma 16.5 (`Proofs16Lemma5`, `Proofs16ArrangementSelection`)
uses the printed `θ₁ = section16ThetaOne θ γ k` and
`ζ = section16Zeta θ γ k` only through:
* `0 < θ₁/4 ≤ 1/36`, for the density reparameterization;
* `ζ ≤ section10Zeta α` for every `θ₁/4 ≤ α ≤ 1/6`, for the radius
  comparison with Theorem 10.13.

Here both are parameters `(t1, zeta)`. The two proof steps are the corpus
proofs verbatim, with `section16ThetaOne θ γ k ↦ t1` and
`section16Zeta θ γ k ↦ zeta`:
* `section16_good_sidelengths_with`;
* `section16_selected_side_model_with`.

`lemma_16_5_with` assembles them. Its instances are the printed pair
(`lemma_16_5_with_printed`), and the Fejér density with the tight radius
`tightZeta (t1/4)` (`tightZeta_condition`), which is the input the
propagation of Notes L.16 needs. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

'''

TAIL = '''
/-- **Lemma 16.5 with parameters**: from the arrangement conditions at density
`t1`, many sidelengths carry a Bohr difference model at radius `zeta`. -/
theorem lemma_16_5_with {N k : Nat} [NeZero N] (t1 zeta : Real)
    (B : Finset (Point N (k + 1))) (phi : Point N (k + 1) → ZMod N)
    (ha0 : 0 < t1 / 4) (haS : t1 / 4 ≤ 1 / 36)
    (hzeta : ∀ alpha : Real, t1 / 4 ≤ alpha → alpha ≤ 1 / 6 → zeta ≤ section10Zeta alpha)
    (hB : t1 * (N : Real) ^ (17 * k + 15) ≤ generalArrangementCount 8 B ∧
      (1 - (2 : Real) ^ (-(44 : Real))) * generalArrangementCount 8 B ≤
        respectedGeneralArrangementCount 8 B phi) :
    ∃ H : Finset (Point N k),
      t1 / 4 * (N : Real) ^ (17 * k + 15) ≤
          ∑ h ∈ H, (section16ArrangementCountAtSide 8 B h : Real) ∧
      ∃ Y : (h : Point N k) → Finset (Section16CubeElement B h),
        ∃ psi : Point N k → ZMod N → ZMod N,
          ∀ h, h ∈ H →
            (2 : Real) ^ (-(27 : Real)) * t1 ^ 6 *
                (section16CubeDomain B h).card ≤ (Y h).card ∧
            HasBohrDifferenceModel
              (section16CubeMultifunctionDomain B h)
              (section16InducedCubeMap B h phi)
              (section16LargeSpectrum B h (section16Delta t1)) zeta (Y h) (psi h) := by
  classical
  have ht1 : 0 ≤ t1 := by linarith
  obtain ⟨H, hmass, hgood⟩ := section16_good_sidelengths_with t1 B phi ht1 hB
  refine ⟨H, hmass, ?_⟩
  have hex : ∀ h : Point N k,
      ∃ Y : Finset (Section16CubeElement B h), ∃ psi : ZMod N → ZMod N,
        h ∈ H →
        (2 : Real) ^ (-(27 : Real)) * t1 ^ 6 * (section16CubeDomain B h).card ≤ Y.card ∧
        HasBohrDifferenceModel (section16CubeMultifunctionDomain B h)
          (section16InducedCubeMap B h phi) (section16LargeSpectrum B h (section16Delta t1))
          zeta Y psi := by
    intro h
    by_cases hh : h ∈ H
    · obtain ⟨Y, psi, hY⟩ := section16_selected_side_model_with t1 zeta B phi h ha0 haS hzeta
        (hgood h hh).1 (hgood h hh).2
      exact ⟨Y, psi, fun _ => hY⟩
    · exact ⟨∅, fun _ => 0, fun hmem => (hh hmem).elim⟩
  choose Y psi hY using hex
  exact ⟨Y, psi, hY⟩

/-- The printed parameters satisfy the hypotheses: `lemma_16_5_with` contains
the printed Lemma 16.5's conclusion. -/
theorem lemma_16_5_with_printed_hyps {theta gamma : Real} (k : Nat)
    (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1) :
    0 < section16ThetaOne theta gamma k / 4 ∧ section16ThetaOne theta gamma k / 4 ≤ 1 / 36 ∧
      ∀ alpha : Real, section16ThetaOne theta gamma k / 4 ≤ alpha → alpha ≤ 1 / 6 →
        section16Zeta theta gamma k ≤ section10Zeta alpha := by
  obtain ⟨h0, h1⟩ := section16_density_parameter_bounds k ht ht1 hg hg1
  exact ⟨h0, h1, fun alpha ha ha1 => section16_zeta_le_section10Zeta k ht ht1 hg hg1 ha ha1⟩

/-- The tight radius `tightZeta (t1/4)` satisfies the radius hypothesis for
every density `t1`. -/
theorem tightZeta_condition {t1 : Real} (ha0 : 0 < t1 / 4) :
    ∀ alpha : Real, t1 / 4 ≤ alpha → alpha ≤ 1 / 6 → tightZeta (t1 / 4) ≤ section10Zeta alpha :=
  fun _ ha ha1 => tightZeta_le_section10Zeta ha0 ha ha1

end LeanProofs.GowersSzemeredi
'''
out = HEADER + sel + '\n' + mod + TAIL
(GS / 'Proofs16Lemma5With.lean').write_text(out, encoding='utf-8', newline='\n')
print('wrote', len(out.splitlines()))
