"""Proofs16PolyPieceTwoDataWith: dimension-two pieces with (θ₁, ζ) as parameters."""
import re
from pathlib import Path

GS = Path(r'C:\ProveIt\.claude\worktrees\q-fabius-deformations-merge-9bc27b\Combinatorics\Ramsey\Lean\GowersSzemeredi')
LEFT = re.compile(r'section16ThetaOne|section16Zeta|\btheta\b|polyPieceBudget theta|\bht\b|\bht1\b')

src = (GS / 'Proofs16PolyPieceTwoData.lean').read_text(encoding='utf-8')
i = src.index('/-- **A dimension-two piece with its Freiman data, in the original frame.** -/')
j = src.rindex('end LeanProofs.GowersSzemeredi')
thm = src[i:j]


def sub(t, pairs):
    for a, b in pairs:
        assert a in t, ('missing', a[:90])
        t = t.replace(a, b)
    return t


thm = sub(thm, [
    ('theorem section16_poly_piece_two_data\n', 'theorem section16_poly_piece_two_data_with\n'),
    ('    {theta gamma : Real} (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1)\n',
     '    {t1 zeta gamma : Real} (ha0 : 0 < t1 / 4) (haS : t1 / 4 ≤ 1 / 36)\n'
     '    (hzeta : ∀ alpha : Real, t1 / 4 ≤ alpha → alpha ≤ 1 / 6 → zeta ≤ section10Zeta alpha)\n'
     '    (hz0 : 0 < zeta) (hg : 0 < gamma) (hg1 : gamma ≤ 1)\n'),
    ('  obtain ⟨hθ₁pos, hθ₁le, hδpos, hδle⟩ := section16_theta_delta_bounds 1 ht ht1 hg hg1\n',
     '  obtain ⟨hθ₁pos, hθ₁le, hδpos, hδle⟩ := section16_theta_delta_bounds_with ha0 haS\n'),
    ('  obtain ⟨hθ₂pos, hθ₂le⟩ := section16ThetaTwo_pos_le 1 ht ht1 hg hg1\n',
     '  obtain ⟨hθ₂pos, hθ₂le⟩ := section16ThetaTwo_pos_le_with ha0 haS\n'),
    ('    unfold polyPieceBudget; positivity\n', '    unfold polyPieceBudgetW; linarith\n'),
    ('    unfold polyPieceBudget; linarith\n', '    unfold polyPieceBudgetW; linarith\n'),
    ('    rw [hθ\'def, polyPieceBudget]; ring\n', '    rw [hθ\'def, polyPieceBudgetW]; ring\n'),
    ('    section16_dense_induced_selection_of_arrangements (Fact.out : N.Prime) theta gamma B phi\n'
     '      ht ht1 hg hg1 hBarr\n',
     '    section16_dense_induced_selection_with (Fact.out : N.Prime) t1 zeta B phi\n'
     '      ha0 haS hzeta hz0 hBarr\n'),
    ('lemma_16_7_holds N 1 theta gamma B phi H Y phiPrime',
     'lemma_16_7_with t1 zeta hθ₁pos.le B phi H Y phiPrime'),
])
thm = thm.replace('polyPieceBudget theta gamma', 'polyPieceBudgetW t1')
thm = thm.replace('polyPieceSpecCount theta gamma', 'polyPieceSpecCountW t1')
thm = thm.replace('polyPieceFaceCount theta gamma', 'polyPieceFaceCountW t1 gamma')
thm = thm.replace('section16ThetaOne theta gamma 1', 't1').replace('section16Zeta theta gamma 1', 'zeta')
bad = [l for l in thm.split('\n') if LEFT.search(l)]
assert not bad, bad

HEADER = '''import GowersSzemeredi.Proofs16PolyPieceTwoData
import GowersSzemeredi.Proofs16DenseSelectionWith

/-! **Dimension-two pieces with `(θ₁, ζ)` as parameters** (Notes L.16d).

`section16_poly_piece_two_data` builds the pieces of the uniform
dimension-two cover, the seed of the split-class recursion (Notes L.16c).
Its output, `PolyPieceTwoData Γ ζ mass qs qr ql`, is already generic in the
radius and the counts. Only the producer fixes the printed
`θ₁ = section16ThetaOne θ γ 1` and `ζ = section16Zeta θ γ 1`.

* `polyPieceBudgetW t1 = θ₂(t1)/8`, `polyPieceSpecCountW t1` and
  `polyPieceFaceCountW t1 γ`: the deletion budget and the Freiman-family
  counts as functions of the density `t1`. At the printed `t1` they are
  `polyPieceBudget`, `polyPieceSpecCount` and `polyPieceFaceCount`.
* `section16_theta_delta_bounds_with` and `section16ThetaTwo_pos_le_with`:
  the bounds the proof uses, from `0 < t1/4 ≤ 1/36`.
* `section16_poly_piece_two_data_with`: the producer with `(t1, zeta)`. It
  is generated from the corpus proof by a script with a guard that no
  printed parameter survives, and runs through `Proofs16DenseSelectionWith`. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

/-- The deletion budget `θ₂(t1)/8` of a dimension-two piece. -/
def polyPieceBudgetW (t1 : Real) : Real := section16ThetaTwo t1 / 8

/-- The Freiman-family count of the spectrum relation, at density `t1`. -/
def polyPieceSpecCountW (t1 : Real) : Nat :=
  section16BaseFamilyBound (section16Delta t1) (polyPieceBudgetW t1)

/-- The Freiman-family count of the faces and slices, at density `t1`. -/
def polyPieceFaceCountW (t1 gamma : Real) : Nat :=
  section16BaseFamilyBound gamma (polyPieceBudgetW t1)

theorem polyPieceBudgetW_printed (theta gamma : Real) :
    polyPieceBudgetW (section16ThetaOne theta gamma 1) = polyPieceBudget theta gamma := rfl

theorem polyPieceSpecCountW_printed (theta gamma : Real) :
    polyPieceSpecCountW (section16ThetaOne theta gamma 1) = polyPieceSpecCount theta gamma := rfl

theorem polyPieceFaceCountW_printed (theta gamma : Real) :
    polyPieceFaceCountW (section16ThetaOne theta gamma 1) gamma =
      polyPieceFaceCount theta gamma := rfl

theorem section16_theta_delta_bounds_with {t1 : Real} (ha0 : 0 < t1 / 4) (haS : t1 / 4 ≤ 1 / 36) :
    0 < t1 ∧ t1 ≤ 1 ∧ 0 < section16Delta t1 ∧ section16Delta t1 ≤ 1 := by
  refine ⟨by linarith, by linarith, ?_, ?_⟩
  · unfold section16Delta
    exact mul_pos (by positivity) (Real.rpow_pos_of_pos ha0 _)
  · unfold section16Delta
    have h1 : (t1 / 4) ^ ((11 : Real) / 2) ≤ 1 :=
      Real.rpow_le_one ha0.le (by linarith) (by norm_num)
    have h2 : (2 : Real) ^ (-(37 : Real)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
    calc (2 : Real) ^ (-(37 : Real)) * (t1 / 4) ^ ((11 : Real) / 2) ≤ 1 * 1 :=
          mul_le_mul h2 h1 (Real.rpow_nonneg ha0.le _) (by norm_num)
      _ = 1 := by norm_num

theorem section16ThetaTwo_pos_le_with {t1 : Real} (ha0 : 0 < t1 / 4) (haS : t1 / 4 ≤ 1 / 36) :
    0 < section16ThetaTwo t1 ∧ section16ThetaTwo t1 ≤ 1 := by
  have ht : 0 < t1 := by linarith
  have ht1 : t1 ≤ 1 := by linarith
  unfold section16ThetaTwo
  refine ⟨mul_pos (by positivity) (pow_pos ht 8), ?_⟩
  have h1 : t1 ^ 8 ≤ 1 := pow_le_one₀ ht.le ht1
  have h2 : (2 : Real) ^ (-(32 : Real)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  calc (2 : Real) ^ (-(32 : Real)) * t1 ^ 8 ≤ 1 * 1 :=
        mul_le_mul h2 h1 (pow_nonneg ht.le 8) (by norm_num)
    _ = 1 := by norm_num

'''
out = HEADER + thm + 'end LeanProofs.GowersSzemeredi\n'
(GS / 'Proofs16PolyPieceTwoDataWith.lean').write_text(out, encoding='utf-8', newline='\n')
print('wrote', len(out.splitlines()))
