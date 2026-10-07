/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.BigOperators
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.Linarith

namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

variable {ι : Type*} [Fintype ι]

noncomputable def preparedUniformDegreeTolerance (t : ι → ℝ) (Qσ : ℝ) : ℝ :=
  min (∏ i, t i) (Real.exp (-Qσ))

noncomputable def preparedUniformDegreeScaleLog (pRadius : ℝ) (Ptail : ι → ℝ)
    (Qσ : ℝ) : ℝ :=
  pRadius + ∑ i, Ptail i + Qσ

theorem preparedUniformDegreeTolerance_bounds (t Ptail : ι → ℝ)
    {pRadius Qσ : ℝ} (ht : ∀ i, 0 < t i) (ht1 : ∀ i, t i ≤ 1)
    (hPtail : ∀ i, 0 ≤ Ptail i) (hinv : ∀ i, (t i)⁻¹ ≤ Real.exp (Ptail i))
    (hQσ : 0 ≤ Qσ) (hpRadius : 0 ≤ pRadius) :
    let σ := preparedUniformDegreeTolerance t Qσ
    let Pscale := preparedUniformDegreeScaleLog pRadius Ptail Qσ
    0 < σ ∧ σ ≤ 1 ∧ (∀ i, σ ≤ t i) ∧ σ ≤ Real.exp (-Qσ) ∧
      σ⁻¹ ≤ Real.exp Pscale ∧ 0 ≤ Pscale ∧ (∀ i, Ptail i ≤ Pscale) := by
  classical
  dsimp only
  have hprod : 0 < ∏ i, t i := Finset.prod_pos (fun i _ => ht i)
  have hprod1 : ∏ i, t i ≤ 1 :=
    Finset.prod_le_one₀ (fun i _ => (ht i).le) (fun i _ => ht1 i)
  have hprodi (i : ι) : ∏ j, t j ≤ t i := by
    simpa only [Finset.prod_singleton] using
      (Finset.prod_le_prod_of_subset_of_le_one₀ (Finset.subset_univ {i})
        (fun j _ => (ht j).le) (fun j _ _ => ht1 j))
  have hsum : 0 ≤ ∑ i, Ptail i := Finset.sum_nonneg (fun i _ => hPtail i)
  have hsumScale : (∑ i, Ptail i) ≤ preparedUniformDegreeScaleLog pRadius Ptail Qσ := by
    unfold preparedUniformDegreeScaleLog
    linarith only [hpRadius, hQσ]
  have hQScale : Qσ ≤ preparedUniformDegreeScaleLog pRadius Ptail Qσ := by
    unfold preparedUniformDegreeScaleLog
    linarith only [hpRadius, hsum]
  have hprodInv : (∏ i, t i)⁻¹ ≤ Real.exp (∑ i, Ptail i) := by
    rw [← Finset.prod_inv_distrib, Real.exp_sum]
    exact Finset.prod_le_prod₀ (fun i _ => inv_nonneg.mpr (ht i).le) (fun i _ => hinv i)
  refine ⟨lt_min hprod (Real.exp_pos _), (min_le_left _ _).trans hprod1,
    fun i => (min_le_left _ _).trans (hprodi i), min_le_right _ _, ?_,
    hsum.trans hsumScale, ?_⟩
  · unfold preparedUniformDegreeTolerance
    rcases le_total (∏ i, t i) (Real.exp (-Qσ)) with h | h
    · rw [min_eq_left h]
      exact hprodInv.trans (Real.exp_le_exp.mpr hsumScale)
    · rw [min_eq_right h, ← Real.exp_neg, neg_neg]
      exact Real.exp_le_exp.mpr hQScale
  · intro i
    exact (Finset.single_le_sum (fun j _ => hPtail j) (Finset.mem_univ i)).trans hsumScale

end Erdos3.VectorPolynomial

end

end OAI
