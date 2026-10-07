import OAI.Combinatorics.Progressions.Fourier.LogCharacterBudget

namespace OAI

section

namespace Erdos3.NilpotentLieBCHGroup

open Module
open scoped NNReal ENNReal

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [IsScalarTower ℚ ℝ L] [TopologicalSpace L] [IsTopologicalAddGroup L]
  [ContinuousSMul ℝ L] [T2Space L]
  {s H : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

theorem central_logCharacter_coset_dist_le (e : Basis ι ℝ L) (c : ι → ι → ι → ℚ)
    (hstructure : ∀ i j k, algebraMap ℚ ℝ (c i j k) = e.repr ⁅e i, e j⁆ k)
    (hc : ∀ i j k, RationalHeightLE (c i j k) H)
    (Γ T : Subgroup (NilpotentLieBCHGroup L s hnil))
    (hΓ : IsClosed (Γ : Set (NilpotentLieBCHGroup L s hnil)))
    (hT : ∀ z ∈ T, ∀ v : L, ⁅z.coord, v⁆ = 0)
    (η : L →ₗ[ℝ] ℝ) (A : ℝ≥0) (hη : ∀ x, |η x| ≤ A * ‖e.equivFun x‖)
    (hint : ∀ γ ∈ Γ, ∃ n : ℤ, η γ.coord = n) (x y : T) :
    letI := quotientMetricSpace e Γ hΓ
    dist (logCharacter η x.val) (logCharacter η y.val) ≤
      logCharacterMetricConstant s (Fintype.card ι) H A *
        dist (QuotientGroup.mk x.val : _ ⧸ Γ) (QuotientGroup.mk y.val) := by
  let := rightMetricSpace (hnil := hnil) e
  let := rightMetricSpace_isIsometricSMul (hnil := hnil) e
  let := quotientMetricSpace e Γ hΓ
  let K := logCharacterMetricConstant s (Fintype.card ι) H A
  have hdist (γ : Γ) : dist (logCharacter η x.val) (logCharacter η y.val) ≤
      K * dist x.val (y.val * γ.val) := by
    rw [dist_eq_norm, logCharacter_norm_sub_eq_relative η x.val y.val γ.val
      (hT x.val x.property) (hT y.val y.property) (logCharacter_of_integral η γ.val (hint γ.val γ.property))]
    have h := logCharacter_dist_one_le e c hstructure hc η A hη (y.val * γ.val * x.val⁻¹)
    have heq : dist (1 : NilpotentLieBCHGroup L s hnil) (y.val * γ.val * x.val⁻¹) =
        dist x.val (y.val * γ.val) := by
      simpa only [mul_inv_cancel] using dist_mul_right x.val (y.val * γ.val) x.val⁻¹
    exact h.trans_eq (congrArg (fun r : ℝ => (K : ℝ) * r) heq)
  have he : edist (logCharacter η x.val) (logCharacter η y.val) ≤
      (K : ℝ≥0∞) * edist (QuotientGroup.mk x.val : _ ⧸ Γ) (QuotientGroup.mk y.val) := by
    rw [quotientMetricSpace_edist_mk, ENNReal.mul_iInf (by simp)]
    apply le_iInf
    intro γ
    simpa only [edist_dist, ENNReal.ofReal_mul K.coe_nonneg, ENNReal.ofReal_coe_nnreal] using
      ENNReal.ofReal_le_ofReal (hdist γ)
  have h := ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.coe_ne_top (edist_ne_top _ _)) he
  simpa only [ENNReal.toReal_mul, ENNReal.coe_toReal, edist_dist,
    ENNReal.toReal_ofReal dist_nonneg] using h

end Erdos3.NilpotentLieBCHGroup

end

end OAI
