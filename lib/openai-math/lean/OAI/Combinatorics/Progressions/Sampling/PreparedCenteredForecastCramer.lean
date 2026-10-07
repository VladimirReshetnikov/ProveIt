import OAI.Combinatorics.Progressions.Linear.FixedSpatialKernelSliceDensity
import OAI.Combinatorics.Progressions.Probability.FixedSpatialDensityBudget

namespace OAI

section

namespace Erdos3.VectorPolynomial

variable {G X T : Type*} [Fintype X] [DecidableEq X]

theorem preparedCenteredForecast_cramer_bounds
    (e : G ≃ X ⊕ (X ⊕ T)) (W L : ℝ) (z : Option G × X → ℝ)
    {P B H κ0 κ1 : ℝ} (hP : 0 ≤ P) (hX : (Fintype.card X : ℝ) ≤ P)
    (hH : H ∈ Set.Icc (0 : ℝ) 1) (hκ0 : 0 < κ0) (hκ1 : 0 < κ1)
    (hi0 : κ0⁻¹ ≤ Real.exp B) (hi1 : κ1⁻¹ ≤ Real.exp B)
    (hentry : ∀ i j, |fixedSpatialKernelBlock e W L z false i j| ≤ H)
    (hdet0 : κ0 ≤ |(fixedSpatialKernelBlock e W L z false).det|)
    (hdet1 : κ1 ≤ |(fixedSpatialKernelBlock e W L z true).det|) :
    ∃ h0 : (fixedSpatialKernelBlock e W L z false).det ≠ 0,
    ∃ h1 : (fixedSpatialKernelBlock e W L z true).det ≠ 0,
      inverseJacobian (fixedSpatialKernelBlockEquiv e W L z true h1) ≤
        Real.exp (B + P ^ 2 + P) ∧
      ‖(fixedSpatialKernelBlockEquiv e W L z false h0).symm.toContinuousLinearMap‖ ≤
        Real.exp (B + P ^ 2 + P) := by
  have h0 : (fixedSpatialKernelBlock e W L z false).det ≠ 0 :=
    abs_pos.mp (hκ0.trans_le hdet0)
  have h1 : (fixedSpatialKernelBlock e W L z true).det ≠ 0 :=
    abs_pos.mp (hκ1.trans_le hdet1)
  refine ⟨h0, h1, ?_, ?_⟩
  · rw [fixedSpatialKernelBlockEquiv_jacobian]
    exact ((inv_anti₀ hκ1 hdet1).trans hi1).trans
      (Real.exp_le_exp.mpr (by nlinarith [sq_nonneg P]))
  · have hnorm := (matrixSupCLM_inverse_norm_le (fixedSpatialKernelBlock e W L z false)
      hH.1 hentry hκ0 hdet0).2
    rw [← fixedSpatialKernelBlockEquiv_coe e W L z false h0,
      ContinuousLinearMap.inverse_equiv] at hnorm
    have hfac := factorial_le_exp_square (Fintype.card X) hP hX
    have hpow : H ^ (Fintype.card X - 1) ≤ 1 := pow_le_one₀ hH.1 hH.2
    have hXexp : (Fintype.card X : ℝ) ≤ Real.exp P :=
      hX.trans (by linarith [Real.add_one_le_exp P])
    have hinner : ((Fintype.card X).factorial : ℝ) * H ^ (Fintype.card X - 1) / κ0 ≤
        Real.exp (P ^ 2) * Real.exp B := by
      rw [div_eq_mul_inv]
      apply mul_le_mul _ hi0 (inv_nonneg.mpr hκ0.le) (Real.exp_nonneg _)
      exact (mul_le_mul_of_nonneg_left hpow (Nat.cast_nonneg _)).trans
        (by simpa only [mul_one] using hfac)
    calc
      _ ≤ Fintype.card X * ((Fintype.card X).factorial * H ^ (Fintype.card X - 1) / κ0) :=
        hnorm
      _ ≤ Real.exp P * (Real.exp (P ^ 2) * Real.exp B) :=
        mul_le_mul hXexp hinner
          (div_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hH.1 _)) hκ0.le)
          (Real.exp_nonneg _)
      _ = Real.exp (B + P ^ 2 + P) := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        ring

end Erdos3.VectorPolynomial

end

end OAI
