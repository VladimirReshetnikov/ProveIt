/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.BigOperators
import OAI.Combinatorics.Progressions.Dynamics.JointExceptionalGainBudget
import OAI.Combinatorics.Progressions.Lattices.ModularCoefficientBadPrimeProduct

namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

theorem preparedCenteredForecast_badRadius_bound
    {X : Type*} [Fintype X] (m : ℕ) (stride : X → ℕ)
    {gainLog Qstride : ℝ} (hgainLog : 0 ≤ gainLog)
    (hstride : ∀ x, (stride x : ℝ) ≤ Real.exp Qstride) :
    (((∏ x, stride x) ^ 2 * (smallPrimePowerCorrection (modularCoefficientPrimeThreshold m) *
      quantitativeBadPrimeRadius (gainLog + 8)) : ℕ) : ℝ) ≤
      Real.exp (2 * Fintype.card X * Qstride +
        (smallPrimePowerCorrection (modularCoefficientPrimeThreshold m) : ℝ) + gainLog + 11) := by
  let correction := smallPrimePowerCorrection (modularCoefficientPrimeThreshold m)
  have hprod : ((∏ x, stride x : ℕ) : ℝ) ≤ Real.exp (Fintype.card X * Qstride) := by
    calc
      _ = ∏ x, (stride x : ℝ) := by simp only [Nat.cast_prod]
      _ ≤ ∏ _x : X, Real.exp Qstride :=
        Finset.prod_le_prod₀ (fun x _ => Nat.cast_nonneg (stride x)) (fun x _ => hstride x)
      _ = Real.exp (Fintype.card X * Qstride) := by
        rw [Finset.prod_const, Finset.card_univ, ← Real.exp_nat_mul]
  have hcorrection : (correction : ℝ) ≤ Real.exp correction := by
    linarith [Real.add_one_le_exp (correction : ℝ)]
  have hradius : (quantitativeBadPrimeRadius (gainLog + 8) : ℝ) ≤ Real.exp (gainLog + 11) := by
    simpa only [show gainLog + 8 + 3 = gainLog + 11 by ring] using
      (quantitativeBadPrimeRadius_bounds (show 0 ≤ gainLog + 8 by linarith)).2.1
  have hproduct := mul_le_mul
    (pow_le_pow_left₀ (Nat.cast_nonneg _) hprod 2)
    (mul_le_mul hcorrection hradius (Nat.cast_nonneg _) (Real.exp_nonneg _))
    (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    (sq_nonneg (Real.exp (Fintype.card X * Qstride)))
  calc
    _ = ((∏ x, stride x : ℕ) : ℝ) ^ 2 *
        ((correction : ℝ) * (quantitativeBadPrimeRadius (gainLog + 8) : ℝ)) := by
      simp only [Nat.cast_mul, Nat.cast_pow, correction]
    _ ≤ (Real.exp (Fintype.card X * Qstride)) ^ 2 *
        (Real.exp correction * Real.exp (gainLog + 11)) := hproduct
    _ = _ := by
      rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
      congr 1
      dsimp only [correction]
      ring

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

noncomputable def preparedCenteredForecastThresholdExponent : ℕ :=
  Classical.choose exists_jointSpatialError_polynomial_budget

theorem preparedCenteredForecastThresholdExponent_two_le :
    2 ≤ preparedCenteredForecastThresholdExponent :=
  (Classical.choose_spec exists_jointSpatialError_polynomial_budget).1

theorem preparedCenteredForecast_threshold_inverse {P g : ℝ} {n : ℕ}
    (hP : 0 ≤ P) (hn : 0 < n) (hnP : (n : ℝ) ≤ P) (hg : 0 ≤ g) (hgP : g ≤ P) :
    (spatialMatrixBlockThreshold n (jointSpatialError g))⁻¹ ≤
      Real.exp ((P + preparedCenteredForecastThresholdExponent) ^
        preparedCenteredForecastThresholdExponent) :=
  ((Classical.choose_spec exists_jointSpatialError_polynomial_budget).2 hP hn hnP hg hgP).1

theorem preparedCenteredForecast_half_threshold_inverse {P g : ℝ} {n : ℕ}
    (hP : 0 ≤ P) (hn : 0 < n) (hnP : (n : ℝ) ≤ P) (hg : 0 ≤ g) (hgP : g ≤ P) :
    (spatialMatrixBlockThreshold n (jointSpatialError g) / 2)⁻¹ ≤
      Real.exp ((P + preparedCenteredForecastThresholdExponent) ^
        preparedCenteredForecastThresholdExponent + 2) := by
  have h := preparedCenteredForecast_threshold_inverse hP hn hnP hg hgP
  have hthreshold := spatialMatrixBlockThreshold_pos hn (jointSpatialError_pos g)
  rw [inv_div, div_eq_mul_inv, Real.exp_add]
  have h2 : (2 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
  exact (mul_le_mul h2 h (inv_nonneg.mpr hthreshold.le) (Real.exp_nonneg _)).trans_eq (mul_comm _ _)

noncomputable def preparedCenteredForecastSpatialLog (P : ℝ) : ℝ :=
  P * (P + 1) + ((P + preparedCenteredForecastThresholdExponent) ^
    preparedCenteredForecastThresholdExponent + 2) + P ^ 2 + P

theorem preparedCenteredForecastSpatialLog_nonneg {P : ℝ} (hP : 0 ≤ P) :
    0 ≤ preparedCenteredForecastSpatialLog P := by
  unfold preparedCenteredForecastSpatialLog
  positivity

theorem exists_preparedCenteredForecastSpatialLog_budget :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {P : ℝ}, 0 ≤ P →
      preparedCenteredForecastSpatialLog P ≤ (P + C) ^ C := by
  let X : Polynomial ℕ := Polynomial.X
  let A := preparedCenteredForecastThresholdExponent
  let Q : Polynomial ℕ := X * (X + 1) + ((X + Polynomial.C A) ^ A + 2) + X ^ 2 + X
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget Q
  refine ⟨C, hC, ?_⟩
  intro P hP
  simpa [Q, X, A, preparedCenteredForecastSpatialLog, Polynomial.eval₂_pow] using hbound P hP

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

theorem exists_preparedCenteredForecastPathLog_envelope (m : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {P Qstride gainLog : ℝ} {nX : ℕ},
      0 ≤ P → (nX : ℝ) ≤ P → Qstride ∈ Set.Icc 0 P → gainLog ∈ Set.Icc 0 P →
      preparedCenteredForecastSpatialLog P +
        (2 * nX * Qstride +
          (smallPrimePowerCorrection (modularCoefficientPrimeThreshold m) : ℝ) + gainLog + 11) ≤
        (P + C) ^ C := by
  let X : Polynomial ℕ := Polynomial.X
  let A := preparedCenteredForecastThresholdExponent
  let correction := smallPrimePowerCorrection (modularCoefficientPrimeThreshold m)
  let spatial : Polynomial ℕ :=
    X * (X + 1) + ((X + Polynomial.C A) ^ A + 2) + X ^ 2 + X
  let Q : Polynomial ℕ := spatial + (2 * X ^ 2 + Polynomial.C correction + X + 11)
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget Q
  refine ⟨C, hC, ?_⟩
  intro P Qstride gainLog nX hP hnX hQstride hgainLog
  have hprod : 2 * (nX : ℝ) * Qstride ≤ 2 * P ^ 2 := by
    have hmul := mul_le_mul hnX hQstride.2 hQstride.1 hP
    nlinarith
  have hpolynomial : preparedCenteredForecastSpatialLog P +
      (2 * P ^ 2 + (correction : ℝ) + P + 11) ≤ (P + C) ^ C := by
    simpa [Q, spatial, X, A, preparedCenteredForecastSpatialLog, Polynomial.eval₂_pow] using hbound P hP
  change preparedCenteredForecastSpatialLog P +
    (2 * (nX : ℝ) * Qstride + (correction : ℝ) + gainLog + 11) ≤ _
  linarith [hgainLog.2]

end Erdos3.VectorPolynomial

end

end OAI
