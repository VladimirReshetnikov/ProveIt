import OAI.Combinatorics.Progressions.Estimates.CanonicalEmptyLayerGeometry
import OAI.Combinatorics.Progressions.Estimates.IndexedComparableScalarGeometryData

namespace OAI

section

namespace Erdos3.VectorPolynomial

theorem exists_preparedScalarSpatialWidthPower (s latePower : ℕ) :
    ∃ widthExponent : ℕ, 2 ≤ widthExponent ∧
      ∀ p : ℝ, 2 ≤ p → ∀ nX : ℕ, (nX : ℝ) ≤ p →
        ∀ S : ℕ, (S : ℝ) ≤ Real.exp ((p + 2) ^ latePower) →
          unconditionedSpatialWidthCutoff ((scalarNativeDimension s : ℝ) * S)
            (unconditionedSpatialTrimFraction nX (Real.exp (-p))) 1 ≤
              Real.exp ((p + 2) ^ widthExponent) := by
  obtain ⟨c, hc⟩ := exists_nat_ge (probabilityProfileLipschitz : ℝ)
  let Q : Polynomial ℕ := Polynomial.C (scalarNativeDimension s) +
    (Polynomial.X + 2) ^ latePower +
      2 * (2 * Polynomial.X + 33 + Polynomial.C c) + 16
  obtain ⟨widthExponent, hwidthExponent, hbudget⟩ :=
    exists_natPolynomial_fixed_power_budget Q
  refine ⟨widthExponent, hwidthExponent, ?_⟩
  intro p hp nX hnX S hS
  let t := (p + 2) ^ latePower
  let P : ℝ := 2 * p + 33 + c
  have hp0 : 0 ≤ p := by linarith
  have ht : 0 ≤ t := by dsimp only [t]; positivity
  have hP : 0 ≤ P := by dsimp only [P]; positivity
  have hdim : (scalarNativeDimension s : ℝ) ≤
      Real.exp (scalarNativeDimension s : ℝ) :=
    le_trans (by linarith) (Real.add_one_le_exp _)
  have hW : (scalarNativeDimension s : ℝ) * S ≤
      Real.exp ((scalarNativeDimension s : ℝ) + t) := by
    calc
      _ ≤ Real.exp (scalarNativeDimension s : ℝ) * Real.exp t :=
        mul_le_mul hdim hS (Nat.cast_nonneg _) (Real.exp_pos _).le
      _ = _ := (Real.exp_add _ _).symm
  have hτ : 0 < unconditionedSpatialTrimFraction nX (Real.exp (-p)) := by
    unfold unconditionedSpatialTrimFraction
    positivity
  have hτP : (unconditionedSpatialTrimFraction nX (Real.exp (-p)))⁻¹ ≤
      Real.exp P := by
    have h32 : (32 : ℝ) ≤ Real.exp 32 := by
      linarith [Real.add_one_le_exp (32 : ℝ)]
    have hnExp : (nX : ℝ) + 1 ≤ Real.exp (p + 1) := by
      linarith [Real.add_one_le_exp (p + 1)]
    calc
      _ = 32 * ((nX : ℝ) + 1) * Real.exp p := by
        simp [unconditionedSpatialTrimFraction, Real.exp_neg]
      _ ≤ Real.exp 32 * Real.exp (p + 1) * Real.exp p := by gcongr
      _ = Real.exp (2 * p + 33) := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
      _ ≤ Real.exp P := Real.exp_le_exp.mpr
        (by dsimp only [P]; linarith [Nat.cast_nonneg (α := ℝ) c])
  have hprofile : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P := by
    have hcExp : (c : ℝ) ≤ Real.exp c :=
      le_trans (by linarith) (Real.add_one_le_exp _)
    exact (hc.trans hcExp).trans
      (Real.exp_le_exp.mpr (by dsimp only [P]; linarith))
  apply (unconditionedSpatialWidthCutoff_le_exp hP
    (show 0 ≤ (scalarNativeDimension s : ℝ) + t by positivity)
    hW hτ hτP hprofile).trans
  apply Real.exp_le_exp.mpr
  simpa [Q, P, t, Polynomial.eval₂_pow] using hbudget p hp0

end Erdos3.VectorPolynomial

end

end OAI
