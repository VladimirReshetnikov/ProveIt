import OAI.Combinatorics.Progressions.Estimates.NormalizedTupleParameterBounds

namespace OAI

section

namespace Erdos3

private noncomputable def detectedPhysicalUpper {R : Type*} [Semiring R]
    (m : ℕ) (Q : R) : R := 4 * Q + (m + 1 : ℕ) + 8

private noncomputable def detectedPrecisionUpper {R : Type*} [Semiring R]
    (m : ℕ) (Q : R) : R := coefficientErrorSpatialLog (detectedPhysicalUpper m Q) + 8

private noncomputable def detectedWidthUpper {R : Type*} [Semiring R]
    (m : ℕ) (Q : R) : R :=
  let r := spatialPrimitiveEnvelope (detectedPhysicalUpper m Q) (Q + 32) 0
  2 * (r + spatialTupleToleranceLog r) + 4

private theorem detectedCoefficientErrorSpatialLog_mono {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    coefficientErrorSpatialLog x ≤ coefficientErrorSpatialLog y := by
  dsimp only [coefficientErrorSpatialLog, coefficientErrorVolumeLog, anisotropicSpatialCapLog]
  gcongr; linarith

private theorem detectedWidth_mono {x y a b : ℝ}
    (hx : 0 ≤ x) (ha : 0 ≤ a) (hxy : x ≤ y) (hab : a ≤ b) :
    let r := spatialPrimitiveEnvelope x a 0
    let R := spatialPrimitiveEnvelope y b 0
    2 * (r + spatialTupleToleranceLog r) + 4 ≤
      2 * (R + spatialTupleToleranceLog R) + 4 := by
  dsimp only [spatialPrimitiveEnvelope, spatialTupleToleranceLog,
    spatialDisplacementEnvelope, spatialDiscretizationEnvelope, spatialLipschitzCostEnvelope,
    spatialThresholdEnvelope, spatialBoundaryEnvelope, spatialMovementEnvelope,
    spatialMeshEnvelope, spatialLipschitzEnvelope, spatialFixedProfileEnvelope,
    coefficientErrorVolumeLog, anisotropicSpatialCapLog]
  gcongr <;> linarith

theorem exists_detectedCanonicalPhysicalBudget (m A Cgeom : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {P Pk Qstride gainLog : ℝ} (nX : ℕ),
      0 ≤ P → 0 ≤ Pk → 0 ≤ Qstride → 0 ≤ gainLog →
      let Q := (P + A) ^ A
      Pk ≤ Q → Qstride ≤ Q → gainLog ≤ Q → (nX : ℝ) ≤ Q →
      let Pphysical := Q + Pk + Qstride + nX + (m + 1 : ℕ) + 8
      let coarseTarget := gainLog + 32
      let Eextra := coefficientErrorSpatialLog Pphysical + 8
      let target := gainLog + 32 + Eextra
      let τ := Real.exp (-Pphysical)
      let R := spatialPrimitiveEnvelope Pphysical coarseTarget 0
      let ξLog := 2 * (R + spatialTupleToleranceLog R) + 4
      0 ≤ Eextra ∧ coarseTarget + coefficientErrorSpatialLog Pphysical + 8 = target ∧
      0 < τ ∧ τ ≤ 1 / 2 ∧ (nX : ℝ) * τ ≤ 1 / 2 ∧ 1 / τ = Real.exp Pphysical ∧
      Pphysical ≤ (P + C) ^ C ∧ coarseTarget ≤ (P + C) ^ C ∧
      Eextra ≤ (P + C) ^ C ∧ target ≤ (P + C) ^ C ∧
      ξLog ≤ (P + C) ^ C ∧ (P + Eextra + Cgeom) ^ Cgeom ≤ (P + C) ^ C := by
  let q : Polynomial ℕ := (Polynomial.X + Polynomial.C A) ^ A
  let f := detectedPhysicalUpper m q
  let e := detectedPrecisionUpper m q
  let w := detectedWidthUpper m q
  let total : Polynomial ℕ := f + (q + 32) + e + (q + 32 + e) + w +
    (Polynomial.X + e + Polynomial.C Cgeom) ^ Cgeom
  obtain ⟨C, hC, htotal⟩ := exists_natPolynomial_eval_budget total
  refine ⟨C, hC, ?_⟩
  intro P Pk Qstride gainLog nX hP hPk hQs hg Q hPkQ hQsQ hgQ hnQ
    Pphysical coarseTarget Eextra target τ R ξLog
  have hQ : 0 ≤ Q := by dsimp only [Q]; positivity
  have hp : 0 ≤ Pphysical := by dsimp only [Pphysical]; positivity
  have hc : 0 ≤ coarseTarget := by dsimp only [coarseTarget]; positivity
  have he : 0 ≤ Eextra := by
    dsimp only [Eextra]
    linarith [coefficientErrorSpatialLog_nonneg hp]
  have hphys : Pphysical ≤ detectedPhysicalUpper m Q := by
    dsimp only [Pphysical, detectedPhysicalUpper]
    linarith
  have hcoarse : coarseTarget ≤ Q + 32 := by dsimp only [coarseTarget]; linarith
  have hextra : Eextra ≤ detectedPrecisionUpper m Q := by
    dsimp only [Eextra, detectedPrecisionUpper]
    linarith [detectedCoefficientErrorSpatialLog_mono hp hphys]
  have htarget : target ≤ Q + 32 + detectedPrecisionUpper m Q :=
    add_le_add hcoarse hextra
  have hwidth : ξLog ≤ detectedWidthUpper m Q := detectedWidth_mono hp hc hphys hcoarse
  have hgeom : (P + Eextra + Cgeom) ^ Cgeom ≤
      (P + detectedPrecisionUpper m Q + Cgeom) ^ Cgeom := by gcongr
  have hf0 : 0 ≤ detectedPhysicalUpper m Q := by dsimp only [detectedPhysicalUpper]; positivity
  have he0 : 0 ≤ detectedPrecisionUpper m Q := by
    dsimp only [detectedPrecisionUpper]
    linarith [coefficientErrorSpatialLog_nonneg hf0]
  have hw0 : 0 ≤ detectedWidthUpper m Q := by
    have hr := (spatialPrimitiveEnvelope_bounds hf0 (show 0 ≤ Q + 32 by positivity) le_rfl).1
    have ht := spatialTupleToleranceLog_nonneg hr
    dsimp only [detectedWidthUpper]
    linarith
  have hb := htotal P hP
  have hsum : detectedPhysicalUpper m Q + (Q + 32) + detectedPrecisionUpper m Q +
      (Q + 32 + detectedPrecisionUpper m Q) + detectedWidthUpper m Q +
      (P + detectedPrecisionUpper m Q + Cgeom) ^ Cgeom ≤ (P + C) ^ C := by
    simpa [total, f, e, w, q, Q, detectedPhysicalUpper, detectedPrecisionUpper,
      detectedWidthUpper, spatialPrimitiveEnvelope, spatialTupleToleranceLog,
      spatialDisplacementEnvelope, spatialDiscretizationEnvelope, spatialLipschitzCostEnvelope,
      spatialThresholdEnvelope, spatialBoundaryEnvelope, spatialMovementEnvelope,
      spatialMeshEnvelope, spatialLipschitzEnvelope, spatialFixedProfileEnvelope,
      coefficientErrorSpatialLog, coefficientErrorVolumeLog, anisotropicSpatialCapLog,
      Polynomial.eval₂_pow] using hb
  have hgeom0 : 0 ≤ (P + detectedPrecisionUpper m Q + Cgeom) ^ Cgeom := by positivity
  have hp8 : 8 ≤ Pphysical := by
    dsimp only [Pphysical]
    have hm0 : (0 : ℝ) ≤ (m + 1 : ℕ) := Nat.cast_nonneg _
    linarith [Nat.cast_nonneg (α := ℝ) nX]
  have hnphys : 2 * (nX : ℝ) ≤ Pphysical := by dsimp only [Pphysical]; linarith
  have hτ : 0 < τ := Real.exp_pos _
  have hτhalf : τ ≤ 1 / 2 := by
    dsimp only [τ]
    rw [Real.exp_neg, inv_eq_one_div, div_le_iff₀ (Real.exp_pos _)]
    linarith [Real.add_one_le_exp Pphysical]
  have hnτ : (nX : ℝ) * τ ≤ 1 / 2 := by
    dsimp only [τ]
    rw [Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos _)]
    linarith [Real.add_one_le_exp Pphysical]
  refine ⟨he, by dsimp only [coarseTarget, Eextra, target]; ring,
    hτ, hτhalf, hnτ, by simp [τ, Real.exp_neg], ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals linarith

end Erdos3

end

end OAI
