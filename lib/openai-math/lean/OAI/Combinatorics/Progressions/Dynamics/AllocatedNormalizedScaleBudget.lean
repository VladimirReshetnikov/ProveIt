import OAI.Combinatorics.Progressions.Estimates.AllocatedProxyAccuracy

namespace OAI

section

namespace Erdos3.VectorPolynomial

noncomputable def allocatedNormalizedInitialLog {A : Type*} [Semiring A]
    (m : ℕ) (p Pc E T : A) : A :=
  allocatedJointLengthEnvelope m (allocatedComparisonDimension m p) Pc
    (coefficientErrorAccuracyLog (allocatedComparisonDimension m p + 1) (E + 3)) + p * T

noncomputable def allocatedNormalizedScaleInput {A : Type*} [Semiring A]
    (m : ℕ) (p Pc E T : A) : A :=
  allocatedComparisonDimension m p + allocatedNormalizedInitialLog m p Pc E T + Pc + 1

noncomputable def allocatedNormalizedScaleLog {A : Type*} [Semiring A]
    (m : ℕ) (p Pc E T : A) : A :=
  let Q := allocatedNormalizedScaleInput m p Pc E T
  (1 + Q ^ 2) * (5 * Q + 49)

theorem allocatedCoefficientAccuracyLog_nonneg (m : ℕ) {p E : ℝ}
    (hp : 0 ≤ p) (hE : 0 ≤ E) : 0 ≤ allocatedCoefficientAccuracyLog m p E := by
  have hD : 0 ≤ allocatedComparisonDimension m p + 1 :=
    add_nonneg (allocatedComparisonDimension_bounds m hp).1 zero_le_one
  have hs := coefficientErrorSpatialLog_nonneg hD
  have hm := coefficientMajorantMassLog_nonneg hD
  unfold allocatedCoefficientAccuracyLog coefficientErrorAccuracyLog
  positivity

theorem allocatedJointLengthEnvelope_nonneg (m : ℕ) {D p e : ℝ}
    (hD : 0 ≤ D) (hp : 0 ≤ p) (he : 0 ≤ e) :
    0 ≤ allocatedJointLengthEnvelope m D p e := by
  have hi := kernelInverseEnvelope_nonneg hD hp
  have hd := allocatedDensityEnvelope_nonneg m hD hp
  dsimp only [allocatedJointLengthEnvelope, allocatedFrontEnvelope,
    allocatedKernelEnvelope, allocatedAccuracyEnvelope, allocatedTupleEnvelope]
  positivity

theorem allocatedNormalizedScaleBudget_bounds (m : ℕ) {p Pc E T : ℝ}
    (hp : 0 ≤ p) (hPc : 0 ≤ Pc) (hE : 0 ≤ E) (hT : 0 ≤ T) :
    let D := allocatedComparisonDimension m p
    let L := allocatedNormalizedInitialLog m p Pc E T
    let Q := allocatedNormalizedScaleInput m p Pc E T
    0 ≤ L ∧ 0 ≤ Q ∧ D ≤ Q ∧ Pc ≤ Q ∧ L + 1 ≤ Q ∧
      Q ≤ allocatedNormalizedScaleLog m p Pc E T := by
  have hD := (allocatedComparisonDimension_bounds m hp).1
  have he := allocatedCoefficientAccuracyLog_nonneg m hp (show 0 ≤ E + 3 by positivity)
  have hJ := allocatedJointLengthEnvelope_nonneg m hD hPc he
  have hL : 0 ≤ allocatedNormalizedInitialLog m p Pc E T :=
    add_nonneg hJ (mul_nonneg hp hT)
  have hQ : 0 ≤ allocatedNormalizedScaleInput m p Pc E T := by
    unfold allocatedNormalizedScaleInput
    positivity
  refine ⟨hL, hQ, ?_, ?_, ?_, le_allocatedScaleLog hQ⟩
  all_goals dsimp only [allocatedNormalizedScaleInput]; linarith

theorem allocatedRefinedLengthLog_le_normalizedInitial
    {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
    {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    {α : Type*} [Fintype α] {O : Fin m → Type*} [∀ j, Fintype (O j)]
    (rows : ∀ j, O j → Finset α) (hq : Fintype.card α ≤ m + 1)
    (hinj : ∀ j, Function.Injective (rows j))
    (X : Type*) [Fintype X] {p Pc E T : ℝ}
    (hp : 0 ≤ p) (hPc : 0 ≤ Pc) (hE : 0 ≤ E) (hT : 0 ≤ T)
    (hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ p)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ p) (hn : ∀ j, (n j : ℝ) ≤ p)
    (hX : (Fintype.card X : ℝ) ≤ p) :
    allocatedRefinedJointLengthLog (G := G) B α O Pc
      (allocatedCoefficientAccuracyLog m p (E + 3))
      ((m + 1 : ℕ) * Pc + Fintype.card X * T) ≤
        allocatedNormalizedInitialLog m p Pc E T := by
  have hd := allocatedComparisonDimensions_of_primitive B rows hq hinj hp hvars hI hn
  have he := allocatedCoefficientAccuracyLog_nonneg m hp (show 0 ≤ E + 3 by positivity)
  have hlength := allocatedJointLengthLog_le_envelope B hd hPc he
  exact (allocatedRefinedJointLengthLog_stride_cost B α O Pc
    (allocatedCoefficientAccuracyLog m p (E + 3)) (Fintype.card X) hT).trans
      (add_le_add hlength (mul_le_mul_of_nonneg_right hX hT))

end Erdos3.VectorPolynomial

end

end OAI
