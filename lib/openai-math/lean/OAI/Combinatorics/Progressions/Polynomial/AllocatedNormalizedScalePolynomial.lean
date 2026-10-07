import OAI.Combinatorics.Progressions.Estimates.AllocatedCoverLogBounds
import OAI.Combinatorics.Progressions.Estimates.AllocatedNormalizedScaleChoice

namespace OAI

section

namespace Erdos3.VectorPolynomial

theorem allocatedNormalizedScaleLog_mono (m : ℕ) {p Pc E T p' Pc' E' T' : ℝ}
    (hp : 0 ≤ p) (hPc : 0 ≤ Pc) (hE : 0 ≤ E) (hT : 0 ≤ T)
    (hpp : p ≤ p') (hPcc : Pc ≤ Pc') (hEE : E ≤ E') (hTT : T ≤ T') :
    allocatedNormalizedScaleLog m p Pc E T ≤ allocatedNormalizedScaleLog m p' Pc' E' T' := by
  have hD := (allocatedComparisonDimension_bounds m hp).1
  have hDD := allocatedComparisonDimension_mono m hp hpp
  have hee := coefficientErrorAccuracyLog_mono (show 0 ≤ allocatedComparisonDimension m p + 1 by positivity)
    (add_le_add hDD le_rfl) (add_le_add hEE (le_refl (3 : ℝ)))
  have hJ := allocatedJointLengthEnvelope_mono m hD hPc hDD hPcc hee
  have hL : allocatedNormalizedInitialLog m p Pc E T ≤ allocatedNormalizedInitialLog m p' Pc' E' T' := by
    unfold allocatedNormalizedInitialLog
    exact add_le_add hJ (mul_le_mul hpp hTT hT (hp.trans hpp))
  have hQ : allocatedNormalizedScaleInput m p Pc E T ≤ allocatedNormalizedScaleInput m p' Pc' E' T' := by
    unfold allocatedNormalizedScaleInput
    exact add_le_add (add_le_add (add_le_add hDD hL) hPcc) le_rfl
  have hQ0 := (allocatedNormalizedScaleBudget_bounds m hp hPc hE hT).2.1
  have hQ' : 0 ≤ allocatedNormalizedScaleInput m p' Pc' E' T' := hQ0.trans hQ
  dsimp only [allocatedNormalizedScaleLog]
  gcongr

theorem exists_allocatedNormalizedScaleLog_bound (m : ℕ) :
    ∃ a : ℕ, 2 ≤ a ∧ ∀ {p Pc E T : ℝ}, 0 ≤ p → 0 ≤ Pc → 0 ≤ E → 0 ≤ T →
      allocatedNormalizedScaleLog m p Pc E T ≤ (p + Pc + E + T + a) ^ a := by
  let poly : Polynomial ℕ := allocatedNormalizedScaleLog m Polynomial.X Polynomial.X Polynomial.X Polynomial.X
  obtain ⟨a, ha, hbound⟩ := exists_natPolynomial_eval_budget poly
  refine ⟨a, ha, ?_⟩
  intro p Pc E T hp hPc hE hT
  have hmono := allocatedNormalizedScaleLog_mono m hp hPc hE hT
    (show p ≤ p + Pc + E + T by linarith) (show Pc ≤ p + Pc + E + T by linarith)
    (show E ≤ p + Pc + E + T by linarith) (show T ≤ p + Pc + E + T by linarith)
  apply hmono.trans
  simpa [poly, allocatedNormalizedScaleLog, allocatedNormalizedScaleInput,
    allocatedNormalizedInitialLog, allocatedJointLengthEnvelope, allocatedFrontEnvelope,
    allocatedAccuracyEnvelope, allocatedTupleEnvelope, allocatedKernelEnvelope,
    allocatedDensityEnvelope, kernelOutputEnvelope, kernelGeometryEnvelope, kernelInverseEnvelope,
    coefficientErrorAccuracyLog, coefficientErrorSpatialLog, coefficientMajorantMassLog,
    coefficientErrorVolumeLog, anisotropicSpatialCapLog, allocatedComparisonDimension,
    Polynomial.eval₂_pow] using hbound (p + Pc + E + T) (by positivity)

theorem exists_allocatedNormalizedScale_polynomial_upper (m : ℕ) :
    ∃ a : ℕ, 2 ≤ a ∧ ∀ {G : Type*} [Fintype G]
      {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
      (B : LayerSamplerAxis I n → Type*) [∀ v, Fintype (B v)]
      {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
      (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
      {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
      {p Pc E T : ℝ}, 0 ≤ p → 0 ≤ Pc → 0 ≤ E → 0 ≤ T →
      (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ p →
      (∀ j, (n j : ℝ) ≤ p) → (∀ j, (R j)⁻¹ ≤ Real.exp Pc) → (∀ j, (σ j)⁻¹ ≤ Real.exp Pc) →
      ((allocatedNormalizedScale (G := G) B U b hR hσ p Pc E T).value : ℝ) ≤
        Real.exp ((p + Pc + E + T + a) ^ a) := by
  obtain ⟨a, ha, hlog⟩ := exists_allocatedNormalizedScaleLog_bound m
  refine ⟨a, ha, ?_⟩
  intro G _ I _ n B _ J _ U b R σ hR hσ p Pc E T hp hPc hE hT hvars hn hRi hσi
  exact (allocatedNormalizedScale_upper B U b hR hσ hp hPc hE hT hvars hn hRi hσi).trans
    (Real.exp_le_exp.mpr (hlog hp hPc hE hT))

end Erdos3.VectorPolynomial

end

end OAI
