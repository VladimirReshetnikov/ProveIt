import OAI.Combinatorics.Progressions.Geometry.AllocatedProjectedSpatialComparison

namespace OAI

section

namespace Erdos3.VectorPolynomial

theorem allocatedSpatialLateLog_nonneg {m : ℕ} {G : Type*} [Fintype G]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    {P Q : ℝ} (hP : 0 ≤ P) (hQ : 0 ≤ Q) :
    0 ≤ allocatedSpatialLateLog (G := G) B P Q := by
  have := allocatedAmbientLog_nonneg m hP
  unfold allocatedSpatialLateLog
  positivity

theorem exists_allocatedSpatialLateLog_bound (m : ℕ) :
    ∃ a : ℕ, 2 ≤ a ∧ ∀ {G : Type*} [Fintype G]
      {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
      (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] {P Q T : ℝ},
      0 ≤ P → 0 ≤ Q → P ≤ T → Q ≤ T →
      (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ T →
      allocatedSpatialLateLog (G := G) B P Q ≤ (T + a) ^ a := by
  let scalar : Polynomial ℕ := 7 * (Polynomial.C (layerTailDegree m + 1) * (4 * (Polynomial.X + 8)) + 8)
  let common : Polynomial ℕ := Polynomial.X + Polynomial.X * scalar + 1
  let width : Polynomial ℕ := Polynomial.C (m + 4) * (Polynomial.X + 8)
  let mixed : Polynomial ℕ := (2 * Polynomial.X + 1) * (width + common) + 3 * Polynomial.X + 1
  let ambient : Polynomial ℕ := Polynomial.X + Polynomial.X * (2 * mixed + 4 * Polynomial.X + 9) + 1
  let poly : Polynomial ℕ := 2 * Polynomial.X + 3 +
    Polynomial.C (m * (m + 1)) * (Polynomial.X + 1) ^ m * ambient
  obtain ⟨a, ha, hbound⟩ := exists_natPolynomial_eval_budget poly
  refine ⟨a, ha, ?_⟩
  intro G _ I _ n B _ P Q T hP hQ hPT hQT hvars
  have hT : 0 ≤ T := hP.trans hPT
  have hslots : (Fintype.card (CoefficientSlot (LayerSamplerVariables G I n B) m) : ℝ) ≤
      (m : ℝ) * (m + 1) * (T + 1) ^ m := by
    have h : (Fintype.card (CoefficientSlot (LayerSamplerVariables G I n B) m) : ℝ) ≤
        (m : ℝ) * (m + 1) * ((Fintype.card (LayerSamplerVariables G I n B) : ℝ) + 1) ^ m := by
      exact_mod_cast coefficientSlot_card_le (K := LayerSamplerVariables G I n B) m
    apply h.trans
    gcongr
  have hambient : allocatedAmbientLog m P ≤ allocatedAmbientLog m T := by
    dsimp only [allocatedAmbientLog, allocatedMixedLog, allocatedWidthLog, allocatedCommonLog,
      allocatedScalarLog, integerInterpolationLogEnvelope]
    gcongr
  have hA0 := allocatedAmbientLog_nonneg m hP
  calc
    allocatedSpatialLateLog (G := G) B P Q ≤
        2 * T + 3 + ((m : ℝ) * (m + 1) * (T + 1) ^ m) * allocatedAmbientLog m T := by
      unfold allocatedSpatialLateLog
      gcongr
    _ ≤ _ := by
      simpa [poly, ambient, mixed, width, common, scalar, allocatedAmbientLog, allocatedMixedLog,
        allocatedWidthLog, allocatedCommonLog, allocatedScalarLog, integerInterpolationLogEnvelope,
        Polynomial.eval₂_pow] using hbound T hT

end Erdos3.VectorPolynomial

end

end OAI
