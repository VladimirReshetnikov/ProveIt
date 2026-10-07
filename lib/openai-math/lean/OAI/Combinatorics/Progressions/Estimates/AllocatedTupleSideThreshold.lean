import OAI.Combinatorics.Progressions.Polynomial.AllocatedSpatialLogPolynomial

namespace OAI

section

namespace Erdos3

noncomputable def tupleEarlyLogEnvelope {A : Type*} [Semiring A] (p E : A) : A :=
  p + (p ^ 3 + anisotropicSpatialCapLog p) + (coefficientErrorVolumeLog p + 4) +
    spatialDisplacementEnvelope p + E + 3

noncomputable def tupleWidthLogEnvelope {A : Type*} [Semiring A] (p E : A) : A :=
  2 * (tupleEarlyLogEnvelope p E + spatialTupleToleranceLog (tupleEarlyLogEnvelope p E)) + 4

noncomputable def tupleLateLogEnvelope {A : Type*} [Semiring A] (p E l : A) : A :=
  spatialDiscretizationEnvelope p l + spatialMeshEnvelope p l + spatialLipschitzCostEnvelope p l +
    spatialTupleToleranceLog (tupleEarlyLogEnvelope p E) + E + 3 + 2 * l +
    (1 + 2 * p) + (1 + 2 * p) * p + p + 40

noncomputable def tupleSideLogEnvelope {A : Type*} [Semiring A] (p E l : A) : A :=
  3 * tupleLateLogEnvelope p E l + tupleWidthLogEnvelope p E + 3 * l + 17

theorem tupleLogEnvelopes_nonneg {p E l : ℝ} (hp : 0 ≤ p) (hE : 0 ≤ E) (hl : 0 ≤ l) :
    0 ≤ tupleEarlyLogEnvelope p E ∧ 0 ≤ tupleWidthLogEnvelope p E ∧
      0 ≤ tupleLateLogEnvelope p E l ∧ 0 ≤ tupleSideLogEnvelope p E l := by
  dsimp only [tupleEarlyLogEnvelope, tupleWidthLogEnvelope, tupleLateLogEnvelope, tupleSideLogEnvelope,
    spatialTupleToleranceLog, spatialDiscretizationEnvelope, spatialMeshEnvelope,
    spatialLipschitzCostEnvelope, spatialLipschitzEnvelope, spatialDisplacementEnvelope,
    spatialFixedProfileEnvelope, anisotropicSpatialCapLog, coefficientErrorVolumeLog]
  exact ⟨by positivity, by positivity, by positivity, by positivity⟩

theorem normalizedTuple_log_envelopes (X N : Type*) [Fintype X] [Fintype N]
    {G : Type*} [Fintype G] {q : ℕ} (s : Fin q ↪ G) {p E l : ℝ}
    (hp : 0 ≤ p) (hE : 0 ≤ E) (hl : 0 ≤ l)
    (hq : (Fintype.card (Unit ⊕ Fin q) : ℝ) ≤ p)
    (hG : (Fintype.card G : ℝ) ≤ p) (hN : (Fintype.card N : ℝ) ≤ p)
    (hX : (Fintype.card X : ℝ) ≤ p) :
    normalizedTupleWidthLog N s p E ≤ tupleWidthLogEnvelope p E ∧
      normalizedTupleSideLog X N s p E l ≤ tupleSideLogEnvelope p E l := by
  obtain ⟨he, hd, hcoords⟩ := spatialAuxiliaryDimensions (N := N) s hG hN
  have hdis := spatialDisplacementLog_le_envelope _ _ _ _ hp hq hd he hN
  have hearly : anisotropicTupleEarlyBudget N s p (E + 3) ≤ tupleEarlyLogEnvelope p E := by
    unfold anisotropicTupleEarlyBudget tupleEarlyLogEnvelope
    linarith
  have hearly0 := (anisotropicTupleEarlyBudget_bounds N s hp (by linarith : 0 ≤ E + 3)).1
  have ht : spatialTupleToleranceLog (anisotropicTupleEarlyBudget N s p (E + 3)) ≤
      spatialTupleToleranceLog (tupleEarlyLogEnvelope p E) := by
    unfold spatialTupleToleranceLog
    gcongr
  have hw : normalizedTupleWidthLog N s p E ≤ tupleWidthLogEnvelope p E := by
    unfold normalizedTupleWidthLog tupleWidthLogEnvelope
    linarith
  have hA := spatialDiscretizationLog_le_envelope _ _ hp hl hq hd
  have hT := anisotropicSpatialMeshLog_le_envelope _ _ hp hl hq hd
  have hprof := spatialProfileLog_le_fixedEnvelope _ _ hp hq (he.trans (by linarith))
  have hK : p ^ 3 + anisotropicSpatialCapLog p +
      2 * spatialProfileLog (Fintype.card (Unit ⊕ Fin q)) (Fintype.card (UnselectedColumn s)) p + l + 1 ≤
        spatialLipschitzCostEnvelope p l := by
    unfold spatialLipschitzCostEnvelope spatialLipschitzEnvelope
    linarith
  have hprod : (Fintype.card (Option (G ⊕ N) × X) : ℝ) ≤ (1 + 2 * p) * p := by
    simp only [Fintype.card_prod, Nat.cast_mul]
    exact mul_le_mul hcoords hX (Nat.cast_nonneg _) (by positivity)
  have hlate : normalizedTupleLateBudget X N s p E l ≤ tupleLateLogEnvelope p E l := by
    unfold normalizedTupleLateBudget tupleLateLogEnvelope
    linarith
  refine ⟨hw, ?_⟩
  unfold normalizedTupleSideLog tupleSideLogEnvelope
  linarith

theorem tupleSideLogEnvelope_mono {p E l P F L : ℝ}
    (hp : 0 ≤ p) (hE : 0 ≤ E) (hl : 0 ≤ l) (hP : p ≤ P) (hF : E ≤ F) (hL : l ≤ L) :
    tupleSideLogEnvelope p E l ≤ tupleSideLogEnvelope P F L := by
  have hP0 : 0 ≤ P := hp.trans hP
  dsimp only [tupleEarlyLogEnvelope, tupleWidthLogEnvelope, tupleLateLogEnvelope, tupleSideLogEnvelope,
    spatialTupleToleranceLog, spatialDiscretizationEnvelope, spatialMeshEnvelope,
    spatialLipschitzCostEnvelope, spatialLipschitzEnvelope, spatialDisplacementEnvelope,
    spatialFixedProfileEnvelope, anisotropicSpatialCapLog, coefficientErrorVolumeLog]
  gcongr

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

theorem exists_allocatedTupleSideThreshold_bound (m : ℕ) :
    ∃ a : ℕ, 2 ≤ a ∧ ∀ {G : Type*} [Fintype G]
      {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
      (B : LayerSamplerAxis I n → Type*) [∀ i, Fintype (B i)]
      (X : Type*) [Fintype X] {q : ℕ} (s : Fin q ↪ G) {P Q p E : ℝ},
      0 ≤ P → 0 ≤ Q → 0 ≤ p → 0 ≤ E → P ≤ Q → p ≤ Q → E ≤ Q →
      (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ p →
      (Fintype.card X : ℝ) ≤ p → (Fintype.card (Unit ⊕ Fin q) : ℝ) ≤ p →
      normalizedTupleSideLog X (PrincipalTupleIndex B (layerSamplerDegree I n)) s p E
        (allocatedSpatialLateLog (G := G) B P Q) ≤ (Q + a) ^ a := by
  obtain ⟨b, _hb, hlate⟩ := exists_allocatedSpatialLateLog_bound m
  let poly : Polynomial ℕ := tupleSideLogEnvelope Polynomial.X Polynomial.X
    ((Polynomial.X + Polynomial.C b) ^ b)
  obtain ⟨a, ha, hbound⟩ := exists_natPolynomial_eval_budget poly
  refine ⟨a, ha, ?_⟩
  intro G _ I _ n B _ X _ q s P Q p E hP hQ hp hE hPQ hpQ hEQ hvars hX hq
  have hG : (Fintype.card G : ℝ) ≤ p :=
    (Nat.cast_le.mpr (allocatedKernelVariables_card_le_variables (G := G) B)).trans hvars
  have hN : (Fintype.card (PrincipalTupleIndex B (layerSamplerDegree I n)) : ℝ) ≤ p :=
    (Nat.cast_le.mpr (allocatedPrincipalIndex_card_le_variables (G := G) B)).trans hvars
  have hl := allocatedSpatialLateLog_nonneg (G := G) B hP hQ
  have hlb := hlate B hP hQ hPQ (le_refl Q) (hvars.trans hpQ)
  have hraw := (normalizedTuple_log_envelopes X (PrincipalTupleIndex B (layerSamplerDegree I n))
    s hp hE hl hq hG hN hX).2
  have hmono := tupleSideLogEnvelope_mono hp hE hl hpQ hEQ hlb
  apply (hraw.trans hmono).trans
  simpa [poly, tupleSideLogEnvelope, tupleLateLogEnvelope, tupleWidthLogEnvelope,
    tupleEarlyLogEnvelope, spatialTupleToleranceLog, spatialDiscretizationEnvelope,
    spatialMeshEnvelope, spatialLipschitzCostEnvelope, spatialLipschitzEnvelope,
    spatialDisplacementEnvelope, spatialFixedProfileEnvelope, anisotropicSpatialCapLog,
    coefficientErrorVolumeLog, Polynomial.eval₂_pow] using hbound Q hQ

end Erdos3.VectorPolynomial

end

end OAI
