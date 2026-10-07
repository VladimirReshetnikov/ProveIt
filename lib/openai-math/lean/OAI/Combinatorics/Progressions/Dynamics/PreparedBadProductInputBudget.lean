import OAI.Combinatorics.Progressions.Sampling.ForecastPreparedScaleBudget

namespace OAI

section

namespace Erdos3.VectorPolynomial
open BooleanCubeKernel
open scoped BigOperators Classical

theorem boundedCoefficientExponent_card_le_common_dimension
    {K : Type*} [Fintype K] (m pnum : ℕ) (hK : Fintype.card K ≤ pnum)
    {h : ℕ} (hh : h ≤ m) :
    Fintype.card (BoundedCoefficientExponent K h) ≤ (m + 1) * (pnum + 1) ^ m := by
  apply (boundedCoefficientExponent_card_le h).trans
  apply Nat.mul_le_mul (Nat.add_le_add_right hh 1)
  exact (Nat.pow_le_pow_left (Nat.add_le_add_right hK 1) h).trans
    (Nat.pow_le_pow_right (Nat.succ_pos pnum) hh)

variable {X J : Type} {m : ℕ} (L : RankPreparationFamily X J m)

theorem preparedBadProduct_input_counts
    (Jalloc nX : ℕ) {M : ℕ} (hM : ∀ j, Fintype.card (L j).Coord ≤ M) :
    let pnum := enlargedPreparedCommonSamplerDimension m M Jalloc
    let G := EnlargedPreparedCommonKernel m Jalloc
    let I := PreparedSamplerContinuous L
    let n := preparedSamplerTransverse L
    let B := EnlargedPreparedCommonSamplerBlock L Jalloc
    let vars := LayerSamplerVariables G I n B
    m ≤ pnum ∧ M ≤ pnum ∧ Jalloc ≤ pnum ∧ Fintype.card G ≤ pnum ∧
      Fintype.card vars ≤ pnum ∧
      (∀ j, Fintype.card (I j) ≤ pnum) ∧ (∀ j, n j ≤ pnum) ∧
      (∀ j, Fintype.card (L j).Coord ≤ pnum) ∧
      (∀ j : Fin m, Fintype.card (BoundedCoefficientExponent vars (j.val + 1)) ≤
        (m + 1) * (pnum + 1) ^ m) ∧
      Fintype.card (Option vars × Fin nX) ≤ (pnum + 1) * nX := by
  intro pnum G I n B vars
  obtain ⟨hvars, hI, hn⟩ := enlargedPreparedCommonSampler_dimensions L Jalloc hM
  have hpM := enlargedPreparedCommonSamplerDimension_ge m M Jalloc
  have halloc := enlargedPreparedCommonSamplerDimension_allocation m M Jalloc
  have hm : m ≤ pnum := by unfold pnum enlargedPreparedCommonSamplerDimension; omega
  have hG : Fintype.card G ≤ pnum := by
    simp only [G, EnlargedPreparedCommonKernel, Fintype.card_fin]
    unfold pnum enlargedPreparedCommonSamplerDimension
    omega
  refine ⟨hm, hpM, halloc, hG, hvars, hI, hn, fun j => (hM j).trans hpM, ?_, ?_⟩
  · intro j
    exact boundedCoefficientExponent_card_le_common_dimension m pnum hvars (Nat.succ_le_of_lt j.isLt)
  · simp only [Fintype.card_prod, Fintype.card_option, Fintype.card_fin]
    exact Nat.mul_le_mul_right nX (Nat.add_le_add_right hvars 1)

theorem preparedBadProduct_coefficient_card
    (Jalloc : ℕ) {M : ℕ} (hM : ∀ j, Fintype.card (L j).Coord ≤ M) (j : Fin m) :
    Fintype.card (BoundedCoefficientExponent
      (LayerSamplerVariables (EnlargedPreparedCommonKernel m Jalloc)
        (PreparedSamplerContinuous L) (preparedSamplerTransverse L)
        (EnlargedPreparedCommonSamplerBlock L Jalloc)) (j.val + 1)) ≤
      (m + 1) * (enlargedPreparedCommonSamplerDimension m M Jalloc + 1) ^ m :=
  boundedCoefficientExponent_card_le_common_dimension m _
    (enlargedPreparedCommonSampler_dimensions L Jalloc hM).1 (Nat.succ_le_of_lt j.isLt)

theorem preparedBadProduct_frame_card
    (Jalloc nX : ℕ) {M : ℕ} (hM : ∀ j, Fintype.card (L j).Coord ≤ M) :
    Fintype.card (Option
      (LayerSamplerVariables (EnlargedPreparedCommonKernel m Jalloc)
        (PreparedSamplerContinuous L) (preparedSamplerTransverse L)
        (EnlargedPreparedCommonSamplerBlock L Jalloc)) × Fin nX) ≤
      (enlargedPreparedCommonSamplerDimension m M Jalloc + 1) * nX := by
  simp only [Fintype.card_prod, Fintype.card_option, Fintype.card_fin]
  exact Nat.mul_le_mul_right nX
    (Nat.add_le_add_right (enlargedPreparedCommonSampler_dimensions L Jalloc hM).1 1)

end Erdos3.VectorPolynomial

end

end OAI
