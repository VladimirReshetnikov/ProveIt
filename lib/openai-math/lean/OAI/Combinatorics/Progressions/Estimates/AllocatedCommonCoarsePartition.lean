import OAI.Combinatorics.Progressions.Dynamics.AllocatedCommonCoarseBudget

namespace OAI

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped NNReal

theorem allocatedCoarseInputEnvelope_bounds (m dim : ℕ) {s : ℝ} (hs : 0 ≤ s) :
    let R := s + (m + dim + 2 : ℕ)
    let T := allocatedCoarseInputEnvelope m dim s
    0 ≤ T ∧ R ≤ T ∧ R ^ 3 ≤ T ∧
      R ^ 3 + anisotropicSpatialCapLog R ≤ T ∧
      R ^ 3 + spatialLipschitzEnvelope R + R ≤ T ∧
      allocatedCoarseMassBudget m dim s ≤ T := by
  intro R T
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hcap := anisotropicSpatialCapLog_nonneg hR
  have hlip := (spatialCostEnvelopes_nonneg hR (le_refl (0 : ℝ))).2.2.2.2
  have hmass := allocatedCoarseMassBudget_nonneg m dim hs
  have hcube : 0 ≤ R ^ 3 := pow_nonneg hR _
  dsimp only [T, allocatedCoarseInputEnvelope]
  change 0 ≤ 2 * R + R ^ 3 + anisotropicSpatialCapLog R + spatialLipschitzEnvelope R +
      allocatedCoarseMassBudget m dim s + 4 ∧ _
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith

theorem allocatedCommonCoarseMesh_partition_budget (m : ℕ) {dim : ℕ}
    {G : Type*} [Fintype G] (X : Type*) [Fintype X]
    (selection : Fin dim ↪ G) {M modulus : ℕ} {p c P e E : ℝ}
    (hp : 0 ≤ p) (hc : 0 ≤ c) (hP : 0 ≤ P) (he : 0 ≤ e) (hE : 0 ≤ E)
    (hG : (Fintype.card G : ℝ) ≤ p) (hX : (Fintype.card X : ℝ) ≤ P)
    (hM : 0 < M) (hMP : (M : ℝ) ≤ Real.exp P) (hmod : modulus ≤ M ^ (m + 1)) :
    let r := allocatedCommonCoarseMesh m X selection M modulus p c P e E
    let T := allocatedCoarseInputEnvelope m dim (p + c + P + e + E)
    r⁻¹ ≤ Real.exp (coarseSpatialReciprocalLog T) ∧
      allocatedSpatialCoefficientCap X selection M modulus r ≤
        Real.exp (coarseSpatialPartitionLog T) := by
  let s := p + c + P + e + E
  let R := s + (m + dim + 2 : ℕ)
  let T := allocatedCoarseInputEnvelope m dim s
  have hs : 0 ≤ s := by dsimp [s]; positivity
  have hR2 : 2 ≤ R := by
    dsimp [R]
    push_cast
    linarith only [hs, Nat.cast_nonneg (α := ℝ) m, Nat.cast_nonneg (α := ℝ) dim]
  have hR : 0 ≤ R := by linarith only [hR2]
  obtain ⟨hT, hRT, hcubeT, hcapT, hlipT, hmassT⟩ :=
    allocatedCoarseInputEnvelope_bounds m dim hs
  change R ≤ T at hRT
  have hPR : P ≤ R := by
    dsimp [R, s]; push_cast
    linarith only [hp, hc, he, hE, Nat.cast_nonneg (α := ℝ) m, Nat.cast_nonneg (α := ℝ) dim]
  have hpR : p + 1 ≤ R := by
    dsimp [R, s]; push_cast
    linarith only [hc, hP, he, hE, Nat.cast_nonneg (α := ℝ) m, Nat.cast_nonneg (α := ℝ) dim]
  have hER : E + 2 ≤ R := by
    dsimp [R, s]; push_cast
    linarith only [hp, hc, hP, he, Nat.cast_nonneg (α := ℝ) m, Nat.cast_nonneg (α := ℝ) dim]
  have hmR : ((m + 1 : ℕ) : ℝ) ≤ R := by
    dsimp [R]; push_cast
    linarith only [hs, Nat.cast_nonneg (α := ℝ) dim]
  have hnR : (Fintype.card (Unit ⊕ Fin dim) : ℝ) ≤ R := by
    simp only [Fintype.card_sum, Fintype.card_unique, Fintype.card_fin, Nat.cast_add,
      Nat.cast_one]
    dsimp [R]
    push_cast
    linarith only [hs, Nat.cast_nonneg (α := ℝ) m]
  have hGR : (Fintype.card G : ℝ) ≤ R := hG.trans (by linarith only [hpR])
  have hXR : (Fintype.card X : ℝ) ≤ R := hX.trans hPR
  have hMR := hMP.trans (Real.exp_le_exp.mpr hPR)
  have hmodR := coefficientErrorPeriod_exp_sq hR hmR hMR hmod
  have hΓ : (modulus : ℝ) ^ Fintype.card (Unit ⊕ Fin dim) ≤ Real.exp (R ^ 3) :=
    (pow_le_exp_mul_of_le_exp (Nat.cast_nonneg _) hmodR (sq_nonneg R) _ hnR).trans_eq
      (congrArg Real.exp (by ring))
  have hκ : 0 ≤ 1 / (M : ℝ) := by positivity
  have hC0 := anisotropicSpatialDensityCap_nonneg selection hκ
  have hL0 := anisotropicSpatialDensityLip_nonneg selection hκ
  have hC := anisotropicSpatialDensityCap_exp_bound selection hR hM hMR hnR hGR
  have hfree : (Fintype.card (UnselectedColumn selection) : ℝ) ≤ 2 * R := by
    have hcard := selectedColumn_card selection
    have hb : (Fintype.card (UnselectedColumn selection) : ℝ) ≤ R :=
      (Nat.cast_le.mpr (by omega)).trans hGR
    linarith only [hb, hR]
  have hprofile := spatialProfileLog_le_fixedEnvelope _ _ hR hnR hfree
  have hL : anisotropicSpatialDensityLip selection (1 / (M : ℝ)) ≤
      Real.exp (spatialLipschitzEnvelope R) :=
    (anisotropicSpatialDensityLip_le_exp selection hR hM hMR hnR hGR).trans
      (Real.exp_le_exp.mpr (add_le_add le_rfl (mul_le_mul_of_nonneg_left hprofile (by norm_num))))
  have hQ : (allocatedPrimitiveRootRatio p : ℝ) ≤ Real.exp R :=
    (allocatedPrimitiveRootRatio_bounds hp).2.2.trans (Real.exp_le_exp.mpr hpR)
  have hcapInput : (modulus : ℝ) ^ Fintype.card (Unit ⊕ Fin dim) *
      anisotropicSpatialDensityCap selection (1 / (M : ℝ)) ≤ Real.exp T := by
    calc
      _ ≤ Real.exp (R ^ 3) * Real.exp (anisotropicSpatialCapLog R) := by gcongr
      _ = Real.exp (R ^ 3 + anisotropicSpatialCapLog R) := (Real.exp_add _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr hcapT
  have hlipInput : (modulus : ℝ) ^ Fintype.card (Unit ⊕ Fin dim) *
      (anisotropicSpatialDensityLip selection (1 / (M : ℝ)) * allocatedPrimitiveRootRatio p) ≤
      Real.exp T := by
    calc
      _ ≤ Real.exp (R ^ 3) * (Real.exp (spatialLipschitzEnvelope R) * Real.exp R) := by gcongr
      _ = Real.exp (R ^ 3 + spatialLipschitzEnvelope R + R) := by
        rw [← Real.exp_add, ← Real.exp_add, add_assoc]
      _ ≤ _ := Real.exp_le_exp.mpr hlipT
  have hmassInput := (allocatedCommonCoarseMass_le_exp m dim X hp hc hP he hE hX).trans
    (Real.exp_le_exp.mpr hmassT)
  have hε : 0 < normalizedSpatialShare E := Real.exp_pos _
  have hεInput : (normalizedSpatialShare E)⁻¹ ≤ Real.exp T := by
    rw [normalizedSpatialShare, ← Real.exp_neg, neg_neg]
    exact Real.exp_le_exp.mpr (hER.trans hRT)
  have hsquare : R ^ 2 ≤ R ^ 3 := by
    calc
      R ^ 2 = R ^ 2 * 1 := (mul_one _).symm
      _ ≤ R ^ 2 * R := mul_le_mul_of_nonneg_left (by linarith only [hR2]) (sq_nonneg R)
      _ = R ^ 3 := by ring
  have hmodInput := hmodR.trans (Real.exp_le_exp.mpr (hsquare.trans hcubeT))
  have hΓInput := hΓ.trans (Real.exp_le_exp.mpr hcubeT)
  have hCInput := hC.trans (Real.exp_le_exp.mpr
    (show anisotropicSpatialCapLog R ≤ T from
      (le_add_of_nonneg_left (pow_nonneg hR 3)).trans hcapT))
  exact spatialTupleCoarseMesh_partition_budget (Fintype.card X)
    (Fintype.card (Unit ⊕ Fin dim)) (mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _) hC0)
    (allocatedCommonCoarseMass_nonneg m dim X hp)
    (mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _) (mul_nonneg hL0 (NNReal.coe_nonneg _)))
    (Nat.cast_nonneg _) hC0 hε hT (hXR.trans hRT) (hnR.trans hRT)
    hcapInput hmassInput hlipInput hεInput hmodInput hΓInput hCInput

end Erdos3.VectorPolynomial

end

end OAI
