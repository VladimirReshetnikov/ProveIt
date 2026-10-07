import OAI.Combinatorics.Progressions.Nilpotent.BCHSmoothPartitionBudget

namespace OAI

section

namespace Erdos3.NilpotentLieBCHGroup

open CircleFourier

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

noncomputable def logCharacter (η : L →ₗ[ℝ] ℝ) (g : NilpotentLieBCHGroup L s hnil) : ℂ :=
  character (η g.coord : CircleFourier.Circle)

theorem logCharacter_norm (η : L →ₗ[ℝ] ℝ) (g : NilpotentLieBCHGroup L s hnil) :
    ‖logCharacter η g‖ = 1 := norm_character _

theorem logCharacter_mul (η : L →ₗ[ℝ] ℝ) (g h : NilpotentLieBCHGroup L s hnil)
    (hgh : ⁅g.coord, h.coord⁆ = 0) :
    logCharacter η (g * h) = logCharacter η g * logCharacter η h := by
  simp only [logCharacter, coord_mul, lieBCH_eq_add_of_lie_eq_zero hnil hgh,
    map_add, AddCircle.coe_add, character_add]

theorem logCharacter_inv_mul (η : L →ₗ[ℝ] ℝ) (g : NilpotentLieBCHGroup L s hnil) :
    logCharacter η g⁻¹ * logCharacter η g = 1 := by
  simp only [logCharacter, coord_inv, map_neg, AddCircle.coe_neg, ← character_add,
    neg_add_cancel, character_zero]

theorem logCharacter_of_integral (η : L →ₗ[ℝ] ℝ) (g : NilpotentLieBCHGroup L s hnil)
    (hg : ∃ n : ℤ, η g.coord = n) : logCharacter η g = 1 := by
  obtain ⟨n, hn⟩ := hg
  apply (character_eq_one_iff _).mpr
  apply (AddCircle.coe_eq_zero_iff (1 : ℝ)).mpr
  exact ⟨n, by simpa only [zsmul_eq_mul, mul_one] using hn.symm⟩

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3.NilpotentLieBCHGroup

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

theorem logCharacter_norm_sub_eq_relative (η : L →ₗ[ℝ] ℝ)
    (x y γ : NilpotentLieBCHGroup L s hnil)
    (hx : ∀ v : L, ⁅x.coord, v⁆ = 0) (hy : ∀ v : L, ⁅y.coord, v⁆ = 0)
    (hγ : logCharacter η γ = 1) :
    ‖logCharacter η x - logCharacter η y‖ =
      ‖logCharacter η (y * γ * x⁻¹) - 1‖ := by
  have hzero : ⁅(y * γ).coord, x.coord⁆ = 0 := by rw [← lie_skew, hx, neg_zero]
  have hright : ⁅(y * γ).coord, x⁻¹.coord⁆ = 0 := by
    simp only [coord_inv, lie_neg, hzero, neg_zero]
  have hprod : logCharacter η (y * γ * x⁻¹) * logCharacter η x = logCharacter η y := by
    rw [logCharacter_mul η (y * γ) x⁻¹ hright,
      logCharacter_mul η y γ (hy γ.coord), hγ, mul_one, mul_assoc, logCharacter_inv_mul, mul_one]
  calc
    _ = ‖logCharacter η y - logCharacter η x‖ := norm_sub_rev _ _
    _ = ‖(logCharacter η (y * γ * x⁻¹) - 1) * logCharacter η x‖ := by
      rw [sub_mul, one_mul, hprod]
    _ = _ := by rw [norm_mul, logCharacter_norm, mul_one]

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3

open scoped NNReal

noncomputable def logCharacterMetricConstant (s d H : ℕ) (A : ℝ≥0) : ℝ≥0 :=
  (2 + CircleFourier.characterLipConstant * A) * bchLogMetricConstant s d H 1

namespace NilpotentLieBCHGroup

open Module

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [IsScalarTower ℚ ℝ L] [TopologicalSpace L] [IsTopologicalAddGroup L]
  [ContinuousSMul ℝ L] [T2Space L]
  {s H : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

theorem logCharacter_dist_one_le (e : Basis ι ℝ L) (c : ι → ι → ι → ℚ)
    (hstructure : ∀ i j k, algebraMap ℚ ℝ (c i j k) = e.repr ⁅e i, e j⁆ k)
    (hc : ∀ i j k, RationalHeightLE (c i j k) H)
    (η : L →ₗ[ℝ] ℝ) (A : ℝ≥0) (hη : ∀ x, |η x| ≤ A * ‖e.equivFun x‖)
    (g : NilpotentLieBCHGroup L s hnil) :
    letI := rightMetricSpace (hnil := hnil) e
    ‖logCharacter η g - 1‖ ≤ logCharacterMetricConstant s (Fintype.card ι) H A * dist 1 g := by
  let := rightMetricSpace (hnil := hnil) e
  let C := bchLogMetricConstant s (Fintype.card ι) H 1
  change ‖logCharacter η g - 1‖ ≤
    (2 + (CircleFourier.characterLipConstant : ℝ) * A) * C * dist 1 g
  by_cases hnear : (C : ℝ) * dist 1 g < 1
  · have hcoord := norm_coordinates_le_of_near_one e c hstructure hc 1 le_rfl g hnear
    have hchar := norm_character_real_sub_one_le (η g.coord)
    have hlinear := hη g.coord
    have hscale := mul_le_mul_of_nonneg_left hcoord A.coe_nonneg
    change ‖e.equivFun g.coord‖ ≤ (C : ℝ) * dist 1 g at hcoord
    have hbound : |η g.coord| ≤ A * ((C : ℝ) * dist 1 g) := hlinear.trans hscale
    apply hchar.trans
    have h := mul_le_mul_of_nonneg_left hbound CircleFourier.characterLipConstant.coe_nonneg
    nlinarith [C.coe_nonneg, dist_nonneg (x := (1 : NilpotentLieBCHGroup L s hnil)) (y := g)]
  · have hfar : 1 ≤ (C : ℝ) * dist 1 g := le_of_not_gt hnear
    apply (CircleFourier.norm_character_sub_one_le_two _).trans
    nlinarith [CircleFourier.characterLipConstant.coe_nonneg, A.coe_nonneg,
      C.coe_nonneg, dist_nonneg (x := (1 : NilpotentLieBCHGroup L s hnil)) (y := g),
      mul_nonneg CircleFourier.characterLipConstant.coe_nonneg A.coe_nonneg]

end NilpotentLieBCHGroup
end Erdos3

end

section

namespace Erdos3

open scoped NNReal

theorem bchLogMetricConstant_le_inverse (s d H : ℕ) :
    bchLogMetricConstant s d H 1 ≤ bchInverseBoxConstant s d H 1 := by
  change bchBoxCoordinateBound s d H 1 + 1 ≤
    (bchBoxCoordinateBound s d H 1 + 2 * 1) * (bchBoxCoordinateBound s d H 1 + 1)
  have h := bchBoxCoordinateBound_nonneg s d H (by norm_num : (0 : ℝ) ≤ 1)
  nlinarith

theorem exists_logCharacterMetricConstant_exp_bound (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (d H : ℕ) (A : ℝ≥0) (p : ℝ),
      0 ≤ p → (d : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p → (A : ℝ) ≤ Real.exp p →
      ((2 * logCharacterMetricConstant s d H A : ℝ≥0) : ℝ) ≤ Real.exp ((p + C) ^ C) := by
  obtain ⟨a, _, hbound⟩ := exists_bchInverseBoxConstant_exp_bound s 0
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hpoly⟩ := exists_natPolynomial_eval_budget (X + 11 + (X + Polynomial.C a) ^ a)
  refine ⟨C, hC, ?_⟩
  intro d H A p hp hd hH hA
  have hlog : (bchLogMetricConstant s d H 1 : ℝ) ≤ Real.exp ((p + a) ^ a) :=
    (show (bchLogMetricConstant s d H 1 : ℝ) ≤ bchInverseBoxConstant s d H 1 from
      bchLogMetricConstant_le_inverse s d H).trans
      (hbound d H 1 p hp hd hH (by simp only [NNReal.coe_one, pow_zero]; exact Real.one_le_exp zero_le_one))
  have hfront : 2 + (CircleFourier.characterLipConstant : ℝ) * A ≤ Real.exp (p + 10) := by
    have hpi : (CircleFourier.characterLipConstant : ℝ) ≤ 8 := by
      rw [CircleFourier.coe_characterLipConstant]
      linarith [Real.pi_lt_four]
    have hten : (10 : ℝ) ≤ Real.exp 10 := by linarith [Real.add_one_le_exp (10 : ℝ)]
    have hone := Real.one_le_exp hp
    rw [Real.exp_add]
    nlinarith [mul_le_mul_of_nonneg_right hpi A.coe_nonneg]
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hsmall : ((2 * logCharacterMetricConstant s d H A : ℝ≥0) : ℝ) ≤
      Real.exp (p + 11 + (p + a) ^ a) := by
    change 2 * ((2 + (CircleFourier.characterLipConstant : ℝ) * A) *
      (bchLogMetricConstant s d H 1 : ℝ)) ≤ _
    calc
      _ ≤ Real.exp 1 * (Real.exp (p + 10) * Real.exp ((p + a) ^ a)) :=
        mul_le_mul htwo (mul_le_mul hfront hlog (by positivity) (Real.exp_pos _).le)
          (by positivity) (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  apply hsmall.trans (Real.exp_le_exp.mpr ?_)
  simpa [X, Polynomial.eval₂_pow] using hpoly p hp

end Erdos3

end

end OAI
