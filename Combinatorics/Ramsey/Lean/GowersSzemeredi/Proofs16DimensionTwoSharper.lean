import GowersSzemeredi.Proofs16DimensionTwo

/-! A smaller iteration parameter in the two-dimensional structural theorem.
The actual extraction needs gamma^(-2)*S(theta,gamma,1)^10, rather than
 gamma^(-2)*S(theta,gamma,2). This is a structural improvement only. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

def section16DimensionTwoParameter (theta gamma : Real) : Real :=
  gamma ^ (-(2 : Int)) * (multipleS theta gamma 1)^10

theorem section16_cubic_piece_mass_inverse_le {theta gamma : Real}
    (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1) :
    (section16CubicPieceMass theta gamma)⁻¹ ≤ (multipleS theta gamma 1)^2 :=
  (section16_thetaTwo_inverse_le_iteration 1 (by positivity : 0 < theta / 2)
    (by linarith) hg hg1).trans (multipleS_half_le_square 1 ht ht1 hg hg1)

theorem section16_cubic_sharper_piece_budget {theta gamma : Real}
    (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1) :
    (multipleS theta gamma 1)^8 ≤
      section16CubicPieceMass theta gamma * (multipleS theta gamma 1)^10 := by
  have hm := section16CubicPieceMass_pos ht hg
  have hmul := mul_le_mul_of_nonneg_left
    (section16_cubic_piece_mass_inverse_le ht ht1 hg hg1) hm.le
  rw [mul_inv_cancel₀ hm.ne'] at hmul
  have hS : 0 ≤ multipleS theta gamma 1 := (one_le_multipleS 1 ht ht1 hg hg1).trans' (by norm_num)
  have hh := mul_le_mul_of_nonneg_right hmul (pow_nonneg hS 8)
  simpa only [one_mul, mul_assoc, ← pow_add] using hh

/-- The improved count parameter fits the printed dimension-two parameter. -/
theorem section16DimensionTwoParameter_le_source {theta gamma : Real}
    (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1) :
    section16DimensionTwoParameter theta gamma ≤ gamma ^ (-(2 : Int)) * multipleS theta gamma 2 := by
  exact mul_le_mul_of_nonneg_left
    (multipleS_pow_le_succ 1 10 ht ht1 hg hg1 (by norm_num)) (by positivity)

/-- The parameter improvement is strict throughout the density range. -/
theorem section16DimensionTwoParameter_lt_source {theta gamma : Real}
    (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1) :
    section16DimensionTwoParameter theta gamma < gamma ^ (-(2 : Int)) * multipleS theta gamma 2 := by
  have hp : 0 < theta * gamma := mul_pos ht hg
  have hp1 : theta * gamma ≤ 1 := mul_le_one₀ ht1 hg.le hg1
  have hb : 1 < 2 / (theta * gamma) := (lt_div_iff₀ hp).mpr (by linarith)
  apply mul_lt_mul_of_pos_left _ (by positivity : 0 < gamma ^ (-(2 : Int)))
  unfold multipleS
  rw [← pow_mul]
  exact pow_lt_pow_right₀ hb (by norm_num)

/-- Arbitrary two-dimensional product relations admit the source structural
conclusion with the smaller parameter gamma^-2*S(theta,gamma,1)^10. -/
theorem theorem_16_2_at_two_sharper (gamma theta : Real)
    (hg : 0 < gamma) (hg1 : gamma ≤ 1) (ht : 0 < theta) (ht1 : theta ≤ 1) :
    ∃ N0 : Nat, ∀ (N : Nat) [NeZero N] [Fact N.Prime], N0 ≤ N →
      ∀ Gamma : Finset (Point N 2 × ZMod N),
        (Gamma.card : Real) ≤ gamma ^ (-(2 : Int)) * (N : Real)^2 →
        RelationProductProperty gamma Gamma →
        ∃ J : Finset (Point N 2), (1 - theta) * (N : Real)^2 ≤ J.card ∧
          MultiplyLinear gamma (section16DimensionTwoParameter theta gamma) (restrictRelation Gamma J) := by
  obtain ⟨N0, hN0⟩ := section16_cubic_relation_piece ht ht1 hg hg1
  have hS := one_le_multipleS 1 ht ht1 hg hg1
  have hginv : 1 ≤ gamma ^ (-(2 : Int)) := by
    rw [zpow_neg, zpow_ofNat]
    exact (one_le_inv₀ (pow_pos hg 2)).mpr (pow_le_one₀ hg.le hg1)
  have hm := section16CubicPieceMass_pos ht hg
  have hb := section16_cubic_sharper_piece_budget ht ht1 hg hg1
  refine ⟨N0, fun N _ _ hN Gamma hcard hprod => ?_⟩
  have hNpos : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  apply section16_multiplyLinear_of_budgeted_pieces Gamma hg hg1
    (by positivity : 0 < section16CubicPieceMass theta gamma * (N : Real)^2)
    (one_le_pow₀ hS (n := 8))
    (one_le_mul_of_one_le_of_one_le hginv (one_le_pow₀ hS (n := 10)))
  · calc
      (Gamma.card : Real) * (multipleS theta gamma 1)^8 ≤
          (gamma ^ (-(2 : Int)) * (N : Real)^2) * (multipleS theta gamma 1)^8 :=
        mul_le_mul_of_nonneg_right hcard (by positivity)
      _ ≤ (gamma ^ (-(2 : Int)) * (N : Real)^2) *
          (section16CubicPieceMass theta gamma * (multipleS theta gamma 1)^10) :=
        mul_le_mul_of_nonneg_left hb (by positivity)
      _ = _ := by ring
  · intro Delta hDelta hlarge
    obtain ⟨D, hD, hmass, hML⟩ := hN0 N hN Delta (hprod.mono hDelta) hlarge
    exact ⟨D, hD, hmass, hML.cubic_two_source_control ht ht1 hg hg1⟩

end LeanProofs.GowersSzemeredi
