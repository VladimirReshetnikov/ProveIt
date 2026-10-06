import GowersSzemeredi.Proofs16RadiusBounds

/-! # Comparing the Section 16 radius with the Section 10 extraction radius -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- The arrangement-density parameter is positive and small enough for
exact-density reparameterization. -/
theorem section16_density_parameter_bounds {theta gamma : Real} (k : Nat)
    (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1) :
    0 < section16ThetaOne theta gamma k / 4 ∧
      section16ThetaOne theta gamma k / 4 ≤ 1 / 36 := by
  have hx : 0 < theta * gamma / 4 := by positivity
  have hx1 : theta * gamma / 4 ≤ 1 / 4 := by nlinarith
  have hE : 2 ≤ (2 : Nat) ^ ((2 : Nat) ^ (k + 5)) :=
    le_trans (by norm_num : 2 ≤ 2 ^ 1)
      (Nat.pow_le_pow_right (by norm_num) (Nat.one_le_iff_ne_zero.mpr (by positivity)))
  constructor
  · unfold section16ThetaOne; positivity
  · have hpow : (theta * gamma / 4) ^ ((2 : Nat) ^ ((2 : Nat) ^ (k + 5))) ≤ (1 / 4 : Real) ^ 2 := by
      calc
        _ ≤ (1 / 4 : Real) ^ ((2 : Nat) ^ ((2 : Nat) ^ (k + 5))) :=
          pow_le_pow_left₀ hx.le hx1 _
        _ ≤ _ := pow_le_pow_of_le_one (by norm_num) (by norm_num) hE
    unfold section16ThetaOne
    norm_num at hpow ⊢
    linarith

/-- The very large Section 16 iteration parameter absorbs the explicit
ceiling and density costs in the Section 10 radius. -/
theorem section16_radius_exponent_budget {theta gamma : Real} (k : Nat)
    (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1) :
    (2 : Real) ^ (83 : Nat) / (section16ThetaOne theta gamma k / 4) ^ 11 ≤
      multipleS theta gamma k := by
  let A : Nat := 2 ^ (2 ^ (k + 5))
  let b : Real := 2 / (theta * gamma)
  let a : Real := section16ThetaOne theta gamma k / 4
  have hp : 0 < theta * gamma := mul_pos ht hg
  have hp1 : theta * gamma ≤ 1 := by nlinarith
  have hb : 2 ≤ b := (le_div_iff₀ hp).mpr (by nlinarith)
  have hA : 128 ≤ A := by
    have hexp : 7 ≤ (2 : Nat) ^ (k + 5) := by
      have h := Nat.pow_le_pow_right (n := 2) (by norm_num) (show 3 ≤ k + 5 by omega)
      norm_num at h
      omega
    exact (by norm_num : 128 ≤ 2 ^ 7).trans (Nat.pow_le_pow_right (by norm_num) hexp)
  have he : (2 : Nat) ^ ((2 : Nat) ^ (k + 6)) = A ^ 2 := by
    dsimp [A]
    rw [show k + 6 = (k + 5) + 1 by omega, pow_succ, pow_mul]
  have haInv : a⁻¹ = 4 * (2 * b) ^ A := by
    calc
      a⁻¹ = 4 * ((theta * gamma / 4)⁻¹) ^ A := by
        dsimp [a, section16ThetaOne, A]
        rw [inv_div, div_eq_mul_inv, inv_pow]
      _ = 4 * (2 * b) ^ A := by
        congr 1
        congr 1
        dsimp [b]
        rw [inv_div]
        ring
  have hform : (2 : Real) ^ (83 : Nat) / a ^ 11 =
      (2 : Real) ^ (105 : Nat) * (2 * b) ^ (11 * A) := by
    rw [div_eq_mul_inv, ← inv_pow, haInv]
    ring
  change (2 : Real) ^ (83 : Nat) / a ^ 11 ≤ _
  rw [hform]
  change _ ≤ b ^ (2 ^ (2 ^ (k + 6)))
  rw [he]
  calc
    _ ≤ b ^ (105 : Nat) * (b ^ 2) ^ (11 * A) := by
      gcongr
      nlinarith
    _ = b ^ (22 * A + 105) := by ring
    _ ≤ b ^ (A ^ 2) := pow_le_pow_right₀ (by linarith) (by nlinarith)

/-- The radius requested by Lemma 16.5 is available at every admissible
exact density above its lower density parameter. -/
theorem section16_zeta_le_section10Zeta {theta gamma alpha : Real} (k : Nat)
    (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    (halpha : section16ThetaOne theta gamma k / 4 ≤ alpha) (halpha1 : alpha ≤ 1 / 6) :
    section16Zeta theta gamma k ≤ section10Zeta alpha := by
  have ha := (section16_density_parameter_bounds k ht ht1 hg hg1).1
  apply le_trans _ (section10Zeta_lower_budget ha halpha halpha1)
  unfold section16Zeta
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  exact neg_le_neg (section16_radius_exponent_budget k ht ht1 hg hg1)

end LeanProofs.GowersSzemeredi
