import GowersSzemeredi.Proofs16ClassStep
import GowersSzemeredi.Proofs18LengthSixCounts

/-! Power bounds for the step of route (II), in every dimension (Notes L.6, E5).

Part A: the parameters of a `(k+1)`-dimensional piece, in the base
`u = 2/(γθ)`, with `X = 2^(k+5)`:
* `θ₁⁻¹ ≤ u^(2^(X+1))` (`thetaOne_inv_le_gen`);
* `θ′⁻¹, δ⁻¹ ≤ u^(2^(X+5))` (`classBudget_inv_le`, `classDelta_inv_le`);
* `classPieces γ θ k ≤ u^(2^(X+6))`;
* Lemma 15.6's threshold `≤ u^(2^(X+6))` for `k ≥ 1`
  (`lemma156ExplicitThreshold_le_gen`);
* `ζ⁻¹ ≤ exp(u^(2^(2^(k+6))))` (`section16Zeta_inv_le_gen`).

The side conditions are symbolic in `k`, so they are proved from `n < 2^n`
by `omega`, not by evaluation. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi
open BaseCase

/-! ### Symbolic exponent facts -/

theorem two_pow_k5_ge (k : Nat) : k + 5 ≤ 2 ^ (k + 5) :=
  (Nat.lt_two_pow_self (n := k + 5)).le

theorem two_pow_X_ge (k : Nat) : 2 ^ (k + 5) + 1 ≤ 2 ^ (2 ^ (k + 5)) :=
  Nat.lt_two_pow_self

theorem gen_exp_fact1 (k : Nat) : k + 34 + 2 ^ (2 ^ (k + 5) + 4) ≤ 2 ^ (2 ^ (k + 5) + 5) := by
  have h1 := two_pow_k5_ge k
  have h2 := two_pow_X_ge k
  have h3 : 2 ^ (2 ^ (k + 5) + 4) = 2 ^ (2 ^ (k + 5)) * 16 := by rw [pow_add]; norm_num
  have h4 : 2 ^ (2 ^ (k + 5) + 5) = 2 ^ (2 ^ (k + 5)) * 32 := by rw [pow_add]; norm_num
  omega

theorem gen_exp_fact2 (k : Nat) : 37 + (2 ^ (2 ^ (k + 5) + 1) + 2) * 6 ≤ 2 ^ (2 ^ (k + 5) + 5) := by
  have h1 := two_pow_k5_ge k
  have h2 := two_pow_X_ge k
  have h3 : 2 ^ (2 ^ (k + 5) + 1) = 2 ^ (2 ^ (k + 5)) * 2 := by rw [pow_add]; norm_num
  have h4 : 2 ^ (2 ^ (k + 5) + 5) = 2 ^ (2 ^ (k + 5)) * 32 := by rw [pow_add]; norm_num
  omega

theorem gen_exp_fact3 (k : Nat) : 2 + 2 ^ (2 ^ (k + 5) + 5) ≤ 2 ^ (2 ^ (k + 5) + 6) := by
  have h1 := two_pow_k5_ge k
  have h2 := two_pow_X_ge k
  have h4 : 2 ^ (2 ^ (k + 5) + 5) = 2 ^ (2 ^ (k + 5)) * 32 := by rw [pow_add]; norm_num
  have h5 : 2 ^ (2 ^ (k + 5) + 6) = 2 ^ (2 ^ (k + 5)) * 64 := by rw [pow_add]; norm_num
  omega

/-! ### θ₁, θ₂, θ′ and δ -/

theorem thetaOne_inv_le_gen {gamma theta : Real} (k : Nat) (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    (ht : 0 < theta) (ht1 : theta ≤ 1) :
    (section16ThetaOne theta gamma k)⁻¹ ≤ (2 / (gamma * theta)) ^ (2 ^ (2 ^ (k + 5) + 1)) := by
  obtain ⟨hu2, -, -, -, -⟩ := prod_scale_basic hg hg1 ht ht1
  have hq := quarter_prod_ge_inv_sq hg ht hu2
  have hq0 : 0 < theta * gamma / 4 := by positivity
  set u := 2 / (gamma * theta) with hu
  clear_value u
  have hupos : 0 < u := lt_of_lt_of_le (by norm_num) hu2
  have hqi : (theta * gamma / 4)⁻¹ ≤ u ^ 2 := by
    have := inv_anti₀ (inv_pos.mpr (pow_pos hupos 2)) hq
    rwa [inv_inv] at this
  unfold section16ThetaOne
  rw [← inv_pow]
  calc ((theta * gamma / 4)⁻¹) ^ (2 ^ (2 ^ (k + 5))) ≤ (u ^ 2) ^ (2 ^ (2 ^ (k + 5))) :=
        pow_le_pow_left₀ (by positivity) hqi _
    _ = u ^ (2 ^ (2 ^ (k + 5) + 1)) := by
        rw [← pow_mul]
        congr 1
        rw [pow_succ (2 : Nat) (2 ^ (k + 5))]
        ring

theorem classBudget_inv_le {gamma theta : Real} (k : Nat) (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    (ht : 0 < theta) (ht1 : theta ≤ 1) :
    (classBudget theta gamma k)⁻¹ ≤ (2 / (gamma * theta)) ^ (2 ^ (2 ^ (k + 5) + 5)) := by
  obtain ⟨hu2, -, -, -, -⟩ := prod_scale_basic hg hg1 ht ht1
  obtain ⟨h0, -, -, -⟩ := section16_theta_delta_bounds k ht ht1 hg hg1
  have hθi := thetaOne_inv_le_gen k hg hg1 ht ht1
  have hval : (classBudget theta gamma k)⁻¹ = 2 ^ (k + 2) *
      ((2 : Real) ^ (32 : Real) * ((section16ThetaOne theta gamma k)⁻¹) ^ 8) := by
    unfold classBudget section16ThetaTwo
    rw [Real.rpow_neg (by norm_num), inv_div, div_eq_mul_inv, mul_inv, inv_inv, inv_pow]
  rw [hval]
  set t := section16ThetaOne theta gamma k
  set u := 2 / (gamma * theta) with hu
  clear_value u t
  have hupos : 0 < u := lt_of_lt_of_le (by norm_num) hu2
  have hu1 : 1 ≤ u := le_trans (by norm_num) hu2
  have h32 : (2 : Real) ^ (32 : Real) ≤ u ^ 32 := by
    rw [show (32 : Real) = ((32 : Nat) : Real) by norm_num, Real.rpow_natCast]
    exact pow_le_pow_left₀ (by norm_num) hu2 32
  have hk2 : (2 : Real) ^ (k + 2) ≤ u ^ (k + 2) := pow_le_pow_left₀ (by norm_num) hu2 _
  have ht8 : (t⁻¹) ^ 8 ≤ (u ^ (2 ^ (2 ^ (k + 5) + 1))) ^ 8 :=
    pow_le_pow_left₀ (inv_pos.mpr h0).le hθi 8
  calc (2 : Real) ^ (k + 2) * ((2 : Real) ^ (32 : Real) * (t⁻¹) ^ 8)
      ≤ u ^ (k + 2) * (u ^ 32 * (u ^ (2 ^ (2 ^ (k + 5) + 1))) ^ 8) :=
        mul_le_mul hk2 (mul_le_mul h32 ht8 (by positivity) (pow_nonneg hupos.le _))
          (by positivity) (pow_nonneg hupos.le _)
    _ = u ^ (k + 34 + 2 ^ (2 ^ (k + 5) + 4)) := by
        rw [← pow_mul, ← pow_add, ← pow_add]
        congr 1
        rw [show 2 ^ (2 ^ (k + 5) + 4) = 2 ^ (2 ^ (k + 5) + 1) * 8 by
          rw [show 2 ^ (k + 5) + 4 = (2 ^ (k + 5) + 1) + 3 by omega, pow_add]; norm_num]
        omega
    _ ≤ u ^ (2 ^ (2 ^ (k + 5) + 5)) := pow_le_pow_right₀ hu1 (gen_exp_fact1 k)

theorem classDelta_inv_le {gamma theta : Real} (k : Nat) (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    (ht : 0 < theta) (ht1 : theta ≤ 1) :
    (classDelta theta gamma k)⁻¹ ≤ (2 / (gamma * theta)) ^ (2 ^ (2 ^ (k + 5) + 5)) := by
  obtain ⟨hu2, -, -, -, -⟩ := prod_scale_basic hg hg1 ht ht1
  obtain ⟨h0, h1, -, -⟩ := section16_theta_delta_bounds k ht ht1 hg hg1
  have hθi := thetaOne_inv_le_gen k hg hg1 ht ht1
  have hval : (classDelta theta gamma k)⁻¹ = (2 : Real) ^ (37 : Real) *
      (4 / section16ThetaOne theta gamma k) ^ ((11 : Real) / 2) := by
    unfold classDelta section16Delta
    rw [mul_inv, Real.rpow_neg (by norm_num), inv_inv, ← Real.inv_rpow (by positivity), inv_div]
  rw [hval]
  set t := section16ThetaOne theta gamma k
  set u := 2 / (gamma * theta) with hu
  clear_value u t
  have hupos : 0 < u := lt_of_lt_of_le (by norm_num) hu2
  have hu1 : 1 ≤ u := le_trans (by norm_num) hu2
  have h4t : 4 / t ≤ u ^ (2 ^ (2 ^ (k + 5) + 1) + 2) := by
    rw [div_eq_mul_inv, pow_add, mul_comm]
    exact mul_le_mul hθi (show (4 : Real) ≤ u ^ 2 by nlinarith only [hu2]) (by norm_num)
      (pow_nonneg hupos.le _)
  have h4t1 : 1 ≤ 4 / t := by rw [le_div_iff₀ h0]; linarith only [h1]
  have h37 : (2 : Real) ^ (37 : Real) ≤ u ^ 37 := by
    rw [show (37 : Real) = ((37 : Nat) : Real) by norm_num, Real.rpow_natCast]
    exact pow_le_pow_left₀ (by norm_num) hu2 37
  have h6 : (4 / t) ^ ((11 : Real) / 2) ≤ (4 / t) ^ 6 := by
    rw [show (4 / t) ^ 6 = (4 / t) ^ ((6 : Nat) : Real) by rw [Real.rpow_natCast]]
    exact Real.rpow_le_rpow_of_exponent_le h4t1 (by norm_num)
  calc (2 : Real) ^ (37 : Real) * (4 / t) ^ ((11 : Real) / 2)
      ≤ u ^ 37 * (u ^ (2 ^ (2 ^ (k + 5) + 1) + 2)) ^ 6 :=
        mul_le_mul h37 (h6.trans (pow_le_pow_left₀ (by positivity) h4t 6))
          (Real.rpow_nonneg (by positivity) _) (pow_nonneg hupos.le _)
    _ = u ^ (37 + (2 ^ (2 ^ (k + 5) + 1) + 2) * 6) := by rw [← pow_mul, ← pow_add]
    _ ≤ u ^ (2 ^ (2 ^ (k + 5) + 5)) := pow_le_pow_right₀ hu1 (gen_exp_fact2 k)

theorem classPieces_le_gen {gamma theta : Real} (k : Nat) (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    (ht : 0 < theta) (ht1 : theta ≤ 1) :
    (classPieces gamma theta k : Real) ≤ (2 / (gamma * theta)) ^ (2 ^ (2 ^ (k + 5) + 6)) := by
  obtain ⟨hu2, hginv, -, -, -⟩ := prod_scale_basic hg hg1 ht ht1
  obtain ⟨hb, -⟩ := classBudget_pos_le k ht ht1 hg hg1
  have hbi := classBudget_inv_le k hg hg1 ht ht1
  set u := 2 / (gamma * theta) with hu
  clear_value u
  have hupos : 0 < u := lt_of_lt_of_le (by norm_num) hu2
  have hu1 : 1 ≤ u := le_trans (by norm_num) hu2
  have hg2 : gamma ^ (-(2 : Int)) ≤ u ^ 2 := by
    rw [zpow_neg, zpow_ofNat, ← inv_pow]
    exact pow_le_pow_left₀ (by positivity) hginv 2
  unfold classPieces
  refine (Nat.floor_le (by positivity)).trans ?_
  rw [div_eq_mul_inv]
  calc gamma ^ (-(2 : Int)) * (classBudget theta gamma k)⁻¹
      ≤ u ^ 2 * u ^ (2 ^ (2 ^ (k + 5) + 5)) :=
        mul_le_mul hg2 hbi (inv_pos.mpr hb).le (pow_nonneg hupos.le _)
    _ = u ^ (2 + 2 ^ (2 ^ (k + 5) + 5)) := by rw [← pow_add]
    _ ≤ u ^ (2 ^ (2 ^ (k + 5) + 6)) := pow_le_pow_right₀ hu1 (gen_exp_fact3 k)

/-! ### The Bohr radius -/

theorem section16Zeta_inv_le_gen {gamma theta : Real} (k : Nat) (hg : 0 < gamma) (ht : 0 < theta) :
    0 < section16Zeta theta gamma k ∧ section16Zeta theta gamma k ≤ 1 ∧
      (section16Zeta theta gamma k)⁻¹ ≤
        Real.exp ((2 / (gamma * theta)) ^ ((2 : Nat) ^ ((2 : Nat) ^ (k + 6)))) := by
  have hms : multipleS theta gamma k = (2 / (gamma * theta)) ^ ((2 : Nat) ^ ((2 : Nat) ^ (k + 6))) := by
    unfold multipleS; rw [mul_comm theta gamma]
  have hm0 : 0 ≤ multipleS theta gamma k := by rw [hms]; positivity
  unfold section16Zeta
  refine ⟨Real.rpow_pos_of_pos (by norm_num) _, ?_, ?_⟩
  · exact Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith only [hm0])
  · rw [Real.rpow_neg (by norm_num), inv_inv, Real.rpow_def_of_pos (by norm_num), ← hms]
    apply Real.exp_le_exp.mpr
    have h : Real.log 2 ≤ 1 := by have := Real.log_two_lt_d9; linarith only [this]
    calc Real.log 2 * multipleS theta gamma k ≤ 1 * multipleS theta gamma k :=
          mul_le_mul_of_nonneg_right h hm0
      _ = multipleS theta gamma k := one_mul _


/-! ### Lemma 15.6's threshold -/

theorem gen_exp_fact4 (k : Nat) :
    32 * 2 ^ k + k + (7 * 4 ^ (k + 1) + 21 * k * 4 ^ (k + 1) + 46) *
        arrangementSelectionExponent k + 2 ≤ 2 ^ (2 ^ (k + 5) + 6) := by
  have hA : k < 2 ^ k := Nat.lt_two_pow_self
  have h4 : 4 ^ (k + 1) = 2 ^ (2 * k + 2) := by
    rw [show (4 : Nat) = 2 ^ 2 by norm_num, ← pow_mul]; ring_nf
  have h5 : 2 ^ (k + 5) = 2 ^ k * 32 := by rw [pow_add]; norm_num
  have hlin : 7 + 21 * k ≤ 2 ^ (k + 5) := by omega
  have hc : 7 * 4 ^ (k + 1) + 21 * k * 4 ^ (k + 1) + 46 ≤ 2 ^ (3 * k + 8) := by
    have h1 : 7 * 4 ^ (k + 1) + 21 * k * 4 ^ (k + 1) = (7 + 21 * k) * 2 ^ (2 * k + 2) := by
      rw [h4]; ring
    have h2 : (7 + 21 * k) * 2 ^ (2 * k + 2) ≤ 2 ^ (k + 5) * 2 ^ (2 * k + 2) :=
      Nat.mul_le_mul_right _ hlin
    have h3 : 2 ^ (k + 5) * 2 ^ (2 * k + 2) = 2 ^ (3 * k + 7) := by
      rw [← pow_add]; ring_nf
    have h6 : 2 ^ (3 * k + 8) = 2 ^ (3 * k + 7) * 2 := by rw [pow_succ]
    have h7 : 2 ^ 7 ≤ 2 ^ (3 * k + 7) := Nat.pow_le_pow_right (by norm_num) (by omega)
    calc 7 * 4 ^ (k + 1) + 21 * k * 4 ^ (k + 1) + 46
        = (7 + 21 * k) * 2 ^ (2 * k + 2) + 46 := by rw [h1]
      _ ≤ 2 ^ (k + 5) * 2 ^ (2 * k + 2) + 46 := Nat.add_le_add_right h2 46
      _ = 2 ^ (3 * k + 7) + 46 := by rw [h3]
      _ ≤ 2 ^ (3 * k + 7) + 2 ^ (3 * k + 7) :=
          Nat.add_le_add_left (le_trans (by norm_num) h7) _
      _ = 2 ^ (3 * k + 8) := by rw [h6]; ring
  have hE : (7 * 4 ^ (k + 1) + 21 * k * 4 ^ (k + 1) + 46) * arrangementSelectionExponent k ≤
      2 ^ (2 ^ (k + 4) + 4 * k + 11) := by
    unfold arrangementSelectionExponent
    calc (7 * 4 ^ (k + 1) + 21 * k * 4 ^ (k + 1) + 46) * 2 ^ (2 ^ (k + 4) + k + 3)
        ≤ 2 ^ (3 * k + 8) * 2 ^ (2 ^ (k + 4) + k + 3) := Nat.mul_le_mul_right _ hc
      _ = 2 ^ (2 ^ (k + 4) + 4 * k + 11) := by rw [← pow_add]; ring_nf
  have hsmall : 32 * 2 ^ k + k + 2 ≤ 2 ^ (2 ^ (k + 4) + 4 * k + 11) := by
    have h1 : 2 ^ (k + 6) ≤ 2 ^ (2 ^ (k + 4) + 4 * k + 11) := Nat.pow_le_pow_right (by norm_num)
      (by have := Nat.zero_le (2 ^ (k + 4)); omega)
    have h2 : 2 ^ (k + 6) = 2 ^ k * 64 := by rw [pow_add]; norm_num
    omega
  have hfin : 2 ^ (2 ^ (k + 4) + 4 * k + 12) ≤ 2 ^ (2 ^ (k + 5) + 6) := by
    apply Nat.pow_le_pow_right (by norm_num)
    have h1 : 2 ^ (k + 4) = 2 ^ k * 16 := by rw [pow_add]; norm_num
    have h2 : 2 ^ (k + 5) = 2 ^ k * 32 := by rw [pow_add]; norm_num
    omega
  have h12 : 2 ^ (2 ^ (k + 4) + 4 * k + 12) = 2 ^ (2 ^ (k + 4) + 4 * k + 11) * 2 := by
    rw [pow_succ]
  omega

/-- **Lemma 15.6's threshold at `β = θ/2` is polynomial in every dimension.** -/
theorem lemma156ExplicitThreshold_le_gen {gamma theta : Real} {k : Nat} (hk : 1 ≤ k)
    (hg : 0 < gamma) (hg1 : gamma ≤ 1) (ht : 0 < theta) (ht1 : theta ≤ 1) :
    lemma156ExplicitThreshold k (theta / 2) gamma ≤ (2 / (gamma * theta)) ^ (2 ^ (2 ^ (k + 5) + 6)) := by
  obtain ⟨hu2, -, -, h1, h2⟩ := prod_scale_basic hg hg1 ht ht1
  set u := 2 / (gamma * theta) with hu
  clear_value u
  have hupos : 0 < u := lt_of_lt_of_le (by norm_num) hu2
  set c := 7 * 4 ^ (k + 1) + 21 * k * 4 ^ (k + 1) with hcdef
  have hbase : (u ^ c)⁻¹ ≤ (theta / 2) ^ (7 * 4 ^ (k + 1)) * gamma ^ (21 * k * 4 ^ (k + 1)) := by
    have hp1 := pow_le_pow_left₀ (inv_pos.mpr hupos).le h1 (7 * 4 ^ (k + 1))
    have hp2 := pow_le_pow_left₀ (inv_pos.mpr hupos).le h2 (21 * k * 4 ^ (k + 1))
    calc (u ^ c)⁻¹ = u⁻¹ ^ (7 * 4 ^ (k + 1)) * u⁻¹ ^ (21 * k * 4 ^ (k + 1)) := by
          rw [← pow_add, inv_pow]
      _ ≤ _ := mul_le_mul hp1 hp2 (by positivity) (by positivity)
  exact lemma156ExplicitThreshold_le_power_of_selection_base hk hu2 hbase
    (by simpa only [hcdef, Nat.add_assoc] using gen_exp_fact4 k)
end LeanProofs.GowersSzemeredi
