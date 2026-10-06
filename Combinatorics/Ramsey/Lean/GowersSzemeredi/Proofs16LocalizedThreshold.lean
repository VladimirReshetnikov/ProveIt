import GowersSzemeredi.Proofs16LocalizationBudget

/-! # Threshold slack after preliminary localization

The reciprocal Section 16 radius dominates the polynomial threshold with
room for the factor sixteen lost by localization and integer rounding.
-/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- There is a strict exponent margin in the Section 16 threshold comparison. -/
theorem section16_iteration_dominates_polynomial_margin (k : Nat) :
    40 * (k + 1) ^ 3 + 1 ≤ (2 : Nat) ^ ((2 : Nat) ^ (k + 6)) := by
  have hk : k + 1 ≤ 2 ^ k := Nat.lt_two_pow_self
  have hpow : (k + 1) ^ 3 ≤ (2 ^ k) ^ 3 := Nat.pow_le_pow_left hk 3
  have hpos : 1 ≤ (2 ^ k) ^ 3 := one_le_pow₀ (one_le_pow₀ (by norm_num))
  have hexp : 3 * k + 6 ≤ (2 : Nat) ^ (k + 6) := by
    rw [pow_add]
    norm_num
    omega
  calc
    40 * (k + 1) ^ 3 + 1 ≤ 64 * (2 ^ k) ^ 3 := by omega
    _ = (2 : Nat) ^ (3 * k + 6) := by rw [pow_add]; ring
    _ ≤ _ := Nat.pow_le_pow_right (by norm_num) hexp

/-- The Section 16 radius absorbs the factor sixteen in the recurrence root. -/
theorem section16_polynomial_threshold_radius_margin {theta gamma : Real} (k : Nat)
    (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1) :
    16 * ((2 * polynomialPartitionThreshold (k + 1) : Nat) : Real) ≤
      (2 / section16Zeta theta gamma k) ^ (2 : Nat) := by
  let W : Nat := 2 ^ (40 * (k + 1) ^ 3)
  let S := multipleS theta gamma k
  have hp : 0 < theta * gamma := mul_pos ht hg
  have hb : (2 : Real) ≤ 2 / (theta * gamma) := by
    apply (le_div_iff₀ hp).mpr
    nlinarith
  have hW : (2 : Real) ≤ W := by
    have hpow : 1 ≤ 40 * (k + 1) ^ 3 := by
      have h : 0 < 40 * (k + 1) ^ 3 := by positivity
      omega
    exact_mod_cast (show (2 : Nat) ≤ W from
      (by simpa only [pow_one] using Nat.pow_le_pow_right (by norm_num : 1 ≤ (2 : Nat)) hpow))
  have hS : 2 * (W : Real) ≤ S := by
    have htwice : 2 * (W : Real) = (2 : Real) ^ (40 * (k + 1) ^ 3 + 1) := by
      dsimp [W]
      push_cast
      rw [pow_succ]
      ring
    rw [htwice]
    calc
      _ ≤ (2 : Real) ^ ((2 : Nat) ^ ((2 : Nat) ^ (k + 6))) :=
        pow_le_pow_right₀ (by norm_num) (section16_iteration_dominates_polynomial_margin k)
      _ ≤ _ := pow_le_pow_left₀ (by norm_num) hb _
  have hleft : 16 * ((2 * polynomialPartitionThreshold (k + 1) : Nat) : Real) =
      (2 : Real) ^ (5 + 2 * (W : Real)) := by
    unfold polynomialPartitionThreshold weylThreshold
    push_cast
    rw [Real.rpow_add (by norm_num : (0 : Real) < 2),
      mul_comm (2 : Real) (W : Real), Real.rpow_mul (by norm_num : (0 : Real) ≤ 2),
      Real.rpow_natCast, Real.rpow_ofNat]
    norm_num
    ring
  have hright : (2 / section16Zeta theta gamma k) ^ (2 : Nat) =
      (2 : Real) ^ (2 + 2 * S) := by
    unfold section16Zeta
    change (2 / (2 : Real) ^ (-S)) ^ (2 : Nat) = _
    rw [Real.rpow_neg (by norm_num : (0 : Real) ≤ 2), div_inv_eq_mul, mul_pow,
      ← Real.rpow_natCast ((2 : Real) ^ S) 2, ← Real.rpow_mul (by norm_num : (0 : Real) ≤ 2)]
    rw [Real.rpow_add (by norm_num : (0 : Real) < 2)]
    norm_num [mul_comm]
  rw [hleft, hright]
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)

/-- A large original target supplies the full threshold even after the
recurrence root loses its localization factor. -/
theorem section16_localized_threshold {theta gamma s : Real} {k q p : Nat}
    (hk : 1 ≤ k) (hp : 0 < p)
    (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    (hs : 0 ≤ s) (hroot : s ≤ 16 * (p : Real) ^ section16RecurrenceExponent k q)
    (hlarge : 1 < (section16Zeta theta gamma k / 2) * Real.sqrt s) :
    section16WidthThreshold k q ≤ p := by
  have hz := (section16Zeta_pos_le_half k ht ht1 hg hg1).1
  have hscale : 2 / section16Zeta theta gamma k ≤ Real.sqrt s := by
    apply (div_le_iff₀ hz).mpr
    nlinarith
  have hsq := pow_le_pow_left₀ (by positivity : 0 ≤ 2 / section16Zeta theta gamma k) hscale 2
  rw [Real.sq_sqrt hs] at hsq
  have hmargin := section16_polynomial_threshold_radius_margin k ht ht1 hg hg1
  apply section16WidthThreshold_of_root hk hp
  linarith

/-- The Bohr radius is small enough for the localized ceiling budget. -/
theorem section16Zeta_pos_le_one_div_32 {theta gamma : Real} (k : Nat)
    (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1) :
    0 < section16Zeta theta gamma k ∧ section16Zeta theta gamma k ≤ 1 / 32 := by
  have hp : 0 < theta * gamma := mul_pos ht hg
  have hb : (2 : Real) ≤ 2 / (theta * gamma) := by
    apply (le_div_iff₀ hp).mpr
    nlinarith
  have he : 3 ≤ (2 : Nat) ^ ((2 : Nat) ^ (k + 6)) := by
    have h : k + 6 < (2 : Nat) ^ (k + 6) := Nat.lt_two_pow_self
    have h' : (2 : Nat) ^ (k + 6) < 2 ^ ((2 : Nat) ^ (k + 6)) := Nat.lt_two_pow_self
    omega
  have hS : 5 ≤ multipleS theta gamma k := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : Real) ≤ 2) hb ((2 : Nat) ^ ((2 : Nat) ^ (k + 6)))
    have h' := pow_le_pow_right₀ (by norm_num : (1 : Real) ≤ 2) he
    norm_num at h'
    change 5 ≤ (2 / (theta * gamma)) ^ ((2 : Nat) ^ ((2 : Nat) ^ (k + 6)))
    linarith
  constructor
  · unfold section16Zeta; positivity
  · unfold section16Zeta
    have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : Real) ≤ 2) (neg_le_neg hS)
    norm_num at h
    exact h

/-- The recurrence exponent always lies in (0,1], including zero frequencies. -/
theorem section16RecurrenceExponent_pos_le_one (k q : Nat) :
    0 < section16RecurrenceExponent k q ∧ section16RecurrenceExponent k q ≤ 1 := by
  have hK : (1 : Real) ≤ section16K k := by
    have h : 0 < section16K k := by unfold section16K; positivity
    exact_mod_cast h
  unfold section16RecurrenceExponent
  rw [zpow_neg, zpow_natCast]
  have hpow : (1 : Real) ≤ (section16K k : Real) ^ (2 ^ (k + 1) * q) := one_le_pow₀ hK
  exact ⟨inv_pos.mpr (by linarith), inv_le_one_of_one_le₀ hpow⟩

/-- All scale hypotheses for the localized recurrence follow from the
original above-one width target, without reducing that target. -/
theorem section16_localized_parameters {theta gamma a : Real} {k q m : Nat}
    (hk : 1 ≤ k) (hm : 1 ≤ m)
    (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    (ha : 0 < a) (ha1 : a ≤ 1)
    (hlarge : 1 < (section16Zeta theta gamma k / 2) *
      Real.sqrt ((m : Real) ^ (a * section16RecurrenceExponent k q))) :
    let p := Nat.floor (((m : Real) / 8) ^ a)
    4 ≤ m ∧ 0 < p ∧ section16WidthThreshold k q ≤ p ∧
      ∃ v : Nat, 2 ≤ v ∧
        (section16Zeta theta gamma k / 2) *
          Real.sqrt ((m : Real) ^ (a * section16RecurrenceExponent k q)) ≤ (v - 1 : Nat) ∧
        (v : Real) ^ 2 + 1 ≤ (p : Real) ^ section16RecurrenceExponent k q ∧
        2 * (p : Real) ^ (-section16RecurrenceExponent k q) ≤ section16Zeta theta gamma k / v := by
  obtain ⟨he, he1⟩ := section16RecurrenceExponent_pos_le_one k q
  obtain ⟨hz, hz32⟩ := section16Zeta_pos_le_one_div_32 k ht ht1 hg hg1
  have hmr : (1 : Real) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : Real) < m := by linarith
  obtain ⟨hm4, hx⟩ := localization_inputs_of_large_target hmr ha ha1 he he1 hz hz32 hlarge
  obtain ⟨hp, hroot⟩ := localization_recurrence_root hm0 ha ha1 he he1 hx
  have hs := Real.rpow_pos_of_pos hm0 (a * section16RecurrenceExponent k q)
  have hthreshold := section16_localized_threshold hk hp ht ht1 hg hg1 hs.le hroot hlarge
  obtain ⟨v, hv, hvwidth, hvscale, hvbudget⟩ := section16_localized_short_scale
    _ _ _ hs hroot hz hz32 hlarge
  refine ⟨by exact_mod_cast hm4, hp, hthreshold, v, hv, hvwidth, hvscale, ?_⟩
  have hp0 : (0 : Real) ≤ Nat.floor (((m : Real) / 8) ^ a) := Nat.cast_nonneg _
  rw [Real.rpow_neg hp0]
  simpa only [div_eq_mul_inv] using hvbudget

end LeanProofs.GowersSzemeredi
