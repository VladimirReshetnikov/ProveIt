import GowersSzemeredi.Proofs16CoverParameterMonotonicity

/-! Quantitative absorption of the compatible-tiling loss when adding one
unused coordinate. This concerns dimension extension, not the unresolved
sampling comparison of Lemma 16.10. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

theorem section16_dimension_exponent_gap (k : Nat) {gamma theta s : Real}
    (hg : 0 < gamma) (hg1 : gamma ≤ 1) (ht : 0 < theta) (ht1 : theta ≤ 1) (hs : 2 ≤ s) :
    0 < (multipleC (s⁻¹ * theta) gamma k) ^ s ∧
      (multipleC (s⁻¹ * theta) gamma k) ^ s ≤ 1 ∧
      0 < (multipleC (s⁻¹ * theta) gamma (k + 1)) ^ s ∧
      16 * (multipleC (s⁻¹ * theta) gamma (k + 1)) ^ s ≤
        (multipleC (s⁻¹ * theta) gamma k) ^ s := by
  let b := gamma * (s⁻¹ * theta)
  let E : Nat := 2 ^ (2 ^ (k + 8))
  let c := multipleC (s⁻¹ * theta) gamma k
  let a := c ^ s
  have hs0 : 0 < s := by linarith
  have hb : 0 < b := by dsimp [b]; positivity
  have hbhalf : b ≤ 1 / 2 := by
    have hi : s⁻¹ ≤ (2 : Real)⁻¹ := inv_anti₀ (by norm_num) hs
    calc
      b ≤ 1 * ((2 : Real)⁻¹ * 1) := by
        dsimp [b]
        exact mul_le_mul hg1 (mul_le_mul hi ht1 ht.le (by positivity)) (by positivity) (by norm_num)
      _ = 1 / 2 := by norm_num
  have hE : 5 ≤ E := by
    have hinner : 3 ≤ (2 : Nat) ^ (k + 8) :=
      (by norm_num : 3 ≤ 2 ^ 2).trans (Nat.pow_le_pow_right (by omega) (by omega))
    exact (by norm_num : 5 ≤ 2 ^ 3).trans (Nat.pow_le_pow_right (by omega) hinner)
  have hc : 0 < c := pow_pos hb E
  have hchalf : c ≤ 1 / 2 :=
    (pow_le_of_le_one hb.le (by linarith : b ≤ 1) (by omega : E ≠ 0)).trans hbhalf
  have ha : 0 < a := Real.rpow_pos_of_pos hc s
  have hahalf : a ≤ 1 / 2 := by
    calc
      a ≤ c ^ (1 : Real) := Real.rpow_le_rpow_of_exponent_ge hc (by linarith) (by linarith)
      _ = c := Real.rpow_one _
      _ ≤ _ := hchalf
  have heq : (multipleC (s⁻¹ * theta) gamma (k + 1)) ^ s = a ^ E := by
    have he : (2 : Nat) ^ (2 ^ (k + 1 + 8)) = E * E := by
      rw [show k + 1 + 8 = (k + 8) + 1 by omega, pow_succ, pow_mul]
      simp only [E, pow_two]
    change (b ^ (2 ^ (2 ^ (k + 1 + 8)))) ^ s = a ^ E
    rw [he, pow_mul]
    exact (Real.rpow_pow_comm (by positivity : 0 ≤ b ^ E) s E).symm
  refine ⟨ha, by linarith, by rw [heq]; positivity, ?_⟩
  rw [heq]
  have hbound : a ^ E ≤ a / 16 := by
    calc
      a ^ E ≤ a ^ 5 := pow_le_pow_of_le_one ha.le (by linarith) hE
      _ = a * a ^ 4 := by ring
      _ ≤ a * (1 / 2 : Real) ^ 4 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ha.le hahalf 4) ha.le
      _ = a / 16 := by ring
  linarith

/-- If the higher-dimensional target exceeds two, its exponent gap absorbs
both localization and the square-root tiling loss, and guarantees large scale. -/
theorem section16_unused_coordinate_width_budget {m a A : Real}
    (hm : 1 ≤ m) (ha : 0 < a) (ha1 : a ≤ 1) (hA : 0 < A)
    (hgap : 16 * A ≤ a) (hlarge : 2 < m ^ A) :
    4 ≤ m ∧ 16 ≤ (m / 8) ^ a ∧ m ^ A ≤ Real.sqrt ((m / 8) ^ a) / 4 := by
  let x := m ^ A
  have hx : 2 < x := hlarge
  have hx0 : 0 < x := by linarith
  have hpow : x ^ 16 ≤ m ^ a := by
    rw [show x ^ 16 = m ^ (A * 16) by
      dsimp [x]
      simpa only [Nat.cast_ofNat] using (Real.rpow_mul_natCast (by linarith : 0 ≤ m) A 16).symm]
    exact Real.rpow_le_rpow_of_exponent_le hm (by linarith)
  have h14 : (128 : Real) ≤ x ^ 14 := by
    exact (by norm_num : (128 : Real) ≤ 2 ^ 14).trans
      (pow_le_pow_left₀ (by norm_num) hx.le 14)
  have hmain : 128 * x ^ 2 ≤ m ^ a := by
    calc
      _ ≤ x ^ 14 * x ^ 2 := mul_le_mul_of_nonneg_right h14 (sq_nonneg x)
      _ = x ^ 16 := by ring
      _ ≤ _ := hpow
  have haM : m ^ a ≤ m := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hm ha1
  have h8 : (8 : Real) ^ a ≤ 8 := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : Real) ≤ 8) ha1
  have hZ : 16 * x ^ 2 ≤ (m / 8) ^ a := by
    rw [Real.div_rpow (by linarith : 0 ≤ m) (by norm_num : (0 : Real) ≤ 8)]
    apply (le_div_iff₀ (Real.rpow_pos_of_pos (by norm_num : (0 : Real) < 8) a)).mpr
    calc
      _ ≤ (16 * x ^ 2) * 8 := mul_le_mul_of_nonneg_left h8 (by positivity)
      _ = 128 * x ^ 2 := by ring
      _ ≤ _ := hmain
  have hZ0 : 0 ≤ (m / 8) ^ a := Real.rpow_nonneg (by linarith) a
  have hsq := Real.sq_sqrt hZ0
  have hsqrt := Real.sqrt_nonneg ((m / 8) ^ a)
  refine ⟨by nlinarith, by nlinarith, ?_⟩
  change x ≤ _
  nlinarith

end LeanProofs.GowersSzemeredi
