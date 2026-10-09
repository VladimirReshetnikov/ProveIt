import GowersSzemeredi.Proofs16VarietyCountBounds
import GowersSzemeredi.Proofs16Lemma6Parameters

/-! Power bounds for the scales of the variety route, in `x = 2/(θγ)`.

The master loss bound of the variety route
(`Proofs16VarietyLossBound`) needs every count, density and Milićević bound of
the route bounded by a power of `x = 2/(θγ)`. The scales are:
* the variety family at `(γ, θ/4/2)` and its inverse density
  (`variety_family_le`, `variety_density_inv_le`);
* at the spectrum level, `θ₁ = θ₁(θ/2, γ, 2)` and `δ = δ(θ₁)`
  (`thetaOne_half_inv_le`, `delta_thetaOne_inv_le`), the spectrum family
  `bihomFamilySize … δ (θ₁/16)` and its inverse density
  (`spectrum_family_le`, `spectrum_density_inv_le`);
* `multipleS (θ/2) γ 2` (`multipleS_half_two_le`).

Every bound is stated with `x` opaque. The proofs only rewrite and apply
monotonicity, so no tactic expands a power with a large literal exponent. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

section
variable {theta gamma : Real}

theorem two_le_two_div (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1) :
    2 ≤ 2 / (theta * gamma) := by
  rw [le_div_iff₀ (by positivity)]
  nlinarith [mul_le_one₀ ht1 hg.le hg1]

theorem theta_inv_le (ht : 0 < theta) (hg : 0 < gamma) (hg1 : gamma ≤ 1) :
    theta⁻¹ ≤ 2 / (theta * gamma) := by
  rw [inv_eq_one_div, div_le_div_iff₀ ht (by positivity)]
  nlinarith

/-- `c ≤ x^k` from `c ≤ 2^k`. -/
theorem le_pow_of_two_le {x c : Real} {k : Nat} (hx : 2 ≤ x) (hc : c ≤ 2 ^ k) : c ≤ x ^ k :=
  hc.trans (pow_le_pow_left₀ (by norm_num) hx k)

/-- **The variety family at `(γ, θ/4/2)` is at most `x^(2^26)`.** -/
theorem variety_family_le (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1) :
    (bihomFamilySize (densePieceMassGen section16SharperLineMass) gamma (theta / 4 / 2) : Real) ≤
      (2 / (theta * gamma)) ^ ((2 : Nat) ^ 26) := by
  have h := bihomFamilySize_sharper_le_pow (theta := theta / 4 / 2) (by positivity) (by linarith) hg hg1
  have hx := two_le_two_div ht ht1 hg hg1
  have hbase : 2 / (theta / 4 / 2 * gamma) = 8 * (2 / (theta * gamma)) := by field_simp; ring
  rw [hbase] at h
  generalize 2 / (theta * gamma) = x at h hx ⊢
  have h8 : 8 * x ≤ x ^ 4 := by
    have : (8 : Real) ≤ x ^ 3 := le_pow_of_two_le hx (by norm_num)
    calc 8 * x ≤ x ^ 3 * x := mul_le_mul_of_nonneg_right this (le_trans (by norm_num) hx)
      _ = x ^ 4 := by ring
  calc _ ≤ (8 * x) ^ ((2 : Nat) ^ 24) := h
    _ ≤ (x ^ 4) ^ ((2 : Nat) ^ 24) := pow_le_pow_left₀ (by positivity) h8 _
    _ = x ^ ((2 : Nat) ^ 26) := by rw [← pow_mul]; norm_num

/-- **The inverse variety density, times four, is at most `x^(2^27)`.** -/
theorem variety_density_inv_le (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma)
    (hg1 : gamma ≤ 1) :
    4 / (theta / 4 / 2 / (bihomFamilySize (densePieceMassGen section16SharperLineMass) gamma
      (theta / 4 / 2) : Real)) ≤ (2 / (theta * gamma)) ^ ((2 : Nat) ^ 27) := by
  have hf := variety_family_le ht ht1 hg hg1
  have hti := theta_inv_le ht hg hg1
  have hx := two_le_two_div ht ht1 hg hg1
  have hfam : 4 / (theta / 4 / 2 / (bihomFamilySize (densePieceMassGen section16SharperLineMass)
      gamma (theta / 4 / 2) : Real)) = 32 * (bihomFamilySize (densePieceMassGen
        section16SharperLineMass) gamma (theta / 4 / 2) : Real) * theta⁻¹ := by
    field_simp; ring
  rw [hfam]
  have hF0 : (0 : Real) ≤ (bihomFamilySize (densePieceMassGen section16SharperLineMass) gamma
    (theta / 4 / 2) : Real) := Nat.cast_nonneg _
  generalize (bihomFamilySize (densePieceMassGen section16SharperLineMass) gamma (theta / 4 / 2) :
    Real) = F at hf hF0 ⊢
  generalize 2 / (theta * gamma) = x at hf hti hx ⊢
  have hx1 : 1 ≤ x := le_trans (by norm_num) hx
  have h32 : (32 : Real) ≤ x ^ 5 := le_pow_of_two_le hx (by norm_num)
  calc 32 * F * theta⁻¹ ≤ x ^ 5 * x ^ ((2 : Nat) ^ 26) * x :=
        mul_le_mul (mul_le_mul h32 hf hF0 (by positivity)) hti (by positivity) (by positivity)
    _ = x ^ ((2 : Nat) ^ 26 + 6) := by ring
    _ ≤ x ^ ((2 : Nat) ^ 27) := pow_le_pow_right₀ hx1 (by norm_num)

/-- **`θ₁(θ/2, γ, 2)⁻¹ ≤ x^(3·2^128)`.** -/
theorem thetaOne_half_inv_le (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma)
    (hg1 : gamma ≤ 1) :
    (section16ThetaOne (theta / 2) gamma 2)⁻¹ ≤ (2 / (theta * gamma)) ^ (3 * (2 : Nat) ^ 128) := by
  have hx := two_le_two_div ht ht1 hg hg1
  unfold section16ThetaOne
  have hbase : theta / 2 * gamma / 4 = (4 * (2 / (theta * gamma)))⁻¹ := by field_simp
  rw [hbase, inv_pow, inv_inv]
  generalize 2 / (theta * gamma) = x at hx ⊢
  have h4 : 4 * x ≤ x ^ 3 := by
    have : (4 : Real) ≤ x ^ 2 := le_pow_of_two_le hx (by norm_num)
    calc 4 * x ≤ x ^ 2 * x := mul_le_mul_of_nonneg_right this (by linarith)
      _ = x ^ 3 := by ring
  calc (4 * x) ^ ((2 : Nat) ^ ((2 : Nat) ^ (2 + 5))) ≤ (x ^ 3) ^ ((2 : Nat) ^ ((2 : Nat) ^ (2 + 5))) :=
        pow_le_pow_left₀ (by linarith) h4 _
    _ = x ^ (3 * (2 : Nat) ^ 128) := by rw [← pow_mul]; norm_num

/-- **`δ(θ₁)⁻¹ ≤ x^(19·2^128)`.** -/
theorem delta_thetaOne_inv_le (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma)
    (hg1 : gamma ≤ 1) :
    (section16Delta (section16ThetaOne (theta / 2) gamma 2))⁻¹ ≤
      (2 / (theta * gamma)) ^ (19 * (2 : Nat) ^ 128) := by
  -- arithmetic first: `linarith` must not see the big-power hypothesis `hθ1`
  obtain ⟨h1pos, h1le, -, -⟩ :=
    section16_theta_delta_bounds 2 (by positivity : 0 < theta / 2) (by linarith) hg hg1
  have hx := two_le_two_div ht ht1 hg hg1
  have hθ1 := thetaOne_half_inv_le ht ht1 hg hg1
  unfold section16Delta
  generalize section16ThetaOne (theta / 2) gamma 2 = t at hθ1 h1pos h1le ⊢
  generalize 2 / (theta * gamma) = x at hθ1 hx ⊢
  have hx1 : 1 ≤ x := le_trans (by norm_num) hx
  have h4t : 1 ≤ 4 / t := (one_le_div h1pos).mpr (h1le.trans (by norm_num))
  have hinv : ((2 : Real) ^ (-(37 : Real)) * (t / 4) ^ ((11 : Real) / 2))⁻¹ =
      2 ^ 37 * (4 / t) ^ ((11 : Real) / 2) := by
    rw [mul_inv, Real.rpow_neg (by norm_num), inv_inv, ← Real.inv_rpow (by positivity), inv_div,
      show (37 : Real) = ((37 : Nat) : Real) by norm_num, Real.rpow_natCast]
  rw [hinv]
  have h6 : (4 / t) ^ ((11 : Real) / 2) ≤ (4 / t) ^ (6 : Nat) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le h4t (by norm_num)
  have h4x : 4 / t ≤ x ^ (2 + 3 * 2 ^ 128) := by
    rw [div_eq_mul_inv, pow_add]
    exact mul_le_mul (le_pow_of_two_le hx (by norm_num)) hθ1 (by positivity) (by positivity)
  calc 2 ^ 37 * (4 / t) ^ ((11 : Real) / 2) ≤ x ^ 37 * (x ^ (2 + 3 * 2 ^ 128)) ^ 6 :=
        mul_le_mul (le_pow_of_two_le hx le_rfl) (h6.trans (pow_le_pow_left₀ (by positivity) h4x 6))
          (by positivity) (by positivity)
    _ = x ^ (49 + 18 * 2 ^ 128) := by rw [← pow_mul, ← pow_add]; norm_num
    _ ≤ x ^ (19 * (2 : Nat) ^ 128) := pow_le_pow_right₀ hx1 (by norm_num)

/-- **The spectrum family `bihomFamilySize … δ (θ₁/8/2)` is at most `x^(2^157)`.** -/
theorem spectrum_family_le (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1) :
    (bihomFamilySize (densePieceMassGen section16SharperLineMass)
      (section16Delta (section16ThetaOne (theta / 2) gamma 2))
      (section16ThetaOne (theta / 2) gamma 2 / 8 / 2) : Real) ≤
      (2 / (theta * gamma)) ^ ((2 : Nat) ^ 157) := by
  obtain ⟨h1pos, h1le, hdpos, hdle⟩ :=
    section16_theta_delta_bounds 2 (by positivity : 0 < theta / 2) (by linarith) hg hg1
  have hx := two_le_two_div ht ht1 hg hg1
  have h16 : section16ThetaOne (theta / 2) gamma 2 / 8 / 2 ≤ 1 := by linarith
  have h := bihomFamilySize_sharper_le_pow (theta := section16ThetaOne (theta / 2) gamma 2 / 8 / 2)
    (gamma := section16Delta (section16ThetaOne (theta / 2) gamma 2)) (by positivity) h16
    hdpos hdle
  have hθ1 := thetaOne_half_inv_le ht ht1 hg hg1
  have hδ := delta_thetaOne_inv_le ht ht1 hg hg1
  generalize section16Delta (section16ThetaOne (theta / 2) gamma 2) = d at hδ hdpos hdle h ⊢
  generalize section16ThetaOne (theta / 2) gamma 2 = t at hθ1 h1pos h1le h16 h ⊢
  generalize 2 / (theta * gamma) = x at hθ1 hδ hx ⊢
  have hx1 : 1 ≤ x := le_trans (by norm_num) hx
  have hbase : 2 / (t / 8 / 2 * d) = 32 * t⁻¹ * d⁻¹ := by field_simp; ring
  rw [hbase] at h
  have hB : 32 * t⁻¹ * d⁻¹ ≤ x ^ 5 * x ^ (3 * 2 ^ 128) * x ^ (19 * 2 ^ 128) :=
    mul_le_mul (mul_le_mul (le_pow_of_two_le hx (by norm_num)) hθ1 (by positivity) (by positivity))
      hδ (by positivity) (by positivity)
  calc _ ≤ (32 * t⁻¹ * d⁻¹) ^ ((2 : Nat) ^ 24) := h
    _ ≤ (x ^ 5 * x ^ (3 * 2 ^ 128) * x ^ (19 * 2 ^ 128)) ^ ((2 : Nat) ^ 24) :=
        pow_le_pow_left₀ (by positivity) hB _
    _ = x ^ ((5 + 22 * 2 ^ 128) * 2 ^ 24) := by rw [← pow_add, ← pow_add, ← pow_mul]; norm_num
    _ ≤ x ^ ((2 : Nat) ^ 157) := pow_le_pow_right₀ hx1 (by norm_num)

/-- **The inverse spectrum density, times four, is at most `x^(2^158)`.** -/
theorem spectrum_density_inv_le (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma)
    (hg1 : gamma ≤ 1) :
    4 / (section16ThetaOne (theta / 2) gamma 2 / 8 / 2 /
      (bihomFamilySize (densePieceMassGen section16SharperLineMass)
        (section16Delta (section16ThetaOne (theta / 2) gamma 2))
        (section16ThetaOne (theta / 2) gamma 2 / 8 / 2) : Real)) ≤
      (2 / (theta * gamma)) ^ ((2 : Nat) ^ 158) := by
  obtain ⟨h1pos, -, -, -⟩ :=
    section16_theta_delta_bounds 2 (by positivity : 0 < theta / 2) (by linarith) hg hg1
  have hx := two_le_two_div ht ht1 hg hg1
  have hf := spectrum_family_le ht ht1 hg hg1
  have hθ1 := thetaOne_half_inv_le ht ht1 hg hg1
  have hF0 : (0 : Real) ≤ (bihomFamilySize (densePieceMassGen section16SharperLineMass)
      (section16Delta (section16ThetaOne (theta / 2) gamma 2))
      (section16ThetaOne (theta / 2) gamma 2 / 8 / 2) : Real) := Nat.cast_nonneg _
  generalize (bihomFamilySize (densePieceMassGen section16SharperLineMass)
      (section16Delta (section16ThetaOne (theta / 2) gamma 2))
      (section16ThetaOne (theta / 2) gamma 2 / 8 / 2) : Real) = F at hf hF0 ⊢
  generalize section16ThetaOne (theta / 2) gamma 2 = t at hθ1 h1pos ⊢
  generalize 2 / (theta * gamma) = x at hf hθ1 hx ⊢
  have hx1 : 1 ≤ x := le_trans (by norm_num) hx
  have hfam : 4 / (t / 8 / 2 / F) = 64 * F * t⁻¹ := by
    rcases hF0.eq_or_lt with h0 | h0
    · subst h0; simp
    · field_simp; ring
  rw [hfam]
  calc 64 * F * t⁻¹ ≤ x ^ 6 * x ^ ((2 : Nat) ^ 157) * x ^ (3 * 2 ^ 128) :=
        mul_le_mul (mul_le_mul (le_pow_of_two_le hx (by norm_num)) hf hF0 (by positivity)) hθ1
          (by positivity) (by positivity)
    _ = x ^ (6 + 2 ^ 157 + 3 * 2 ^ 128) := by rw [← pow_add, ← pow_add]
    _ ≤ x ^ ((2 : Nat) ^ 158) := pow_le_pow_right₀ hx1 (by norm_num)

/-- **`multipleS (θ/2) γ 2 ≤ x^(2·2^256)`.** -/
theorem multipleS_half_two_le (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma)
    (hg1 : gamma ≤ 1) :
    multipleS (theta / 2) gamma 2 ≤ (2 / (theta * gamma)) ^ (2 * (2 : Nat) ^ ((2 : Nat) ^ (2 + 6))) := by
  have hx := two_le_two_div ht ht1 hg hg1
  unfold multipleS
  have hbase : 2 / (theta / 2 * gamma) = 2 * (2 / (theta * gamma)) := by field_simp
  rw [hbase]
  generalize 2 / (theta * gamma) = x at hx ⊢
  have h2x : 2 * x ≤ x ^ 2 := by nlinarith
  calc (2 * x) ^ ((2 : Nat) ^ ((2 : Nat) ^ (2 + 6))) ≤ (x ^ 2) ^ ((2 : Nat) ^ ((2 : Nat) ^ (2 + 6))) :=
        pow_le_pow_left₀ (by linarith) h2x _
    _ = x ^ (2 * (2 : Nat) ^ ((2 : Nat) ^ (2 + 6))) := by rw [← pow_mul]

end

end LeanProofs.GowersSzemeredi
