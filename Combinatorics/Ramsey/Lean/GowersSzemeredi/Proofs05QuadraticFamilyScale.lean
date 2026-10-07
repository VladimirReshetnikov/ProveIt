import GowersSzemeredi.Proofs05QuadraticFamily

/-! The simultaneous quadratic budget fits the printed recurrence exponents
without an asymptotic Weyl threshold. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

theorem quadraticFamilyBudget_root_bound {r : Real} (hr : 0 ≤ r)
    {q U : Nat} (hq : 1 ≤ q)
    (hroot : 4 ≤ r ^ ((2048 : Real) ^ q)⁻¹)
    (hU : (U : Real) ≤ r ^ ((2048 : Real) ^ q)⁻¹) :
    (quadraticFamilyBudget q U : Real) ≤ r := by
  let W := r ^ ((2048 : Real) ^ q)⁻¹
  have hW : 1 ≤ W := by dsimp [W]; linarith only [hroot]
  have hfour : 4 * (U : Real) ≤ W ^ 2 := by
    have hu : (U : Real) ≤ W := hU
    have hw : 4 ≤ W := hroot
    nlinarith [sq_nonneg (W - 4)]
  have htwo : 2 ≤ (2 : Nat) ^ q := by
    exact (show (2 : Nat) ^ 1 = 2 by norm_num) ▸
      Nat.pow_le_pow_right (by omega) hq
  have hupper : 4 * (U : Real) ≤ W ^ (2 ^ q) :=
    hfour.trans (pow_le_pow_right₀ hW htwo)
  have hpower : (W ^ (2 ^ q)) ^ (1024 ^ q) = r := by
    rw [← pow_mul, ← mul_pow]
    change W ^ (2048 ^ q) = r
    have he : ((2048 ^ q : Nat) : Real) = (2048 : Real) ^ q := by push_cast; rfl
    simpa only [W, he] using
      (Real.rpow_inv_natCast_pow hr (by positivity : (2048 : Nat) ^ q ≠ 0))
  have hb : 4 * (quadraticFamilyBudget q U : Real) ≤ (4 * (U : Real)) ^ (1024 ^ q) := by
    exact_mod_cast quadraticFamilyBudget_bound q U
  have hp := pow_le_pow_left₀ (by positivity : (0 : Real) ≤ 4 * U) hupper (1024 ^ q)
  rw [hpower] at hp
  have hf : (0 : Real) ≤ quadraticFamilyBudget q U := Nat.cast_nonneg _
  linarith only [hb, hp, hf]

theorem quadratic_family_floor_scale {r : Real} (hr : 1 ≤ r) {q : Nat} (hq : 1 ≤ q)
    (hlarge : 2 < r ^ ((4096 : Real) ^ q)⁻¹) :
    let U := Nat.floor (r ^ ((2048 : Real) ^ q)⁻¹)
    4 ≤ U ∧ (quadraticFamilyBudget q U : Real) ≤ r ∧
      r ^ ((4096 : Real) ^ q)⁻¹ / 2 ≤ U ∧
      1 / (2 * (U : Real)) ≤ r ^ (-((2048 : Real) ^ q)⁻¹) := by
  let X := r ^ ((4096 : Real) ^ q)⁻¹
  let W := r ^ ((2048 : Real) ^ q)⁻¹
  let U := Nat.floor W
  have hr0 : 0 ≤ r := by linarith only [hr]
  have hX : 2 < X := hlarge
  have hden : 2 * (2048 : Real) ^ q ≤ (4096 : Real) ^ q := by
    have htwo : (2 : Real) ≤ 2 ^ q := by
      simpa using pow_le_pow_right₀ (by norm_num : (1 : Real) ≤ 2) hq
    calc
      _ ≤ (2 : Real) ^ q * (2048 : Real) ^ q :=
        mul_le_mul_of_nonneg_right htwo (by positivity)
      _ = _ := by rw [← mul_pow]; norm_num
  have hXsq : X ^ 2 ≤ W := by
    dsimp [X, W]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hr0]
    apply Real.rpow_le_rpow_of_exponent_le hr
    apply (mul_le_mul_iff_right₀ (by positivity : (0 : Real) < (4096 : Real) ^ q)).mp
    field_simp
    exact hden
  have hWfour : 4 < W := by nlinarith only [hX, hXsq]
  have hUfour : 4 ≤ U := by
    apply (Nat.le_floor_iff (by positivity : 0 ≤ W)).mpr
    exact hWfour.le
  have hUle : (U : Real) ≤ W := Nat.floor_le (by positivity)
  have hround : W < (U : Real) + 1 := Nat.lt_floor_add_one W
  have hUpos : (0 : Real) < U := by exact_mod_cast (by omega : 0 < U)
  have hhalf : W ≤ 2 * (U : Real) := by
    have hu4 : (4 : Real) ≤ U := by exact_mod_cast hUfour
    linarith only [hround, hu4]
  refine ⟨hUfour, quadraticFamilyBudget_root_bound hr0 hq hWfour.le hUle, ?_, ?_⟩
  · change X / 2 ≤ (U : Real)
    have hxw : X ≤ W := by nlinarith only [hX, hXsq]
    linarith only [hxw, hhalf]
  · rw [Real.rpow_neg hr0]
    change 1 / (2 * (U : Real)) ≤ W⁻¹
    simpa only [one_div] using one_div_le_one_div_of_le (by linarith only [hWfour]) hhalf

end LeanProofs.GowersSzemeredi
