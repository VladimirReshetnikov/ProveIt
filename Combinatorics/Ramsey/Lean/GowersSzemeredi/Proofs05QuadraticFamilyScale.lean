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
  generalize hW : r ^ ((2048 : Real) ^ q)⁻¹ = W at hroot hU
  have hpower : (W ^ (2 ^ q)) ^ (1024 ^ q) = r := by
    rw [← hW, ← pow_mul, ← mul_pow]
    exact_mod_cast Real.rpow_inv_natCast_pow hr (by positivity : (2048 : Nat) ^ q ≠ 0)
  have hupper : 4 * (U : Real) ≤ W ^ (2 ^ q) := by
    nlinarith [sq_nonneg (W - 4),
      pow_le_pow_right₀ (by linarith : 1 ≤ W) (Nat.le_self_pow (by omega : q ≠ 0) 2)]
  have hb : 4 * (quadraticFamilyBudget q U : Real) ≤ (4 * (U : Real)) ^ (1024 ^ q) := by
    exact_mod_cast quadraticFamilyBudget_bound q U
  have hp := hpower ▸ pow_le_pow_left₀ (by positivity) hupper (1024 ^ q)
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
  have hr0 : 0 ≤ r := by linarith only [hr]
  have hX : 2 < X := hlarge
  -- `X ^ 2 = r ^ (2 / 4096 ^ q) ≤ r ^ (1 / 2048 ^ q) = W` since `2 * 2048 ^ q ≤ 4096 ^ q`
  have hXsq : X ^ 2 ≤ W := by
    dsimp only [X, W]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hr0]
    refine Real.rpow_le_rpow_of_exponent_le hr ((inv_mul_le_iff₀ (by positivity)).mpr
      ((le_mul_inv_iff₀ (by positivity)).mpr ?_))
    rw [Nat.cast_ofNat, show (4096 : Real) = 2 * 2048 by norm_num, mul_pow]
    gcongr
    exact le_self_pow₀ one_le_two (by omega)
  have hWfour : 4 < W := by nlinarith only [hX, hXsq]
  have hUfour : 4 ≤ ⌊W⌋₊ := Nat.le_floor (by exact_mod_cast hWfour.le)
  have hround : W < (⌊W⌋₊ : Real) + 1 := Nat.lt_floor_add_one W
  have hhalf : W ≤ 2 * (⌊W⌋₊ : Real) := by
    have hu4 : (4 : Real) ≤ ⌊W⌋₊ := by exact_mod_cast hUfour
    linarith only [hround, hu4]
  refine ⟨hUfour, quadraticFamilyBudget_root_bound hr0 hq hWfour.le
    (Nat.floor_le (by positivity)), ?_, ?_⟩
  · change X / 2 ≤ (⌊W⌋₊ : Real)
    nlinarith only [hX, hXsq, hhalf]
  · rw [Real.rpow_neg hr0, one_div]
    exact inv_anti₀ (by linarith only [hWfour]) hhalf

end LeanProofs.GowersSzemeredi
