import GowersSzemeredi.Section05

/-! Rounding the exact Corollary 5.8 target length. These inequalities
explain why the same target can be used in the variance and localization
branches without imposing an additional scale hypothesis. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

theorem threshold_free_target_scale {S : Real} {K : Nat}
    (hS : 1 ≤ S) (hK : 4 ≤ K) :
    let L := Nat.ceil (S ^ (K : Real)⁻¹ / 8)
    1 ≤ L ∧ S ^ (K : Real)⁻¹ / 8 ≤ L ∧
      (2 ≤ L → (4 * (L : Real)) ^ K < S ∧ (L : Real) ^ 3 < S) := by
  let x : Real := S ^ (K : Real)⁻¹ / 8
  let L := Nat.ceil x
  have hS0 : 0 < S := zero_lt_one.trans_le hS
  have hx : 0 < x := by dsimp [x]; positivity
  have hL : 1 ≤ L := Nat.ceil_pos.mpr hx
  have hxL : x ≤ L := Nat.le_ceil x
  refine ⟨hL, hxL, ?_⟩
  intro hL2
  change 2 ≤ L at hL2
  have hx1 : 1 < x := by
    by_contra hno
    have hle : L ≤ 1 := Nat.ceil_le.mpr (by simpa only [Nat.cast_one] using le_of_not_gt hno)
    omega
  have hLx : (L : Real) < 2 * x := by
    have hceil := Nat.ceil_lt_add_one hx.le
    change (L : Real) < x + 1 at hceil
    linarith
  have hroot : (4 * (L : Real)) < S ^ (K : Real)⁻¹ := by
    dsimp [x] at hLx
    linarith
  have hK0 : (K : Real) ≠ 0 := by exact_mod_cast (show K ≠ 0 by omega)
  have hpow : (S ^ (K : Real)⁻¹) ^ K = S := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hS0.le, inv_mul_cancel₀ hK0, Real.rpow_one]
  have hscale : (4 * (L : Real)) ^ K < S := by
    rw [← hpow]
    exact pow_lt_pow_left₀ hroot (by positivity) (by omega)
  refine ⟨hscale, lt_of_le_of_lt ?_ hscale⟩
  have hLr : (1 : Real) ≤ L := by exact_mod_cast hL
  calc
    (L : Real) ^ 3 ≤ (4 * (L : Real)) ^ 3 := pow_le_pow_left₀ (by positivity) (by linarith) _
    _ ≤ (4 * (L : Real)) ^ K := pow_le_pow_right₀ (by linarith) (by omega)

theorem threshold_free_localization_budget {K L : Nat} (hK : 4 ≤ K) (hL : 1 ≤ L) :
    8 * (L : Real) * (2 * (L : Real)) ^ (K / 2) ≤ (4 * (L : Real)) ^ K := by
  have hLr : (1 : Real) ≤ L := by exact_mod_cast hL
  have hhalf : K / 2 + 1 ≤ K := by omega
  have hfour : (4 : Real) ≤ (2 : Real) ^ K := by
    calc
      (4 : Real) = (2 : Real) ^ 2 := by norm_num
      _ ≤ (2 : Real) ^ K := pow_le_pow_right₀ (by norm_num) (by omega)
  calc
    _ = 4 * (2 * (L : Real)) ^ (K / 2 + 1) := by rw [pow_succ]; ring
    _ ≤ 4 * (2 * (L : Real)) ^ K :=
      mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by linarith) hhalf) (by norm_num)
    _ ≤ (2 : Real) ^ K * (2 * (L : Real)) ^ K :=
      mul_le_mul_of_nonneg_right hfour (by positivity)
    _ = (4 * (L : Real)) ^ K := by rw [← mul_pow]; congr 1; ring

theorem threshold_free_parent_large {K L M N r : Nat}
    (hK : 4 ≤ K) (hL : 1 ≤ L) (hM : 0 < M) (hN : 0 < N)
    (hscale : (4 * (L : Real)) ^ K < (N : Real) / M)
    (hparent : 3 * (N : Real) < 8 * L * M * r) :
    (2 * L) ^ (K / 2) < r := by
  have hMr : (0 : Real) < M := by exact_mod_cast hM
  have hLr : (0 : Real) < L := by exact_mod_cast (show 0 < L by omega)
  have hNr : (0 : Real) < N := by exact_mod_cast hN
  have hscale' := (lt_div_iff₀ hMr).mp hscale
  have hbudget := mul_le_mul_of_nonneg_right (threshold_free_localization_budget hK hL) hMr.le
  have h : 8 * (L : Real) * M * (2 * (L : Real)) ^ (K / 2) <
      8 * (L : Real) * M * r := by nlinarith [hbudget, hscale', hparent]
  have hcancel := (mul_lt_mul_iff_right₀ (show (0 : Real) < 8 * L * M by positivity)).mp h
  exact_mod_cast hcancel

end LeanProofs.GowersSzemeredi
