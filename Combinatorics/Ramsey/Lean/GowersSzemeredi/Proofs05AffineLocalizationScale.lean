import GowersSzemeredi.Section05

/-! A diameter scale for lossless affine localization. The integer ceiling
is accounted for without any extra lower bound on the ambient modulus. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

theorem affine_localization_eighth_power_budget {L : Nat} (hL : 2 ≤ L) :
    1024 * L ^ 3 ≤ (2 * L) ^ 8 := by
  have hpow : 4 ≤ L ^ 5 := (by norm_num : (4 : Nat) ≤ 2 ^ 5).trans (Nat.pow_le_pow_left hL 5)
  calc
    1024 * L ^ 3 ≤ (256 * L ^ 5) * L ^ 3 := Nat.mul_le_mul_right _ (by omega)
    _ = (2 * L) ^ 8 := by ring

theorem affine_localization_diameter_scale {N r L : Nat}
    (hN : 0 < N) (hL : 2 ≤ L) (hr : 1024 * L ^ 3 ≤ r) (hrN : r ≤ N) :
    ∃ s : Nat, 0 < s ∧ s ≤ N ∧ N ≤ r * s ∧
      (L : Real) ≤ Real.sqrt ((r : Real) * s / (16 * N)) ∧
      2 * Real.pi * s / N ≤ 1 / (4 * L) := by
  have hNr : (0 : Real) < N := by exact_mod_cast hN
  have hLr : (2 : Real) ≤ L := by exact_mod_cast hL
  have hrr : 1024 * (L : Real) ^ 3 ≤ r := by exact_mod_cast hr
  have hrNr : (r : Real) ≤ N := by exact_mod_cast hrN
  have hL2 : (4 : Real) ≤ (L : Real) ^ 2 := by
    linarith [mul_le_mul hLr hLr (by norm_num) (by linarith)]
  -- `s = ⌈x⌉` with `x = N / (64 L) ≥ 16 L²`, so `x ≤ s < x + 1 ≤ 2x`
  set x : Real := N / (64 * L)
  have hxL : x * (64 * L) = N := div_mul_cancel₀ _ (by positivity)
  have hx : 16 * (L : Real) ^ 2 ≤ x := (le_div_iff₀ (by positivity)).mpr (by linarith)
  have hx0 : 0 ≤ x := by linarith
  obtain ⟨s, hslo, hshi⟩ : ∃ s : Nat, x ≤ s ∧ (s : Real) < x + 1 :=
    ⟨⌈x⌉₊, Nat.le_ceil x, Nat.ceil_lt_add_one hx0⟩
  have hprod : 16 * (L : Real) ^ 2 * N ≤ r * s := by
    rw [← hxL]
    linarith [mul_le_mul_of_nonneg_right hrr hx0,
      mul_le_mul_of_nonneg_left hslo (Nat.cast_nonneg r)]
  refine ⟨s, by exact_mod_cast (show (0 : Real) < s by linarith), ?_, ?_, ?_, ?_⟩
  · exact_mod_cast (show (s : Real) ≤ N by linarith [mul_le_mul_of_nonneg_left hLr hx0])
  · exact_mod_cast (show (N : Real) ≤ r * s by
      linarith [mul_le_mul_of_nonneg_right hL2 hNr.le])
  · exact Real.le_sqrt_of_sq_le ((le_div_iff₀ (by positivity)).mpr (by linarith))
  · rw [div_le_div_iff₀ hNr (by positivity)]
    linarith [mul_le_mul_of_nonneg_left (show (s : Real) ≤ 2 * x by linarith)
      (by positivity : (0 : Real) ≤ Real.pi * L),
      mul_le_mul_of_nonneg_right Real.pi_le_four (by positivity : (0 : Real) ≤ L * x)]

end LeanProofs.GowersSzemeredi
