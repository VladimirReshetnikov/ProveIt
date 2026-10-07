import GowersSzemeredi.Section05

/-! A diameter scale for lossless affine localization. The integer ceiling
is accounted for without any extra lower bound on the ambient modulus. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

theorem affine_localization_eighth_power_budget {L : Nat} (hL : 2 ≤ L) :
    1024 * L ^ 3 ≤ (2 * L) ^ 8 := by
  have hpow : 4 ≤ L ^ 5 := by
    exact (by norm_num : (4 : Nat) ≤ 2 ^ 5).trans (Nat.pow_le_pow_left hL 5)
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
  have hL0 : (0 : Real) < L := by linarith
  have hrr : 1024 * (L : Real) ^ 3 ≤ r := by exact_mod_cast hr
  have hrNr : (r : Real) ≤ N := by exact_mod_cast hrN
  have hscale : 64 * (L : Real) ≤ N := by
    have hp : (1 : Real) ≤ (L : Real) ^ 2 := one_le_pow₀ (by linarith)
    have hm := mul_le_mul_of_nonneg_left hp hL0.le
    nlinarith [hrr, hrNr, hm]
  let s := Nat.ceil ((N : Real) / (64 * L))
  have hslo : (N : Real) / (64 * L) ≤ s := Nat.le_ceil _
  have hx1 : (1 : Real) ≤ (N : Real) / (64 * L) :=
    (le_div_iff₀ (by positivity)).mpr (by simpa only [one_mul] using hscale)
  have hs0 : 0 < s := by
    have hsr : (0 : Real) < s := zero_lt_one.trans_le (hx1.trans hslo)
    exact_mod_cast hsr
  have hsN : s ≤ N := by
    apply Nat.ceil_le.mpr
    apply (div_le_iff₀ (by positivity : (0 : Real) < 64 * L)).mpr
    nlinarith
  have hshi : (s : Real) ≤ (N : Real) / (32 * L) := by
    have hc := Nat.ceil_lt_add_one (show 0 ≤ (N : Real) / (64 * L) by positivity)
    change (s : Real) < (N : Real) / (64 * L) + 1 at hc
    have heq : (N : Real) / (32 * L) = 2 * ((N : Real) / (64 * L)) := by ring
    rw [heq]
    linarith
  have hlow := (div_le_iff₀ (by positivity : (0 : Real) < 64 * L)).mp hslo
  have hprod : 16 * (L : Real) ^ 2 * N ≤ (r : Real) * s := by
    calc
      _ ≤ 16 * (L : Real) ^ 2 * (s * (64 * L)) :=
        mul_le_mul_of_nonneg_left hlow (by positivity)
      _ = (1024 * (L : Real) ^ 3) * s := by ring
      _ ≤ (r : Real) * s := mul_le_mul_of_nonneg_right hrr (by positivity)
  have hrs : N ≤ r * s := by
    have hp : (1 : Real) ≤ (L : Real) ^ 2 := one_le_pow₀ (by linarith)
    have hm := mul_le_mul_of_nonneg_right hp hNr.le
    have hh : (N : Real) ≤ (r : Real) * s := by nlinarith [hprod, hm]
    exact_mod_cast hh
  refine ⟨s, hs0, hsN, hrs, ?_, ?_⟩
  · apply Real.le_sqrt_of_sq_le
    apply (le_div_iff₀ (by positivity : (0 : Real) < 16 * N)).mpr
    nlinarith [hprod]
  · calc
      _ ≤ (8 : Real) * s / N := by
        apply div_le_div_of_nonneg_right _ hNr.le
        have hpi := Real.pi_le_four
        nlinarith [mul_le_mul_of_nonneg_right hpi (show (0 : Real) ≤ s by positivity)]
      _ ≤ 8 * ((N : Real) / (32 * L)) / N := by gcongr
      _ = 1 / (4 * L) := by field_simp; ring

end LeanProofs.GowersSzemeredi
