import GowersSzemeredi.Proofs16PolynomialRecurrenceProfile
import GowersSzemeredi.Proofs16ShortScale

/-! Rounding and threshold absorption for the polynomial recurrence.

A polynomial prefactor in the phase-count base pays for the recurrence
threshold. Once the resulting width target exceeds one, a rounded integer
scale satisfies the localized input budget. This is the arithmetic needed
to combine the large-scale line-cover result with singleton partitions.
-/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- Above the singleton regime, the target with exponent `a/(4*E)` and
prefactor `zeta/(4*b)` supplies an integer recurrence scale between `b^E`
and `(m/8)^a`. The resulting retiled width dominates that target. -/
theorem polynomial_localized_recurrence_parameters {m b E : Nat} {a zeta : Real}
    (hm : 1 ≤ m) (hb : 2 ≤ b) (hE : 0 < E)
    (ha : 0 < a) (ha1 : a ≤ 1) (hz : 0 < zeta) (hzHalf : zeta ≤ 1 / 2)
    (hlarge : 1 < (zeta / (4 * b)) * (m : Real) ^ (a / (4 * E))) :
    ∃ n : Nat, 4 ≤ m ∧ 0 < n ∧
      (n : Real) ≤ ((m : Real) / 8) ^ a ∧ b ^ E ≤ n ∧
      (zeta / (4 * b)) * (m : Real) ^ (a / (4 * E)) ≤
        (zeta / 2) * Real.sqrt ((n : Real) ^ ((E : Real)⁻¹)) := by
  have hmR : (1 : Real) ≤ m := by exact_mod_cast hm
  have hmpos : (0 : Real) < m := zero_lt_one.trans_le hmR
  have hbR : (2 : Real) ≤ b := by exact_mod_cast hb
  have hER : (0 : Real) < E := by exact_mod_cast hE
  have hEone : (1 : Real) ≤ E := by exact_mod_cast hE
  let x : Real := (m : Real) ^ (a / (4 * E))
  have hxpos : 0 < x := Real.rpow_pos_of_pos hmpos _
  change 1 < (zeta / (4 * b)) * x at hlarge
  have hden : (0 : Real) < 4 * b := by positivity
  have hscaled : 4 * (b : Real) < zeta * x := by
    have h := mul_lt_mul_of_pos_right hlarge hden
    have heq : (zeta / (4 * (b : Real)) * x) * (4 * b) = zeta * x := by field_simp
    simpa only [one_mul, heq] using h
  have hzx : zeta * x ≤ (1 / 2) * x := mul_le_mul_of_nonneg_right hzHalf hxpos.le
  have hx16 : 16 < x := by nlinarith
  have hbx : (b : Real) ≤ x := by nlinarith
  let H : Nat := Nat.ceil x
  have hxH : x ≤ (H : Real) := Nat.le_ceil x
  have hH : 0 < H := Nat.ceil_pos.mpr hxpos
  have hHbound : (H : Real) ≤ x ^ 2 / 8 := by
    have hc : (H : Real) ≤ x + 1 := (Nat.ceil_lt_add_one hxpos.le).le
    nlinarith
  have hxpow : x ^ (4 * E) = (m : Real) ^ a := by
    dsimp only [x]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hmpos.le]
    congr 1
    push_cast
    exact div_mul_cancel₀ _ (by positivity)
  let n : Nat := H ^ (2 * E)
  have hn : 0 < n := pow_pos hH _
  have h8a : (8 : Real) ^ a ≤ 8 := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : Real) ≤ 8) ha1
  have h8E : (8 : Real) ≤ (8 : Real) ^ (2 * E) := by
    simpa only [pow_one] using pow_le_pow_right₀ (by norm_num : (1 : Real) ≤ 8)
      (by omega : 1 ≤ 2 * E)
  have hnscale : (n : Real) ≤ ((m : Real) / 8) ^ a := by
    rw [Real.div_rpow hmpos.le (by norm_num : (0 : Real) ≤ 8)]
    calc
      (n : Real) = (H : Real) ^ (2 * E) := by simp only [n, Nat.cast_pow]
      _ ≤ (x ^ 2 / 8) ^ (2 * E) := pow_le_pow_left₀ (Nat.cast_nonneg H) hHbound _
      _ = (m : Real) ^ a / (8 : Real) ^ (2 * E) := by
        rw [div_pow, ← pow_mul, show 2 * (2 * E) = 4 * E by omega, hxpow]
      _ ≤ (m : Real) ^ a / (8 : Real) ^ a :=
        div_le_div_of_nonneg_left (Real.rpow_nonneg hmpos.le _)
          (Real.rpow_pos_of_pos (by norm_num : (0 : Real) < 8) _) (h8a.trans h8E)
  have hbH : b ≤ H := by exact_mod_cast hbx.trans hxH
  have hthreshold : b ^ E ≤ n :=
    (Nat.pow_le_pow_left hbH _).trans (Nat.pow_le_pow_right hH (by omega : E ≤ 2 * E))
  have hxle : x ≤ (m : Real) := by
    have he : a / (4 * (E : Real)) ≤ 1 := (div_le_iff₀ (by positivity)).mpr (by nlinarith)
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hmR he
  have hm4 : 4 ≤ m := by
    have h : (4 : Real) ≤ m := by linarith
    exact_mod_cast h
  have hnroot : (n : Real) ^ ((E : Real)⁻¹) = (H : Real) ^ 2 := by
    dsimp only [n]
    rw [Nat.cast_pow, ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg H)]
    rw [← Real.rpow_natCast]
    congr 1
    push_cast
    field_simp
  refine ⟨n, hm4, hn, hnscale, hthreshold, ?_⟩
  rw [hnroot, Real.sqrt_sq (Nat.cast_nonneg H)]
  have hfactor : zeta / (4 * (b : Real)) ≤ zeta / 2 :=
    div_le_div_of_nonneg_left hz.le (by norm_num) (by nlinarith)
  exact mul_le_mul hfactor hxH hxpos.le (by positivity)

end LeanProofs.GowersSzemeredi
