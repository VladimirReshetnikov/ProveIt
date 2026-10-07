import GowersSzemeredi.Section05

/-! Pay for the logarithm in the finite Weyl estimate using half the gap
between its residual power and one. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

theorem finite_weyl_log_root_bound {t m : Real} (ht : 1 ≤ t) (hm : 0 < m) :
    1 + Real.log t ≤ (2 * m + 1) * t ^ (1 / (2 * m)) := by
  have hp : 1 ≤ t ^ (1 / (2 * m)) := Real.one_le_rpow ht (by positivity)
  have hl := Real.log_le_rpow_div (by linarith : 0 ≤ t) (show 0 < 1 / (2 * m) by positivity)
  have he : t ^ (1 / (2 * m)) / (1 / (2 * m)) = 2 * m * t ^ (1 / (2 * m)) := by
    field_simp
  rw [he] at hl
  nlinarith only [hp, hl]

theorem finite_weyl_budget_of_root_bound {t m B C : Real}
    (ht : 1 ≤ t) (hm : 0 < m) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hroot : B * C * (2 * m + 1) ≤ t ^ (1 / (2 * m))) :
    B * (C * t ^ (1 - 1 / m) * (1 + Real.log t)) ≤ t := by
  have ht0 : 0 < t := by linarith
  have hexp : 1 / (2 * m) + ((1 - 1 / m) + 1 / (2 * m)) = 1 := by field_simp; ring
  calc
    _ ≤ B * (C * t ^ (1 - 1 / m) * ((2 * m + 1) * t ^ (1 / (2 * m)))) := by
      gcongr
      exact finite_weyl_log_root_bound ht hm
    _ = (B * C * (2 * m + 1)) * t ^ ((1 - 1 / m) + 1 / (2 * m)) := by
      rw [Real.rpow_add ht0]
      ring
    _ ≤ t ^ (1 / (2 * m)) * t ^ ((1 - 1 / m) + 1 / (2 * m)) := by gcongr
    _ = t := by rw [← Real.rpow_add ht0, hexp, Real.rpow_one]

theorem finite_weyl_budget_at_nat_power {S B C : Real} {m : Nat}
    (hS : 1 ≤ S) (hm : 1 ≤ m) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hscale : B * C * (2 * (m : Real) + 1) ≤ S) :
    B * (C * (S ^ (2 * m)) ^ (1 - 1 / (m : Real)) *
      (1 + Real.log (S ^ (2 * m)))) ≤ S ^ (2 * m) := by
  have hm0 : (0 : Real) < m := by exact_mod_cast (show 0 < m by omega)
  apply finite_weyl_budget_of_root_bound (one_le_pow₀ hS) hm0 hB hC
  have hroot : (S ^ (2 * m)) ^ (1 / (2 * (m : Real))) = S := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith : 0 ≤ S)]
    have he : ((2 * m : Nat) : Real) * (1 / (2 * (m : Real))) = 1 := by
      push_cast
      field_simp
    rw [he, Real.rpow_one]
  rwa [hroot]

end LeanProofs.GowersSzemeredi
