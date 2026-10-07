import GowersSzemeredi.Section05

/-! A numerical recurrence criterion, independent of the polynomial degree.
The Fourier lower-bound denominator is `A`, and `D` is the finite Weyl
coefficient including its power and logarithm. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

theorem finite_recurrence_frequency_budget {R t A D q h : Real}
    (hR : 1 ≤ R) (ht : 0 < t) (hA : 0 < A) (hD : 0 ≤ D) (hq : 0 < q)
    (hh : h ≤ 4 * R ^ 2)
    (hweyl : 1 / A ≤ D * (q⁻¹ + 2 / t))
    (hbudget : 16 * A * R ^ 3 * D ≤ t) : h * q < t / R := by
  have hR0 : 0 < R := by linarith
  have hR3 : 1 ≤ R ^ 3 := one_le_pow₀ hR
  by_contra hfail
  have hprod : t ≤ 4 * R ^ 3 * q := by
    have h1 : t / R ≤ 4 * R ^ 2 * q := (le_of_not_gt hfail).trans
      (mul_le_mul_of_nonneg_right hh hq.le)
    have h2 := (div_le_iff₀ hR0).mp h1
    nlinarith only [h2]
  have hinv : q⁻¹ ≤ 4 * R ^ 3 / t := by
    rw [← one_div q]
    apply (div_le_div_iff₀ hq ht).mpr
    simpa only [one_mul] using hprod
  have hupper : 1 / A ≤ D * (4 * R ^ 3 + 2) / t := by
    calc
      _ ≤ _ := hweyl
      _ ≤ D * (4 * R ^ 3 / t + 2 / t) := by gcongr
      _ = _ := by ring
  have hmain : t ≤ A * (D * (4 * R ^ 3 + 2)) := by
    have h1 := (le_div_iff₀ ht).mp hupper
    have h2 : t / A ≤ D * (4 * R ^ 3 + 2) := by
      calc
        t / A = (1 / A) * t := by ring
        _ ≤ _ := h1
    have h3 := (div_le_iff₀ hA).mp h2
    nlinarith only [h3]
  have hmain2 : t ≤ 8 * A * R ^ 3 * D := by
    calc
      _ ≤ _ := hmain
      _ ≤ A * (D * (8 * R ^ 3)) := by gcongr; linarith
      _ = _ := by ring
  nlinarith only [hbudget, hmain2, ht]

end LeanProofs.GowersSzemeredi
