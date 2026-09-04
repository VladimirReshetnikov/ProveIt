import FabiusFunction.LagrangeInversionUniqueness

/-!
# The Lagrange functional equation with an arbitrary weight

For every formal series `φ` over a commutative ring there is exactly one series
`g` satisfying `g = X * φ.subst g`.  Its constant coefficient vanishes automatically;
the constant coefficient of `φ` need not be invertible or even nonzero.

Write `φ(t) = a + t * ψ(t)` and normalize the weight to
`Φ(t) = 1 + t * ψ(a*t)`.  The existing unit-weight theorem constructs its unique
solution `h`; then `g = a*h` is a solution for `φ`.

Uniqueness also reduces to that same unit-weight theorem without dividing by `a`.
For any solution `g`, the series `B = 1 - X * ψ(g)` has constant coefficient one.
Its multiplicative inverse gives the lift `h = X/B`, and the original equation
implies both `g = a*h` and `h = X * Φ(h)`.  This works unchanged with zero divisors
or in positive characteristic.
-/

set_option autoImplicit false

open PowerSeries

namespace Fabius.Lagrange

variable {R : Type*} [CommRing R]

private noncomputable def normalizedWeight (a : R) (ψ : R⟦X⟧) : R⟦X⟧ :=
  1 + X * ψ.subst (C a * X)

private theorem constantCoeff_normalizedWeight (a : R) (ψ : R⟦X⟧) :
    constantCoeff (normalizedWeight a ψ) = 1 := by
  rw [normalizedWeight, map_add, map_one, constantCoeff_X_mul, add_zero]

private theorem normalizedWeight_subst (a : R) (ψ : R⟦X⟧)
    {h : R⟦X⟧} (hh : constantCoeff h = 0) :
    (normalizedWeight a ψ).subst h = 1 + h * ψ.subst (C a * h) := by
  have hs : HasSubst h := HasSubst.of_constantCoeff_zero' hh
  have ha : HasSubst (C a * X : R⟦X⟧) :=
    HasSubst.of_constantCoeff_zero' (by rw [map_mul, constantCoeff_X, mul_zero])
  have hone : (1 : R⟦X⟧).subst h = 1 := by rw [← coe_substAlgHom hs, map_one]
  rw [normalizedWeight, subst_add hs, hone, subst_mul hs, subst_X hs,
    subst_comp_subst_apply ha hs, subst_mul hs, subst_C, subst_X hs]
  rfl

private theorem scale_normalized_solution (a : R) (ψ : R⟦X⟧) {h : R⟦X⟧}
    (hh : h = X * (normalizedWeight a ψ).subst h) :
    C a * h = X * (C a + X * ψ).subst (C a * h) := by
  have hh0 : constantCoeff h = 0 := constantCoeff_eq_zero_of_eq_X_mul hh
  have hs : HasSubst (C a * h) :=
    HasSubst.of_constantCoeff_zero' (by rw [map_mul, hh0, mul_zero])
  rw [normalizedWeight_subst a ψ hh0] at hh
  rw [subst_add hs, subst_C, subst_mul hs, subst_X hs]
  rw [← PowerSeries.C_apply]
  linear_combination (C a) * hh

private theorem lift_normalized_solution (a : R) (ψ : R⟦X⟧) {g : R⟦X⟧}
    (hg : g = X * (C a + g * ψ.subst g)) :
    ∃ h : R⟦X⟧, h = X * (normalizedWeight a ψ).subst h ∧ g = C a * h := by
  let B : R⟦X⟧ := 1 - X * ψ.subst g
  have hB : constantCoeff B = 1 := by
    dsimp [B]
    rw [map_sub, map_one, constantCoeff_X_mul, sub_zero]
  have hBu : IsUnit B := PowerSeries.isUnit_iff_constantCoeff.mpr
    (by rw [hB]; exact isUnit_one)
  obtain ⟨b, hb⟩ := hBu.exists_right_inv
  have hgB : g * B = C a * X := by
    dsimp [B]
    linear_combination hg
  have hga : g = C a * (X * b) := by
    calc
      g = g * (B * b) := by rw [hb, mul_one]
      _ = (g * B) * b := by ring
      _ = C a * (X * b) := by rw [hgB]; ring
  have hbexpand : b = 1 + (X * b) * ψ.subst g := by
    dsimp [B] at hb
    linear_combination hb
  refine ⟨X * b, ?_, hga⟩
  calc
    X * b = X * (1 + (X * b) * ψ.subst g) := congrArg (X * ·) hbexpand
    _ = X * (normalizedWeight a ψ).subst (X * b) := by
      rw [normalizedWeight_subst a ψ (constantCoeff_X_mul b), ← hga]

private theorem lift_solution {φ g : R⟦X⟧} (hg : g = X * φ.subst g) :
    ∃ h : R⟦X⟧,
      h = X * (normalizedWeight (constantCoeff φ)
        (mk fun n => coeff (n + 1) φ)).subst h ∧ g = C (constantCoeff φ) * h := by
  have hφ : φ = C (constantCoeff φ) + X * (mk fun n => coeff (n + 1) φ) := by
    simpa only [add_comm] using eq_X_mul_shift_add_const φ
  have hs : HasSubst g := hasSubst_of_eq_X_mul hg
  rw [hφ, subst_add hs, subst_C, subst_mul hs, subst_X hs] at hg
  exact lift_normalized_solution (constantCoeff φ) (mk fun n => coeff (n + 1) φ) hg

/-- Over every commutative ring, `g = X * φ(g)` has exactly one formal power-series
solution for every weight `φ`. No hypothesis on the constant coefficient of `φ`
is required, and the equation forces the constant coefficient of `g` to be zero. -/
theorem existsUnique_eq_X_mul_subst (φ : R⟦X⟧) :
    ∃! g : R⟦X⟧, g = X * φ.subst g := by
  let a : R := constantCoeff φ
  let ψ : R⟦X⟧ := mk fun n => coeff (n + 1) φ
  have hφ : φ = C a + X * ψ := by
    simpa only [a, ψ, add_comm] using eq_X_mul_shift_add_const φ
  obtain ⟨h, hh, huniq⟩ := existsUnique_of_isUnit_constantCoeff
    (φ := normalizedWeight a ψ) (by rw [constantCoeff_normalizedWeight]; exact isUnit_one)
  refine ⟨C a * h, ?_, ?_⟩
  · rw [hφ]
    exact scale_normalized_solution a ψ hh
  · intro g hg
    obtain ⟨h', hh', hgh'⟩ := lift_solution hg
    rw [hgh', huniq h' hh']

/-- Every solution is divisible by the constant series with value `φ(0)`. This
holds even when `φ(0)` is a zero divisor; no cancellation is involved. -/
theorem C_constantCoeff_dvd_of_eq_X_mul_subst {φ g : R⟦X⟧}
    (hg : g = X * φ.subst g) : C (constantCoeff φ) ∣ g := by
  obtain ⟨h, _, hgh⟩ := lift_solution hg
  exact ⟨h, hgh⟩

/-- A nilpotent constant coefficient makes the Lagrange solution nilpotent with
the same exponent, including the boundary case of exponent zero in a zero ring. -/
theorem pow_eq_zero_of_constantCoeff_pow_eq_zero {φ g : R⟦X⟧} {m : ℕ}
    (hg : g = X * φ.subst g) (hφ : constantCoeff φ ^ m = 0) : g ^ m = 0 := by
  obtain ⟨h, hgh⟩ := C_constantCoeff_dvd_of_eq_X_mul_subst hg
  rw [hgh, mul_pow, ← map_pow, hφ, map_zero, zero_mul]

/-- If the weight has zero constant coefficient, the unique solution of the
Lagrange functional equation is the zero series, even over rings with zero divisors. -/
theorem eq_zero_of_eq_X_mul_subst_of_constantCoeff_zero {φ g : R⟦X⟧}
    (hφ : constantCoeff φ = 0) (hg : g = X * φ.subst g) : g = 0 := by
  obtain ⟨h, hgh⟩ := C_constantCoeff_dvd_of_eq_X_mul_subst hg
  rw [hφ, map_zero, zero_mul] at hgh
  exact hgh

end Fabius.Lagrange
