import FabiusFunction.LagrangeInversion

/-!
# Uniqueness and the Jacobian form of Lagrange inversion

The functional equation `g = X * φ.subst g` has a unique solution whenever the constant
coefficient of `φ` is a unit.  This is valid over every commutative ring: composition with
the inverse of `X * ψ`, where `φ * ψ = 1`, identifies every solution with the canonical one.
The functional equation itself forces the constant coefficient of `g` to vanish.

Over a commutative `ℚ`-algebra, the alternative Lagrange–Bürmann identity is

`[X^n] H(g) = [X^n] H * φ^(n-1) * (φ - X * φ')`, for `n ≥ 1`.

Its algebraic mechanism is coefficient integration by parts, proved first over an arbitrary
commutative ring with the factor `n` retained.  No formal residue theory is required.
-/

set_option autoImplicit false

open PowerSeries

namespace Fabius.Lagrange

section CommRing

variable {R : Type*} [CommRing R]
variable {φ ψ g : R⟦X⟧}

/-- Every solution of `g = X * φ(g)` equals the canonical Lagrange solution; the functional
equation already implies that `g` has zero constant coefficient.

The heartbeat allowance is needed: `solution` unfolds to `substInvOfIsUnit`, and the final
`calc` step's `rw` makes the elaborator `whnf` that term, which exceeds the default budget on
this machine (the module had never been compiled here when it entered the facade). -/
set_option maxHeartbeats 1600000 in
theorem eq_solution_of_eq_X_mul_subst (hψ : φ * ψ = 1)
    (hg : g = X * φ.subst g) : g = solution φ ψ hψ := by
  have hs : HasSubst g := hasSubst_of_eq_X_mul hg
  have hunit : φ.subst g * ψ.subst g = 1 := by
    rw [← subst_mul hs, hψ, ← coe_substAlgHom hs, map_one]
  have hcomp : (X * ψ).subst g = X := by
    calc
      (X * ψ).subst g = g * ψ.subst g := by rw [subst_mul hs, subst_X hs]
      _ = (X * φ.subst g) * ψ.subst g := congrArg (· * ψ.subst g) hg
      _ = X := by rw [mul_assoc, hunit, mul_one]
  have hf : HasSubst (X * ψ) :=
    HasSubst.of_constantCoeff_zero' (constantCoeff_X_mul ψ)
  have hinv : (solution φ ψ hψ).subst (X * ψ) = X := by
    unfold solution
    exact subst_substInvOfIsUnit_left (X * ψ) (constantCoeff_X_mul ψ)
      (by rw [coeff_one_X_mul]; exact isUnit_constantCoeff_right φ ψ hψ)
  calc
    g = X.subst g := (subst_X hs).symm
    _ = ((solution φ ψ hψ).subst (X * ψ)).subst g := by rw [hinv]
    _ = (solution φ ψ hψ).subst ((X * ψ).subst g) :=
      subst_comp_subst_apply hf hs (solution φ ψ hψ)
    _ = solution φ ψ hψ := by rw [hcomp, X_subst]

/-- Over any commutative ring, an invertible weight series has exactly one Lagrange solution. -/
theorem existsUnique_solution (hψ : φ * ψ = 1) :
    ∃! g : R⟦X⟧, g = X * φ.subst g :=
  ⟨solution φ ψ hψ, solution_eq φ ψ hψ,
    fun _ hg => eq_solution_of_eq_X_mul_subst hψ hg⟩

/-- An invertible constant coefficient is sufficient for existence and uniqueness of the
solution of `g = X * φ(g)`, over any commutative ring. -/
theorem existsUnique_of_isUnit_constantCoeff (hφ : IsUnit (constantCoeff φ)) :
    ∃! g : R⟦X⟧, g = X * φ.subst g := by
  obtain ⟨ψ, hψ⟩ := (PowerSeries.isUnit_iff_constantCoeff.mpr hφ).exists_right_inv
  exact existsUnique_solution hψ

/-- Coefficient integration by parts: the Jacobian form of Lagrange inversion, with its
factor `n` retained, is an identity over every commutative ring. -/
theorem coeff_jacobian_mul (H φ : R⟦X⟧) (n : ℕ) (hn : 1 ≤ n) :
    (n : R) * coeff n (H * φ ^ (n - 1) * (φ - X * d⁄dX R φ)) =
      coeff (n - 1) (d⁄dX R H * φ ^ n) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hder : d⁄dX R (H * φ ^ (m + 1)) =
      d⁄dX R H * φ ^ (m + 1) +
        C ((m + 1 : ℕ) : R) * (H * φ ^ m * d⁄dX R φ) := by
    rw [Derivation.leibniz, derivative_pow, Nat.add_sub_cancel]
    simp only [smul_eq_mul, map_natCast]
    ring
  have hcoeff := congrArg (coeff m) hder
  rw [coeff_derivative, map_add, coeff_C_mul] at hcoeff
  have hjac : H * φ ^ m * (φ - X * d⁄dX R φ) =
      H * φ ^ (m + 1) - X * (H * φ ^ m * d⁄dX R φ) := by
    rw [pow_succ]
    ring
  rw [Nat.add_sub_cancel, hjac, map_sub, coeff_succ_X_mul]
  push_cast at hcoeff ⊢
  linear_combination hcoeff

end CommRing

section RatAlgebra

variable {R : Type*} [CommRing R] [Algebra ℚ R]
variable {φ g u v : R⟦X⟧}

/-- The alternative Lagrange–Bürmann formula: the coefficient of `H(g)` is obtained by
multiplying `H` by `φ^(n-1) * (φ - X * φ')` and taking the coefficient in the same degree. -/
theorem coeff_subst_alt (hg : g = X * u) (hu : u = φ.subst g) (hv : u * v = 1)
    (H : R⟦X⟧) (n : ℕ) (hn : 1 ≤ n) :
    coeff n (H.subst g) = coeff n (H * φ ^ (n - 1) * (φ - X * d⁄dX R φ)) := by
  have hnQ : IsUnit (n : ℚ) := isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr (by omega))
  have hnR : IsUnit (n : R) := by
    simpa only [map_natCast] using hnQ.map (algebraMap ℚ R)
  apply hnR.mul_left_cancel
  rw [coeff_subst_derivative hg hu hv H n hn, coeff_jacobian_mul H φ n hn]

/-- The alternative Lagrange–Bürmann formula for the constructed, unique solution. -/
theorem coeff_solution_subst_alt (φ ψ : R⟦X⟧) (hψ : φ * ψ = 1)
    (H : R⟦X⟧) (n : ℕ) (hn : 1 ≤ n) :
    coeff n (H.subst (solution φ ψ hψ)) =
      coeff n (H * φ ^ (n - 1) * (φ - X * d⁄dX R φ)) :=
  coeff_subst_alt (solution_eq φ ψ hψ) rfl (subst_solution_mul φ ψ hψ) H n hn

end RatAlgebra

end Fabius.Lagrange
