import FabiusFunction.AlgebraicInverseGermBinomial
import FabiusFunction.InverseQuarterAnchor
import FabiusFunction.QuadraticCompositionalInverse
import Mathlib.RingTheory.PowerSeries.Catalan
import Mathlib.RingTheory.PowerSeries.Inverse

/-!
# Catalan formal germs at the quarter anchor

The exact quarter-anchor equation is

`D + 4 D^2 = (4 / 9) X`.

This module packages that equation in two compatible ways.  The explicit
series `quarterCatalanGermSeries` is the zero-constant Catalan solution

`D(X) = (4 / 9) X C(-(16 / 9) X)`,

whose coefficient of degree `m >= 1` is

`(-1)^(m-1) Catalan_(m-1) 2^(4m-2) / 9^m`.

The existing dyadic quantile germ `dyadicGermTwo` satisfies the same scaled
quadratic.  Rescaling its parameter by `9 / 4` identifies it with the
unscaled compositional inverse of `X + 4 X^2`, and yields the corresponding
Catalan coefficient formula.

All constructions here are formal power series.  They do not assert that the
series converges to `quarterInverseGerm`.  The downstream module
`FabiusInverseQuarterJet` separately identifies the actual inverse-Fabius
derivative jet with the unscaled quadratic inverse.
-/

set_option autoImplicit false

namespace Fabius

noncomputable section

open PowerSeries

/-! ## Catalan coefficients -/

/-- The coefficient sequence of the formal quarter inverse germ.

The successor clause is exactly the coefficient normalization used in the
inverse-frontier report.  The proof of the formal-series identity below
rewrites it as the equivalent scaled-Catalan form
`(4/9) * (-16/9)^n * Catalan_n`. -/
def quarterCatalanCoefficient : ℕ → ℚ
  | 0 => 0
  | n + 1 =>
      (-1 : ℚ) ^ n * (catalan n : ℚ) *
        2 ^ (4 * n + 2) / 9 ^ (n + 1)

/-- The report coefficient sequence starts in degree one. -/
@[simp]
theorem quarterCatalanCoefficient_zero : quarterCatalanCoefficient 0 = 0 := rfl

private theorem quarterCatalan_scale_pow (n : ℕ) :
    (4 / 9 : ℚ) * (-16 / 9 : ℚ) ^ n =
      (-1 : ℚ) ^ n * 2 ^ (4 * n + 2) / 9 ^ (n + 1) := by
  have h16 : (16 : ℚ) ^ n = 2 ^ (4 * n) := by
    rw [pow_mul]
    norm_num
  calc
    (4 / 9 : ℚ) * (-16 / 9 : ℚ) ^ n =
        (4 / 9 : ℚ) * (((-1 : ℚ) * 16) / 9) ^ n := by norm_num
    _ = (4 / 9 : ℚ) *
        (((-1 : ℚ) ^ n * 16 ^ n) / 9 ^ n) := by
          rw [div_pow, mul_pow]
    _ = (4 / 9 : ℚ) *
        (((-1 : ℚ) ^ n * 2 ^ (4 * n)) / 9 ^ n) := by rw [h16]
    _ = (-1 : ℚ) ^ n * 2 ^ (4 * n + 2) / 9 ^ (n + 1) := by
      rw [show (2 : ℚ) ^ (4 * n + 2) =
          2 ^ (4 * n) * 2 ^ 2 by rw [pow_add], pow_succ]
      norm_num
      (field_simp; ring)

/-- Exact report form of every positive-degree coefficient:

`delta_(n+1) = (-1)^n Catalan_n 2^(4n+2) / 9^(n+1)`.

This is the formula
`delta_m = (-1)^(m-1) Catalan_(m-1) 2^(4m-2) / 9^m`
with `m = n + 1`. -/
theorem quarterCatalanCoefficient_succ_eq_report (n : ℕ) :
    quarterCatalanCoefficient (n + 1) =
      (-1 : ℚ) ^ n * (catalan n : ℚ) *
        2 ^ (4 * n + 2) / 9 ^ (n + 1) := by
  rfl

/-! ## The formal solution -/

private def rationalCatalanSeries : PowerSeries ℚ :=
  PowerSeries.map (Nat.castRingHom ℚ) PowerSeries.catalanSeries

@[simp]
private theorem rationalCatalanSeries_coeff (n : ℕ) :
    PowerSeries.coeff n rationalCatalanSeries = (catalan n : ℚ) := by
  simp [rationalCatalanSeries]

private theorem rationalCatalanSeries_equation :
    rationalCatalanSeries ^ 2 * PowerSeries.X + 1 =
      rationalCatalanSeries := by
  have h := congrArg
    (fun S : PowerSeries ℕ ↦ PowerSeries.map (Nat.castRingHom ℚ) S)
    PowerSeries.catalanSeries_sq_mul_X_add_one
  simpa only [rationalCatalanSeries, map_add, map_mul, map_pow, map_one,
    PowerSeries.map_X] using h

private def quarterScaledCatalanSeries : PowerSeries ℚ :=
  PowerSeries.rescale (-16 / 9 : ℚ) rationalCatalanSeries

@[simp]
private theorem quarterScaledCatalanSeries_coeff (n : ℕ) :
    PowerSeries.coeff n quarterScaledCatalanSeries =
      (-16 / 9 : ℚ) ^ n * (catalan n : ℚ) := by
  simp [quarterScaledCatalanSeries]

private theorem quarterScaledCatalanSeries_equation :
    quarterScaledCatalanSeries ^ 2 *
        (PowerSeries.C (-16 / 9 : ℚ) * PowerSeries.X) + 1 =
      quarterScaledCatalanSeries := by
  have h := congrArg
    (fun S : PowerSeries ℚ ↦ PowerSeries.rescale (-16 / 9 : ℚ) S)
    rationalCatalanSeries_equation
  simpa only [quarterScaledCatalanSeries, map_add, map_mul, map_pow,
    map_one, PowerSeries.rescale_X] using h

/-- The zero-constant Catalan solution of the quarter-anchor quadratic in
`Q[[X]]`:

`D(X) = (4/9) X C(-(16/9)X)`.

Here the Catalan generating series is first mapped coefficientwise from
`N[[X]]` to `Q[[X]]`, then rescaled by `-16/9`. -/
def quarterCatalanGermSeries : PowerSeries ℚ :=
  PowerSeries.C (4 / 9 : ℚ) *
    (PowerSeries.X * quarterScaledCatalanSeries)

/-- Coefficient extraction identifies the packaged formal series with
`quarterCatalanCoefficient` in every degree. -/
@[simp]
theorem quarterCatalanGermSeries_coeff (n : ℕ) :
    PowerSeries.coeff n quarterCatalanGermSeries =
      quarterCatalanCoefficient n := by
  cases n with
  | zero => simp [quarterCatalanGermSeries, quarterCatalanCoefficient]
  | succ n =>
      rw [quarterCatalanGermSeries, PowerSeries.coeff_C_mul,
        PowerSeries.coeff_succ_X_mul, quarterScaledCatalanSeries_coeff,
        quarterCatalanCoefficient]
      rw [← mul_assoc, quarterCatalan_scale_pow]
      ring

/-- Positive-degree coefficient extraction in the exact normalization of the
inverse-frontier report. -/
theorem quarterCatalanGermSeries_coeff_succ (n : ℕ) :
    PowerSeries.coeff (n + 1) quarterCatalanGermSeries =
      (-1 : ℚ) ^ n * (catalan n : ℚ) *
        2 ^ (4 * n + 2) / 9 ^ (n + 1) := by
  rw [quarterCatalanGermSeries_coeff,
    quarterCatalanCoefficient_succ_eq_report]

/-- The Catalan germ has zero constant coefficient. -/
@[simp]
theorem quarterCatalanGermSeries_constantCoeff :
    PowerSeries.constantCoeff quarterCatalanGermSeries = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply,
    quarterCatalanGermSeries_coeff]
  rfl

/-- The Catalan germ satisfies the exact formal quarter-anchor equation
`D + 4 D^2 = (4/9) X`. -/
theorem quarterCatalanGermSeries_equation :
    quarterCatalanGermSeries + 4 * quarterCatalanGermSeries ^ 2 =
      PowerSeries.C (4 / 9 : ℚ) * PowerSeries.X := by
  let C : PowerSeries ℚ := quarterScaledCatalanSeries
  let A : PowerSeries ℚ := PowerSeries.C (4 / 9 : ℚ)
  have hC :
      C ^ 2 * (PowerSeries.C (-16 / 9 : ℚ) * PowerSeries.X) + 1 = C := by
    simpa only [C] using quarterScaledCatalanSeries_equation
  have hscale :
      PowerSeries.C (-16 / 9 : ℚ) = -(4 * A) := by
    dsimp only [A]
    rw [show (-16 / 9 : ℚ) = -4 * (4 / 9 : ℚ) by norm_num,
      map_mul, map_neg, map_ofNat]
    ring
  rw [hscale] at hC
  have hbranch : C + 4 * A * PowerSeries.X * C ^ 2 = 1 := by
    linear_combination -hC
  change
    A * (PowerSeries.X * C) +
        4 * (A * (PowerSeries.X * C)) ^ 2 =
      A * PowerSeries.X
  calc
    A * (PowerSeries.X * C) +
        4 * (A * (PowerSeries.X * C)) ^ 2 =
        A * PowerSeries.X *
          (C + 4 * A * PowerSeries.X * C ^ 2) := by ring
    _ = A * PowerSeries.X := by rw [hbranch, mul_one]

/-! ## Algebraic uniqueness -/

/-- A formal-power-series quadratic `D ↦ D + u D^2` is injective on
series with zero constant coefficient.

This stronger ring-generic lemma is the algebra behind uniqueness of the
quarter germ.  The difference factors as
`(D-E)(1 + u(D+E))`; the second factor has constant coefficient one and is
therefore a unit.  No integral-domain hypothesis is needed. -/
theorem powerSeries_quadratic_injectiveOn_zeroConstant
    {R : Type*} [CommRing R] (u : PowerSeries R)
    {D E : PowerSeries R}
    (hD0 : PowerSeries.constantCoeff D = 0)
    (hE0 : PowerSeries.constantCoeff E = 0)
    (hEq : D + u * D ^ 2 = E + u * E ^ 2) :
    D = E := by
  have hfactor :
      (D - E) * (1 + u * (D + E)) = 0 := by
    calc
      (D - E) * (1 + u * (D + E)) =
          (D + u * D ^ 2) - (E + u * E ^ 2) := by ring
      _ = 0 := sub_eq_zero.mpr hEq
  have hunit : IsUnit (1 + u * (D + E)) := by
    rw [PowerSeries.isUnit_iff_constantCoeff]
    simp [hD0, hE0]
  exact sub_eq_zero.mp ((hunit.mul_left_eq_zero).mp hfactor)

/-- Every zero-constant formal solution of the quarter quadratic is the
Catalan germ. -/
theorem eq_quarterCatalanGermSeries_of_equation
    {D : PowerSeries ℚ}
    (hD0 : PowerSeries.constantCoeff D = 0)
    (hD : D + 4 * D ^ 2 =
      PowerSeries.C (4 / 9 : ℚ) * PowerSeries.X) :
    D = quarterCatalanGermSeries := by
  exact powerSeries_quadratic_injectiveOn_zeroConstant
    (4 : PowerSeries ℚ) hD0 quarterCatalanGermSeries_constantCoeff
    (hD.trans quarterCatalanGermSeries_equation.symm)

/-- The Catalan germ is the unique zero-constant solution in `Q[[X]]` of
`D + 4 D^2 = (4/9) X`. -/
theorem existsUnique_quarterCatalanGermSeries :
    ∃! D : PowerSeries ℚ,
      PowerSeries.constantCoeff D = 0 ∧
        D + 4 * D ^ 2 =
          PowerSeries.C (4 / 9 : ℚ) * PowerSeries.X := by
  refine ⟨quarterCatalanGermSeries,
    ⟨quarterCatalanGermSeries_constantCoeff,
      quarterCatalanGermSeries_equation⟩, ?_⟩
  intro D hD
  exact eq_quarterCatalanGermSeries_of_equation hD.1 hD.2

/-! ## Bridge to the dyadic quantile germ -/

/-- The distinguished dyadic germ satisfies the scaled quarter-anchor
quadratic equation. -/
theorem dyadicGermTwo_functionalEquation :
    dyadicGermTwo + 4 * dyadicGermTwo ^ 2 =
      PowerSeries.C ((4 : ℚ) / 9) * PowerSeries.X := by
  have h := eval_germRoot dyadicWeightsTwo dyadicJetTwo rfl
    dyadicJetTwo_coeff_zero
    (by rw [dyadicJetTwo_coeff_one]; exact isUnit_one)
  rw [germPolynomial_dyadicTwo_eval] at h
  exact sub_eq_zero.mp h

/-- Rescaling the dyadic parameter by `9 / 4` gives the Catalan reversion of
`X + 4 * X²`. -/
theorem rescale_dyadicGermTwo_eq_quadraticInverse :
    PowerSeries.rescale ((9 : ℚ) / 4) dyadicGermTwo =
      QuadraticInverse.inverse (4 : ℚ) := by
  apply QuadraticInverse.eq_inverse
  · rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply,
      PowerSeries.coeff_rescale, pow_zero, one_mul,
      PowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact constantCoeff_germRoot _ _ _ _ _
  · have hC (q : ℚ) :
        PowerSeries.rescale ((9 : ℚ) / 4) (PowerSeries.C q) =
          PowerSeries.C q := by
      ext n
      simp only [PowerSeries.coeff_rescale, PowerSeries.coeff_C]
      split_ifs with hn
      · subst n
        simp
      · simp
    have h := congrArg (PowerSeries.rescale ((9 : ℚ) / 4))
      dyadicGermTwo_functionalEquation
    simp only [map_add, map_mul, map_pow, map_ofNat, hC,
      PowerSeries.rescale_X] at h
    have hfour : (4 : PowerSeries ℚ) = PowerSeries.C (4 : ℚ) :=
      (map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 4).symm
    rw [hfour] at h
    calc
      PowerSeries.rescale ((9 : ℚ) / 4) dyadicGermTwo +
          PowerSeries.C (4 : ℚ) *
            PowerSeries.rescale ((9 : ℚ) / 4) dyadicGermTwo ^ 2 =
          PowerSeries.C ((4 : ℚ) / 9) *
            (PowerSeries.C ((9 : ℚ) / 4) * PowerSeries.X) := h
      _ = PowerSeries.X := by
        rw [← mul_assoc, ← map_mul,
          show ((4 : ℚ) / 9) * ((9 : ℚ) / 4) = 1 by norm_num,
          map_one, one_mul]

/-- Equivalently, the dyadic germ is the quarter Catalan inverse with its
variable rescaled by `4 / 9`. -/
theorem dyadicGermTwo_eq_rescale_quadraticInverse :
    dyadicGermTwo =
      PowerSeries.rescale ((4 : ℚ) / 9)
        (QuadraticInverse.inverse (4 : ℚ)) := by
  calc
    dyadicGermTwo =
        PowerSeries.rescale ((4 : ℚ) / 9)
          (PowerSeries.rescale ((9 : ℚ) / 4) dyadicGermTwo) := by
      rw [PowerSeries.rescale_rescale]
      norm_num
    _ = PowerSeries.rescale ((4 : ℚ) / 9)
        (QuadraticInverse.inverse (4 : ℚ)) := by
      rw [rescale_dyadicGermTwo_eq_quadraticInverse]

/-- The report-facing Catalan normalization of every positive-degree dyadic
germ coefficient.  The extra power `(4 / 9)^(m + 1)` is exactly the parameter
rescaling that distinguishes the finite-spline germ from the unscaled quarter
inverse shadow. -/
@[simp]
theorem coeff_dyadicGermTwo_succ (m : ℕ) :
    PowerSeries.coeff (m + 1) dyadicGermTwo =
      ((4 : ℚ) / 9) ^ (m + 1) * (-4 : ℚ) ^ m * (catalan m : ℚ) := by
  rw [dyadicGermTwo_eq_rescale_quadraticInverse,
    PowerSeries.coeff_rescale, QuadraticInverse.coeff_succ_inverse]
  ring

end

end Fabius
