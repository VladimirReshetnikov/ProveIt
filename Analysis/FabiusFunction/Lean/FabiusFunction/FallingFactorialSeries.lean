import FabiusFunction.BellDerivative
import FabiusFunction.StirlingFirstReverse
import Mathlib.RingTheory.PowerSeries.Log
import Mathlib.Algebra.Polynomial.Derivation

/-!
# The falling-factorial generating function `(1+t)^u = ∑_n (u)_n t^n/n!`

For `u` in a commutative `ℚ`-algebra `A` the series `F_u(t) = ∑_n (u)_n t^n/n!` of falling
factorials is characterised by the first-order equation `(1+t) F_u' = u F_u` with `F_u(0) = 1`
(`one_add_X_mul_derivative_fallingSeries`, `eq_zero_of_one_add_X_mul_derivative_eq`).  This gives
the product law `F_u F_v = F_{u+v}` (`fallingSeries_mul`), the Vandermonde identity for falling
factorials (`descPochhammer_eval_add`), the shift `F_{u+1} = (1+t) F_u` (`fallingSeries_add_one`),
and, for `u = x` a polynomial variable, the derivative identity
`∂_x (1+t)^x = log(1+t) · (1+t)^x` (`Dx_fallingPoly`), with `∂_x` the coefficientwise derivation
`Dx` of `ℚ[x][[t]]`.

## Main results

* `egfA_add`, `C_mul_egfA`, `invOneAdd`, `one_add_X_mul_invOneAdd`,
  `eq_zero_of_one_add_X_mul_derivative_eq`, `derivative_mul'`.
* `fallingSeries`, `one_add_X_mul_derivative_fallingSeries`, `constantCoeff_fallingSeries`,
  `fallingSeries_zero`, `fallingSeries_one`, `fallingSeries_mul`, `descPochhammer_eval_add`,
  `fallingSeries_add_one`.
* `Dx`, `Dx_add`, `Dx_sub`, `Dx_mul`, `Dx_C`, `Dx_map_C`, `Dx_one`, `Dx_X`, `Dx_one_add_X`,
  `Dx_derivative_comm`, `derivative_log`, `logPoly`, `Dx_logPoly`, `derivative_map_C`,
  `one_add_X_mul_derivative_logPoly`, `fallingPoly`, `Dx_fallingPoly`.
-/

set_option autoImplicit false

open Finset PowerSeries

namespace Fabius

section Generic

variable (A : Type*) [CommRing A] [Algebra ℚ A]

/-- Exponential generating functions preserve pointwise addition of sequences. -/
theorem egfA_add (a b : ℕ → A) : egfA A a + egfA A b = egfA A (a + b) := by
  ext n
  rw [map_add, coeff_egfA, coeff_egfA, coeff_egfA, Pi.add_apply, mul_add]

/-- Multiplication by a constant series scales every term of an exponential generating function. -/
theorem C_mul_egfA (c : A) (a : ℕ → A) :
    PowerSeries.C c * egfA A a = egfA A fun n => c * a n := by
  ext n
  rw [coeff_C_mul, coeff_egfA, coeff_egfA]
  ring

/-- `1/(1+t) = ∑_n (-1)^n t^n`. -/
noncomputable def invOneAdd : A⟦X⟧ := rescale (-1 : A) (PowerSeries.mk 1)

/-- The geometric series `invOneAdd` is a right inverse of `1 + X`. -/
theorem one_add_X_mul_invOneAdd : (1 + X) * invOneAdd A = 1 := by
  have h := congrArg (rescale (-1 : A)) (mk_one_mul_one_sub_eq_one (S := A))
  rw [map_mul, map_sub, map_one, rescale_neg_one_X, sub_neg_eq_add] at h
  rw [invOneAdd, mul_comm]
  exact h

/-- **Uniqueness** for `(1+t) F' = c F` with `F(0) = 0`. -/
theorem eq_zero_of_one_add_X_mul_derivative_eq {F : A⟦X⟧} (c : A)
    (hF : (1 + X) * d⁄dX A F = PowerSeries.C c * F) (h0 : constantCoeff F = 0) : F = 0 := by
  refine eq_zero_of_derivative_eq_mul A (g := PowerSeries.C c * invOneAdd A) ?_ h0
  have h := congrArg (· * invOneAdd A) hF
  rw [mul_right_comm, one_add_X_mul_invOneAdd, one_mul] at h
  rw [h]
  ring

/-- The product rule for `d/dt`, in the form used below. -/
theorem derivative_mul' (f g : A⟦X⟧) :
    d⁄dX A (f * g) = f * d⁄dX A g + g * d⁄dX A f := by
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]

/-- `(1+t)^u = ∑_n (u)_n t^n/n!`. -/
noncomputable def fallingSeries (u : A) : A⟦X⟧ :=
  egfA A fun n => (descPochhammer A n).eval u

/-- The defining equation `(1+t) F_u' = u F_u`. -/
theorem one_add_X_mul_derivative_fallingSeries (u : A) :
    (1 + X) * d⁄dX A (fallingSeries A u) = PowerSeries.C u * fallingSeries A u := by
  rw [fallingSeries, add_mul, one_mul, X_mul_derivative_egfA, derivative_egfA, egfA_add,
    C_mul_egfA]
  congr 1
  funext n
  rw [Pi.add_apply, Bell.shift_apply, descPochhammer_succ_eval]
  ring

/-- Every falling-factorial series has constant coefficient `1`. -/
@[simp] theorem constantCoeff_fallingSeries (u : A) : constantCoeff (fallingSeries A u) = 1 := by
  rw [fallingSeries, constantCoeff_egfA, descPochhammer_zero, Polynomial.eval_one]

/-- The falling-factorial series at exponent zero is the constant series `1`. -/
theorem fallingSeries_zero : fallingSeries A 0 = 1 := by
  ext n
  rw [fallingSeries, coeff_egfA, coeff_one, descPochhammer_eval_zero]
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rw [if_neg hn, mul_zero]

/-- The falling-factorial series at exponent one is `1 + X`. -/
theorem fallingSeries_one : fallingSeries A 1 = 1 + X := by
  ext n
  rw [fallingSeries, coeff_egfA, map_add, coeff_one, coeff_X]
  rcases n with _ | _ | n
  · simp
  · simp [descPochhammer_one]
  · rw [descPochhammer_succ_left, Polynomial.eval_mul, Polynomial.eval_comp, Polynomial.eval_sub,
      Polynomial.eval_X, Polynomial.eval_one, sub_self, descPochhammer_eval_zero,
      if_neg (Nat.succ_ne_zero n), mul_zero, mul_zero]
    simp

/-- **The product law** `(1+t)^u (1+t)^v = (1+t)^{u+v}`. -/
theorem fallingSeries_mul (u v : A) :
    fallingSeries A u * fallingSeries A v = fallingSeries A (u + v) := by
  have h1 := one_add_X_mul_derivative_fallingSeries A u
  have h2 := one_add_X_mul_derivative_fallingSeries A v
  have h3 := one_add_X_mul_derivative_fallingSeries A (u + v)
  rw [map_add] at h3
  have hF : (1 + X) * d⁄dX A (fallingSeries A u * fallingSeries A v - fallingSeries A (u + v)) =
      PowerSeries.C (u + v) * (fallingSeries A u * fallingSeries A v - fallingSeries A (u + v)) := by
    rw [map_sub, Derivation.leibniz, smul_eq_mul, smul_eq_mul, map_add]
    linear_combination (fallingSeries A v) * h1 + (fallingSeries A u) * h2 - h3
  have h0 : constantCoeff (fallingSeries A u * fallingSeries A v - fallingSeries A (u + v)) = 0 := by
    rw [map_sub, map_mul, constantCoeff_fallingSeries, constantCoeff_fallingSeries,
      constantCoeff_fallingSeries, one_mul, sub_self]
  exact sub_eq_zero.mp (eq_zero_of_one_add_X_mul_derivative_eq A (u + v) hF h0)

/-- **Vandermonde for falling factorials:** `(u+v)_n = ∑_k C(n,k) (u)_k (v)_{n-k}`. -/
theorem descPochhammer_eval_add (u v : A) (n : ℕ) :
    (descPochhammer A n).eval (u + v) =
      ∑ k ∈ range (n + 1),
        (n.choose k : A) * ((descPochhammer A k).eval u * (descPochhammer A (n - k)).eval v) := by
  have h := congrFun (seq_eq_of_egfA_eq A (a := fun n => (descPochhammer A n).eval (u + v))
    (b := Bell.binomialConv (fun k => (descPochhammer A k).eval u)
      (fun k => (descPochhammer A k).eval v))
    (by rw [← egfA_mul]; exact (fallingSeries_mul A u v).symm)) n
  rw [Bell.binomialConv_eq_sum_range] at h
  exact h

/-- The shift `(1+t)^{u+1} = (1+t)^u (1+t)`. -/
theorem fallingSeries_add_one (u : A) : fallingSeries A (u + 1) = fallingSeries A u * (1 + X) := by
  rw [← fallingSeries_mul, fallingSeries_one]

end Generic

/-! ### The `x`-derivative of `(1+t)^x` -/

section PolyDeriv

/-- The coefficientwise `∂/∂x` on `ℚ[x][[t]]`. -/
noncomputable def Dx (f : (Polynomial ℚ)⟦X⟧) : (Polynomial ℚ)⟦X⟧ :=
  PowerSeries.mk fun n => Polynomial.derivative (coeff n f)

/-- The `n`-th coefficient of `Dx f` is the derivative of the `n`-th coefficient of `f`. -/
@[simp] theorem coeff_Dx (f : (Polynomial ℚ)⟦X⟧) (n : ℕ) :
    coeff n (Dx f) = Polynomial.derivative (coeff n f) := coeff_mk _ _

/-- The coefficientwise polynomial derivative preserves addition. -/
theorem Dx_add (f g : (Polynomial ℚ)⟦X⟧) : Dx (f + g) = Dx f + Dx g := by
  refine PowerSeries.ext fun n => ?_
  simp only [coeff_Dx, map_add]

/-- The coefficientwise polynomial derivative preserves subtraction. -/
theorem Dx_sub (f g : (Polynomial ℚ)⟦X⟧) : Dx (f - g) = Dx f - Dx g := by
  refine PowerSeries.ext fun n => ?_
  simp only [coeff_Dx, map_sub]

/-- **Leibniz rule** for the coefficientwise `∂/∂x`. -/
theorem Dx_mul (f g : (Polynomial ℚ)⟦X⟧) : Dx (f * g) = Dx f * g + f * Dx g := by
  refine PowerSeries.ext fun n => ?_
  rw [coeff_Dx, coeff_mul, Polynomial.derivative_sum, map_add, coeff_mul, coeff_mul,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Polynomial.derivative_mul, coeff_Dx, coeff_Dx]

/-- On a constant power series, `Dx` differentiates its polynomial value. -/
theorem Dx_C (p : Polynomial ℚ) :
    Dx (PowerSeries.C p) = PowerSeries.C (Polynomial.derivative p) := by
  ext n
  rw [coeff_Dx, coeff_C, coeff_C]
  split_ifs <;> simp

/-- A power series whose coefficients are constant polynomials is annihilated by `Dx`. -/
theorem Dx_map_C (f : ℚ⟦X⟧) : Dx (PowerSeries.map (Polynomial.C : ℚ →+* Polynomial ℚ) f) = 0 := by
  ext n
  rw [coeff_Dx, coeff_map, map_zero, Polynomial.derivative_C]

/-- The coefficientwise polynomial derivative of the unit series vanishes. -/
theorem Dx_one : Dx (1 : (Polynomial ℚ)⟦X⟧) = 0 := by
  ext n
  rw [coeff_Dx, coeff_one, map_zero]
  split_ifs <;> simp

/-- The coefficientwise polynomial derivative does not differentiate the series variable `X`. -/
theorem Dx_X : Dx (X : (Polynomial ℚ)⟦X⟧) = 0 := by
  ext n
  rw [coeff_Dx, coeff_X, map_zero]
  split_ifs <;> simp

/-- The coefficientwise polynomial derivative annihilates `1 + X`. -/
theorem Dx_one_add_X : Dx (1 + X : (Polynomial ℚ)⟦X⟧) = 0 := by
  rw [Dx_add, Dx_one, Dx_X, add_zero]

/-- `∂/∂x` commutes with `d/dt`. -/
theorem Dx_derivative_comm (f : (Polynomial ℚ)⟦X⟧) :
    Dx (d⁄dX (Polynomial ℚ) f) = d⁄dX (Polynomial ℚ) (Dx f) := by
  ext n
  rw [coeff_Dx, coeff_derivative, coeff_derivative, coeff_Dx]
  have hz : Polynomial.derivative ((n : Polynomial ℚ) + 1) = 0 := by simp
  rw [Polynomial.derivative_mul, hz, mul_zero, add_zero]

/-- `d/dt log(1+t) = 1/(1+t)`. -/
theorem derivative_log : d⁄dX ℚ (log ℚ) = invOneAdd ℚ := by
  ext n
  rw [coeff_derivative, coeff_log, if_neg (Nat.succ_ne_zero n), invOneAdd, coeff_rescale, coeff_mk,
    Pi.one_apply, Algebra.algebraMap_self, RingHom.id_apply]
  have hn : ((n : ℚ) + 1) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

/-- `log(1+t)` with constant coefficients in `ℚ[x][[t]]`. -/
noncomputable def logPoly : (Polynomial ℚ)⟦X⟧ :=
  PowerSeries.map (Polynomial.C : ℚ →+* Polynomial ℚ) (log ℚ)

/-- The constant coefficient of `logPoly` is zero. -/
theorem constantCoeff_logPoly : constantCoeff logPoly = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply, logPoly, coeff_map, coeff_zero_eq_constantCoeff_apply,
    constantCoeff_log, map_zero]

/-- Since `logPoly` has constant polynomial coefficients, `Dx logPoly = 0`. -/
theorem Dx_logPoly : Dx logPoly = 0 := Dx_map_C _

/-- Formal differentiation commutes with mapping rational coefficients to constant polynomials. -/
theorem derivative_map_C (f : ℚ⟦X⟧) :
    d⁄dX (Polynomial ℚ) (PowerSeries.map (Polynomial.C : ℚ →+* Polynomial ℚ) f) =
      PowerSeries.map (Polynomial.C : ℚ →+* Polynomial ℚ) (d⁄dX ℚ f) := by
  ext n
  rw [coeff_derivative, coeff_map, coeff_map, coeff_derivative, map_mul, map_add, map_natCast,
    map_one]

/-- The mapped logarithm satisfies `(1 + X) logPoly' = 1`. -/
theorem one_add_X_mul_derivative_logPoly : (1 + X) * d⁄dX (Polynomial ℚ) logPoly = 1 := by
  rw [logPoly, derivative_map_C, derivative_log]
  have h2 := congrArg (PowerSeries.map (Polynomial.C : ℚ →+* Polynomial ℚ))
    (one_add_X_mul_invOneAdd ℚ)
  rw [map_mul, map_add, map_one, PowerSeries.map_X] at h2
  exact h2

/-- The series `(1+t)^x = ∑_n (x)_n t^n/n!` over `ℚ[x]`. -/
noncomputable def fallingPoly : (Polynomial ℚ)⟦X⟧ := fallingSeries (Polynomial ℚ) Polynomial.X

/-- The universal falling-factorial series has constant coefficient `1`. -/
theorem constantCoeff_fallingPoly : constantCoeff fallingPoly = 1 :=
  constantCoeff_fallingSeries (Polynomial ℚ) Polynomial.X

/-- **`∂_x (1+t)^x = log(1+t) · (1+t)^x`.** -/
theorem Dx_fallingPoly : Dx fallingPoly = logPoly * fallingPoly := by
  have hB : (1 + X) * d⁄dX (Polynomial ℚ) fallingPoly =
      PowerSeries.C Polynomial.X * fallingPoly :=
    one_add_X_mul_derivative_fallingSeries (Polynomial ℚ) Polynomial.X
  have h1 : (1 + X) * d⁄dX (Polynomial ℚ) (Dx fallingPoly) =
      fallingPoly + PowerSeries.C Polynomial.X * Dx fallingPoly := by
    have h := congrArg Dx hB
    rw [Dx_mul, Dx_one_add_X, zero_mul, zero_add, Dx_derivative_comm, Dx_mul, Dx_C,
      Polynomial.derivative_X, map_one, one_mul] at h
    exact h
  have h2 := one_add_X_mul_derivative_logPoly
  have hF : (1 + X) * d⁄dX (Polynomial ℚ) (Dx fallingPoly - logPoly * fallingPoly) =
      PowerSeries.C Polynomial.X * (Dx fallingPoly - logPoly * fallingPoly) := by
    rw [map_sub, derivative_mul' (Polynomial ℚ) logPoly fallingPoly]
    linear_combination h1 - fallingPoly * h2 - logPoly * hB
  have h0 : constantCoeff (Dx fallingPoly - logPoly * fallingPoly) = 0 := by
    rw [map_sub, map_mul, constantCoeff_logPoly, zero_mul, sub_zero,
      ← coeff_zero_eq_constantCoeff_apply, coeff_Dx, coeff_zero_eq_constantCoeff_apply,
      constantCoeff_fallingPoly, Polynomial.derivative_one]
  exact sub_eq_zero.mp
    (eq_zero_of_one_add_X_mul_derivative_eq (Polynomial ℚ) Polynomial.X hF h0)

end PolyDeriv

end Fabius
