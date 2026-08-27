import FabiusFunction.ThueMorseIntegerLiftEquation
import Mathlib.RingTheory.PowerSeries.Derivative

/-!
# The three-term recurrence of the integral lift

The last piece of the atlas's integer-lift theorem: the constructed
sequence satisfies `n·c(n) = (5-2n)·c(n-1) + 3(n-1)·c(n-2) + 1`.

Differentiating the proven algebraic equation gives a quadratic
relation between `C` and `C'`; multiplying by the unit-square factor
`(1-z)(2(1-z)C+1)` and reducing by the equation itself — one
`linear_combination` certificate — linearizes it to the first-order
equation `(1+3z)(1-z)²·C' = 1 + 3(1-z²)·C`.  Extracting coefficients
yields a four-term relation, which telescopes into the atlas's
three-term recurrence by induction.

* `integerLiftSeries_ode` — the linear ODE.
* `integerLift_four_term` — its coefficient form.
* `integerLift_recurrence` — **the recurrence**
  (`eq:integer-lift-recurrence`).
-/

set_option autoImplicit false

open Finset PowerSeries

namespace Fabius

private theorem derivative_one_sub_X :
    d⁄dX ℤ (1 - X : PowerSeries ℤ) = -1 := by
  rw [map_sub, derivative_X, Derivation.map_one_eq_zero]
  ring

set_option maxHeartbeats 1600000 in
/-- **The linear ODE of the integral lift**:
`(1+3z)·(1-z)²·C'(z) = 1 + 3·(1-z²)·C(z)`. -/
theorem integerLiftSeries_ode :
    (1 + 3 * X) * (1 - X : PowerSeries ℤ) ^ 2 *
        (d⁄dX ℤ integerLiftSeries) =
      1 + 3 * (1 - X ^ 2) * integerLiftSeries := by
  have hE := integerLiftSeries_algebraic
  -- differentiate the algebraic equation
  have hD0 : -3 * (1 - X : PowerSeries ℤ) ^ 2 * integerLiftSeries ^ 2 +
      (1 - X) ^ 3 * (2 * integerLiftSeries * (d⁄dX ℤ integerLiftSeries)) -
      2 * (1 - X) * integerLiftSeries +
      (1 - X) ^ 2 * (d⁄dX ℤ integerLiftSeries) = 1 := by
    have hd := congrArg (fun f => d⁄dX ℤ f) hE
    simp only [map_add, Derivation.leibniz, Derivation.leibniz_pow,
      derivative_one_sub_X, derivative_X, smul_eq_mul, nsmul_eq_mul] at hd
    push_cast at hd
    linear_combination hd
  linear_combination
    ((1 - X : PowerSeries ℤ) * (2 * (1 - X) * integerLiftSeries + 1)) * hD0 -
      (4 * (1 - X) ^ 2 * (d⁄dX ℤ integerLiftSeries) -
        6 * (1 - X) * integerLiftSeries - 1) * hE

/-- The coefficient form: a four-term relation for `n ≥ 2`. -/
theorem integerLift_four_term (n : ℕ) (hn : 2 ≤ n) :
    ((n : ℤ) + 1) * integerLift (n + 1) + (n : ℤ) * integerLift n -
      5 * ((n : ℤ) - 1) * integerLift (n - 1) +
      3 * ((n : ℤ) - 2) * integerLift (n - 2) =
    3 * integerLift n - 3 * integerLift (n - 2) := by
  have hODE := integerLiftSeries_ode
  -- rewrite both sides in constant-times-shift normal form
  have hL : (1 + 3 * X) * (1 - X : PowerSeries ℤ) ^ 2 *
      (d⁄dX ℤ integerLiftSeries) =
      (d⁄dX ℤ integerLiftSeries) +
        X * (d⁄dX ℤ integerLiftSeries) -
        (PowerSeries.C (R := ℤ)) 5 *
          (X ^ 2 * (d⁄dX ℤ integerLiftSeries)) +
        (PowerSeries.C (R := ℤ)) 3 *
          (X ^ 3 * (d⁄dX ℤ integerLiftSeries)) := by
    have h5 : ((PowerSeries.C (R := ℤ)) 5 : PowerSeries ℤ) = 5 :=
      map_ofNat _ 5
    have h3 : ((PowerSeries.C (R := ℤ)) 3 : PowerSeries ℤ) = 3 :=
      map_ofNat _ 3
    rw [h5, h3]
    ring
  have hR : (1 : PowerSeries ℤ) + 3 * (1 - X ^ 2) * integerLiftSeries =
      1 + (PowerSeries.C (R := ℤ)) 3 * integerLiftSeries -
        (PowerSeries.C (R := ℤ)) 3 * (X ^ 2 * integerLiftSeries) := by
    have h3 : ((PowerSeries.C (R := ℤ)) 3 : PowerSeries ℤ) = 3 :=
      map_ofNat _ 3
    rw [h3]
    ring
  rw [hL, hR] at hODE
  have hcoeff := congrArg (fun f => (PowerSeries.coeff n) f) hODE
  simp only [map_add, map_sub, PowerSeries.coeff_C_mul] at hcoeff
  -- evaluate each shifted coefficient
  have hD : ∀ k : ℕ, (PowerSeries.coeff k) (d⁄dX ℤ integerLiftSeries) =
      integerLift (k + 1) * ((k : ℤ) + 1) := by
    intro k
    rw [PowerSeries.coeff_derivative, integerLiftSeries,
      PowerSeries.coeff_mk]
    try push_cast
    try ring
  have hXD : (PowerSeries.coeff n)
      (X * (d⁄dX ℤ integerLiftSeries)) =
      integerLift n * (n : ℤ) := by
    obtain ⟨p, rfl⟩ : ∃ p, n = p + 1 := ⟨n - 1, by omega⟩
    rw [PowerSeries.coeff_succ_X_mul, hD]
    push_cast
    try ring
  have hX2D : (PowerSeries.coeff n)
      (X ^ 2 * (d⁄dX ℤ integerLiftSeries)) =
      integerLift (n - 1) * ((n : ℤ) - 1) := by
    rw [PowerSeries.coeff_X_pow_mul', if_pos hn, hD]
    rw [show n - 2 + 1 = n - 1 by omega]
    push_cast [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_sub
      (by omega : 2 ≤ n)]
    ring
  have hX3D : (PowerSeries.coeff n)
      (X ^ 3 * (d⁄dX ℤ integerLiftSeries)) =
      if 3 ≤ n then integerLift (n - 2) * ((n : ℤ) - 2) else 0 := by
    rw [PowerSeries.coeff_X_pow_mul']
    split_ifs with h
    · rw [hD, show n - 3 + 1 = n - 2 by omega]
      push_cast [Nat.cast_sub (by omega : 2 ≤ n), Nat.cast_sub h]
      ring
    · rfl
  have hX2C : (PowerSeries.coeff n) (X ^ 2 * integerLiftSeries) =
      integerLift (n - 2) := by
    rw [PowerSeries.coeff_X_pow_mul', if_pos hn, integerLiftSeries,
      PowerSeries.coeff_mk]
  have hone : (PowerSeries.coeff n) (1 : PowerSeries ℤ) = 0 := by
    rw [PowerSeries.coeff_one, if_neg (by omega)]
  have hC : (PowerSeries.coeff n) integerLiftSeries = integerLift n := by
    rw [integerLiftSeries, PowerSeries.coeff_mk]
  rw [hD n, hXD, hX2D, hX3D, hX2C, hone, hC] at hcoeff
  rcases Nat.lt_or_ge n 3 with h3 | h3
  · -- `n = 2`: the cubic-shift term is absent and its coefficient vanishes
    have hn2 : n = 2 := by omega
    subst hn2
    rw [if_neg (by omega)] at hcoeff
    push_cast at hcoeff ⊢
    linarith [hcoeff]
  · rw [if_pos h3] at hcoeff
    try push_cast at hcoeff ⊢
    linarith [hcoeff]

/-- `c(2) = 1`. -/
private theorem integerLift_two : integerLift 2 = 1 := by
  rw [integerLift, show Icc 1 2 = {1, 2} from rfl]
  rw [Finset.sum_insert (by norm_num), Finset.sum_singleton]
  norm_num [catalan_one]

/-- **The three-term recurrence** (`eq:integer-lift-recurrence`):
`n·c(n) = (5-2n)·c(n-1) + 3·(n-1)·c(n-2) + 1` for `n ≥ 2`. -/
theorem integerLift_recurrence (n : ℕ) (hn : 2 ≤ n) :
    (n : ℤ) * integerLift n =
      (5 - 2 * (n : ℤ)) * integerLift (n - 1) +
        3 * ((n : ℤ) - 1) * integerLift (n - 2) + 1 := by
  induction n with
  | zero => omega
  | succ n ih =>
      rcases Nat.lt_or_ge n 2 with hn2 | hn2
      · -- base case `n + 1 = 2`
        have h2 : n = 1 := by omega
        subst h2
        rw [integerLift_two, show (2 : ℕ) - 1 = 1 from rfl,
          show (2 : ℕ) - 2 = 0 from rfl, integerLift_one, integerLift_zero]
        norm_num
      · -- inductive step through the four-term relation
        have hR3 := ih hn2
        have hR4 := integerLift_four_term n hn2
        have harg1 : n + 1 - 1 = n := by omega
        have harg2 : n + 1 - 2 = n - 1 := by omega
        rw [harg1, harg2]
        have hcast : ((n : ℤ) + 1) = ((n + 1 : ℕ) : ℤ) := by push_cast; ring
        rw [← hcast]
        linear_combination hR4 + hR3

end Fabius
