import Mathlib

/-!
# Algebraic trigonometry independent of classical real analysis

This file is a Mathlib-level prototype of the division-free layer used in the
accompanying iPRA report.  It deliberately assumes only an additive angle
group, a commutative coefficient ring, the sine/cosine addition laws, the
Pythagorean identity, and a quarter turn.  The analytic iPRA realization of
these assumptions is specified in `IPRABridge.lean` and in the article.

The file is intended as a clean first target for a complete Lean development.
It was not compiled in the artifact-building environment, which did not contain
Lean.  No theorem below uses excluded middle or choice.
-/

namespace TrigIPRA

class TrigSystem (Angle R : Type*) [AddCommGroup Angle] [CommRing R] where
  sin : Angle → R
  cos : Angle → R
  q : Angle                         -- quarter turn, eventually pi/2
  sin_zero : sin 0 = 0
  cos_zero : cos 0 = 1
  sin_add : ∀ x y, sin (x + y) = sin x * cos y + cos x * sin y
  cos_add : ∀ x y, cos (x + y) = cos x * cos y - sin x * sin y
  pythagorean : ∀ x, sin x ^ 2 + cos x ^ 2 = 1
  sin_q : sin q = 1
  cos_q : cos q = 0

namespace TrigSystem

variable {Angle R : Type*} [AddCommGroup Angle] [CommRing R]
  [TrigSystem Angle R]

local notation "S" => TrigSystem.sin (Angle := Angle) (R := R)
local notation "C" => TrigSystem.cos (Angle := Angle) (R := R)
local notation "q" => TrigSystem.q (Angle := Angle) (R := R)

/-- Constructive parity of sine, derived rather than postulated. -/
theorem sin_neg (x : Angle) : S (-x) = -S x := by
  have hs : S x * C (-x) + C x * S (-x) = 0 := by
    simpa using TrigSystem.sin_add (Angle := Angle) (R := R) x (-x)
  have hc : C x * C (-x) - S x * S (-x) = 1 := by
    simpa using TrigSystem.cos_add (Angle := Angle) (R := R) x (-x)
  calc
    S (-x) = (S x ^ 2 + C x ^ 2) * S (-x) := by
      rw [TrigSystem.pythagorean (Angle := Angle) (R := R) x]
      ring
    _ = C x * (S x * C (-x) + C x * S (-x))
          - S x * (C x * C (-x) - S x * S (-x)) := by ring
    _ = -S x := by rw [hs, hc]; ring

/-- Constructive parity of cosine, derived rather than postulated. -/
theorem cos_neg (x : Angle) : C (-x) = C x := by
  have hs : S x * C (-x) + C x * S (-x) = 0 := by
    simpa using TrigSystem.sin_add (Angle := Angle) (R := R) x (-x)
  have hc : C x * C (-x) - S x * S (-x) = 1 := by
    simpa using TrigSystem.cos_add (Angle := Angle) (R := R) x (-x)
  calc
    C (-x) = (S x ^ 2 + C x ^ 2) * C (-x) := by
      rw [TrigSystem.pythagorean (Angle := Angle) (R := R) x]
      ring
    _ = S x * (S x * C (-x) + C x * S (-x))
          + C x * (C x * C (-x) - S x * S (-x)) := by ring
    _ = C x := by rw [hs, hc]; ring

@[simp] theorem sin_sub (x y : Angle) :
    S (x - y) = S x * C y - C x * S y := by
  rw [sub_eq_add_neg, TrigSystem.sin_add, sin_neg, cos_neg]
  ring

@[simp] theorem cos_sub (x y : Angle) :
    C (x - y) = C x * C y + S x * S y := by
  rw [sub_eq_add_neg, TrigSystem.cos_add, sin_neg, cos_neg]
  ring

abbrev pi : Angle := q + q
abbrev tau : Angle := pi (Angle := Angle) (R := R) + pi (Angle := Angle) (R := R)

@[simp] theorem sin_pi : S (pi (Angle := Angle) (R := R)) = 0 := by
  simp [pi, TrigSystem.sin_add, TrigSystem.sin_q, TrigSystem.cos_q]

@[simp] theorem cos_pi : C (pi (Angle := Angle) (R := R)) = -1 := by
  simp [pi, TrigSystem.cos_add, TrigSystem.sin_q, TrigSystem.cos_q]

@[simp] theorem sin_add_q (x : Angle) : S (x + q) = C x := by
  simp [TrigSystem.sin_add, TrigSystem.sin_q, TrigSystem.cos_q]

@[simp] theorem cos_add_q (x : Angle) : C (x + q) = -S x := by
  simp [TrigSystem.cos_add, TrigSystem.sin_q, TrigSystem.cos_q]

@[simp] theorem sin_add_pi (x : Angle) :
    S (x + pi (Angle := Angle) (R := R)) = -S x := by
  simp [TrigSystem.sin_add]

@[simp] theorem cos_add_pi (x : Angle) :
    C (x + pi (Angle := Angle) (R := R)) = -C x := by
  simp [TrigSystem.cos_add]

@[simp] theorem sin_period_tau (x : Angle) :
    S (x + tau (Angle := Angle) (R := R)) = S x := by
  simp [tau, add_assoc]

@[simp] theorem cos_period_tau (x : Angle) :
    C (x + tau (Angle := Angle) (R := R)) = C x := by
  simp [tau, add_assoc]

@[simp] theorem sin_two_mul (x : Angle) : S (x + x) = 2 * S x * C x := by
  rw [TrigSystem.sin_add]
  ring

@[simp] theorem cos_two_mul (x : Angle) : C (x + x) = C x ^ 2 - S x ^ 2 := by
  rw [TrigSystem.cos_add]
  ring

@[simp] theorem cos_two_mul_cos (x : Angle) : C (x + x) = 2 * C x ^ 2 - 1 := by
  rw [cos_two_mul]
  have hp := TrigSystem.pythagorean (Angle := Angle) (R := R) x
  linear_combination hp

@[simp] theorem cos_two_mul_sin (x : Angle) : C (x + x) = 1 - 2 * S x ^ 2 := by
  rw [cos_two_mul]
  have hp := TrigSystem.pythagorean (Angle := Angle) (R := R) x
  linear_combination -hp

@[simp] theorem sin_three_mul (x : Angle) :
    S (x + x + x) = 3 * S x - 4 * S x ^ 3 := by
  rw [TrigSystem.sin_add, sin_two_mul, cos_two_mul_sin]
  have hp := TrigSystem.pythagorean (Angle := Angle) (R := R) x
  linear_combination 2 * S x * hp

@[simp] theorem cos_three_mul (x : Angle) :
    C (x + x + x) = 4 * C x ^ 3 - 3 * C x := by
  rw [TrigSystem.cos_add, cos_two_mul_cos, sin_two_mul]
  have hp := TrigSystem.pythagorean (Angle := Angle) (R := R) x
  linear_combination -2 * C x * hp

/-- The recurrence behind Chebyshev polynomials. -/
theorem cos_succ_recurrence (x y : Angle) :
    C (x + y) + C (x - y) = 2 * C x * C y := by
  rw [TrigSystem.cos_add, cos_sub]
  ring

/-- The companion recurrence for sine. -/
theorem sin_succ_recurrence (x y : Angle) :
    S (x + y) + S (x - y) = 2 * S x * C y := by
  rw [TrigSystem.sin_add, sin_sub]
  ring

section DivisionByTwo

variable [Field R] [CharZero R]

/-- Product-to-sum, with division only by the numeral two. -/
theorem cos_mul_cos (x y : Angle) :
    C x * C y = (C (x - y) + C (x + y)) / 2 := by
  rw [cos_sub, TrigSystem.cos_add]
  ring

/-- Product-to-sum, with division only by the numeral two. -/
theorem sin_mul_sin (x y : Angle) :
    S x * S y = (C (x - y) - C (x + y)) / 2 := by
  rw [cos_sub, TrigSystem.cos_add]
  ring

/-- Product-to-sum, with division only by the numeral two. -/
theorem sin_mul_cos (x y : Angle) :
    S x * C y = (S (x + y) + S (x - y)) / 2 := by
  rw [TrigSystem.sin_add, sin_sub]
  ring

/-- Product-to-sum, with division only by the numeral two. -/
theorem cos_mul_sin (x y : Angle) :
    C x * S y = (S (x + y) - S (x - y)) / 2 := by
  rw [TrigSystem.sin_add, sin_sub]
  ring

/-- The square half-angle identity in division-free analytic form. -/
theorem sin_sq_half_core (x : Angle) : S x ^ 2 = (1 - C (x + x)) / 2 := by
  rw [cos_two_mul_sin]
  ring

/-- The square half-angle identity in division-free analytic form. -/
theorem cos_sq_half_core (x : Angle) : C x ^ 2 = (1 + C (x + x)) / 2 := by
  rw [cos_two_mul_cos]
  ring

end DivisionByTwo

end TrigSystem

/-!
The next implementation module should add:

* a syntax of integer angle vectors and Gaussian Laurent polynomials;
* a primitive-recursive normalizer;
* an evaluator into every `TrigSystem`;
* a soundness theorem saying that a zero normalized residue proves the
  corresponding identity;
* rational expressions represented by a numerator and a denominator, with
  the semantic theorem guarded by apartness certificates for every evaluated
  denominator.

The Python artifact `scripts/verify_identities.py` is an executable reference
implementation of precisely that normalizer.
-/

end TrigIPRA
