import Surreal.Surcomplex.FiniteTrigonometry
import Mathlib.RingTheory.Polynomial.Chebyshev
import Mathlib.Tactic.LinearCombination

/-!
# Derived identities of finite surreal trigonometry

This file proves the standard identities listed below, for the phase-coordinate sine and cosine
`finiteSin`, `finiteCos` of `Surreal/Surcomplex/FiniteTrigonometry.lean` on the finite real
surreal subring `O_R`. They cover the double-angle, half-angle, sum-to-product and
product-to-sum clauses of `trigonometry:thm:identities` in
`docs/surcomplex/trigonometry/article.tex`, and the consequences displayed after that theorem,
including `trigonometry:eq:chebyshev`. The source's list of "usual" identities is open-ended.
Some standard forms are not stated here: the tangent sum form
`tan α ± tan β = sin (α ± β) / (cos α cos β)`, the tangent-parameter double-angle forms of `sin 2θ`
and `cos 2θ`, and the sign-resolved square-root half-angle forms. The half-angle identities
for sine and cosine appear only in squared form.

* Half angles. `finiteHalf θ` is `θ / 2`, formed inside `O_R`; it is the unique finite angle
  whose double is `θ`. The half-angle identities `cos² (θ/2) = (1 + cos θ) / 2`,
  `sin² (θ/2) = (1 - cos θ) / 2`, `tan² (θ/2) = (1 - cos θ) / (1 + cos θ)` and
  `tan (θ/2) = sin θ / (1 + cos θ) = (1 - cos θ) / sin θ` hold, as do the power-reduction forms
  for an arbitrary angle and the two further double-angle forms of cosine.
* Product-to-sum and sum-to-product. All four identities of each kind, e.g.
  `2 sin α sin β = cos (α - β) - cos (α + β)` and
  `cos α - cos β = -2 sin ((α + β)/2) sin ((α - β)/2)`.
* Tangent. `finiteTan θ = sin θ / cos θ`; the addition, subtraction and doubling formulas hold
  when the cosines of the given angles are nonzero.
* Chebyshev (`trigonometry:eq:chebyshev`). `cos (n α) = T_n (cos α)` and
  `sin (n α) = sin α · U_{n-1} (cos α)` for every ordinary integer `n`, with Mathlib's
  integer-indexed Chebyshev polynomials. These satisfy `T_0 = 1`, `T_1 = X`, `U_0 = 1`,
  `U_1 = 2X` and the three-term recurrence of the source for all integer indices, so the
  source's range `n ≥ 1` for the sine formula is included. The proof is the source's: both sides
  satisfy the same recurrence, via a generic uniqueness statement
  `eq_of_chebyshev_recurrence` over an arbitrary commutative ring.

Quotients follow Lean's convention `x / 0 = 0`. The half-angle tangent formulas then need no
hypothesis at all: when a denominator vanishes, both sides are zero. This is stronger than the
source's "every quotient restricted to a nonzero denominator". The tangent addition formula
needs only `cos α ≠ 0` and `cos β ≠ 0`; no condition on `cos (α + β)` is required.

Pending in `trigonometry:thm:identities`: the derivative clauses `sin' = cos`, `cos' = -sin`,
`cis' = i cis`, and the identification of the phase coordinates with the separate even and odd
Taylor sums `trigonometry:eq:sinfinite`, `trigonometry:eq:cosfinite`. These are not addressed
here.
-/

universe u

namespace Surreal.Surcomplex

open Foundations Polynomial

noncomputable section

/-! ### Chebyshev recurrences -/

/-- Two integer-indexed sequences that satisfy the Chebyshev three-term recurrence
`f (m + 1) = 2 c f m - f (m - 1)` with the same multiplier `c`, and agree at `0` and `1`,
agree everywhere. -/
theorem eq_of_chebyshev_recurrence {R : Type*} [CommRing R] (c : R) {f g : ℤ → R}
    (hf : ∀ m, f (m + 1) = 2 * c * f m - f (m - 1))
    (hg : ∀ m, g (m + 1) = 2 * c * g m - g (m - 1))
    (h0 : f 0 = g 0) (h1 : f 1 = g 1) (n : ℤ) : f n = g n := by
  induction n using Polynomial.Chebyshev.induct with
  | zero => exact h0
  | one => exact h1
  | add_two n ih1 ih2 =>
    have ef := hf ((n : ℤ) + 1)
    have eg := hg ((n : ℤ) + 1)
    rw [show (n : ℤ) + 1 + 1 = n + 2 by ring, add_sub_cancel_right] at ef eg
    rw [ef, eg, ih1, ih2]
  | neg_add_one n ih1 ih2 =>
    have ef := hf (-(n : ℤ))
    have eg := hg (-(n : ℤ))
    linear_combination ef - eg - ih2 + 2 * c * ih1

/-- The cosine of integer multiples satisfies the Chebyshev recurrence. -/
theorem finiteCos_zsmul_add_one (θ : SignSequence.FiniteElement.{u}) (m : ℤ) :
    finiteCos ((m + 1) • θ) =
      2 * finiteCos θ * finiteCos (m • θ) - finiteCos ((m - 1) • θ) := by
  rw [add_one_zsmul, sub_one_zsmul, ← sub_eq_add_neg, finiteCos_add, finiteCos_sub]
  ring

/-- The sine of integer multiples satisfies the Chebyshev recurrence. -/
theorem finiteSin_zsmul_add_one (θ : SignSequence.FiniteElement.{u}) (m : ℤ) :
    finiteSin ((m + 1) • θ) =
      2 * finiteCos θ * finiteSin (m • θ) - finiteSin ((m - 1) • θ) := by
  rw [add_one_zsmul, sub_one_zsmul, ← sub_eq_add_neg, finiteSin_add, finiteSin_sub]
  ring

/-- `trigonometry:eq:chebyshev`, first kind: `cos (n θ) = T_n (cos θ)` for every integer `n`. -/
theorem chebyshev_T_eval_finiteCos (n : ℤ) (θ : SignSequence.FiniteElement.{u}) :
    (Chebyshev.T SignSequence.{u} n).eval (finiteCos θ) = finiteCos (n • θ) := by
  refine eq_of_chebyshev_recurrence (finiteCos θ)
    (f := fun n => (Chebyshev.T SignSequence.{u} n).eval (finiteCos θ))
    (g := fun n => finiteCos (n • θ)) ?_ ?_ ?_ ?_ n
  · intro m
    simp only [Chebyshev.T_add_one, eval_sub, eval_mul, eval_ofNat, eval_X]
  · intro m
    exact finiteCos_zsmul_add_one θ m
  · simp
  · simp

/-- Second kind in Mathlib's normalization: `U_n (cos θ) sin θ = sin ((n + 1) θ)` for every
integer `n`. -/
theorem chebyshev_U_eval_finiteCos_mul_finiteSin (n : ℤ) (θ : SignSequence.FiniteElement.{u}) :
    (Chebyshev.U SignSequence.{u} n).eval (finiteCos θ) * finiteSin θ =
      finiteSin ((n + 1) • θ) := by
  refine eq_of_chebyshev_recurrence (finiteCos θ)
    (f := fun n => (Chebyshev.U SignSequence.{u} n).eval (finiteCos θ) * finiteSin θ)
    (g := fun n => finiteSin ((n + 1) • θ)) ?_ ?_ ?_ ?_ n
  · intro m
    simp only [Chebyshev.U_add_one, eval_sub, eval_mul, eval_ofNat, eval_X]
    ring
  · intro m
    rw [sub_add_cancel, finiteSin_zsmul_add_one θ (m + 1), add_sub_cancel_right]
  · simp
  · simp only [Chebyshev.U_one, eval_mul, eval_ofNat, eval_X]
    rw [add_zsmul, one_zsmul, finiteSin_add]
    ring

/-- `trigonometry:eq:chebyshev`, second kind in the source's form:
`sin (n θ) = sin θ · U_{n-1} (cos θ)`, for every integer `n` (the source states `n ≥ 1`). -/
theorem finiteSin_zsmul_eq_mul_chebyshev_U (n : ℤ) (θ : SignSequence.FiniteElement.{u}) :
    finiteSin (n • θ) =
      finiteSin θ * (Chebyshev.U SignSequence.{u} (n - 1)).eval (finiteCos θ) := by
  rw [mul_comm, chebyshev_U_eval_finiteCos_mul_finiteSin, sub_add_cancel]

/-! ### Double angles and power reduction -/

/-- Double-angle cosine in terms of cosine alone. -/
theorem finiteCos_two_mul_eq_cos_sq (θ : SignSequence.FiniteElement.{u}) :
    finiteCos (2 * θ) = 2 * finiteCos θ ^ 2 - 1 := by
  rw [finiteCos_two_mul]
  linear_combination -finiteCos_sq_add_finiteSin_sq θ

/-- Double-angle cosine in terms of sine alone. -/
theorem finiteCos_two_mul_eq_sin_sq (θ : SignSequence.FiniteElement.{u}) :
    finiteCos (2 * θ) = 1 - 2 * finiteSin θ ^ 2 := by
  rw [finiteCos_two_mul]
  linear_combination finiteCos_sq_add_finiteSin_sq θ

/-- Power reduction for the square of the cosine. -/
theorem finiteCos_sq_eq (θ : SignSequence.FiniteElement.{u}) :
    finiteCos θ ^ 2 = (1 + finiteCos (2 * θ)) / 2 := by
  rw [finiteCos_two_mul_eq_cos_sq]
  ring

/-- Power reduction for the square of the sine. -/
theorem finiteSin_sq_eq (θ : SignSequence.FiniteElement.{u}) :
    finiteSin θ ^ 2 = (1 - finiteCos (2 * θ)) / 2 := by
  rw [finiteCos_two_mul_eq_sin_sq]
  ring

/-! ### Half angles -/

/-- The half `θ / 2` of a finite angle, formed inside the finite subring. -/
def finiteHalf (θ : SignSequence.FiniteElement.{u}) : SignSequence.FiniteElement.{u} :=
  ((2⁻¹ : ℚ) : SignSequence.FiniteElement.{u}) * θ

@[simp] theorem val_finiteHalf (θ : SignSequence.FiniteElement.{u}) :
    (finiteHalf θ).1 = θ.1 / 2 := by
  change ((2⁻¹ : ℚ) : SignSequence.{u}) * θ.1 = θ.1 / 2
  push_cast
  ring

theorem finiteHalf_add_finiteHalf (θ : SignSequence.FiniteElement.{u}) :
    finiteHalf θ + finiteHalf θ = θ := by
  apply ArchimedeanClass.FiniteElement.ext
  rw [ArchimedeanClass.FiniteElement.val_add, val_finiteHalf, add_halves]

theorem two_mul_finiteHalf (θ : SignSequence.FiniteElement.{u}) :
    2 * finiteHalf θ = θ := by
  rw [two_mul, finiteHalf_add_finiteHalf]

/-- The half is the unique finite angle whose double is the given angle. -/
theorem eq_finiteHalf_iff (θ φ : SignSequence.FiniteElement.{u}) :
    φ = finiteHalf θ ↔ 2 * φ = θ := by
  constructor
  · rintro rfl
    exact two_mul_finiteHalf θ
  · rintro rfl
    apply ArchimedeanClass.FiniteElement.ext
    rw [val_finiteHalf, two_mul, ArchimedeanClass.FiniteElement.val_add, add_self_div_two]

theorem finiteHalf_add_add_finiteHalf_sub (α β : SignSequence.FiniteElement.{u}) :
    finiteHalf (α + β) + finiteHalf (α - β) = α := by
  apply ArchimedeanClass.FiniteElement.ext
  simp only [ArchimedeanClass.FiniteElement.val_add, ArchimedeanClass.FiniteElement.val_sub,
    val_finiteHalf]
  ring

theorem finiteHalf_add_sub_finiteHalf_sub (α β : SignSequence.FiniteElement.{u}) :
    finiteHalf (α + β) - finiteHalf (α - β) = β := by
  apply ArchimedeanClass.FiniteElement.ext
  simp only [ArchimedeanClass.FiniteElement.val_add, ArchimedeanClass.FiniteElement.val_sub,
    val_finiteHalf]
  ring

/-- Half-angle formula for cosine (`trigonometry:thm:identities`). -/
theorem finiteCos_finiteHalf_sq (θ : SignSequence.FiniteElement.{u}) :
    finiteCos (finiteHalf θ) ^ 2 = (1 + finiteCos θ) / 2 := by
  rw [finiteCos_sq_eq, two_mul_finiteHalf]

/-- Half-angle formula for sine (`trigonometry:thm:identities`). -/
theorem finiteSin_finiteHalf_sq (θ : SignSequence.FiniteElement.{u}) :
    finiteSin (finiteHalf θ) ^ 2 = (1 - finiteCos θ) / 2 := by
  rw [finiteSin_sq_eq, two_mul_finiteHalf]

/-! ### Tangent -/

/-- Tangent of a finite real surreal angle, with Lean's convention `x / 0 = 0`. -/
def finiteTan (θ : SignSequence.FiniteElement.{u}) : SignSequence.{u} :=
  finiteSin θ / finiteCos θ

@[simp] theorem finiteTan_zero : finiteTan (0 : SignSequence.FiniteElement.{u}) = 0 := by
  simp [finiteTan]

@[simp] theorem finiteTan_neg (θ : SignSequence.FiniteElement.{u}) :
    finiteTan (-θ) = -finiteTan θ := by
  simp only [finiteTan, finiteSin_neg, finiteCos_neg, neg_div]

/-- Tangent addition formula, from the consequences displayed after `trigonometry:thm:identities`
(the unlabeled display ending in `trigonometry:eq:chebyshev`). It assumes only that the cosines
of the two summands are nonzero. -/
theorem finiteTan_add {α β : SignSequence.FiniteElement.{u}} (hα : finiteCos α ≠ 0)
    (hβ : finiteCos β ≠ 0) :
    finiteTan (α + β) = (finiteTan α + finiteTan β) / (1 - finiteTan α * finiteTan β) := by
  simp only [finiteTan]
  rw [finiteSin_add, finiteCos_add, div_add_div _ _ hα hβ, div_mul_div_comm,
    one_sub_div (mul_ne_zero hα hβ), div_div_div_cancel_right₀ (mul_ne_zero hα hβ)]

/-- Tangent subtraction formula. -/
theorem finiteTan_sub {α β : SignSequence.FiniteElement.{u}} (hα : finiteCos α ≠ 0)
    (hβ : finiteCos β ≠ 0) :
    finiteTan (α - β) = (finiteTan α - finiteTan β) / (1 + finiteTan α * finiteTan β) := by
  rw [sub_eq_add_neg, finiteTan_add hα (by rwa [finiteCos_neg]), finiteTan_neg]
  ring

/-- Tangent double-angle formula. -/
theorem finiteTan_two_mul {θ : SignSequence.FiniteElement.{u}} (hθ : finiteCos θ ≠ 0) :
    finiteTan (2 * θ) = 2 * finiteTan θ / (1 - finiteTan θ ^ 2) := by
  rw [two_mul, finiteTan_add hθ hθ]
  ring

/-- Tangent of an angle through the sine and cosine of its double. -/
theorem finiteTan_eq_finiteSin_two_mul_div (θ : SignSequence.FiniteElement.{u}) :
    finiteTan θ = finiteSin (2 * θ) / (1 + finiteCos (2 * θ)) := by
  have h : 1 + finiteCos (2 * θ) = 2 * finiteCos θ * finiteCos θ := by
    rw [finiteCos_two_mul_eq_cos_sq]
    ring
  rw [finiteTan, h, finiteSin_two_mul]
  by_cases hc : finiteCos θ = 0
  · simp [hc]
  · rw [mul_div_mul_right _ _ hc, mul_div_mul_left _ _ two_ne_zero]

/-- Tangent of an angle through the cosine and sine of its double. -/
theorem finiteTan_eq_one_sub_finiteCos_two_mul_div (θ : SignSequence.FiniteElement.{u}) :
    finiteTan θ = (1 - finiteCos (2 * θ)) / finiteSin (2 * θ) := by
  have h : 1 - finiteCos (2 * θ) = 2 * finiteSin θ * finiteSin θ := by
    rw [finiteCos_two_mul_eq_sin_sq]
    ring
  rw [finiteTan, h, finiteSin_two_mul]
  by_cases hs : finiteSin θ = 0
  · simp [hs]
  · rw [mul_div_mul_left _ _ (mul_ne_zero two_ne_zero hs)]

/-- Squared tangent of an angle through the cosine of its double. -/
theorem finiteTan_sq_eq (θ : SignSequence.FiniteElement.{u}) :
    finiteTan θ ^ 2 = (1 - finiteCos (2 * θ)) / (1 + finiteCos (2 * θ)) := by
  rw [finiteTan, div_pow, finiteSin_sq_eq, finiteCos_sq_eq,
    div_div_div_cancel_right₀ two_ne_zero]

/-- Half-angle tangent, first form (`trigonometry:thm:identities`). No hypothesis is needed:
when `1 + cos θ = 0` both sides vanish. -/
theorem finiteTan_finiteHalf_eq_finiteSin_div (θ : SignSequence.FiniteElement.{u}) :
    finiteTan (finiteHalf θ) = finiteSin θ / (1 + finiteCos θ) := by
  rw [finiteTan_eq_finiteSin_two_mul_div, two_mul_finiteHalf]

/-- Half-angle tangent, second form (`trigonometry:thm:identities`). No hypothesis is needed:
when `sin θ = 0` both sides vanish. -/
theorem finiteTan_finiteHalf_eq_one_sub_finiteCos_div (θ : SignSequence.FiniteElement.{u}) :
    finiteTan (finiteHalf θ) = (1 - finiteCos θ) / finiteSin θ := by
  rw [finiteTan_eq_one_sub_finiteCos_two_mul_div, two_mul_finiteHalf]

/-- Squared half-angle tangent. -/
theorem finiteTan_finiteHalf_sq (θ : SignSequence.FiniteElement.{u}) :
    finiteTan (finiteHalf θ) ^ 2 = (1 - finiteCos θ) / (1 + finiteCos θ) := by
  rw [finiteTan_sq_eq, two_mul_finiteHalf]

/-! ### Product-to-sum -/

/-- Product-to-sum for two sines (`trigonometry:thm:identities`). -/
theorem two_mul_finiteSin_mul_finiteSin (α β : SignSequence.FiniteElement.{u}) :
    2 * finiteSin α * finiteSin β = finiteCos (α - β) - finiteCos (α + β) := by
  rw [finiteCos_sub, finiteCos_add]
  ring

/-- Product-to-sum for two cosines. -/
theorem two_mul_finiteCos_mul_finiteCos (α β : SignSequence.FiniteElement.{u}) :
    2 * finiteCos α * finiteCos β = finiteCos (α - β) + finiteCos (α + β) := by
  rw [finiteCos_sub, finiteCos_add]
  ring

/-- Product-to-sum for a sine times a cosine. -/
theorem two_mul_finiteSin_mul_finiteCos (α β : SignSequence.FiniteElement.{u}) :
    2 * finiteSin α * finiteCos β = finiteSin (α + β) + finiteSin (α - β) := by
  rw [finiteSin_sub, finiteSin_add]
  ring

/-- Product-to-sum for a cosine times a sine. -/
theorem two_mul_finiteCos_mul_finiteSin (α β : SignSequence.FiniteElement.{u}) :
    2 * finiteCos α * finiteSin β = finiteSin (α + β) - finiteSin (α - β) := by
  rw [finiteSin_sub, finiteSin_add]
  ring

/-! ### Sum-to-product -/

/-- Sum-to-product for sines (`trigonometry:thm:identities`). -/
theorem finiteSin_add_finiteSin (α β : SignSequence.FiniteElement.{u}) :
    finiteSin α + finiteSin β =
      2 * finiteSin (finiteHalf (α + β)) * finiteCos (finiteHalf (α - β)) := by
  have h := two_mul_finiteSin_mul_finiteCos (finiteHalf (α + β)) (finiteHalf (α - β))
  rw [finiteHalf_add_add_finiteHalf_sub, finiteHalf_add_sub_finiteHalf_sub] at h
  exact h.symm

/-- Sum-to-product for a difference of sines. -/
theorem finiteSin_sub_finiteSin (α β : SignSequence.FiniteElement.{u}) :
    finiteSin α - finiteSin β =
      2 * finiteCos (finiteHalf (α + β)) * finiteSin (finiteHalf (α - β)) := by
  have h := two_mul_finiteCos_mul_finiteSin (finiteHalf (α + β)) (finiteHalf (α - β))
  rw [finiteHalf_add_add_finiteHalf_sub, finiteHalf_add_sub_finiteHalf_sub] at h
  exact h.symm

/-- Sum-to-product for cosines. -/
theorem finiteCos_add_finiteCos (α β : SignSequence.FiniteElement.{u}) :
    finiteCos α + finiteCos β =
      2 * finiteCos (finiteHalf (α + β)) * finiteCos (finiteHalf (α - β)) := by
  have h := two_mul_finiteCos_mul_finiteCos (finiteHalf (α + β)) (finiteHalf (α - β))
  rw [finiteHalf_add_add_finiteHalf_sub, finiteHalf_add_sub_finiteHalf_sub] at h
  linear_combination -h

/-- Sum-to-product for a difference of cosines (`trigonometry:thm:identities`). -/
theorem finiteCos_sub_finiteCos (α β : SignSequence.FiniteElement.{u}) :
    finiteCos α - finiteCos β =
      -2 * finiteSin (finiteHalf (α + β)) * finiteSin (finiteHalf (α - β)) := by
  have h := two_mul_finiteSin_mul_finiteSin (finiteHalf (α + β)) (finiteHalf (α - β))
  rw [finiteHalf_add_add_finiteHalf_sub, finiteHalf_add_sub_finiteHalf_sub] at h
  linear_combination h

end

end Surreal.Surcomplex
