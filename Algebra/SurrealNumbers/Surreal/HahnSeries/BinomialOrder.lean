import Surreal.HahnSeries.BinomialRoots
import Mathlib.RingTheory.HahnSeries.Lex

/-!
# Ordered interpretation of the binomial square root

Over an ordered coefficient field, the binomial root near one is positive
in Mathlib's lexicographic Hahn order. Its half-power is therefore the
unique nonnegative square root of `1 + x` for positive-order `x`.
This supplies the ordered-root identification used in local binomial
expansions in the trigonometry report. It requires no real-closedness
assumption, because the admissible binomial sum constructs this root.

The theorem concerns the set-sized ordered Hahn field, not yet surreal
numbers, a global square-root operation, or analytic convergence.
-/

namespace Surreal.HahnSeries

open _root_.HahnSeries

noncomputable section

variable {Γ K : Type*} [AddCommGroup Γ] [LinearOrder Γ]
  [IsOrderedAddMonoid Γ] [Field K] [LinearOrder K] [IsStrictOrderedRing K]

omit [IsOrderedAddMonoid Γ] in
/-- A Hahn series whose difference from one has positive order has positive
leading coefficient, so is positive in the lexicographic field order. -/
theorem lex_pos_of_sub_one_orderTop_pos (y : K⟦Γ⟧) (hy : 0 < (y - 1).orderTop) :
    0 < toLex y := by
  apply leadingCoeff_pos_iff.mp
  change 0 < y.leadingCoeff
  rw [((orderTop_self_sub_one_pos_iff y).mp hy).2]
  exact zero_lt_one

/-- Every rational binomial power near one is positive in the ordered Hahn field. -/
theorem binomialPower_lex_pos (x : K⟦Γ⟧) (hx : 0 < x.orderTop) (r : ℚ) :
    0 < toLex (binomialPower x hx r) :=
  lex_pos_of_sub_one_orderTop_pos _ (orderTop_binomialPower_sub_one_pos x hx r)

/-- The half-power binomial sum is the nonnegative square root, not merely
one of the two algebraic roots. This is the ordered branch in the local
square-root expansions of the trigonometry report. -/
theorem binomialPower_half_eq_of_nonneg_sq (x : K⟦Γ⟧) (hx : 0 < x.orderTop)
    (y : K⟦Γ⟧) (hy : 0 ≤ toLex y) (hsq : y ^ 2 = 1 + x) :
    y = binomialPower x hx (1 / 2 : ℚ) := by
  have heq : (toLex y) ^ 2 = (toLex (binomialPower x hx (1 / 2 : ℚ))) ^ 2 := by
    exact congrArg (toLex : K⟦Γ⟧ → Lex K⟦Γ⟧)
      (hsq.trans (binomialPower_half_sq x hx).symm)
  exact congrArg ofLex
    ((sq_eq_sq₀ hy (binomialPower_lex_pos x hx (1 / 2 : ℚ)).le).mp heq)

/-- Existence and uniqueness of the nonnegative square root of a
positive-order perturbation of one. -/
theorem exists_unique_nonneg_sqrt_one_add (x : K⟦Γ⟧) (hx : 0 < x.orderTop) :
    ∃! y : K⟦Γ⟧, 0 ≤ toLex y ∧ y ^ 2 = 1 + x := by
  refine ⟨binomialPower x hx (1 / 2 : ℚ),
    ⟨(binomialPower_lex_pos x hx (1 / 2 : ℚ)).le, binomialPower_half_sq x hx⟩, ?_⟩
  intro y hy
  exact binomialPower_half_eq_of_nonneg_sq x hx y hy.1 hy.2

end

end Surreal.HahnSeries
