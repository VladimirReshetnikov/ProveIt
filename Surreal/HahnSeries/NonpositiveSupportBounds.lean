import Surreal.HahnSeries.NonpositiveSupportUnits
import Mathlib.RingTheory.HahnSeries.Lex

/-!
# Constant bounds in the nonpositive-support Hahn ring

The ordered-series step in `odg:def:rem:quarticvariant`. A series whose
square is bounded by the square of a coefficient constant is constant.
The proof uses Mathlib's lexicographic order and works over every ordered
coefficient field, without an Archimedean assumption.
-/

namespace Surreal.HahnSeries

open _root_.HahnSeries

noncomputable section

variable {Γ K : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
  [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- An ordinary coefficient bound on a square excludes negative Hahn order. -/
theorem nonpositiveSupport_eq_constant_of_sq_le (f : nonpositiveSupportSubring Γ K)
    (c : K) (h : (toLex f.val) ^ 2 ≤ (toLex (C c : K⟦Γ⟧)) ^ 2) :
    f = nonpositiveConstants (nonpositiveConstantCoeff f) := by
  apply nonpositiveSupport_eq_constant_of_order_nonneg
  by_contra! hneg
  have hf : f.val ≠ 0 := by intro hz; simp [hz] at hneg
  have ho : f.val.orderTop < (C c : K⟦Γ⟧).orderTop := by
    rw [← order_eq_orderTop_of_ne_zero hf]
    by_cases hc : c = 0
    · simp [hc]
    · simpa [hc] using hneg
  have hg : |toLex (C c : K⟦Γ⟧)| < |toLex f.val| := abs_lt_abs_of_orderTop_ofLex ho
  exact (not_lt_of_ge (sq_le_sq.mp h)) hg

end
end Surreal.HahnSeries
