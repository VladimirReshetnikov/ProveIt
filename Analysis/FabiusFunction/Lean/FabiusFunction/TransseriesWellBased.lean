import Mathlib.Order.WellQuasiOrder
import Mathlib.Data.Set.MulAntidiagonal
import Mathlib.Data.Finset.MulAntidiagonal
import Mathlib.Algebra.Group.Pointwise.Set.Basic

/-!
# Well-based supports: Dickson's lemma and Neumann's lemma

The transseries volume's `q0:lem:dickson` and `q0:lem:neumann`, the two
order-theoretic facts that make Hahn series work: the supports of a product are
again well-based, and each monomial of a product has only finitely many
factorizations, so the coefficient sum defining the product is finite.

Both are Mathlib results once "well-based" is read as `Set.IsPWO`, so this
module is a bridge rather than a proof: it states them in the volume's phrasing
and pins the Mathlib names, which is what the crosswalk needs.  The volume notes
that one of the two is stated in its sources without proof; here both are
machine-checked.

`Set.IsPWO s` says `s` is partially well-ordered by `≤`: every sequence in `s`
has an increasing pair.  For a linear order that is the volume's "well-based"
(no infinite strictly decreasing sequence), and in general it is the right
hypothesis, since it is what closes under products.
-/

set_option autoImplicit false

open Set Pointwise

namespace Fabius

/-! ### Dickson's lemma -/

/-- **`q0:lem:dickson`.**  Every subset of `ℕ^k` is partially well-ordered by the
componentwise order.  This is Mathlib's `Pi.wellQuasiOrderedLE` for a finite
index type together with the well-quasi-order of `ℕ`. -/
theorem dickson_isPWO (k : ℕ) (s : Set (Fin k → ℕ)) : s.IsPWO :=
  Set.isPWO_of_wellQuasiOrderedLE s

/-- **`q0:lem:dickson`, antichain form.**  `ℕ^k` contains no infinite antichain
for the componentwise order. -/
theorem dickson_antichain_finite (k : ℕ) {t : Set (Fin k → ℕ)}
    (h : IsAntichain (· ≤ ·) t) : t.Finite :=
  h.finite_of_partiallyWellOrderedOn (dickson_isPWO k t)

/-- The same for a general finite index type. -/
theorem dickson_isPWO_pi {ι : Type*} [Finite ι] (s : Set (ι → ℕ)) : s.IsPWO :=
  Set.isPWO_of_wellQuasiOrderedLE s

/-! ### Neumann's lemma -/

section Multiplicative

variable {α : Type*} [CommMonoid α] [PartialOrder α] [IsOrderedCancelMonoid α]

/-- **`q0:lem:neumann`, first half.**  The product of two well-based sets is
well-based. -/
theorem neumann_isPWO {A B : Set α} (hA : A.IsPWO) (hB : B.IsPWO) : (A * B).IsPWO :=
  hA.mul hB

/-- **`q0:lem:neumann`, second half.**  Every element of `A * B` has only
finitely many factorizations with one factor in each set.  This is what makes
the convolution defining a Hahn-series product a finite sum. -/
theorem neumann_finite_factorizations {A B : Set α} (hA : A.IsPWO) (hB : B.IsPWO) (c : α) :
    (Set.mulAntidiagonal A B c).Finite :=
  Set.MulAntidiagonal.finite_of_isPWO hA hB c

end Multiplicative

end Fabius
