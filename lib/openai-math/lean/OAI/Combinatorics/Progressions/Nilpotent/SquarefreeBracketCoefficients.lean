/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Combinatorics.Progressions.Polynomial.SquarefreePolynomialQuotient

namespace OAI

section

namespace Erdos3

open VectorPolynomial

noncomputable def SquarefreeIndex.disjointAdd {ι : Type*} (a b : SquarefreeIndex ι)
    (h : Disjoint a.val.support b.val.support) : SquarefreeIndex ι :=
  ⟨a.val + b.val, (squarefreeExponent_add_iff a.val b.val a.property b.property).mpr h⟩

variable {ι L : Type*} [LieRing L] [LieAlgebra ℚ L]

theorem squarefreeMonomial_lie_disjoint (a b : SquarefreeIndex ι)
    (h : Disjoint a.val.support b.val.support) (v w : L) :
    ⁅squarefreeMonomial a v, squarefreeMonomial b w⁆ =
      squarefreeMonomial (a.disjointAdd b h) ⁅v, w⁆ := by
  simp only [squarefreeMonomial_apply, ← LieHom.map_lie, lie_monomial]
  rfl

theorem squarefreeMonomial_lie_overlap (a b : SquarefreeIndex ι)
    (h : ¬Disjoint a.val.support b.val.support) (v w : L) :
    ⁅squarefreeMonomial a v, squarefreeMonomial b w⁆ = 0 := by
  simp only [squarefreeMonomial_apply, ← LieHom.map_lie, lie_monomial]
  exact squarefreeMk_monomial_zero _
    (fun hs => h ((squarefreeExponent_add_iff a.val b.val a.property b.property).mp hs)) _

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {ι L : Type*} [Fintype ι] [DecidableEq ι] [LieRing L] [LieAlgebra ℚ L]

theorem squarefreeMonomial_lie_coefficient (a b c : SquarefreeIndex ι) (x y : L) :
    squarefreePolynomialEquiv (⁅squarefreeMonomial a x, squarefreeMonomial b y⁆) c =
      if a.val + b.val = c.val then ⁅x, y⁆ else 0 := by
  by_cases hs : a.val + b.val = c.val
  · have hd : Disjoint a.val.support b.val.support :=
      (squarefreeExponent_add_iff a.val b.val a.property b.property).mp (hs.symm ▸ c.property)
    rw [ite_eq_left hs, squarefreeMonomial_lie_disjoint a b hd]
    have he : a.disjointAdd b hd = c := Subtype.ext hs
    rw [he, squarefreePolynomialEquiv_monomial_self]
  · rw [ite_eq_right hs]
    by_cases hd : Disjoint a.val.support b.val.support
    · rw [squarefreeMonomial_lie_disjoint a b hd]
      exact squarefreePolynomialEquiv_monomial_ne _ c
        (fun h => hs (congrArg Subtype.val h)) _
    · rw [squarefreeMonomial_lie_overlap a b hd, map_zero, Pi.zero_apply]

theorem squarefree_lie_coefficient (x y : SquarefreePolynomial ι L) (c : SquarefreeIndex ι) :
    squarefreePolynomialEquiv ⁅x, y⁆ c =
      ∑ a : SquarefreeIndex ι, ∑ b : SquarefreeIndex ι,
        if a.val + b.val = c.val then
          ⁅squarefreePolynomialEquiv x a, squarefreePolynomialEquiv y b⁆ else 0 := by
  conv_lhs => rw [← sum_squarefreeMonomial x, ← sum_squarefreeMonomial y, sum_lie_sum]
  simp only [map_sum, Finset.sum_apply, squarefreeMonomial_lie_coefficient]

end Erdos3

end

end OAI
