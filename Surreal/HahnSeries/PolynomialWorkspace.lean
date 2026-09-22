import Surreal.HahnSeries.AlgebraicallyClosed
import Surreal.Algebra.Polynomial
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Polynomial factorization in the constructed complex Hahn workspace

These specialize the finite algebra of `polynomial:thm:fta`,
`polynomial:eq:factorization`, and `polynomial:prop:workspace` to complex Hahn
series, using the proved algebraic-closedness instance. Splitting is supplied
by that construction, including when passing to an arbitrary extension field.

An embedding into the actual surcomplex carrier and preservation of local
algebra lengths remain separate statements.
-/

namespace Surreal.HahnSeries

open Polynomial
open scoped _root_.HahnSeries

noncomputable section

variable {Γ : Type*} [AddCommGroup Γ] [LinearOrder Γ]
  [IsOrderedAddMonoid Γ] [DivisibleBy Γ ℕ]

/-- Every complex Hahn polynomial splits in its original divisible workspace. -/
theorem complex_polynomial_splits (P : Polynomial ℂ⟦Γ⟧) : P.Splits :=
  IsAlgClosed.splits P

/-- The exact multiset factorization in the constructed workspace. -/
theorem complex_polynomial_factorization (P : Polynomial ℂ⟦Γ⟧) :
    P = C P.leadingCoeff * (P.roots.map fun a => X - C a).prod :=
  FinitePolynomial.factorization P

/-- A nonconstant polynomial has a root inside that same workspace. -/
theorem complex_polynomial_exists_root (P : Polynomial ℂ⟦Γ⟧)
    (hP : 0 < P.natDegree) : ∃ a : ℂ⟦Γ⟧, P.IsRoot a :=
  FinitePolynomial.exists_root P hP

/-- The total root multiplicity equals the degree, including degree zero. -/
theorem complex_polynomial_roots_card (P : Polynomial ℂ⟦Γ⟧) :
    P.roots.card = P.natDegree :=
  FinitePolynomial.roots_card P

/-- Both the scalar and multiset of linear factors are uniquely determined. -/
theorem complex_polynomial_exists_unique_factorization
    (P : Polynomial ℂ⟦Γ⟧) (hP : P ≠ 0) :
    ∃! data : ℂ⟦Γ⟧ × Multiset ℂ⟦Γ⟧,
      data.1 ≠ 0 ∧ P = C data.1 * (data.2.map fun a => X - C a).prod :=
  FinitePolynomial.exists_unique_factorization P hP

/-- Workspace enlargement preserves the full root multiset with multiplicity. -/
theorem complex_polynomial_roots_map {L : Type*} [Field L]
    (P : Polynomial ℂ⟦Γ⟧) (i : ℂ⟦Γ⟧ →+* L) :
    (P.map i).roots = P.roots.map i :=
  FinitePolynomial.roots_map_of_isAlgClosed P i

/-- No new root locations appear in any field extension of the workspace. -/
theorem complex_polynomial_root_mem_range {L : Type*} [Field L]
    (P : Polynomial ℂ⟦Γ⟧) (hP : P ≠ 0) (i : ℂ⟦Γ⟧ →+* L)
    {z : L} (hz : (P.map i).IsRoot z) : ∃ a : ℂ⟦Γ⟧, i a = z :=
  FinitePolynomial.root_mem_range P (complex_polynomial_splits P) hP i hz

/-- The values of a character of a finite workspace algebra already lie in
the workspace, even when the character takes values in a larger field. -/
theorem complex_finite_algebra_character_descends {L B : Type*} [Field L]
    [Algebra ℂ⟦Γ⟧ L] [CommRing B] [Algebra ℂ⟦Γ⟧ B] [Module.Finite ℂ⟦Γ⟧ B]
    (φ : B →ₐ[ℂ⟦Γ⟧] L) (b : B) :
    ∃ a : ℂ⟦Γ⟧, algebraMap ℂ⟦Γ⟧ L a = φ b :=
  FinitePolynomial.finite_algebra_character_descends φ b

end

end Surreal.HahnSeries
