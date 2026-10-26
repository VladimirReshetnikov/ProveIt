import Mathlib.Algebra.BigOperators.Fin
import Diophantine.Common.RefinedRelationCombiningPolynomial
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# A closed formula for the two-radicand relation combiner

Jones's nine-variable construction uses exactly two radicands. Expanding
its four signed factors gives the literal formula below, so this case
needs no polynomial selected from an existence theorem or exponent-halving
algorithm. Injective exponent dilation proves the identity in the formal
polynomial ring before evaluation, without choosing square roots.
-/

namespace RefinedPairAlgebraic

open Diophantine
open scoped BigOperators

/-- Literal ordinary-polynomial formula for two radicands. -/
def value {R : Type*} [Add R] [Sub R] [Mul R] [Pow R ℕ]
    [OfNat R 1] [OfNat R 2] [OfNat R 4] (A0 A1 V0 V1 n B C D : R) : R :=
  let K := B * (2 * D - 1)
  let T := B * n + C - K * (C + V0 * V1)
  (T ^ 2 + K ^ 2 * A0 - K ^ 2 * V0 ^ 2 * A1) ^ 2 - 4 * T ^ 2 * K ^ 2 * A0

variable {R : Type*} [CommRing R]

private def pairSigns : (Fin 2 → Bool) ≃ Bool × Bool where
  toFun f := (f 0, f 1)
  invFun p := ![p.1, p.2]
  left_inv f := by funext i; fin_cases i <;> rfl
  right_inv p := by cases p; rfl

private theorem prod_signs {S : Type*} [CommMonoid S] (f : (Fin 2 → Bool) → S) :
    (∏ ε : Fin 2 → Bool, f ε) =
      (f ![true, true] * f ![true, false]) *
        (f ![false, true] * f ![false, false]) := by
  calc
    _ = ∏ p : Bool × Bool, f ![p.1, p.2] := by
      apply Fintype.prod_equiv pairSigns
      intro ε
      congr 1
      funext i
      fin_cases i <;> rfl
    _ = _ := by rw [Fintype.prod_prod_type]; simp only [Fintype.prod_bool]

/-- The signed product is exactly the closed expression in the squared roots. -/
theorem radicalProduct_eq (V r : Fin 2 → R) (n B C D : R) :
    RefinedRelationCombiningPolynomial.radicalProduct 2 V r n B C D =
      value (r 0 ^ 2) (r 1 ^ 2) (V 0) (V 1) n B C D := by
  rw [RefinedRelationCombiningPolynomial.radicalProduct, prod_signs]
  simp [RefinedRelationCombiningPolynomial.weightPrefix, Finset.prod_filter,
    Fin.prod_univ_two, Fin.sum_univ_two, RelationCombiningPolynomial.signed, value]
  ring

open MvPolynomial
open RefinedRelationCombiningPolynomial (Coeff RootPoly)

/-- An identity of polynomials, established by injective exponent dilation. -/
theorem core_eq : RefinedRelationCombiningPolynomial.core 2 =
    value (X 0 : RootPoly 2) (X 1)
      (C (X (Sum.inl 0))) (C (X (Sum.inl 1)))
      (C (X (Sum.inr 0))) (C (X (Sum.inr 1)))
      (C (X (Sum.inr 2))) (C (X (Sum.inr 3))) := by
  apply expand_injective (by decide : 0 < (2 : ℕ))
  rw [RefinedRelationCombiningPolynomial.expand_two_core]
  have h := RefinedRelationCombiningPolynomial.eval₂_rawProduct 2
    (C : Coeff 2 →+* RootPoly 2) (fun i => X i)
  rw [eval₂_eta, radicalProduct_eq] at h
  simpa only [value, map_sub, map_mul, map_add, map_pow, map_ofNat, map_one,
    expand_C, expand_X] using h

/-- No algebraically closed field or chosen square roots are used. -/
theorem value_eq (A V : Fin 2 → ℤ) (n B C D : ℤ) :
    RefinedRelationCombiningPolynomial.value 2 A V n B C D =
      value (A 0) (A 1) (V 0) (V 1) n B C D := by
  unfold RefinedRelationCombiningPolynomial.value
  rw [core_eq]
  simp [value, RefinedRelationCombiningPolynomial.coeffEval]

#print axioms core_eq
#print axioms value_eq
end RefinedPairAlgebraic
