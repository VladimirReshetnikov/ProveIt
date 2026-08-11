import PolynomialFormulas.Fin5TransitiveC5
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.Tactic

/-!
# The `F₂₀` class sum in Lazard's Section 6

This file verifies the finite permutation calculation behind the Molien
numerator printed in Section 6.  In the natural permutation representation on
five variables, the standard affine Frobenius group has cycle classes

* one element of type `1^5`;
* four elements of type `5`;
* five elements of type `1 2^2`;
* ten elements of type `1 4`.

Consequently its Molien class sum simplifies to

`(1 + t^4 + t^5 + t^6 + t^7 + t^8) /
  ((1-t)(1-t^2)(1-t^3)(1-t^4)(1-t^5))`.

The last theorem is an identity in the rational-function field `ℚ(t)`.  It is
deliberately not called a Hilbert-series theorem: turning the class sum into
the Hilbert series of the concrete invariant ring still needs the formal
Molien theorem for this action.  Likewise, the numerator by itself does not
identify Lazard's particular elements `1, i4, ..., i8` as a module basis.
-/

namespace LeanProofs.PolynomialFormulas.LazardQuinticF20Molien

open Equiv
open LeanProofs.PolynomialFormulas.Fin5TransitiveC5

abbrev S5 := Equiv.Perm (Fin 5)

/-- Elements of the concrete `F₂₀` having a prescribed nontrivial-cycle
multiset.  Fixed points do not occur in `Equiv.Perm.cycleType`; thus the four
types below are respectively `1^5`, `5`, `1 2^2`, and `1 4`. -/
def f20ElementsOfCycleType (m : Multiset ℕ) : Finset S5 :=
  f20Elements.filter fun g ↦ g.cycleType = m

set_option maxRecDepth 100000 in
/-- The exact cycle-class calculation for the standard affine copy of
`F₂₀ ≤ S₅`.  This uses the same kernel-reduced enumeration as
`card_f20Elements`; no class-size assumption is supplied to the theorem. -/
theorem f20_cycle_class_counts :
    (f20ElementsOfCycleType 0).card = 1 ∧
    (f20ElementsOfCycleType {5}).card = 4 ∧
    (f20ElementsOfCycleType {2, 2}).card = 5 ∧
    (f20ElementsOfCycleType {4}).card = 10 := by
  decide

set_option maxRecDepth 100000 in
/-- The four displayed classes exhaust `F₂₀`. -/
theorem f20_cycle_types_exhaustive :
    ∀ g ∈ f20Elements,
      g.cycleType = 0 ∨ g.cycleType = {5} ∨
        g.cycleType = {2, 2} ∨ g.cycleType = {4} := by
  decide

/-- The class sum dictated by the four cycle types of the five-dimensional
permutation representation. -/
def f20MolienClassSumAt {F : Type*} [Field F] (t : F) : F :=
  (1 / 20) *
    (1 / (1 - t) ^ 5 +
      4 / (1 - t ^ 5) +
      5 / ((1 - t) * (1 - t ^ 2) ^ 2) +
      10 / ((1 - t) * (1 - t ^ 4)))

/-- Lazard's Section 6 numerator. -/
def f20MolienNumeratorAt {R : Type*} [Semiring R] (t : R) : R :=
  1 + t ^ 4 + t ^ 5 + t ^ 6 + t ^ 7 + t ^ 8

/-- The Hilbert denominator supplied by the elementary symmetric parameters
of degrees `1,2,3,4,5`. -/
def f20SymmetricDenominatorAt {R : Type*} [CommRing R] (t : R) : R :=
  (1 - t) * (1 - t ^ 2) * (1 - t ^ 3) * (1 - t ^ 4) * (1 - t ^ 5)

/-- Cleared-field version of the Molien simplification.  Keeping all pole
hypotheses explicit makes clear exactly what is algebra and what belongs to
the later Hilbert-series interpretation. -/
theorem f20_molien_class_sum_algebraic_identity
    {F : Type*} [Field F] (t : F)
    (h1 : 1 - t ≠ 0) (h2 : 1 - t ^ 2 ≠ 0)
    (h3 : 1 - t ^ 3 ≠ 0) (h4 : 1 - t ^ 4 ≠ 0)
    (h5 : 1 - t ^ 5 ≠ 0) (h20 : (20 : F) ≠ 0) :
    f20MolienClassSumAt t =
      f20MolienNumeratorAt t / f20SymmetricDenominatorAt t := by
  unfold f20MolienClassSumAt f20MolienNumeratorAt
    f20SymmetricDenominatorAt
  field_simp [h1, h2, h3, h4, h5, h20]
  <;> ring

lemma polynomial_one_sub_X_pow_ne_zero (n : ℕ) (hn : 0 < n) :
    (1 - Polynomial.X ^ n : Polynomial ℚ) ≠ 0 := by
  intro h
  have hc := congrArg (fun p : Polynomial ℚ ↦ p.coeff n) h
  rw [Polynomial.coeff_sub, Polynomial.coeff_one,
    Polynomial.coeff_X_pow_self, Polynomial.coeff_zero] at hc
  simp [hn.ne'] at hc

lemma ratFunc_one_sub_X_pow_ne_zero (n : ℕ) (hn : 0 < n) :
    (1 - (RatFunc.X : RatFunc ℚ) ^ n) ≠ 0 := by
  have hp := RatFunc.algebraMap_ne_zero
    (polynomial_one_sub_X_pow_ne_zero n hn)
  simpa only [map_sub, map_one, map_pow, RatFunc.algebraMap_X] using hp

/-- The exact formal rational-function identity underlying the printed
numerator `1+t^4+t^5+t^6+t^7+t^8`. -/
theorem f20_molien_class_sum_identity :
    f20MolienClassSumAt (RatFunc.X : RatFunc ℚ) =
      f20MolienNumeratorAt (RatFunc.X : RatFunc ℚ) /
        f20SymmetricDenominatorAt (RatFunc.X : RatFunc ℚ) := by
  apply f20_molien_class_sum_algebraic_identity
  · simpa using ratFunc_one_sub_X_pow_ne_zero 1 (by norm_num)
  · exact ratFunc_one_sub_X_pow_ne_zero 2 (by norm_num)
  · exact ratFunc_one_sub_X_pow_ne_zero 3 (by norm_num)
  · exact ratFunc_one_sub_X_pow_ne_zero 4 (by norm_num)
  · exact ratFunc_one_sub_X_pow_ne_zero 5 (by norm_num)
  · norm_num

/-- A single package of the two exact calculations used in the Section 6
Molien line.  It intentionally stops short of asserting a Hilbert series. -/
theorem f20_cycle_count_and_molien_identity :
    ((f20ElementsOfCycleType 0).card,
      (f20ElementsOfCycleType {5}).card,
      (f20ElementsOfCycleType {2, 2}).card,
      (f20ElementsOfCycleType {4}).card) = (1, 4, 5, 10) ∧
    f20MolienClassSumAt (RatFunc.X : RatFunc ℚ) =
      f20MolienNumeratorAt (RatFunc.X : RatFunc ℚ) /
        f20SymmetricDenominatorAt (RatFunc.X : RatFunc ℚ) := by
  constructor
  · rcases f20_cycle_class_counts with ⟨h1, h5, h22, h4⟩
    simp only [h1, h5, h22, h4]
  · exact f20_molien_class_sum_identity

end LeanProofs.PolynomialFormulas.LazardQuinticF20Molien
