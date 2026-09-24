import Surreal.Algebra.AlgebraicTypeComputability
import Surreal.Algebra.NumberFieldOmittedType

/-!
# Recursive saturation and the explicit algebraic omitted type

The recursive-saturation consequence in `odg:def:thm:saturation`. We use the
standard unary-type formulation over arbitrary finite parameter tuples.
Parameters occupy the initial bound-variable context of native formulas;
quantifiers extend that context, while the single free variable is realized
by the sought element. Computability uses the explicit native formula coding.
-/

namespace Surreal.RecursiveSaturation
open FirstOrder FirstOrder.Language

/-- Realization of a unary partial type with a fixed finite tuple of parameters. -/
def RealizesAt {R : Type*} [Language.ring.Structure R] {n : ℕ} (a : Fin n → R)
    (T : Set (Language.ring.BoundedFormula (Fin 1) n)) (x : R) : Prop :=
  ∀ φ ∈ T, φ.Realize (fun _ => x) a

/-- Finite satisfiability with all parameters fixed throughout. -/
def FinitelySatisfiableAt {R : Type*} [Language.ring.Structure R] {n : ℕ} (a : Fin n → R)
    (T : Set (Language.ring.BoundedFormula (Fin 1) n)) : Prop :=
  ∀ s : Finset (Language.ring.BoundedFormula (Fin 1) n), (↑s : Set _) ⊆ T →
    ∃ x : R, ∀ φ ∈ s, φ.Realize (fun _ => x) a

/-- Every computable finitely satisfiable unary type over any finite parameter tuple is realized. -/
def RecursivelySaturated (R : Type*) [Language.ring.Structure R] : Prop :=
  ∀ (n : ℕ) (a : Fin n → R) (T : Set (Language.ring.BoundedFormula (Fin 1) n)),
    letI : Primcodable (Language.ring.BoundedFormula (Fin 1) n) := RingFormulaCode.fixedFormulaPrimcodable n
    ComputablePred (fun φ => φ ∈ T) → FinitelySatisfiableAt a T → ∃ x : R, RealizesAt a T x

variable {R : Type*} [Language.ring.Structure R]

/-- At context zero the parameterized definition is exactly the earlier native type realization. -/
theorem realizesAt_zero_iff (a : Fin 0 → R) (T : Set (Language.ring.Formula (Fin 1))) (x : R) :
    RealizesAt a T x ↔ AlgebraicOmittedType.Realizes T x := by
  unfold RealizesAt AlgebraicOmittedType.Realizes Formula.Realize
  rw [show a = default from Subsingleton.elim _ _]

/-- Finite satisfiability at context zero is exactly the earlier parameter-free property. -/
theorem finitelySatisfiableAt_zero_iff (a : Fin 0 → R) (T : Set (Language.ring.Formula (Fin 1))) :
    FinitelySatisfiableAt a T ↔ AlgebraicOmittedType.FinitelySatisfiable R T := by
  unfold FinitelySatisfiableAt AlgebraicOmittedType.FinitelySatisfiable Formula.Realize
  rw [show a = default from Subsingleton.elim _ _]

/-- The explicit computable algebraic type witnesses failure of recursive saturation whenever omitted. -/
theorem not_recursivelySaturated_of_algebraicType (δ : Language.ring.Formula (Fin 1))
    (hfin : AlgebraicOmittedType.FinitelySatisfiable R (AlgebraicOmittedType.formulas δ))
    (homit : ¬ ∃ x : R, AlgebraicOmittedType.Realizes (AlgebraicOmittedType.formulas δ) x) :
    ¬ RecursivelySaturated R := by
  intro hsat
  obtain ⟨x, hx⟩ := hsat 0 Fin.elim0 (AlgebraicOmittedType.formulas δ)
    (AlgebraicTypeCode.membership_computable δ)
    ((finitelySatisfiableAt_zero_iff _ _).mpr hfin)
  exact homit ⟨x, (realizesAt_zero_iff _ _ _).mp hx⟩

/-- A definable coefficient image from any number field prevents recursive saturation.
The construction of the source's tailored number-field guard remains a separate obligation. -/
theorem numberField_not_recursivelySaturated
    {A K O : Type*} [CommRing A] [CharZero A] [FirstOrder.Ring.CompatibleRing A]
    [Field K] [NumberField K] [CommRing O]
    (j : O →+* K) (hj : Function.Injective j) (i : O →+* A)
    (δ : Language.ring.Formula (Fin 1))
    (hδ : ∀ x : A, δ.Realize (fun _ => x) ↔ x ∈ i.range) :
    ¬ RecursivelySaturated A := by
  obtain ⟨hfin, homit⟩ :=
    AlgebraicOmittedType.numberField_finitelySatisfiable_and_omitted j hj i δ hδ
  exact not_recursivelySaturated_of_algebraicType δ hfin homit

end Surreal.RecursiveSaturation
