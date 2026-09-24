import Surreal.Algebra.NaturalArithmeticInterpretation
import Surreal.HahnSeries.DiophantineConstants
import Surreal.HahnSeries.Characteristic

/-!
# Standard arithmetic in integer-constant intermediate Hahn rings

The intermediate-ring semantic clauses of `odg:def:cor:arithmetic`.
Natural arithmetic is interpreted uniformly in every intermediate ring
whose intersection with the ordered coefficient field is exactly Z.
No closure under taking constant terms inside that intermediate ring is assumed.
-/

namespace Surreal.HahnSeries
open FirstOrder FirstOrder.Language
noncomputable section

variable {Γ K : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
    [Field K] [LinearOrder K] [IsStrictOrderedRing K]

local instance intermediateArithmeticStructure (A : Subring (nonpositiveSupportSubring Γ K)) :
    FirstOrder.Ring.CompatibleRing A := FirstOrder.Ring.compatibleRingOfRing A

/-- Xi recognizes exactly the native integer casts of every such intermediate ring. -/
theorem integer_intermediate_xi_cast_iff (A : Subring (nonpositiveSupportSubring Γ K))
    (hA : ∀ a, nonpositiveConstants a ∈ A ↔ a ∈ (Int.castRingHom K).range) (x : A) :
    DiophantineConstants.Xi x ↔ ∃ a : ℤ, x = (a : A) := by
  rw [integer_intermediate_xi_iff A hA]
  apply exists_congr
  intro a
  rw [map_intCast]
  constructor
  · intro h
    apply Subtype.ext
    exact h
  · intro h
    exact congrArg Subtype.val h

/-- Naturalness is detected by mapping square witnesses to the ordered coefficient field. -/
theorem integer_intermediate_realize_naturalGuard (A : Subring (nonpositiveSupportSubring Γ K))
    (hA : ∀ a, nonpositiveConstants a ∈ A ↔ a ∈ (Int.castRingHom K).range) (x : Fin 1 → A) :
    ArithmeticGuards.naturalGuard.Realize x ↔ ∃ a : ℕ, (a : A) = x 0 :=
  StandardArithmetic.realize_naturalGuard_iff_of_ordered_hom
    (nonpositiveConstantCoeff.comp A.subtype) (integer_intermediate_xi_cast_iff A hA) x

/-- The standard integer domain is natively parameter-free definable in every intermediate ring. -/
theorem integer_intermediate_integerConstants_definable (A : Subring (nonpositiveSupportSubring Γ K))
    (hA : ∀ a, nonpositiveConstants a ∈ A ↔ a ∈ (Int.castRingHom K).range) :
    (∅ : Set A).Definable₁ Language.ring (Set.range (Int.cast : ℤ → A)) :=
  ArithmeticGuards.integerConstants_definable (integer_intermediate_xi_cast_iff A hA)

/-- The standard natural domain is also natively parameter-free definable. -/
theorem integer_intermediate_naturalConstants_definable (A : Subring (nonpositiveSupportSubring Γ K))
    (hA : ∀ a, nonpositiveConstants a ∈ A ↔ a ∈ (Int.castRingHom K).range) :
    (∅ : Set A).Definable₁ Language.ring (Set.range (Nat.cast : ℕ → A)) := by
  apply Set.empty_definable_iff.mpr
  refine ⟨ArithmeticGuards.naturalGuard, ?_⟩
  ext x
  exact (integer_intermediate_realize_naturalGuard A hA x).symm

/-- One translation works for arbitrary formulas and standard assignments in every intermediate ring. -/
theorem integer_intermediate_realize_naturalTranslation (A : Subring (nonpositiveSupportSubring Γ K))
    (hA : ∀ a, nonpositiveConstants a ∈ A ↔ a ∈ (Int.castRingHom K).range)
    {α : Type*} {n : ℕ} (φ : StandardArithmetic.language.BoundedFormula α n)
    (v : α → ℕ) (xs : Fin n → ℕ) :
    (StandardArithmetic.naturalTranslation φ).Realize
      (fun a => (v a : A)) (fun j => (xs j : A)) ↔ φ.Realize v xs :=
  StandardArithmetic.realize_naturalTranslation_of_guard
    (integer_intermediate_realize_naturalGuard A hA) φ v xs

/-- Natural arithmetic truth has a uniform semantic reduction to each intermediate ring theory. -/
theorem integer_intermediate_naturalSentence_iff (A : Subring (nonpositiveSupportSubring Γ K))
    (hA : ∀ a, nonpositiveConstants a ∈ A ↔ a ∈ (Int.castRingHom K).range)
    (φ : StandardArithmetic.language.Sentence) :
    (A ⊨ StandardArithmetic.naturalTranslation φ) ↔ (ℕ ⊨ φ) := by
  have h := integer_intermediate_realize_naturalTranslation A hA φ default default
  unfold Sentence.Realize Formula.Realize
  convert h using 2

end
end Surreal.HahnSeries
