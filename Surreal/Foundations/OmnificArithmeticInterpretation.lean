import Surreal.Algebra.ArithmeticGuards
import Surreal.Algebra.FormulaRelativization
import Surreal.Foundations.OmnificNaturalNumbersDefinition
import Surreal.Foundations.OmnificEquationalTransfer

/-!
# Standard arithmetic interpreted in the actual omnific ring

The native parameter-free domains and integer quantifier-relativization
clauses of `odg:def:cor:arithmetic`. The separate computability and
non-axiomatizability consequences are not assumed here.
-/

universe u v
namespace Surreal.Foundations.SignSequence
open FirstOrder FirstOrder.Language

local instance arithmeticIntegerStructure : FirstOrder.Ring.CompatibleRing ℤ :=
  FirstOrder.Ring.compatibleRingOfRing ℤ

noncomputable local instance arithmeticOmnificStructure : FirstOrder.Ring.CompatibleRing OmnificInteger.{u} :=
  FirstOrder.Ring.compatibleRingOfRing OmnificInteger

/-- The explicit first-order guard defines exactly the actual ordinary integer image. -/
theorem omnific_realize_integerGuard (x : Fin 1 → OmnificInteger.{u}) :
    ArithmeticGuards.integerGuard.Realize x ↔ ∃ a : ℤ, omnificIntCast a = x 0 := by
  rw [ArithmeticGuards.realize_integerGuard, omnific_xi_iff]
  exact exists_congr fun _ => eq_comm

/-- The explicit natural guard defines exactly the actual ordinary natural image. -/
theorem omnific_realize_naturalGuard (x : Fin 1 → OmnificInteger.{u}) :
    ArithmeticGuards.naturalGuard.Realize x ↔ ∃ a : ℕ, omnificIntCast a = x 0 := by
  rw [ArithmeticGuards.realize_naturalGuard, ← omnific_natural_iff_xi_four_squares]
  exact exists_congr fun _ => eq_comm

/-- The ordinary integers are parameter-free definable in the actual pure omnific ring. -/
theorem omnific_integerConstants_definable :
    (∅ : Set OmnificInteger.{u}).Definable₁ Language.ring (Set.range omnificIntCast) := by
  apply Set.empty_definable_iff.mpr
  refine ⟨ArithmeticGuards.integerGuard, ?_⟩
  ext x
  exact (omnific_realize_integerGuard x).symm

/-- The ordinary natural numbers, including zero, are parameter-free definable in that ring. -/
theorem omnific_naturalConstants_definable :
    (∅ : Set OmnificInteger.{u}).Definable₁ Language.ring
      (Set.range (fun a : ℕ => omnificIntCast a)) := by
  apply Set.empty_definable_iff.mpr
  refine ⟨ArithmeticGuards.naturalGuard, ?_⟩
  ext x
  exact (omnific_realize_naturalGuard x).symm

/-- The existing integer inclusion as a native first-order embedding. -/
noncomputable def omnificIntegerLanguageEmbedding : ℤ ↪[Language.ring] OmnificInteger.{u} where
  toFun := omnificIntCast
  inj' := omnificConstantCoeff_leftInverse.injective
  map_fun' := (Surreal.ringLanguageHom omnificIntCast).map_fun
  map_rel' r := by cases r

/-- A single recursively defined syntactic translation, independent of the carrier universe. -/
def omnificIntegerTranslation {α : Type v} {n : ℕ}
    (φ : Language.ring.BoundedFormula α n) : Language.ring.BoundedFormula α n :=
  FormulaRelativization.relativize ArithmeticGuards.integerGuard φ

/-- The translation preserves truth for every formula and every standard tuple of free variables. -/
theorem omnific_realize_integerTranslation {α : Type v} {n : ℕ}
    (φ : Language.ring.BoundedFormula α n) (v : α → ℤ) (xs : Fin n → ℤ) :
    (omnificIntegerTranslation φ).Realize (omnificIntCast.{u} ∘ v) (omnificIntCast ∘ xs) ↔
      φ.Realize v xs :=
  FormulaRelativization.realize_relativize ArithmeticGuards.integerGuard
    omnificIntegerLanguageEmbedding omnific_realize_integerGuard φ v xs

/-- In particular, every integer ring sentence has a truth-equivalent pure omnific ring sentence. -/
theorem omnific_integerSentence_iff (φ : Language.ring.Sentence) :
    (OmnificInteger.{u} ⊨ omnificIntegerTranslation φ) ↔ (ℤ ⊨ φ) := by
  have h := omnific_realize_integerTranslation.{u} φ default default
  unfold Sentence.Realize Formula.Realize
  convert h using 2

end Surreal.Foundations.SignSequence
