import Surreal.Algebra.NaturalArithmeticInterpretation
import Surreal.Foundations.OmnificArithmeticInterpretation

/-!
# Natural arithmetic sentences interpreted in the actual omnific ring

The natural-number sentence-translation clause of `odg:def:cor:arithmetic`,
using the literal `(0, 1, +, *)` signature and the native natural guard.
-/

universe u v
namespace Surreal.Foundations.SignSequence
open FirstOrder FirstOrder.Language

noncomputable local instance naturalArithmeticOmnificStructure :
    FirstOrder.Ring.CompatibleRing OmnificInteger.{u} :=
  FirstOrder.Ring.compatibleRingOfRing OmnificInteger

/-- Every natural arithmetic formula is interpreted correctly on standard natural assignments. -/
theorem omnific_realize_naturalTranslation {α : Type v} {n : ℕ}
    (φ : StandardArithmetic.language.BoundedFormula α n) (v : α → ℕ) (xs : Fin n → ℕ) :
    (StandardArithmetic.naturalTranslation φ).Realize
      (fun a => omnificIntCast.{u} (v a)) (fun j => omnificIntCast (xs j)) ↔ φ.Realize v xs := by
  have hNat (x : Fin 1 → OmnificInteger.{u}) : ArithmeticGuards.naturalGuard.Realize x ↔
      ∃ a : ℕ, (a : OmnificInteger.{u}) = x 0 := by
    simpa only [map_natCast] using omnific_realize_naturalGuard x
  simpa only [map_natCast] using StandardArithmetic.realize_naturalTranslation_of_guard hNat φ v xs

/-- Every natural arithmetic sentence has a parameter-free, truth-equivalent omnific ring sentence. -/
theorem omnific_naturalSentence_iff (φ : StandardArithmetic.language.Sentence) :
    (OmnificInteger.{u} ⊨ StandardArithmetic.naturalTranslation φ) ↔ (ℕ ⊨ φ) := by
  have h := omnific_realize_naturalTranslation.{u} φ default default
  unfold Sentence.Realize Formula.Realize
  convert h using 2

end Surreal.Foundations.SignSequence
