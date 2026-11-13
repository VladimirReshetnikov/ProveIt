module
public import Foundation.FirstOrder.Incompleteness.Consistency
public import M6PA.Theory
@[expose] public section
namespace M6.PA
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open scoped FFL.FirstOrder.Arithmetic
/-- Consistency for Foundation's standard provability predicate. -/
noncomputable def consistencySentence : ArithmeticSentence :=
  theory.standardProvability.con
theorem consistency_unprovable (h : Consistent) : theory ⊬ consistencySentence := by
  let : FFL.Entailment.Consistent theory := h
  exact ProvabilityAbstraction.con_unprovable (𝔅 := theory.standardProvability)
theorem unprovable_of_internal_consistency_implication
    (sentence : ArithmeticSentence) (hcons : Consistent)
    (hinternal : theory ⊢ sentence 🡒 consistencySentence) : theory ⊬ sentence := by
  intro hs
  exact consistency_unprovable hcons (hinternal ⨀ hs)
#print axioms consistency_unprovable
end M6.PA
