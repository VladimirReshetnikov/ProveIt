import ZFCinPA.SchemaClosure

set_option autoImplicit false

/-! Recognition of finite standard theories in arithmetic models. -/

namespace LeanProofs.ZFCinPA.FiniteTheoryRecognizer

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder.Arithmetic

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable {L : Language} [L.Encodable] [L.LORDefinable]

lemma singleton_class_iff (sentence : Sentence L) (p : V) :
    (V ⊧/![p] (Theory.Δ₁.singleton sentence).ch.val) ↔ p = (⌜sentence⌝ : V) := by
  change (V ⊧/![p] “x. x = ↑(Encodable.encode sentence)”) ↔ _
  simp [FirstOrder.Sentence.quote_eq_encode,numeral_eq_natCast]

/-- The finite recognizer cannot acquire new nonstandard axiom codes. -/
lemma ofList_class_iff (sentences : List (Sentence L)) (p : V) :
    (V ⊧/![p] (Theory.Δ₁.ofList sentences).ch.val) ↔
      ∃ sentence ∈ sentences, p = (⌜sentence⌝ : V) := by
  induction sentences with
  | nil =>
    change False ↔ _
    simp
  | cons sentence sentences ih =>
    have ih' : (V ⊧/![p] (Theory.Δ₁.ofList sentences).ch.val) ↔
        ∃ sentence ∈ sentences, p = (⌜sentence⌝ : V) := ih
    change (V ⊧/![p] ((Theory.Δ₁.singleton sentence).ch ⋎
      (Theory.Δ₁.ofList sentences).ch).val) ↔ _
    rw [HierarchySymbol.Semiformula.val_or]
    simp only [LogicalConnective.HomClass.map_or,LogicalConnective.Prop.or_eq]
    rw [singleton_class_iff sentence p,ih']
    simp


omit [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] in
lemma union_class_iff (T U : Theory L) [T.Δ₁] [U.Δ₁] (p : V) :
    p ∈ (T ∪ U).Δ₁Class ↔ p ∈ T.Δ₁Class ∨ p ∈ U.Δ₁Class := by
  change (V ⊧/![p] (T.Δ₁ch ⋎ U.Δ₁ch).val) ↔
    (V ⊧/![p] T.Δ₁ch.val) ∨ (V ⊧/![p] U.Δ₁ch.val)
  rw [HierarchySymbol.Semiformula.val_or]
  simp only [LogicalConnective.HomClass.map_or, LogicalConnective.Prop.or_eq]

end LeanProofs.ZFCinPA.FiniteTheoryRecognizer
