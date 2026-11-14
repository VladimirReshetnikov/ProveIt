import Foundation.FirstOrder.Incompleteness.InductionSchemeDelta1
set_option autoImplicit false
namespace PA194FiniteAxioms
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder.Arithmetic LO.FirstOrder
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem ofList_iff (l : List ArithmeticSentence) (p : V) :
    (V ⊧/![p] (Theory.Δ₁.ofList l).ch.val) ↔
      ∃ σ ∈ l, p = (Encodable.encode σ : V) := by
  induction l with
  | nil =>
    change (V ⊧/![p] (⊥ : ArithmeticSemisentence 1)) ↔ _
    simp
  | cons σ l ih =>
    change (V ⊧/![p] ((Theory.Δ₁.singleton σ).ch ⋎ (Theory.Δ₁.ofList l).ch).val) ↔ _
    simp only [HierarchySymbol.Semiformula.val_or, LogicalConnective.HomClass.map_or]
    rw [ih]
    change ((V ⊧/![p] “x. x = ↑(Encodable.encode σ)”) ∨ _) ↔ _
    simp [numeral_eq_natCast]

theorem peanoMinus_iff_sentence (p : V) :
    p ∈ PeanoMinus.Δ₁Class ↔
      ∃ σ ∈ PeanoMinus, p = (Encodable.encode σ : V) := by
  change (V ⊧/![p] (Theory.Δ₁.ofList PeanoMinus.finite.toFinset.toList).ch.val) ↔ _
  rw [ofList_iff]
  simp

theorem finite_branch {P : V → Prop}
    (h : ∀ σ ∈ PeanoMinus, P (Encodable.encode σ : V)) {p : V}
    (hp : p ∈ PeanoMinus.Δ₁Class) : P p := by
  obtain ⟨σ, hσ, rfl⟩ := (peanoMinus_iff_sentence p).mp hp
  exact h σ hσ

#print axioms ofList_iff
#print axioms peanoMinus_iff_sentence
#print axioms finite_branch
end PA194FiniteAxioms
