import Foundation.FirstOrder.Intuitionistic.Deduction

/-! Quantifier rules used by both Foundation arithmetic presentations. -/

set_option autoImplicit false

namespace IPRABridge

open LO LO.FirstOrder LO.Entailment Rewriting
open scoped LO.FirstOrder

/-- Existential monotonicity from an implication in the fresh-variable scope. -/
def existsImpOfFreeImp {L : Language} {Λ : Hilbertᵢ L} {p q : Semipropositionᵢ L 1}
    (h : Λ ⊢! free p 🡒 free q) : Λ ⊢! (∃⁰ p) 🡒 ∃⁰ q := by
  have introQ : Λ ⊢! free q 🡒 shift (∃⁰ q) := by
    change HilbertProofᵢ Λ (free q 🡒 shift (∃⁰ q))
    simpa using HilbertProofᵢ.ex₁ (Λ := Λ) (&0) (shift q)
  have step : Λ ⊢! free (p 🡒 (∃⁰ q)/[]) := by
    simpa only [LogicalConnective.HomClass.map_imply, LawfulSyntacticRewriting.free_subst_nil] using
      Entailment.C_trans h introQ
  exact HilbertProofᵢ.ex₂ p (∃⁰ q) ⨀ HilbertProofᵢ.gen step

end IPRABridge
