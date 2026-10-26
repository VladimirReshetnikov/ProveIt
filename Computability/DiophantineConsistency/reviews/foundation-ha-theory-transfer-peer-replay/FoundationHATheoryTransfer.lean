import DiophantineConsistency.FoundationTheoryGG
import DiophantineConsistency.FoundationPAHFLogic
import DiophantineConsistency.FoundationHAArithmetic

/-! Compose the existing GG and logical proof maps with actual HA proofs
of the finitely used source axioms. No arithmetic-image premise is silently
discharged; the concrete corollary covers the eight proved semiring axioms. -/

set_option autoImplicit false
set_option Elab.async false
namespace DiophantineConsistency
open LO LO.FirstOrder LO.Entailment
open scoped LO.FirstOrder
open SetTheory.PA FoundationPAHFSyntax

namespace HA.Relative

/-- Discharge each finite assumption using its genuine theorem proof.
The supporting axiom lists are combined by the existing deduction rules. -/
theorem discharge {B : Formula → Prop} {G : List Formula} {a : Formula}
    (h : Relative B G a) (hG : ∀ b ∈ G, Relative B [] b) : Relative B [] a := by
  induction G generalizing a with
  | nil => exact h
  | cons b G ih =>
    have hi : Relative B [] (.imp b a) :=
      ih h.imp_intro (fun c hc => hG c (List.mem_cons_of_mem _ hc))
    exact hi.mp (hG b List.mem_cons_self)

end HA.Relative

namespace FoundationHATheoryTransfer

theorem intuitionistic_theory
    {T : Theoryᵢ ℒₒᵣ (𝗜𝗻𝘁¹ : Hilbertᵢ ℒₒᵣ)} {σ : Sentenceᵢ ℒₒᵣ}
    (h : T ⊢ σ) (hax : ∀ τ ∈ T, HA.Proves (sentence τ)) :
    HA.Proves (sentence σ) := by
  obtain ⟨p⟩ := h
  have hp := FoundationPAHFLogic.finite_proof p.prf
  apply HA.Relative.discharge (HA.relative_of_derives hp)
  intro a ha
  obtain ⟨ψ, hψ, rfl⟩ := List.mem_map.mp ha
  obtain ⟨τ, hτ, rfl⟩ := p.subset ψ hψ
  exact hax τ hτ

/-- The source proof and every source-axiom HA image are explicit. This is
a proof-composition theorem, not a claim that arbitrary theories embed in HA. -/
theorem classical_theory {T : Theory ℒₒᵣ} {σ : Sentence ℒₒᵣ}
    (h : T ⊢ σ) (hax : ∀ τ ∈ T, HA.Proves (sentence τᴺ)) :
    HA.Proves (sentence σᴺ) := by
  apply intuitionistic_theory (FoundationTheoryGG.theory_intuitionistic h)
  intro τ hτ
  obtain ⟨ψ, hψ, rfl⟩ := hτ
  exact hax ψ hψ

def semiringTheory : Theory ℒₒᵣ := {σ | σ ∈ FoundationHAArithmetic.semiringAxioms}

/-- For this concrete source theory all image proofs have already been
constructed; no image-provability hypothesis remains. -/
theorem semiring_provable {σ : Sentence ℒₒᵣ} (h : semiringTheory ⊢ σ) :
    HA.Proves (sentence σᴺ) :=
  classical_theory h (fun _ hτ => FoundationHAArithmetic.semiring_axiom hτ)

end FoundationHATheoryTransfer
end DiophantineConsistency
