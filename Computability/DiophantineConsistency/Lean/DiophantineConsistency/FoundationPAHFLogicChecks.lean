import DiophantineConsistency.FoundationPAHFLogic

set_option autoImplicit false
set_option Elab.async false
namespace DiophantineConsistency.FoundationPAHFLogicChecks
open LO LO.FirstOrder LO.Entailment
open scoped LO.FirstOrder
open DiophantineConsistency.FoundationPAHFSyntax
open DiophantineConsistency.FoundationPAHFLogic
open DiophantineConsistency.HA

/-- The concrete intuitionistic EFQ schema is discharged by HA's own bot rule. -/
theorem ex_falso (p : Propositionᵢ ℒₒᵣ) :
    Derives [] (formula (⊥ 🡒 p)) := by
  apply intuitionistic_proof
  exact HilbertProofᵢ.eaxm ⟨p, rfl⟩

theorem universal_distribution (p : Propositionᵢ ℒₒᵣ) (q : Semipropositionᵢ ℒₒᵣ 1) :
    Derives [] (formula (∀⁰ (p/[] 🡒 q) 🡒 p 🡒 ∀⁰ q)) :=
  intuitionistic_proof (HilbertProofᵢ.all₂ p q)

theorem existential_distribution (p : Semipropositionᵢ ℒₒᵣ 1) (q : Propositionᵢ ℒₒᵣ) :
    Derives [] (formula (∀⁰ (p 🡒 q/[]) 🡒 ∃⁰ p 🡒 q)) :=
  intuitionistic_proof (HilbertProofᵢ.ex₂ p q)

theorem generalization (p : Semipropositionᵢ ℒₒᵣ 1)
    (h : HilbertProofᵢ (𝗜𝗻𝘁¹ : Hilbertᵢ ℒₒᵣ) (Rewriting.free p)) :
    Derives [] (formula (∀⁰ p)) := intuitionistic_proof (HilbertProofᵢ.gen h)

theorem instantiation (p : Semipropositionᵢ ℒₒᵣ 1) (t : SyntacticTerm ℒₒᵣ) :
    Derives [] (formula (∀⁰ p 🡒 p/[t])) :=
  intuitionistic_proof (HilbertProofᵢ.all₁ p t)

theorem existential_witness (p : Semipropositionᵢ ℒₒᵣ 1) (t : SyntacticTerm ℒₒᵣ) :
    Derives [] (formula (p/[t] 🡒 ∃⁰ p)) :=
  intuitionistic_proof (HilbertProofᵢ.ex₁ t p)

/-- Actual finite-context source assumptions are still target assumptions. -/
theorem preserve_two (p q : Propositionᵢ ℒₒᵣ) :
    Derives [formula p, formula q] (formula p) := by
  exact finite_proof (FiniteContext.byAxm₀ : [p,q] ⊢[(𝗜𝗻𝘁¹ : Hilbertᵢ ℒₒᵣ)]! p)

/-- Neither duplicates nor order are discarded by the proof map. -/
theorem preserve_duplicate (p : Propositionᵢ ℒₒᵣ) :
    Derives [formula p, formula p] (formula p) := by
  exact finite_proof (FiniteContext.byAxm₀ : [p,p] ⊢[(𝗜𝗻𝘁¹ : Hilbertᵢ ℒₒᵣ)]! p)

theorem empty_context (p q : Propositionᵢ ℒₒᵣ) :
    Derives [] (formula (p 🡒 q 🡒 p)) :=
  intuitionistic_proof (HilbertProofᵢ.implyK p q)

/-- This is only a transfer of genuine intuitionistic proof existence, not
classical provability, semantic truth, or an arithmetic-axiom premise. -/
theorem existence_only {Γ : List (Propositionᵢ ℒₒᵣ)} {p : Propositionᵢ ℒₒᵣ}
    (h : Γ ⊢[(𝗜𝗻𝘁¹ : Hilbertᵢ ℒₒᵣ)] p) :
    Derives (Γ.map formula) (formula p) := finite_provable h

#print axioms ofHilbertProof
#print axioms intuitionistic_proof
#print axioms finite_proof
#print axioms finite_provable
#print axioms ex_falso
#print axioms universal_distribution
#print axioms existential_distribution
#print axioms generalization
#print axioms instantiation
#print axioms existential_witness
#print axioms preserve_two
#print axioms preserve_duplicate
#print axioms empty_context
#print axioms existence_only
end DiophantineConsistency.FoundationPAHFLogicChecks
