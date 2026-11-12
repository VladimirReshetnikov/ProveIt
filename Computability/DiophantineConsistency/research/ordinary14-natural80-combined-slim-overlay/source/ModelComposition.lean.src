import PositiveClient
import AuxGraphEquivalence

/-! Source-only composition of two separately reviewed but uncompiled model
clients. No Lean elaboration, provider route, endpoint or file binding is
claimed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.Model84To78CompositionDraft
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ModelDifferenceRing
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Proposed all-positive model comparison under the exact shared beta-cast
and positivity hypotheses of the two component drafts. -/
theorem positive_zero_iff (p : Fin 4 → ℤ) (beta : V)
    (hbeta : 0<beta) (hport : (p 0 : DiffRing V)=ι beta) :
    (∃ v : Fin 14 → V, (∀ j, 0<v j) ∧
      InternalZero (P84QcubeGraph.graph p).output v) ↔
    (∃ v : Fin 14 → V, (∀ j, 0<v j) ∧
      InternalZero (P78AuxRoot.graph p).output v) := by
  exact (DirectFirstRootPositiveClientDraft.positive_zero_iff p beta hbeta hport).trans
    (AuxGraphEquivalenceDraft.positive_zero_iff p beta hbeta hport)

/-- Proposed natural-port specialization; no external port-byte binding. -/
theorem positive_zero_iff_natural_ports (p : Fin 4 → ℕ)
    (hbeta : 0<(p 0 : V)) :
    (∃ v : Fin 14 → V, (∀ j, 0<v j) ∧
      InternalZero (P84QcubeGraph.graph (fun j => (p j : ℤ))).output v) ↔
    (∃ v : Fin 14 → V, (∀ j, 0<v j) ∧
      InternalZero (P78AuxRoot.graph (fun j => (p j : ℤ))).output v) := by
  exact (DirectFirstRootPositiveClientDraft.positive_zero_iff_natural_ports p hbeta).trans
    (AuxGraphEquivalenceDraft.positive_zero_iff_natural_ports p hbeta)

end DiophantineConsistency.Model84To78CompositionDraft

#print axioms DiophantineConsistency.Model84To78CompositionDraft.positive_zero_iff
#print axioms DiophantineConsistency.Model84To78CompositionDraft.positive_zero_iff_natural_ports
