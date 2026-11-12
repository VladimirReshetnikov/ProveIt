import PositiveMap85To86
import FreshMap86To85

/-! Source-only positive 85↔86 model comparison. Both directions and their
transitive imports are unelaborated drafts; no endpoint/file result is asserted. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.ModelEquivalence8586Draft
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ModelDifferenceRing
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Proposed positive-zero equivalence under an explicit positive natural
beta representation; the remaining integer ports are arbitrary. -/
theorem positive_zero_iff (p : Fin 4 → ℤ) (beta : V)
    (hbeta : 0<beta) (hport : (p 0 : DiffRing V)=ι beta) :
    (∃ v : Fin 14 → V, (∀ j, 0<v j) ∧ InternalZero (P85QcubeGraph.graph p).output v) ↔
    (∃ v : Fin 14 → V, (∀ j, 0<v j) ∧ InternalZero (P86ResidueGraph.graph p).output v) := by
  constructor
  · rintro ⟨v,hv,hz⟩
    exact PositiveMap85To86Draft.positive_map p beta v hport hv hz
  · rintro ⟨v,hv,hz⟩
    exact FreshMap86To85Draft.positive_map p beta v hbeta hport hv hz

/-- Proposed natural-port specialization; no external byte binding. -/
theorem positive_zero_iff_natural_ports (p : Fin 4 → ℕ) (hbeta : 0<(p 0 : V)) :
    (∃ v : Fin 14 → V, (∀ j, 0<v j) ∧ InternalZero (P85QcubeGraph.graph (fun j => (p j : ℤ))).output v) ↔
    (∃ v : Fin 14 → V, (∀ j, 0<v j) ∧ InternalZero (P86ResidueGraph.graph (fun j => (p j : ℤ))).output v) := by
  apply positive_zero_iff (fun j => (p j : ℤ)) (p 0 : V) hbeta
  simpa only using (P72Root.cast_port p 0)

end DiophantineConsistency.ModelEquivalence8586Draft

#print axioms DiophantineConsistency.ModelEquivalence8586Draft.positive_zero_iff
#print axioms DiophantineConsistency.ModelEquivalence8586Draft.positive_zero_iff_natural_ports
