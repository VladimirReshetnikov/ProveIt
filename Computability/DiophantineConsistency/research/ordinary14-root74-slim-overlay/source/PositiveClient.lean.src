import GraphFirstRootClient

/-! Source-only proposal: turn the fixed-other-coordinate first-root draft
into an all-positive valuation comparison. The imported client and its graph
and provider imports are uncompiled drafts. No endpoint or file theorem is
claimed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.DirectFirstRootPositiveClientDraft
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ModelDifferenceRing
open DirectFirstRootGraphClientDraft
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Updating slot 8 with its existing value leaves the valuation unchanged. -/
theorem putRoot_self (v : Fin 14 → V) : putRoot v (v 8)=v := by
  funext j
  by_cases hj : j=8
  · subst j
    simp [putRoot]
  · simp [putRoot,hj]

/-- Proposed positive-valuation existence comparison for integer ports whose
first port has an explicit positive natural representation in the model.
The result is conditional on the uncompiled imported graph client. -/
theorem positive_zero_iff (p : Fin 4 → ℤ) (beta : V)
    (hbeta : 0<beta) (hport : (p 0 : DiffRing V)=ι beta) :
    (∃ v : Fin 14 → V, (∀ j, 0<v j) ∧
      InternalZero (P84QcubeGraph.graph p).output v) ↔
    (∃ v : Fin 14 → V, (∀ j, 0<v j) ∧
      InternalZero (P79DirectPell.graph p).output v) := by
  constructor
  · rintro ⟨v,hv,hz⟩
    have hold : ∃ r : V, 0<r ∧
        InternalZero (P84QcubeGraph.graph p).output (putRoot v r) := by
      refine ⟨v 8,hv 8,?_⟩
      simpa only [putRoot_self] using hz
    obtain ⟨t,ht,hnew⟩ :=
      (positive_first_coordinate_iff p beta v hbeta (hv 0) hport).mp hold
    exact ⟨putRoot v t,putRoot_positive v t hv ht,hnew⟩
  · rintro ⟨v,hv,hz⟩
    have hnew : ∃ t : V, 0<t ∧
        InternalZero (P79DirectPell.graph p).output (putRoot v t) := by
      refine ⟨v 8,hv 8,?_⟩
      simpa only [putRoot_self] using hz
    obtain ⟨r,hr,hold⟩ :=
      (positive_first_coordinate_iff p beta v hbeta (hv 0) hport).mpr hnew
    exact ⟨putRoot v r,putRoot_positive v r hv hr,hold⟩

/-- Natural-number port tuple specialization using the existing source-level
cast lemma. It does not identify any external bytes with a port tuple. -/
theorem positive_zero_iff_natural_ports (p : Fin 4 → ℕ)
    (hbeta : 0<(p 0 : V)) :
    (∃ v : Fin 14 → V, (∀ j, 0<v j) ∧
      InternalZero (P84QcubeGraph.graph (fun j => (p j : ℤ))).output v) ↔
    (∃ v : Fin 14 → V, (∀ j, 0<v j) ∧
      InternalZero (P79DirectPell.graph (fun j => (p j : ℤ))).output v) := by
  apply positive_zero_iff (fun j => (p j : ℤ)) (p 0 : V) hbeta
  simpa only using (P72Root.cast_port p 0)

end DiophantineConsistency.DirectFirstRootPositiveClientDraft

#print axioms DiophantineConsistency.DirectFirstRootPositiveClientDraft.positive_zero_iff
#print axioms DiophantineConsistency.DirectFirstRootPositiveClientDraft.positive_zero_iff_natural_ports
