import DiophantineConsistency.ParsonsRuleEmbedding
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.ParsonsRuleEmbeddingChecks
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open ParsonsRule ParsonsRuleEmbedding

-- Arbitrary, possibly repeated, free formulas can appear in the context.
example {L : Language} [L.ORing] {T : Theory L} (P Q χ : Proposition L)
    (hP : Proof T P) (hQ : Proof T Q)
    (d : Derivation (χ :: ∼([P,Q,P] : List (Proposition L)))) : Proof T χ :=
  fromContext [P,Q,P] (by
    intro ψ h
    have h' : Nonempty (Proof T ψ) := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl <;> first | exact ⟨hP⟩ | exact ⟨hQ⟩
    exact Classical.choice h') χ d

example {L : Language} [L.ORing] {T : Theory L} {σ : Sentence L}
    (p : ParsonsCutFree.CutFreeTheoryProof T σ) : Proof T (Rewriting.emb σ) :=
  embedCutFree p

#print axioms fromContext
#print axioms embedTheory
#print axioms embedCutFree
#print axioms provable_embeds
end DiophantineConsistency.ParsonsRuleEmbeddingChecks
