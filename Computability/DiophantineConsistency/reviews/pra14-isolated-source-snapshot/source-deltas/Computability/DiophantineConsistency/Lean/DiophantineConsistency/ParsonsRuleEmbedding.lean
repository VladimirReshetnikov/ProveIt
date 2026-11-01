import DiophantineConsistency.ParsonsRule
import DiophantineConsistency.ParsonsCutFree
/-! Embed finite Foundation theory proofs into the explicit Σ₁-rule calculus.
The theory is unchanged; this does not eliminate induction axioms. -/
set_option autoImplicit false
namespace DiophantineConsistency.ParsonsRuleEmbedding
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open ParsonsRule
variable {L : Language} [L.ORing] {T : Theory L}

/-- Discharge a finite LK context using actual rule-calculus proofs, preserving
all free parameters. The logical derivation may contain cuts. -/
def fromContext : (Γ : List (Proposition L)) →
    (∀ ψ ∈ Γ, Proof T ψ) → (χ : Proposition L) →
    Derivation (χ :: ∼Γ) → Proof T χ
  | [], _, _, d => .logical d
  | ψ :: Γ, hs, χ, d => by
      have h : Derivation ((ψ 🡒 χ) :: ∼Γ) := by
        have d' : Derivation (∼ψ :: χ :: ∼Γ) := d.contra (by simp)
        simpa [Semiformula.imp_eq] using d'.or
      have hp : Proof T (ψ 🡒 χ) := fromContext Γ (fun θ ht => hs θ (by simp [ht])) _ h
      exact .mp hp (hs ψ (by simp))

/-- An actual finite Foundation proof gives a rule-calculus proof over the
same theory. Classical choice selects antecedents of the embedding map. -/
noncomputable def embedTheory {σ : Sentence L} (p : Theory.Proof T σ) : Proof T (Rewriting.emb σ) := by
  let Γ : List (Proposition L) := p.axioms.map (fun σ => Rewriting.emb σ)
  have h : ∀ ψ ∈ Γ, Proof T ψ := by
    intro ψ hm
    let σ' := Classical.choose (List.mem_map.mp hm)
    have hσ := Classical.choose_spec (List.mem_map.mp hm)
    exact hσ.2 ▸ Proof.axiom (p.axioms_mem σ' hσ.1)
  have d : Derivation (Rewriting.emb σ :: ∼Γ) := by
    simpa [Γ, OneSidedLK.Pullback, Sequent.lcHom_comm] using p.derivation
  exact fromContext Γ h _ d

/-- The same conversion accepts the previously established cut-free package. -/
noncomputable def embedCutFree {σ : Sentence L} (p : ParsonsCutFree.CutFreeTheoryProof T σ) :
    Proof T (Rewriting.emb σ) :=
  embedTheory (ParsonsCutFree.toTheoryProof p)

theorem provable_embeds {σ : Sentence L} (h : T ⊢ σ) :
    Nonempty (Proof T (Rewriting.emb σ)) := by
  obtain ⟨p⟩ := h
  exact ⟨embedTheory p⟩

end DiophantineConsistency.ParsonsRuleEmbedding
