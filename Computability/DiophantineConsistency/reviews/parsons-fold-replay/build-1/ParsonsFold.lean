import DiophantineConsistency.ParsonsStructure
import DiophantineConsistency.ParsonsRuleEmbedding
set_option autoImplicit false
namespace DiophantineConsistency.ParsonsFold
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open ParsonsRule ParsonsStructure

/-- Fold the first finite list of a sequent to a single side disjunction,
retaining the remaining context exactly. -/
def fold_context : (Γ Δ : Sequent ℒₒᵣ) → Derivation (Γ ++ Δ) →
    Derivation (disjoin Γ :: Δ)
  | [], Δ, d => d.contra (by simp [disjoin])
  | P :: Γ, Δ, d => by
    have h1 : Derivation (Γ ++ P :: Δ) := d.contra (by simp)
    have h2 : Derivation (disjoin Γ :: P :: Δ) := fold_context Γ (P :: Δ) h1
    have h3 : Derivation (P :: disjoin Γ :: Δ) := h2.contra (by simp)
    exact h3.or

/-- All-logical leaf of the reduction: no induction axiom is used. -/
def logical_leaf (Γ : Sequent ℒₒᵣ) (d : Derivation Γ) :
    Proof 𝗣𝗔⁻ (disjoin Γ) := by
  apply Proof.logical
  simpa using fold_context Γ [] (by simpa using d)

/-- Base-only leaf: an arbitrary logical sequent from finitely many actual
PA-minus axioms yields a rule proof of the full side disjunction. -/
noncomputable def base_leaf (Γ : Sequent ℒₒᵣ) (B : List ArithmeticSentence)
    (hB : ∀ σ ∈ B, σ ∈ 𝗣𝗔⁻)
    (d : Derivation (Γ ++ B.map (fun σ => ∼(Rewriting.emb σ)))) :
    Proof 𝗣𝗔⁻ (disjoin Γ) := by
  let axioms : List (Proposition ℒₒᵣ) := B.map (fun σ => Rewriting.emb σ)
  have hp : ∀ P ∈ axioms, Proof 𝗣𝗔⁻ P := by
    intro P hm
    let σ := Classical.choose (List.mem_map.mp hm)
    have hs := Classical.choose_spec (List.mem_map.mp hm)
    exact hs.2 ▸ Proof.axiom (hB σ hs.1)
  have hd : Derivation (disjoin Γ :: ∼axioms) := by
    simpa [axioms, List.tilde_def, List.map_map, Function.comp_def] using
      fold_context Γ (B.map (fun σ => ∼(Rewriting.emb σ))) d
  exact ParsonsRuleEmbedding.fromContext axioms hp (disjoin Γ) hd

end DiophantineConsistency.ParsonsFold
