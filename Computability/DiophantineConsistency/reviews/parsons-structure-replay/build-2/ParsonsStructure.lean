import DiophantineConsistency.ParsonsGuardedCollection
set_option autoImplicit false
namespace DiophantineConsistency.ParsonsStructure
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open ParsonsRule ParsonsGuardedCollection

def disjoin : List (Proposition ℒₒᵣ) → Proposition ℒₒᵣ
  | [] => ⊥
  | P :: Γ => P ⋎ disjoin Γ

theorem eval_disjoin (M : Type) [ORingStructure M] (f : ℕ → M)
    (Γ : List (Proposition ℒₒᵣ)) :
    (disjoin Γ).Evalf f ↔ ∃ P ∈ Γ, P.Evalf f := by
  induction Γ with
  | nil => simp [disjoin]
  | cons P Γ ih => simp [disjoin, ih]

/-- Weakening and contraction of any finite side disjunction. -/
noncomputable def weakening (Γ Δ : List (Proposition ℒₒᵣ)) (hsub : Γ ⊆ Δ)
    (h : Proof 𝗣𝗔⁻ (disjoin Γ)) : Proof 𝗣𝗔⁻ (disjoin Δ) := by
  have hp : Proof 𝗣𝗔⁻ (disjoin Γ 🡒 disjoin Δ) := of_semantics _ _ (by
    intro M _ _ f hv
    rw [eval_disjoin] at hv ⊢
    obtain ⟨P, hm, hp⟩ := hv
    exact ⟨P, hsub hm, hp⟩)
  exact .mp hp h

/-- The same monotonicity after any fixed projection of sequent entries. -/
noncomputable def projected_weakening (F : Proposition ℒₒᵣ → Proposition ℒₒᵣ)
    (Γ Δ : List (Proposition ℒₒᵣ)) (hsub : Γ ⊆ Δ)
    (h : Proof 𝗣𝗔⁻ (disjoin (Γ.map F))) : Proof 𝗣𝗔⁻ (disjoin (Δ.map F)) := by
  apply weakening (Γ.map F) (Δ.map F) ?_ h
  intro P hp
  obtain ⟨Q, hQ, rfl⟩ := List.mem_map.mp hp
  exact List.mem_map.mpr ⟨Q, hsub hQ, rfl⟩

/-- The actual contraction case of a height recursion with a fixed projection. -/
theorem contraction_case (F : Proposition ℒₒᵣ → Proposition ℒₒᵣ)
    (Γ Δ : Sequent ℒₒᵣ) (hsub : Δ ⊆ Γ) (d : Derivation Δ)
    (hc : Derivation.IsCutFree d)
    (ih : ∀ e : Derivation Δ, Derivation.IsCutFree e →
      e.height < (d.contraction hsub).height → Nonempty (Proof 𝗣𝗔⁻ (disjoin (Δ.map F)))) :
    Nonempty (Proof 𝗣𝗔⁻ (disjoin (Γ.map F))) := by
  have hh : d.height < (d.contraction hsub).height := by simp
  exact ⟨projected_weakening F Δ Γ hsub (ih d hc hh).some⟩

/-- Discharge a negative occurrence of an actual PA-minus axiom. -/
noncomputable def remove_base (σ : ArithmeticSentence) (hσ : σ ∈ 𝗣𝗔⁻)
    (E : Proposition ℒₒᵣ) (h : Proof 𝗣𝗔⁻ (∼(Rewriting.emb σ) ⋎ E)) :
    Proof 𝗣𝗔⁻ E := by
  let P : Proposition ℒₒᵣ := Rewriting.emb σ
  have hPE : Proof 𝗣𝗔⁻ (P ⋎ E) := by
    have hi : Proof 𝗣𝗔⁻ (P 🡒 (P ⋎ E)) := of_semantics _ _ (by
      intro M _ _ f hp
      simp [hp])
    exact .mp hi (.axiom hσ)
  exact .mp (.mp (.logical (resolution P E)) hPE) h

end DiophantineConsistency.ParsonsStructure
