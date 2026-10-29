import DiophantineConsistency.ParsonsSelection
set_option autoImplicit false
namespace DiophantineConsistency.ParsonsAndContext
open LO LO.FirstOrder
open scoped LO.FirstOrder
open ParsonsSelection

theorem keep_prefix {L : Language} (A B C : Proposition L) (Γ : Sequent L)
    {Δ Ξ : Sequent L} (hs : Selection A B C Δ Ξ) :
    Selection A B C (Γ ++ Δ) (Γ ++ Ξ) := by
  induction Γ with
  | nil => exact hs
  | cons φ Γ ih => exact .keep φ ih

/-- Invert either conjunct at any position below an existential conclusion. -/
theorem invert_below_exs {L : Language} (A B C : Proposition L)
    (hC : C = A ∨ C = B) (D : Semiproposition L 1) (t : SyntacticTerm L) (Γ Δ : Sequent L)
    (d : Derivation (D/[t] :: (Γ ++ (A ⋏ B) :: Δ))) (hc : Derivation.IsCutFree d) :
    ∃ e : Derivation (D/[t] :: (Γ ++ C :: Δ)),
      Derivation.IsCutFree e ∧ e.height < d.exs.height := by
  obtain ⟨e, he, hb⟩ := invert hc (.keep _ (keep_prefix A B C Γ (.replace (same A B C Δ)))) hC
  exact ⟨e, he, by simp only [Derivation.height_exs]; omega⟩
end DiophantineConsistency.ParsonsAndContext
