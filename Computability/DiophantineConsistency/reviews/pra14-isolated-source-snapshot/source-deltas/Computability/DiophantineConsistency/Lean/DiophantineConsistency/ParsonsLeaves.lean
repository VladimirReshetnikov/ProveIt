import DiophantineConsistency.ParsonsUnified
set_option autoImplicit false
namespace DiophantineConsistency.ParsonsLeaves
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open ParsonsRule ParsonsStructure ParsonsBlock ParsonsUnified

theorem closure_has_exists {n : ℕ} (A : ArithmeticSemiformula ℕ (n+1)) :
    ∃ B : ArithmeticSemiformula ℕ 1, (∃⁰* A) = ∃⁰ B := by
  induction n with
  | zero => exact ⟨A, rfl⟩
  | succ n ih =>
    simp only [exsClosure_succ]
    exact ih (∃⁰ A)

theorem block_has_exists (φ : ArithmeticSemiformula ℕ 1) (hφ : Hierarchy 𝚺 1 φ)
    (n : ℕ) (A : ArithmeticSemiformula ℕ n) (hs : State φ A) :
    ∃ B : ArithmeticSemiformula ℕ 1, (Mark.block φ hφ n A hs).formula = ∃⁰ B := by
  cases n with
  | zero =>
    obtain ⟨f, hf⟩ := ParsonsBlock.finish φ A hs
    exact ⟨ParsonsInductionCase.matrix ((Rew.rewrite f).q ▹ φ), by simpa [Mark.formula] using hf⟩
  | succ n => exact closure_has_exists A

theorem identity_no_block {k : ℕ} (r : (ℒₒᵣ).Rel k) (v : Fin k → SyntacticTerm ℒₒᵣ)
    (es : List Mark) (hsub : es.map Mark.formula ⊆ [Semiformula.rel r v, Semiformula.nrel r v]) :
    ∀ e ∈ es, ¬e.isBlock := by
  intro e he
  cases e with
  | side P h => simp [Mark.isBlock]
  | base s => simp [Mark.isBlock]
  | block φ hφ n A hs =>
    have hmem := hsub (List.mem_map_of_mem he)
    obtain ⟨B, hB⟩ := block_has_exists φ hφ n A hs
    rw [hB] at hmem
    simp at hmem

theorem verum_no_block (es : List Mark) (hsub : es.map Mark.formula ⊆ [⊤]) :
    ∀ e ∈ es, ¬e.isBlock := by
  intro e he
  cases e with
  | side P h => simp [Mark.isBlock]
  | base s => simp [Mark.isBlock]
  | block φ hφ n A hs =>
    have hmem := hsub (List.mem_map_of_mem he)
    obtain ⟨B, hB⟩ := block_has_exists φ hφ n A hs
    rw [hB] at hmem
    simp at hmem

/-- Identity and truth leaves of the marked cut-free recursion are closed
without invoking any induction hypothesis. -/
noncomputable def identity_leaf {k : ℕ} (r : (ℒₒᵣ).Rel k) (v : Fin k → SyntacticTerm ℒₒᵣ)
    (es : List Mark) (heq : es.map Mark.formula = [Semiformula.rel r v, Semiformula.nrel r v]) :
    Proof 𝗣𝗔⁻ (disjoin (es.map Mark.output)) := by
  have hn := identity_no_block r v es (by rw [heq])
  have hd : Derivation (es.map Mark.formula) := (Derivation.identity r v).cast heq.symm
  exact base_branch es hn hd

noncomputable def verum_leaf (es : List Mark) (heq : es.map Mark.formula = [⊤]) :
    Proof 𝗣𝗔⁻ (disjoin (es.map Mark.output)) := by
  have hn := verum_no_block es (by rw [heq])
  have hd : Derivation (es.map Mark.formula) := (Derivation.verum : Derivation ([⊤] : Sequent ℒₒᵣ)).cast heq.symm
  exact base_branch es hn hd

end DiophantineConsistency.ParsonsLeaves
