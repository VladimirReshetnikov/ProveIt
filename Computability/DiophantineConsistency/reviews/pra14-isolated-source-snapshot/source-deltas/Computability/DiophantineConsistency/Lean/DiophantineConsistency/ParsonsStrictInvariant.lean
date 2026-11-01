import DiophantineConsistency.ParsonsStrictPrefixTree
set_option autoImplicit false
namespace DiophantineConsistency.ParsonsStrictInvariant
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open ParsonsGuardTree ParsonsUnified ParsonsRule

/-- Syntactically strict existential prefix with a bounded matrix. -/
def Strict (φ : ArithmeticSemiformula ℕ 1) : Prop :=
  ∃ (n : ℕ) (D : ArithmeticSemiformula ℕ (1+n)),
    Hierarchy 𝚺 0 D ∧ φ = ∃⁰^[n] D

theorem sigma {φ : ArithmeticSemiformula ℕ 1} (h : Strict φ) : Hierarchy 𝚺 1 φ := by
  obtain ⟨n,D,hD,rfl⟩ := h
  exact Hierarchy.exsItr_iff.mpr (hD.mono (by decide))

theorem rewrite {φ : ArithmeticSemiformula ℕ 1} (h : Strict φ)
    (f : ℕ → SyntacticTerm ℒₒᵣ) : Strict ((Rew.rewrite f).q ▹ φ) := by
  obtain ⟨n,D,hD,rfl⟩ := h
  refine ⟨n, ((Rew.rewrite f).q).qpow n ▹ D, Hierarchy.rew _ hD, ?_⟩
  simp

theorem base_tree {φ : ArithmeticSemiformula ℕ 1} (h : Strict φ) : Tree (base φ) :=
  .sigma (ParsonsSide.base_sigma φ (sigma h))

theorem step_tree {φ : ArithmeticSemiformula ℕ 1} (h : Strict φ) : Tree (step φ) := by
  obtain ⟨n,D,hD,rfl⟩ := h
  exact ParsonsStrictPrefixTree.strict_step D hD

theorem negative_tree {φ : ArithmeticSemiformula ℕ 1} (h : Strict φ)
    (t : SyntacticTerm ℒₒᵣ) : Tree (∼(φ/[t])) := by
  obtain ⟨n,D,hD,rfl⟩ := h
  exact ParsonsStrictPrefixTree.strict_negative D hD t

def StrictMark : Mark → Prop
  | .block φ _ _ _ _ => Strict φ
  | .side _ _ => True
  | .base _ => True

def StrictBlocks (es : List Mark) : Prop := ∀ e ∈ es, StrictMark e

theorem shift_blocks (es : List Mark) (h : StrictBlocks es) : StrictBlocks (es.map Mark.shift) := by
  intro e he
  obtain ⟨e',he',rfl⟩ := List.mem_map.mp he
  have hs := h e' he'
  cases e' with
  | side P hp => trivial
  | base s => trivial
  | block φ hφ n A hA => exact hs

theorem select_blocks (Δ : Sequent ℒₒᵣ) (es : List Mark)
    (hsub : Δ ⊆ es.map Mark.formula) (h : StrictBlocks es) :
    StrictBlocks (selectEntries Δ es hsub) := by
  intro e he
  exact h e (selected_subset Δ es hsub he)
end DiophantineConsistency.ParsonsStrictInvariant
