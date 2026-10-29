import DiophantineConsistency.ParsonsBasePositive
set_option autoImplicit false
namespace DiophantineConsistency.ParsonsBaseInvariant
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open ParsonsUnified ParsonsGuardTree ParsonsStrictInvariant ParsonsBasePositive

def BaseMark : Mark → Prop
  | .base s => Prefix s.state.positive
  | .side _ _ => True
  | .block _ _ _ _ _ => True

def BaseGood (es : List Mark) : Prop := ∀ e ∈ es, BaseMark e

theorem initial_base {σ : ArithmeticSentence}
    (p : ParsonsTheoryNormalize.NormalizedProof 𝗣𝗔⁻ (Hierarchy 𝚺 1) σ)
    (hσ : Hierarchy 𝚷 2 (Rewriting.emb σ : Proposition ℒₒᵣ)) : BaseGood (initial p hσ) := by
  intro e he
  obtain ⟨e',_,rfl⟩ := List.mem_map.mp he
  cases e' with
  | side P hP => trivial
  | base τ hτ => exact paminus_prefix τ hτ
  | block φ hφ n A hs => trivial

theorem shift_good (es : List Mark) (h : BaseGood es) : BaseGood (es.map Mark.shift) := by
  intro e he
  obtain ⟨e',he',rfl⟩ := List.mem_map.mp he
  have hh := h e' he'
  cases e' with
  | side P hp => trivial
  | base s => exact shift_state s hh
  | block φ hφ n A hs => trivial

theorem select_good (Δ : Sequent ℒₒᵣ) (es : List Mark)
    (hsub : Δ ⊆ es.map Mark.formula) (h : BaseGood es) : BaseGood (selectEntries Δ es hsub) := by
  intro e he
  exact h e (selected_subset Δ es hsub he)

theorem open_good (s : ParsonsBaseShape.ShapedBase) (A : ArithmeticSemiformula ℕ 1)
    (hEq : s.state.positive = ∀⁰ A) (t : SyntacticTerm ℒₒᵣ) (es : List Mark)
    (h : BaseGood (Mark.base s :: es)) :
    BaseGood (Mark.base (ParsonsBaseShape.openState s A hEq t) :: es) := by
  have hp : Prefix s.state.positive := h (Mark.base s) (by simp)
  intro e he
  rcases List.mem_cons.mp he with rfl | he
  · exact open_state s hp A hEq t
  · exact h e (by simp [he])

theorem terminal_good (s : ParsonsBaseShape.ShapedBase) (hp : Positive s.state.positive)
    (es : List Mark) (hg : Good (Mark.base s :: es)) (hb : StrictBlocks (Mark.base s :: es))
    (hz : BaseGood (Mark.base s :: es)) :
    Good (Mark.side s.state.negative ((Hierarchy.neg (sigma hp)).strict_mono _ (by decide)) :: es) ∧
    StrictBlocks (Mark.side s.state.negative ((Hierarchy.neg (sigma hp)).strict_mono _ (by decide)) :: es) ∧
    BaseGood (Mark.side s.state.negative ((Hierarchy.neg (sigma hp)).strict_mono _ (by decide)) :: es) := by
  constructor
  · intro e he
    rcases List.mem_cons.mp he with rfl | he
    · exact terminal_tree s hp
    · exact hg e (by simp [he])
  constructor
  · intro e he
    rcases List.mem_cons.mp he with rfl | he
    · trivial
    · exact hb e (by simp [he])
  · intro e he
    rcases List.mem_cons.mp he with rfl | he
    · trivial
    · exact hz e (by simp [he])
end DiophantineConsistency.ParsonsBaseInvariant
