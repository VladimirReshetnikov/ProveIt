import DiophantineConsistency.ParsonsStrictInvariant
set_option autoImplicit false
namespace DiophantineConsistency.ParsonsBasePositive
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open ParsonsBaseShape ParsonsBaseState ParsonsUnified ParsonsGuardTree

/-- Positive Boolean combinations and existential quantifiers over bounded
matrices. Negating this shape yields a Tree. -/
inductive Positive : {ξ : Type} → {n : ℕ} → Semiformula ℒₒᵣ ξ n → Prop where
  | bounded {ξ : Type} {n} {A : Semiformula ℒₒᵣ ξ n} : Hierarchy 𝚺 0 A → Positive A
  | and {ξ : Type} {n} {A B : Semiformula ℒₒᵣ ξ n} : Positive A → Positive B → Positive (A ⋏ B)
  | or {ξ : Type} {n} {A B : Semiformula ℒₒᵣ ξ n} : Positive A → Positive B → Positive (A ⋎ B)
  | exs {ξ : Type} {n} {A : Semiformula ℒₒᵣ ξ (n+1)} : Positive A → Positive (∃⁰ A)

theorem sigma {ξ : Type} {n : ℕ} {A : Semiformula ℒₒᵣ ξ n} (h : Positive A) : Hierarchy 𝚺 1 A := by
  induction h with
  | bounded h => exact h.mono (by decide)
  | and _ _ ih1 ih2 => exact Hierarchy.and ih1 ih2
  | or _ _ ih1 ih2 => exact Hierarchy.or ih1 ih2
  | exs _ ih => exact Hierarchy.exs ih

theorem negative_tree {ξ : Type} {n : ℕ} {A : Semiformula ℒₒᵣ ξ n}
    (h : Positive A) : ∀ (ω : Rew ℒₒᵣ ξ n ℕ 0), Tree (∼(ω ▹ A)) := by
  induction h with
  | bounded h =>
      intro ω
      have hz := Hierarchy.rew ω h
      exact Tree.sigma (((Hierarchy.neg hz).zero_eq_alt).mono (by decide))
  | and hA hB ihA ihB =>
      intro ω
      simpa using Tree.or (ihA ω) (ihB ω)
  | or hA hB ihA ihB =>
      intro ω
      simpa using Tree.and (ihA ω) (ihB ω)
  | @exs n A hA ih =>
      intro ω
      have hsig : Hierarchy 𝚺 1 (ω ▹ (∃⁰ A)) := Hierarchy.rew ω (Hierarchy.exs (sigma hA))
      have hp : Hierarchy 𝚷 2 (∀⁰ (∼(ω.q ▹ A))) := by
        simpa using (Hierarchy.neg hsig).mono (s' := 2) (by decide)
      have hb : Tree ((∼(ω.q ▹ A)).free) := by
        have heq : (∼(ω.q ▹ A)).free = ∼((Rew.free.comp ω.q) ▹ A) := by
          simp [Rewriting.free, ← TransitiveRewriting.comp_app]
        rw [heq]
        exact ih (Rew.free.comp ω.q)
      simpa using Tree.all (∼(ω.q ▹ A)) hp hb

theorem pos_rewrite {ξ₁ ξ₂ : Type} {n m : ℕ} {A : Semiformula ℒₒᵣ ξ₁ n}
    (h : Positive A) (ω : Rew ℒₒᵣ ξ₁ n ξ₂ m) : Positive (ω ▹ A) := by
  induction h generalizing m with
  | bounded h => exact .bounded (Hierarchy.rew ω h)
  | and hA hB ihA ihB => simpa using Positive.and (ihA ω) (ihB ω)
  | or hA hB ihA ihB => simpa using Positive.or (ihA ω) (ihB ω)
  | exs h ih => simpa using Positive.exs (ih ω.q)

/-- A universal prefix ending in a positive bounded/existential tree. -/
inductive Prefix : {ξ : Type} → {n : ℕ} → Semiformula ℒₒᵣ ξ n → Prop where
  | terminal {ξ : Type} {n} {A : Semiformula ℒₒᵣ ξ n} : Positive A → Prefix A
  | all {ξ : Type} {n} {A : Semiformula ℒₒᵣ ξ (n+1)} : Prefix A → Prefix (∀⁰ A)

theorem allClosure_prefix {ξ : Type} {n : ℕ} (A : Semiformula ℒₒᵣ ξ n) (h : Prefix A) :
    Prefix (∀⁰* A) := by
  induction n with
  | zero => exact h
  | succ n ih => exact ih (∀⁰ A) (.all h)

theorem prefix_rewrite {ξ₁ ξ₂ : Type} {n m : ℕ} {A : Semiformula ℒₒᵣ ξ₁ n}
    (h : Prefix A) (ω : Rew ℒₒᵣ ξ₁ n ξ₂ m) : Prefix (ω ▹ A) := by
  induction h generalizing m with
  | terminal h => exact .terminal (pos_rewrite h ω)
  | all h ih => simpa using Prefix.all (ih ω.q)

theorem eq_prefix_sentence (σ : ArithmeticSentence) (h : σ ∈ 𝗘𝗤 ℒₒᵣ) : Prefix σ := by
  cases h with
  | refl =>
    simp only [Theory.Eq.refl]
    apply Prefix.all
    apply Prefix.terminal
    apply Positive.bounded
    simp
  | symm =>
    simp only [Theory.Eq.symm]
    apply Prefix.all
    apply Prefix.all
    apply Prefix.terminal
    apply Positive.bounded
    simp [Semiformula.imp_eq]
  | trans =>
    simp only [Theory.Eq.trans]
    apply Prefix.all
    apply Prefix.all
    apply Prefix.all
    apply Prefix.terminal
    apply Positive.bounded
    simp [Semiformula.imp_eq]
  | funcExt f =>
    unfold Theory.Eq.funcExt
    apply allClosure_prefix
    apply Prefix.terminal
    apply Positive.bounded
    simp [Semiformula.imp_eq, Hierarchy.conj_iff]
  | relExt r =>
    unfold Theory.Eq.relExt
    apply allClosure_prefix
    apply Prefix.terminal
    apply Positive.bounded
    simp [Semiformula.imp_eq, Hierarchy.conj_iff]

theorem paminus_prefix_sentence (σ : ArithmeticSentence) (h : σ ∈ 𝗣𝗔⁻) : Prefix σ := by
  cases h
  case equal h => exact eq_prefix_sentence σ h
  case addEqOfLt =>
    repeat' apply Prefix.all
    apply Prefix.terminal
    simp only [Semiformula.imp_eq]
    apply Positive.or
    · apply Positive.bounded; simp
    · apply Positive.exs; apply Positive.bounded; simp
  all_goals repeat' (first | apply Prefix.all | apply Prefix.terminal | apply Positive.bounded)
  all_goals simp [Semiformula.imp_eq]

theorem paminus_prefix (σ : ArithmeticSentence) (h : σ ∈ 𝗣𝗔⁻) :
    Prefix (Rewriting.emb σ : Proposition ℒₒᵣ) :=
  prefix_rewrite (paminus_prefix_sentence σ h) Rew.emb

set_option linter.flexible false in
theorem zero_body_of_all {ξ : Type} {n : ℕ} (A : Semiformula ℒₒᵣ ξ (n+1)) :
    Hierarchy 𝚺 0 (∀⁰ A) → Hierarchy 𝚺 0 A := by
  generalize hr : ∀⁰ A = r
  generalize hb : (𝚺 : Polarity) = Γ
  intro H
  cases H <;> try simp [LO.FirstOrder.ball, LO.FirstOrder.bexs] at hr
  case ball => rcases hr with rfl; simpa

theorem positive_body_of_all {ξ : Type} {n : ℕ} (A : Semiformula ℒₒᵣ ξ (n+1))
    (h : Positive (∀⁰ A)) : Positive A := by
  cases h with
  | bounded h => exact .bounded (zero_body_of_all A h)

theorem prefix_open {n : ℕ} (A : ArithmeticSemiformula ℕ (n+1))
    (h : Prefix (∀⁰ A)) : Prefix A := by
  cases h with
  | terminal h => exact .terminal (positive_body_of_all A h)
  | all h => exact h

theorem open_state (s : ShapedBase) (hshape : Prefix s.state.positive)
    (A : ArithmeticSemiformula ℕ 1) (hEq : s.state.positive = ∀⁰ A) (t : SyntacticTerm ℒₒᵣ) :
    Prefix (ParsonsBaseShape.openState s A hEq t).state.positive := by
  have hp : Prefix (∀⁰ A) := by simpa [hEq] using hshape
  have hA : Prefix A := prefix_open A hp
  simpa [ParsonsBaseShape.openState, ParsonsBaseState.openState, ParsonsBaseState.openUniversal]
    using prefix_rewrite hA (Rew.subst ![t])

theorem shift_state (s : ShapedBase) (hshape : Prefix s.state.positive) :
    Prefix (ParsonsBaseShape.shiftState s).state.positive := by
  simpa [ParsonsBaseShape.shiftState, ParsonsBaseState.shiftState, Rewriting.shift] using
    prefix_rewrite hshape Rew.shift

theorem terminal_tree (s : ShapedBase) (h : Positive s.state.positive) : Tree s.state.negative := by
  have ht := negative_tree h (Rew.id : SyntacticRew ℒₒᵣ 0 0)
  simpa [ParsonsBaseState.BaseState.negative] using ht
end DiophantineConsistency.ParsonsBasePositive
