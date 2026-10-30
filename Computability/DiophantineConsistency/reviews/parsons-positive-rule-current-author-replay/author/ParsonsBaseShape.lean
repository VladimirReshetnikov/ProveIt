import DiophantineConsistency.ParsonsBaseState
set_option autoImplicit false
namespace DiophantineConsistency.ParsonsBaseShape
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic

/-- Zero or more leading universals followed by a Σ₁ formula. -/
inductive PrefixSigma : {ξ : Type} → {n : ℕ} → Semiformula ℒₒᵣ ξ n → Prop where
  | terminal {ξ : Type} {n} {A : Semiformula ℒₒᵣ ξ n} : Hierarchy 𝚺 1 A → PrefixSigma A
  | all {ξ : Type} {n} {A : Semiformula ℒₒᵣ ξ (n+1)} : PrefixSigma A → PrefixSigma (∀⁰ A)

theorem allClosure_prefix {ξ : Type} {n : ℕ} (A : Semiformula ℒₒᵣ ξ n) (h : PrefixSigma A) :
    PrefixSigma (∀⁰* A) := by
  induction n with
  | zero => exact h
  | succ n ih => exact ih (∀⁰ A) (.all h)

theorem prefix_pi {ξ : Type} {n : ℕ} (A : Semiformula ℒₒᵣ ξ n) (h : PrefixSigma A) :
    Hierarchy 𝚷 2 A := by
  induction h with
  | terminal h => exact h.strict_mono _ (by decide)
  | all h ih => exact Hierarchy.all ih

theorem prefix_rew {ξ₁ ξ₂ : Type} {n m : ℕ} (A : Semiformula ℒₒᵣ ξ₁ n) (h : PrefixSigma A)
    (ω : Rew ℒₒᵣ ξ₁ n ξ₂ m) : PrefixSigma (ω ▹ A) := by
  induction h generalizing m with
  | terminal h => exact .terminal (Hierarchy.rew ω h)
  | all h ih => simpa using PrefixSigma.all (ih ω.q)

theorem eq_prefix_sentence (σ : ArithmeticSentence) (h : σ ∈ 𝗘𝗤 ℒₒᵣ) :
    PrefixSigma σ := by
  cases h with
  | refl =>
    simp only [Theory.Eq.refl]
    apply PrefixSigma.all
    apply PrefixSigma.terminal
    simp
  | symm =>
    simp only [Theory.Eq.symm]
    apply PrefixSigma.all
    apply PrefixSigma.all
    apply PrefixSigma.terminal
    simp [Semiformula.imp_eq]
  | trans =>
    simp only [Theory.Eq.trans]
    apply PrefixSigma.all
    apply PrefixSigma.all
    apply PrefixSigma.all
    apply PrefixSigma.terminal
    simp [Semiformula.imp_eq]
  | funcExt f =>
    unfold Theory.Eq.funcExt
    apply allClosure_prefix
    apply PrefixSigma.terminal
    simp [Semiformula.imp_eq, Hierarchy.conj_iff]
  | relExt r =>
    unfold Theory.Eq.relExt
    apply allClosure_prefix
    apply PrefixSigma.terminal
    simp [Semiformula.imp_eq, Hierarchy.conj_iff]

theorem paminus_prefix_sentence (σ : ArithmeticSentence) (h : σ ∈ 𝗣𝗔⁻) :
    PrefixSigma σ := by
  cases h
  case equal h => exact eq_prefix_sentence σ h
  all_goals repeat' (first | apply PrefixSigma.all | apply PrefixSigma.terminal)
  all_goals simp [Semiformula.imp_eq]

theorem paminus_prefix (σ : ArithmeticSentence) (h : σ ∈ 𝗣𝗔⁻) :
    PrefixSigma (Rewriting.emb σ : Proposition ℒₒᵣ) := by
  exact prefix_rew σ (paminus_prefix_sentence σ h) Rew.emb

set_option linter.flexible false in
theorem sigma_body_of_all {n : ℕ} (A : ArithmeticSemiformula ℕ (n+1)) :
    Hierarchy 𝚺 1 (∀⁰ A) → Hierarchy 𝚺 1 A := by
  generalize hr : ∀⁰ A = r
  generalize hb : (𝚺 : Polarity) = Γ
  intro H
  cases H <;> try simp [LO.FirstOrder.ball, LO.FirstOrder.bexs] at hr
  case ball => rcases hr with rfl; simpa
  case all hp => cases hb
  case pi hp => cases hb

theorem prefix_open {n : ℕ} (A : ArithmeticSemiformula ℕ (n+1))
    (h : PrefixSigma (∀⁰ A)) : PrefixSigma A := by
  cases h with
  | terminal h => exact .terminal (sigma_body_of_all A h)
  | all h => exact h

/-- A nonterminal prefix must expose a universal rule; if the whole formula
is already Σ₁, its negative can instead be reclassified as a Π₂ side. -/
theorem nonterminal_is_all (P : Proposition ℒₒᵣ) (h : PrefixSigma P)
    (hn : ¬Hierarchy 𝚺 1 P) : ∃ A : ArithmeticSemiformula ℕ 1, P = ∀⁰ A := by
  cases h with
  | terminal h => exact False.elim (hn h)
  | all h => exact ⟨_, rfl⟩

/-- The base state augmented by the actual PA-minus universal-prefix shape. -/
structure ShapedBase where
  state : ParsonsBaseState.BaseState
  shape : PrefixSigma state.positive

def initial (σ : ArithmeticSentence) (hσ : σ ∈ 𝗣𝗔⁻) : ShapedBase := by
  let hs := paminus_prefix σ hσ
  exact ⟨ParsonsBaseState.ofAxiom σ hσ (prefix_pi _ hs), hs⟩

def openState (s : ShapedBase) (A : ArithmeticSemiformula ℕ 1)
    (hEq : s.state.positive = ∀⁰ A) (t : SyntacticTerm ℒₒᵣ) : ShapedBase := by
  have hA : PrefixSigma A := by
    apply prefix_open A
    rw [← hEq]
    exact s.shape
  exact ⟨ParsonsBaseState.openState s.state A hEq t,
    prefix_rew A hA (Rew.subst ![t])⟩

def shiftState (s : ShapedBase) : ShapedBase :=
  ⟨ParsonsBaseState.shiftState s.state, prefix_rew s.state.positive s.shape Rew.shift⟩

end DiophantineConsistency.ParsonsBaseShape
