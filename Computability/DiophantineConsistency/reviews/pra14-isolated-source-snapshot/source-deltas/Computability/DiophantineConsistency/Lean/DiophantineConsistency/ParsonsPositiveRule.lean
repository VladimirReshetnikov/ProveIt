import DiophantineConsistency.ParsonsBasePositive
import DiophantineConsistency.ParsonsRule
/-! A restricted rule calculus whose induction predicates retain positive
bounded/existential syntax, together with its embedding into ParsonsRule. -/
set_option autoImplicit false
namespace DiophantineConsistency.ParsonsPositiveRule
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open ParsonsRule ParsonsBasePositive ParsonsGuard

theorem positive_exsItr {ξ : Type} (m n : ℕ)
    (D : Semiformula ℒₒᵣ ξ (m+n)) (hD : Positive D) : Positive (∃⁰^[n] D) := by
  induction n generalizing m with
  | zero => simpa using hD
  | succ n ih =>
    simp only [exsItr_succ]
    exact ih m (∃⁰ D) (Positive.exs hD)

theorem strict_positive {φ : ArithmeticSemiformula ℕ 1}
    (h : ParsonsStrictInvariant.Strict φ) : Positive φ := by
  obtain ⟨n,D,hD,rfl⟩ := h
  exact positive_exsItr 1 n D (.bounded hD)

theorem positive_guard {φ : ArithmeticSemiformula ℕ 1} {E : Proposition ℒₒᵣ}
    (hφ : Positive φ) (hE : Positive E) : Positive (ParsonsGuard.guard φ E) := by
  unfold ParsonsGuard.guard
  exact Positive.or hφ (pos_rewrite hE Rew.bShift)

/-- The induction predicate must be built from bounded leaves using
conjunction, disjunction, and existential quantification. -/
inductive Proof (T : Theory ℒₒᵣ) : Proposition ℒₒᵣ → Type
  | logical {φ} : Derivation [φ] → Proof T φ
  | axiom {σ : Sentence ℒₒᵣ} : σ ∈ T → Proof T (Rewriting.emb σ)
  | mp {φ ψ} : Proof T (φ 🡒 ψ) → Proof T φ → Proof T ψ
  | generalize {φ : ArithmeticSemiformula ℕ 1} : Proof T φ.free → Proof T (∀⁰ φ)
  | specialize {φ : ArithmeticSemiformula ℕ 1} (t : SyntacticTerm ℒₒᵣ) :
      Proof T (∀⁰ φ) → Proof T (φ/[t])
  | induction {φ : ArithmeticSemiformula ℕ 1} : Positive φ →
      Proof T (base φ) → Proof T (step φ) → Proof T (∀⁰ φ)

def toRule {T : Theory ℒₒᵣ} {φ : Proposition ℒₒᵣ} : Proof T φ → ParsonsRule.Proof T φ
  | .logical d => .logical d
  | .axiom h => .axiom h
  | .mp a b => .mp (toRule a) (toRule b)
  | .generalize a => .generalize (toRule a)
  | .specialize t a => .specialize t (toRule a)
  | .induction h a b => .induction (sigma h) (toRule a) (toRule b)
end DiophantineConsistency.ParsonsPositiveRule
