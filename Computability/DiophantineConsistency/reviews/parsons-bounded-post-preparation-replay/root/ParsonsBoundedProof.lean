import DiophantineConsistency.ParsonsRule
set_option autoImplicit false
namespace DiophantineConsistency.ParsonsBoundedProof
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open ParsonsRule

/-- The same explicit intermediate calculus with only Σ₀ induction rules. -/
inductive Proof (T : Theory ℒₒᵣ) : Proposition ℒₒᵣ → Type
  | logical {φ} : Derivation [φ] → Proof T φ
  | axiom {σ : Sentence ℒₒᵣ} : σ ∈ T → Proof T (Rewriting.emb σ)
  | mp {φ ψ} : Proof T (φ 🡒 ψ) → Proof T φ → Proof T ψ
  | generalize {φ : ArithmeticSemiformula ℕ 1} : Proof T φ.free → Proof T (∀⁰ φ)
  | specialize {φ : ArithmeticSemiformula ℕ 1} (t : SyntacticTerm ℒₒᵣ) :
      Proof T (∀⁰ φ) → Proof T (φ/[t])
  | induction {φ : ArithmeticSemiformula ℕ 1} : Hierarchy 𝚺 0 φ →
      Proof T (base φ) → Proof T (step φ) → Proof T (∀⁰ φ)

def toRule {T : Theory ℒₒᵣ} {φ : Proposition ℒₒᵣ} : Proof T φ → ParsonsRule.Proof T φ
  | .logical d => .logical d
  | .axiom h => .axiom h
  | .mp a b => .mp (toRule a) (toRule b)
  | .generalize a => .generalize (toRule a)
  | .specialize t a => .specialize t (toRule a)
  | .induction h a b => .induction (h.mono (by decide)) (toRule a) (toRule b)

/-- Semantic soundness under the explicitly stated bounded-induction scheme;
this contains no candidate-PRA comparison assumption. -/
theorem sound {T : Theory ℒₒᵣ} {M : Type} [Structure ℒₒᵣ M] [Nonempty M]
    (hT : M↓[ℒₒᵣ] ⊧* T)
    (hInd : ∀ (φ : ArithmeticSemiformula ℕ 1), Hierarchy 𝚺 0 φ →
      ∀ f : ℕ → M, (succInd φ).Evalf f)
    {φ : Proposition ℒₒᵣ} (p : Proof T φ) : ∀ f : ℕ → M, φ.Evalf f := by
  induction p with
  | logical d =>
      intro f
      simpa using Derivation.sound f d
  | «axiom» h =>
      intro f
      have hh := Theory.models (T := T) M h
      simpa [models_iff] using hh
  | mp a b iha ihb =>
      intro f
      have ha := iha f
      have hb := ihb f
      simp only [LogicalConnective.HomClass.map_imply] at ha
      exact ha hb
  | generalize a ih =>
      intro f
      simp only [Semiformula.eval_all]
      intro x
      have hx := ih (x :>ₙ f)
      simpa [Rewriting.free] using hx
  | specialize t a ih =>
      intro f
      have hf := ih f
      simp only [Semiformula.eval_all] at hf
      simpa using hf (t.val ![] f)
  | induction h a b iha ihb =>
      intro f
      have hi := hInd _ h f
      simp [succInd, Semiformula.eval_substs] at hi
      have hb := iha f
      have hs := ihb f
      simp [base, Semiformula.eval_substs] at hb
      simp [step, Semiformula.eval_substs] at hs
      exact hi hb hs
end DiophantineConsistency.ParsonsBoundedProof
