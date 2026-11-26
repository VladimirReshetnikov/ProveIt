import IPRADerivations.Core.Basic
import IPRADerivations.Core.Header

/-!
# The proof-plan compiler

Packet: `foundations/scope_ipra_framework_2026-11-16_2`, `paper/sections/12_compiler.tex`, "A small indexed
plan language" and Theorem `thm:plan-soundness` ("Plan soundness"): there is a total structural function
`compile : Plan(Γ, A) → (Γ ⊢ A)`.

`Plan Γ A` is the indexed plan language of the paper, with one constructor for each node kind:

* `exact`: a stored object derivation (also the endpoint of a reflection, search or trace module);
* `specialize`: a simultaneous term substitution;
* `weaken`: an enlarged local context;
* `supply`: every assumption replaced by a plan under a new context (simultaneous cut);
* `sealed` (the paper's "seal"): a producer of `∃ c V(c)` combined with a continuation under `V(c)`;
* `boundary`: a missing producer retained as the antecedent of an implication.

`compile` (`thm:plan-soundness`) is structural recursion on the plan: `Prf.subst`, `Prf.weaken`, `Prf.trans`,
`Prf.exE` and `Prf.impI`. A scheduler or graph normalizer that emits plans is therefore never trusted: its
output is accepted exactly when it is a well-indexed plan.

`sealed_chain` is a two-certificate example: a producer of `∃ c V(c)`, a dependent producer
`V(c) ⊢ ∃ d W(c, d)` and a consumer `V(c), W(c, d) ⊢ G` compile to `Γ ⊢ G` (the dependent sealing pattern).
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Foundations.ProofPlan

open_ipra

/-- The indexed plan language. -/
inductive Plan : {n : ℕ} → List (Fm PTm n) → Fm PTm n → Type
  | exact {n : ℕ} {Γ : List (Fm PTm n)} {A : Fm PTm n} (h : Γ ⊢[PRAAx] A) : Plan Γ A
  | specialize {n m : ℕ} {Γ : List (Fm PTm n)} {A : Fm PTm n} (p : Plan Γ A) (σ : Fin n → PTm m) :
      Plan (Γ.map (fun C => C.subst σ)) (A.subst σ)
  | weaken {n : ℕ} {Γ Δ : List (Fm PTm n)} {A : Fm PTm n} (p : Plan Γ A) (s : Γ ⊆ Δ) : Plan Δ A
  | supply {n : ℕ} {Γ Δ : List (Fm PTm n)} {A : Fm PTm n} (p : Plan Γ A)
      (s : ∀ C, C ∈ Γ → Plan Δ C) : Plan Δ A
  | sealed {n : ℕ} {Γ : List (Fm PTm n)} {V : Fm PTm (n + 1)} {A : Fm PTm n}
      (producer : Plan Γ (Fm.ex V)) (consumer : Plan (V :: Γ.map Fm.shift) A.shift) : Plan Γ A
  | boundary {n : ℕ} {Γ : List (Fm PTm n)} {A B : Fm PTm n} (body : Plan (B :: Γ) A) : Plan Γ (B ⟶ A)

/-- `thm:plan-soundness`: every plan compiles to an object derivation. -/
theorem compile {n : ℕ} {Γ : List (Fm PTm n)} {A : Fm PTm n} (p : Plan Γ A) : Γ ⊢[PRAAx] A := by
  induction p with
  | exact h => exact h
  | specialize _ σ ih => exact ih.subst σ
  | weaken _ s ih => exact ih.weaken s
  | supply _ _ ih ihs => exact ih.trans ihs
  | sealed _ _ ih₁ ih₂ => exact .exE ih₁ ih₂
  | boundary _ ih => exact .impI ih

/-- A two-certificate plan: producer, dependent producer and consumer, sealed in turn. -/
def chainPlan {n : ℕ} {Γ : List (Fm PTm n)} {V : Fm PTm (n + 1)} {W : Fm PTm (n + 2)} {G : Fm PTm n}
    (h₁ : Γ ⊢[PRAAx] Fm.ex V) (h₂ : (V :: Γ.map Fm.shift) ⊢[PRAAx] Fm.ex W)
    (h₃ : (W :: (V :: Γ.map Fm.shift).map Fm.shift) ⊢[PRAAx] G.shift.shift) : Plan Γ G :=
  .sealed (.exact h₁) (.sealed (.exact h₂) (.exact h₃))

/-- The compiled two-certificate plan. -/
theorem sealed_chain {n : ℕ} {Γ : List (Fm PTm n)} {V : Fm PTm (n + 1)} {W : Fm PTm (n + 2)}
    {G : Fm PTm n} (h₁ : Γ ⊢[PRAAx] Fm.ex V) (h₂ : (V :: Γ.map Fm.shift) ⊢[PRAAx] Fm.ex W)
    (h₃ : (W :: (V :: Γ.map Fm.shift).map Fm.shift) ⊢[PRAAx] G.shift.shift) : Γ ⊢[PRAAx] G :=
  compile (chainPlan h₁ h₂ h₃)

end LeanProofs.IPRA.Foundations.ProofPlan
