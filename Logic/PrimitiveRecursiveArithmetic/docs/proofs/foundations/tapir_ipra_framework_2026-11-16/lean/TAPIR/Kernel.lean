import ConciseIPRA.PR

/-!
# TAPIR: a typed macro IR for ordinary iPRA derivations

This file is intended to be copied under `IPRADerivations/Foundations/TAPIR/` in
VladimirReshetnikov/ProveIt.  It deliberately introduces no semantic evaluator
and no new axiom.  `Plan Γ φ` is an indexed proof plan, and `Plan.run` compiles
it by structural recursion to the canonical judgment `Γ ⊢[PRAAx] φ`.

Formal status in this archive: no intentional placeholders, but unelaborated
because Lean/Lake was unavailable in the build runtime.
-/

namespace LeanProofs.IPRA.TAPIR

open LeanProofs.ConciseIPRA
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

/-- A small typed macro language whose indices are the object-theory endpoint. -/
inductive Plan : {n : ℕ} → List (Fm PTm n) → Fm PTm n → Type
  | prf {n : ℕ} {Γ : List (Fm PTm n)} {φ : Fm PTm n}
      (h : Γ ⊢[PRAAx] φ) : Plan Γ φ
  | weaken {n : ℕ} {Γ Δ : List (Fm PTm n)} {φ : Fm PTm n}
      (p : Plan Γ φ) (s : Γ ⊆ Δ) : Plan Δ φ
  | subst {n m : ℕ} {Γ : List (Fm PTm n)} {φ : Fm PTm n}
      (p : Plan Γ φ) (σ : Fin n → PTm m) :
      Plan (Γ.map fun ψ => ψ.subst σ) (φ.subst σ)
  | cut {n : ℕ} {Γ Δ : List (Fm PTm n)} {φ : Fm PTm n}
      (p : Plan Γ φ) (s : ∀ ψ, ψ ∈ Γ → Plan Δ ψ) : Plan Δ φ
  | botE {n : ℕ} {Γ : List (Fm PTm n)} (φ : Fm PTm n)
      (p : Plan Γ Fm.bot) : Plan Γ φ
  | andI {n : ℕ} {Γ : List (Fm PTm n)} {φ ψ : Fm PTm n}
      (p : Plan Γ φ) (q : Plan Γ ψ) : Plan Γ (φ ⋏ ψ)
  | andE₁ {n : ℕ} {Γ : List (Fm PTm n)} {φ ψ : Fm PTm n}
      (p : Plan Γ (φ ⋏ ψ)) : Plan Γ φ
  | andE₂ {n : ℕ} {Γ : List (Fm PTm n)} {φ ψ : Fm PTm n}
      (p : Plan Γ (φ ⋏ ψ)) : Plan Γ ψ
  | orI₁ {n : ℕ} {Γ : List (Fm PTm n)} {φ ψ : Fm PTm n}
      (p : Plan Γ φ) : Plan Γ (φ ⋎ ψ)
  | orI₂ {n : ℕ} {Γ : List (Fm PTm n)} {φ ψ : Fm PTm n}
      (p : Plan Γ ψ) : Plan Γ (φ ⋎ ψ)
  | orE {n : ℕ} {Γ : List (Fm PTm n)} {φ ψ χ : Fm PTm n}
      (p : Plan Γ (φ ⋎ ψ)) (q : Plan (φ :: Γ) χ)
      (r : Plan (ψ :: Γ) χ) : Plan Γ χ
  | impI {n : ℕ} {Γ : List (Fm PTm n)} {φ ψ : Fm PTm n}
      (p : Plan (φ :: Γ) ψ) : Plan Γ (φ ⟶ ψ)
  | impE {n : ℕ} {Γ : List (Fm PTm n)} {φ ψ : Fm PTm n}
      (p : Plan Γ (φ ⟶ ψ)) (q : Plan Γ φ) : Plan Γ ψ
  | allI {n : ℕ} {Γ : List (Fm PTm n)} {φ : Fm PTm (n + 1)}
      (p : Plan (Γ.map Fm.shift) φ) : Plan Γ (Fm.all φ)
  | allE {n : ℕ} {Γ : List (Fm PTm n)} {φ : Fm PTm (n + 1)}
      (t : PTm n) (p : Plan Γ (Fm.all φ)) : Plan Γ (φ.subst (inst t))
  | exI {n : ℕ} {Γ : List (Fm PTm n)} {φ : Fm PTm (n + 1)}
      (t : PTm n) (p : Plan Γ (φ.subst (inst t))) : Plan Γ (Fm.ex φ)
  | exE {n : ℕ} {Γ : List (Fm PTm n)} {φ : Fm PTm (n + 1)}
      {ψ : Fm PTm n} (p : Plan Γ (Fm.ex φ))
      (q : Plan (φ :: Γ.map Fm.shift) ψ.shift) : Plan Γ ψ
  | eqRefl {n : ℕ} {Γ : List (Fm PTm n)} (t : PTm n) : Plan Γ (t ≐ t)
  | eqSubst {n k : ℕ} {Γ : List (Fm PTm n)}
      (φ : Fm PTm k) (σ σ' : Fin k → PTm n)
      (p : ∀ i, Plan Γ (σ i ≐ σ' i))
      (q : Plan Γ (φ.subst σ)) : Plan Γ (φ.subst σ')
  | qfInd {n : ℕ} {Γ : List (Fm PTm n)}
      (φ : Fm PTm (n + 1)) (hφ : φ.QF)
      (p0 : Plan Γ (φ.subst (inst zero)))
      (pS : Plan (φ :: Γ.map Fm.shift)
        (φ.subst (repl (succ (var 0))))) : Plan Γ (Fm.all φ)

namespace Plan

/-- Compile a typed plan to the ordinary checked derivability judgment. -/
def run : {n : ℕ} → {Γ : List (Fm PTm n)} → {φ : Fm PTm n} →
    Plan Γ φ → (Γ ⊢[PRAAx] φ)
  | _, _, _, .prf h => h
  | _, _, _, .weaken p s => (run p).weaken s
  | _, _, _, .subst p σ => (run p).subst σ
  | _, _, _, .cut p s => (run p).trans fun ψ hψ => run (s ψ hψ)
  | _, _, _, .botE φ p => .botE φ (run p)
  | _, _, _, .andI p q => .andI (run p) (run q)
  | _, _, _, .andE₁ p => .andE₁ (run p)
  | _, _, _, .andE₂ p => .andE₂ (run p)
  | _, _, _, .orI₁ p => .orI₁ (run p)
  | _, _, _, .orI₂ p => .orI₂ (run p)
  | _, _, _, .orE p q r => .orE (run p) (run q) (run r)
  | _, _, _, .impI p => .impI (run p)
  | _, _, _, .impE p q => .impE (run p) (run q)
  | _, _, _, .allI p => .allI (run p)
  | _, _, _, .allE t p => .allE t (run p)
  | _, _, _, .exI t p => .exI t (run p)
  | _, _, _, .exE p q => .exE (run p) (run q)
  | _, _, _, .eqRefl t => .eqRefl t
  | _, _, _, .eqSubst φ σ σ' p q =>
      .eqSubst φ σ σ' (fun i => run (p i)) (run q)
  | _, _, _, .qfInd φ hφ p0 pS =>
      PRA.qfInd φ hφ (run p0) (run pS)

variable {n : ℕ} {Γ Δ : List (Fm PTm n)} {φ ψ : Fm PTm n}

/-- A context member as a plan. -/
def hyp (h : φ ∈ Γ) : Plan Γ φ := .prf (.hyp h)

/-- The head hypothesis. -/
def hyp0 : Plan (φ :: Γ) φ := hyp List.mem_cons_self

/-- Use a closed plan under arbitrary hypotheses. -/
def ofNil (p : Plan ([] : List (Fm PTm n)) φ) : Plan Γ φ :=
  .weaken p (List.nil_subset _)

/-- Seal a proof-local existential witness. -/
def seal {θ : Fm PTm (n + 1)}
    (hex : Plan Γ (Fm.ex θ))
    (body : Plan (θ :: Γ.map Fm.shift) ψ.shift) : Plan Γ ψ :=
  .exE hex body

/-- Close or change a residual context by simultaneous cut. -/
def closeResiduals (p : Plan Γ φ)
    (s : ∀ χ, χ ∈ Γ → Plan Δ χ) : Plan Δ φ :=
  .cut p s

/-- The interpreter is the formal soundness theorem. -/
theorem sound (p : Plan Γ φ) : Γ ⊢[PRAAx] φ := run p

end Plan

end LeanProofs.IPRA.TAPIR
