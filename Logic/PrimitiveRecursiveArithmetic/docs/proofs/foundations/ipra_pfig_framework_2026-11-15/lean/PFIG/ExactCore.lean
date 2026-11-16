import ConciseIPRA.PR

/-!
# Exact object-iPRA contracts used by the PFIG framework

This file is source-oriented and follows the interfaces inspected in the
ProveIt repository.  It contains no `sorry`, but it was not compiled in the
artifact environment.  Integration must pin the repository commit and adjust
imports if upstream module boundaries change.
-/

namespace LeanProofs.ConciseIPRA.PFIG

open Syn
open scoped Fm

/-- An exact output term with an actual object-iPRA correctness derivation. -/
structure ExactContract {n : Nat} (P : Fm PTm n) (Q : Fm PTm (n + 1)) where
  witness : PTm n
  certified : [P] ⊢[PRAAx] Q.subst (inst witness)

namespace ExactContract

variable {n : Nat} {P : Fm PTm n} {Q : Fm PTm (n + 1)}

/-- Existentially hide an exact witness. -/
theorem existsOutput (c : ExactContract P Q) :
    [P] ⊢[PRAAx] Fm.ex Q :=
  Prf.exI c.witness c.certified

/-- Close the contract as an implication. -/
theorem asImplication (c : ExactContract P Q) :
    [] ⊢[PRAAx] P ⟶ Fm.ex Q :=
  Prf.impI c.existsOutput

/-- Sequential composition by substitution and simultaneous cut. -/
def compose {R : Fm PTm (n + 2)}
    (c : ExactContract P Q) (d : ExactContract Q R) :
    ExactContract P (R.subst (up (inst c.witness))) where
  witness := Syn.subst (inst c.witness) d.witness
  certified := by
    have hd := d.certified.subst (inst c.witness)
    rw [Fm.subst_inst] at hd
    apply hd.trans
    intro ψ hψ
    simp only [List.map_cons, List.map_nil, List.mem_singleton] at hψ
    subst ψ
    exact c.certified

/-- Specialize all free input parameters. -/
def specialize {m : Nat} (c : ExactContract P Q) (σ : Fin n → PTm m) :
    ExactContract (P.subst σ) (Q.subst (up σ)) where
  witness := Syn.subst σ c.witness
  certified := by
    have h := c.certified.subst σ
    simpa only [List.map_cons, List.map_nil, Fm.subst_inst] using h

end ExactContract

/-- A loop invariant whose base and step are actual object derivations. -/
structure LoopCertificate {n : Nat} (Γ : List (Fm PTm n)) where
  invariant : Fm PTm (n + 1)
  qf : invariant.QF
  base : Γ ⊢[PRAAx] invariant.subst (inst PTm.zero)
  step : invariant :: Γ.map Fm.shift ⊢[PRAAx]
    invariant.subst (repl (PTm.succ (var 0)))

/-- Quantifier-free induction closes a loop certificate. -/
theorem LoopCertificate.conclude {n : Nat} {Γ : List (Fm PTm n)}
    (c : LoopCertificate Γ) : Γ ⊢[PRAAx] Fm.all c.invariant :=
  PRA.qfInd c.invariant c.qf c.base c.step

/-- Specialize a loop certificate at a supplied fuel term. -/
theorem LoopCertificate.at {n : Nat} {Γ : List (Fm PTm n)}
    (c : LoopCertificate Γ) (fuel : PTm n) :
    Γ ⊢[PRAAx] c.invariant.subst (inst fuel) :=
  Prf.allE fuel c.conclude

/-- Reflect a finite loop result through a terminal extraction implication. -/
theorem loopProduces
    {n : Nat} {Γ : List (Fm PTm n)}
    (c : LoopCertificate Γ) (fuel : PTm n) (C : Fm PTm n)
    (finish : Γ ⊢[PRAAx] c.invariant.subst (inst fuel) ⟶ C) :
    Γ ⊢[PRAAx] C :=
  Prf.impE finish (c.at fuel)

/-- Stable observer for independently produced certificates. -/
theorem stableObserver
    {n : Nat} {Γ : List (Fm PTm n)}
    (C₁ C₂ O : Fm PTm n)
    (h₁ : Γ ⊢[PRAAx] C₁)
    (h₂ : Γ ⊢[PRAAx] C₂)
    (stable : C₁ :: C₂ :: Γ ⊢[PRAAx] O) :
    Γ ⊢[PRAAx] O :=
  Prf.impE (Prf.impE (Prf.impI (Prf.impI stable)) h₂) h₁

/-- The k-ary stable-observer pattern is simultaneous cut. -/
theorem stableObserverMany
    {n : Nat} {Γ Δ : List (Fm PTm n)} {O : Fm PTm n}
    (local : Δ ⊢[PRAAx] O)
    (certified : ∀ A ∈ Δ, Γ ⊢[PRAAx] A) :
    Γ ⊢[PRAAx] O :=
  local.trans certified

end LeanProofs.ConciseIPRA.PFIG
