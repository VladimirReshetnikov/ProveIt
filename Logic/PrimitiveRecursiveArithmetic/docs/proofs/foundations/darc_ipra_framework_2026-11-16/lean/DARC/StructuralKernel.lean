import IPRADerivations.Core.Search

/-!
# DARC structural kernel

Source-oriented wrappers around the current ordinary iPRA interface.  This
file intentionally introduces no axiom and contains no placeholder.  It was
written against ProveIt commit
`2ef31aa3e313d792df6b63bb28babfe48e1f982e`; it was not elaborated in the
artifact runtime because no Lean executable was available there.
-/

namespace LeanProofs.IPRA.DARC

open LeanProofs.ConciseIPRA
open LeanProofs.IPRA
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n m k : ℕ}
variable {Γ Δ : List (Fm PTm n)}
variable {A B : Fm PTm n}

/-- A context-polymorphic contract.  Supplying every formula in `Γ` in any
ambient context supplies `A` there. -/
def OpenContract (Γ : List (Fm PTm n)) (A : Fm PTm n) : Prop :=
  ∀ (Δ : List (Fm PTm n)), (∀ C ∈ Γ, Δ ⊢[PRAAx] C) → Δ ⊢[PRAAx] A

/-- Open contracts are exactly ordinary sequents. -/
theorem openContract_iff : OpenContract Γ A ↔ Γ ⊢[PRAAx] A := by
  constructor
  · intro h
    exact h Γ (fun C hC => .hyp hC)
  · intro h Δ supply
    exact h.trans supply

/-- Simultaneous replacement of all contract assumptions. -/
theorem replaceContext (h : Γ ⊢[PRAAx] A)
    (supply : ∀ C ∈ Γ, Δ ⊢[PRAAx] C) : Δ ⊢[PRAAx] A :=
  h.trans supply

/-- Query specialization by arbitrary terms. -/
theorem specialize (h : Γ ⊢[PRAAx] A) (σ : Fin n → PTm m) :
    Γ.map (fun C => C.subst σ) ⊢[PRAAx] A.subst σ :=
  h.subst σ

/-- A proof-local certificate.  The certificate variable is scoped inside
`valid`; the public conclusion lives in the outer scope and therefore cannot
mention it. -/
structure ScopedCertificate (n : ℕ) (Γ : List (Fm PTm n)) (goal : Fm PTm n) where
  valid : Fm PTm (n + 1)
  consume : valid :: Γ.map Fm.shift ⊢[PRAAx] goal.shift

namespace ScopedCertificate

variable {goal : Fm PTm n} (C : ScopedCertificate n Γ goal)

/-- Seal a local producer and consumer by existential elimination. -/
theorem seal (producer : Γ ⊢[PRAAx] Fm.ex C.valid) : Γ ⊢[PRAAx] goal :=
  .exE producer C.consume

/-- Leave a missing producer as one exact boundary formula. -/
theorem conditional : Γ ⊢[PRAAx] (Fm.ex C.valid) ⟶ goal := by
  apply Prf.impI
  apply Prf.exE Prf.hyp0
  exact C.consume.weaken (by simp)

end ScopedCertificate

/-- Primitive certificate sealing, without the wrapper structure. -/
theorem seal {valid : Fm PTm (n + 1)}
    (producer : Γ ⊢[PRAAx] Fm.ex valid)
    (consumer : valid :: Γ.map Fm.shift ⊢[PRAAx] A.shift) :
    Γ ⊢[PRAAx] A :=
  .exE producer consumer

/-- The checked bounded-search theorem, exposed as the named-certificate
export operation used by DARC. -/
theorem nameLeast {f : PTm 2} {N i x : PTm n}
    (found : Γ ⊢[PRAAx] inst2 f i x ≐ zero)
    (below : Γ ⊢[PRAAx] lt i N) :
    Γ ⊢[PRAAx]
      lt (Search.mu f N x) N ⋏
        ((inst2 f (Search.mu f N x) x ≐ zero) ⋏ le (Search.mu f N x) i) :=
  Search.search_found found below

/-- Data sufficient for one quantifier-free induction loop. -/
structure QFLoop (k : ℕ) where
  invariant : Fm PTm (k + 1)
  qf : invariant.QF
  base : ([] : List (Fm PTm k)) ⊢[PRAAx] invariant.subst (Syn.inst zero)
  step : [invariant] ⊢[PRAAx]
    invariant.subst (repl (succ (var 0)))

namespace QFLoop

/-- Reflect a normalized bounded loop by ordinary iPRA induction. -/
theorem run (L : QFLoop k) :
    ([] : List (Fm PTm (k + 1))) ⊢[PRAAx] L.invariant :=
  IPRA.ind L.invariant L.qf L.base L.step

end QFLoop

/-- A closed compiled theorem may be reused under any local assumptions. -/
theorem reuseClosed (h : ([] : List (Fm PTm n)) ⊢[PRAAx] A) : Γ ⊢[PRAAx] A :=
  h.ofNil

end LeanProofs.IPRA.DARC
