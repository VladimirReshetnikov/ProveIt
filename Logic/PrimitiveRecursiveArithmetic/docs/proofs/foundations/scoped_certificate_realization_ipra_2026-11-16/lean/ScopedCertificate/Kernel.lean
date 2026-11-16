import ConciseIPRA.PR

/-!
# Scoped Certificate Realization: structural kernel

This file is intended to live in the ProveIt Lean workspace.  It uses only the
checked ordinary iPRA interface `Prf PRAAx` and packages the structural steps
on which the SCR framework rests.  There are no new axioms and no placeholder
proofs in this file.  It was source-audited against ProveIt commit
`f444b76e8480ebea128c15b4a59f158e14f478cc`, but it was not elaborated in the
artifact runtime because that runtime had no Lean executable.
-/

namespace LeanProofs.IPRA.ScopedCertificate

open LeanProofs.ConciseIPRA
open Syn
open scoped Fm

variable {n m : ℕ}
variable {Γ Δ : List (Fm PTm n)}
variable {A B : Fm PTm n}

/-- Turn a local derivation from a boundary into the corresponding conditional
 theorem. -/
theorem boundary (h : B :: Γ ⊢[PRAAx] A) : Γ ⊢[PRAAx] B ⟶ A :=
  .impI h

/-- Discharge one already-proved boundary. -/
theorem discharge (hB : Γ ⊢[PRAAx] B) (hA : B :: Γ ⊢[PRAAx] A) :
    Γ ⊢[PRAAx] A :=
  .impE (.impI hA) hB

/-- Replace every local assumption by a derivation of it.  This is the SCR
 composition operation for proof-only nodes. -/
theorem replaceContext (h : Γ ⊢[PRAAx] A)
    (supply : ∀ C ∈ Γ, Δ ⊢[PRAAx] C) : Δ ⊢[PRAAx] A :=
  h.trans supply

/-- Specialize every free query parameter by an arbitrary iPRA term. -/
theorem specialize (h : Γ ⊢[PRAAx] A) (σ : Fin n → PTm m) :
    Γ.map (fun C => C.subst σ) ⊢[PRAAx] A.subst σ :=
  h.subst σ

/-- A certificate contract whose witness is scoped under one existential. -/
structure Contract (n : ℕ) (Γ : List (Fm PTm n)) (goal : Fm PTm n) where
  valid : Fm PTm (n + 1)
  extract : valid :: Γ.map Fm.shift ⊢[PRAAx] goal.shift

namespace Contract

variable {goal : Fm PTm n} (C : Contract n Γ goal)

/-- Seal a producer and a consumer.  The certificate cannot occur in `goal`,
 because `goal` is in the outer scope. -/
theorem close (producer : Γ ⊢[PRAAx] Fm.ex C.valid) : Γ ⊢[PRAAx] goal :=
  .exE producer C.extract

/-- Keep a missing producer as one exact boundary formula. -/
theorem conditional : Γ ⊢[PRAAx] (Fm.ex C.valid) ⟶ goal := by
  apply Prf.impI
  apply Prf.exE Prf.hyp0
  exact C.extract.weaken (by simp)

end Contract

/-- The primitive form of certificate sealing, exposed without a structure. -/
theorem seal {valid : Fm PTm (n + 1)}
    (producer : Γ ⊢[PRAAx] Fm.ex valid)
    (consumer : valid :: Γ.map Fm.shift ⊢[PRAAx] A.shift) :
    Γ ⊢[PRAAx] A :=
  .exE producer consumer

/-- A closed result can be reused under an arbitrary local contract context. -/
theorem reuseClosed (h : ([] : List (Fm PTm n)) ⊢[PRAAx] A) : Γ ⊢[PRAAx] A :=
  h.ofNil

end LeanProofs.IPRA.ScopedCertificate
