import ConciseIPRA.PR

/-!
# SCOPE-iPRA: structural kernel candidate

This file packages only structural operations of the checked ordinary iPRA
calculus.  It contains no new axiom and no placeholder proof.  It is intended
for the ProveIt workspace pinned in `metadata/SOURCE_AUDIT.md`.

The artifact runtime used for this delivery did not contain Lean, so this file
is source-oriented and has not been elaborated here.  Its theorem shapes were
matched to `ConciseIPRA/Deduction.lean` at the pinned revision.
-/

namespace LeanProofs.IPRA.SCOPE

open LeanProofs.ConciseIPRA
open Syn
open scoped Fm

variable {n m : Nat}
variable {Γ Δ : List (Fm PTm n)}
variable {A B : Fm PTm n}

/-- Move one explicit producer boundary into an implication. -/
theorem boundary (h : B :: Γ ⊢[PRAAx] A) : Γ ⊢[PRAAx] B ⟶ A :=
  .impI h

/-- Discharge one already proved producer boundary. -/
theorem discharge (hB : Γ ⊢[PRAAx] B) (hA : B :: Γ ⊢[PRAAx] A) :
    Γ ⊢[PRAAx] A :=
  .impE (.impI hA) hB

/-- Simultaneous cut: replace every local assumption by a derivation. -/
theorem replaceContext (h : Γ ⊢[PRAAx] A)
    (supply : ∀ C ∈ Γ, Δ ⊢[PRAAx] C) : Δ ⊢[PRAAx] A :=
  h.trans supply

/-- Specialize every open parameter by an arbitrary object-language term. -/
theorem specialize (h : Γ ⊢[PRAAx] A) (σ : Fin n → PTm m) :
    Γ.map (fun C => C.subst σ) ⊢[PRAAx] A.subst σ :=
  h.subst σ

/-- A proof-local certificate.  The certificate variable occurs in `valid` and
in the extractor context, but cannot occur in the outer `goal` by typing. -/
structure Contract (n : Nat) (Γ : List (Fm PTm n)) (goal : Fm PTm n) where
  valid : Fm PTm (n + 1)
  extract : valid :: Γ.map Fm.shift ⊢[PRAAx] goal.shift

namespace Contract

variable {goal : Fm PTm n} (C : Contract n Γ goal)

/-- Seal a locally existential certificate. -/
theorem close (producer : Γ ⊢[PRAAx] Fm.ex C.valid) : Γ ⊢[PRAAx] goal :=
  .exE producer C.extract

/-- If the producer is not yet known, expose exactly that producer as a
conditional theorem boundary. -/
theorem conditional : Γ ⊢[PRAAx] (Fm.ex C.valid) ⟶ goal := by
  apply Prf.impI
  apply Prf.exE Prf.hyp0
  exact C.extract.weaken (by simp)

end Contract

/-- Primitive certificate sealing without a wrapper structure. -/
theorem seal {valid : Fm PTm (n + 1)}
    (producer : Γ ⊢[PRAAx] Fm.ex valid)
    (consumer : valid :: Γ.map Fm.shift ⊢[PRAAx] A.shift) :
    Γ ⊢[PRAAx] A :=
  .exE producer consumer

/-- A closed object theorem may be reused under any local assumptions. -/
theorem reuseClosed (h : ([] : List (Fm PTm n)) ⊢[PRAAx] A) : Γ ⊢[PRAAx] A :=
  h.ofNil

end LeanProofs.IPRA.SCOPE
