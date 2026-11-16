import ConciseIPRA.PR

/-!
# STRIVE-iPRA: structural kernel

This file is intended to live in the ProveIt Lean workspace.  It uses only the
ordinary checked interface `Prf PRAAx`.  The statements package the structural
moves needed by the larger compiler: boundary introduction/discharge,
simultaneous cut, specialization, and existential sealing of proof-local
certificates.

The source contains no placeholder proofs.  It was source-audited against
ProveIt commit `58627ed89814ba122e1f0f012f1aba103cda267b`, but was not
elaborated in the artifact runtime because Lean was unavailable.  Consequently
this packet does not claim a new kernel-checked theorem.
-/

namespace LeanProofs.IPRA.STRIVE

open LeanProofs.ConciseIPRA
open Syn
open scoped Fm

variable {n m : ℕ}
variable {Γ Δ : List (Fm PTm n)}
variable {A B : Fm PTm n}

/-- Turn a derivation under one local boundary into a conditional endpoint. -/
theorem boundary (h : B :: Γ ⊢[PRAAx] A) : Γ ⊢[PRAAx] B ⟶ A :=
  .impI h

/-- Discharge one boundary for which a producer has already been proved. -/
theorem discharge (hB : Γ ⊢[PRAAx] B) (hA : B :: Γ ⊢[PRAAx] A) :
    Γ ⊢[PRAAx] A :=
  .impE (.impI hA) hB

/-- Replace every local assumption by a derivation of that assumption. -/
theorem replaceContext (h : Γ ⊢[PRAAx] A)
    (supply : ∀ C ∈ Γ, Δ ⊢[PRAAx] C) : Δ ⊢[PRAAx] A :=
  h.trans supply

/-- Specialize all free query parameters by arbitrary iPRA terms. -/
theorem specialize (h : Γ ⊢[PRAAx] A) (σ : Fin n → PTm m) :
    Γ.map (fun C => C.subst σ) ⊢[PRAAx] A.subst σ :=
  h.subst σ

/-- A proof-local certificate.  `valid` is in the scope extended by the
certificate variable; `goal` is deliberately outside that scope. -/
structure LocalContract (n : ℕ) (Γ : List (Fm PTm n)) (goal : Fm PTm n) where
  valid : Fm PTm (n + 1)
  consume : valid :: Γ.map Fm.shift ⊢[PRAAx] goal.shift

namespace LocalContract

variable {goal : Fm PTm n} (C : LocalContract n Γ goal)

/-- Seal a producer and consumer.  The witness cannot escape into `goal`. -/
theorem close (producer : Γ ⊢[PRAAx] Fm.ex C.valid) : Γ ⊢[PRAAx] goal :=
  .exE producer C.consume

/-- Keep a missing producer as one exact residual boundary formula. -/
theorem conditional : Γ ⊢[PRAAx] (Fm.ex C.valid) ⟶ goal := by
  apply Prf.impI
  apply Prf.exE Prf.hyp0
  exact C.consume.weaken (by simp)

end LocalContract

/-- Primitive certificate sealing without a wrapper structure. -/
theorem seal {valid : Fm PTm (n + 1)}
    (producer : Γ ⊢[PRAAx] Fm.ex valid)
    (consumer : valid :: Γ.map Fm.shift ⊢[PRAAx] A.shift) :
    Γ ⊢[PRAAx] A :=
  .exE producer consumer

/-- Reuse a closed result under an arbitrary local contract context. -/
theorem reuseClosed (h : ([] : List (Fm PTm n)) ⊢[PRAAx] A) : Γ ⊢[PRAAx] A :=
  h.ofNil

/-- A compiled contract graph is already an ordinary open derivation.  This
wrapper records the exact residual list rather than hiding it in metadata. -/
structure CompiledContract (n : ℕ) where
  residuals : List (Fm PTm n)
  goal : Fm PTm n
  proof : residuals ⊢[PRAAx] goal

namespace CompiledContract

/-- Close a compiled graph once every residual producer is supplied. -/
theorem close (C : CompiledContract n)
    (supply : ∀ R ∈ C.residuals, ([] : List (Fm PTm n)) ⊢[PRAAx] R) :
    ([] : List (Fm PTm n)) ⊢[PRAAx] C.goal :=
  C.proof.trans supply

/-- Specialize a compiled graph while retaining its residual boundary. -/
def specialize (C : CompiledContract n) (σ : Fin n → PTm m) : CompiledContract m where
  residuals := C.residuals.map (fun R => R.subst σ)
  goal := C.goal.subst σ
  proof := C.proof.subst σ

end CompiledContract

end LeanProofs.IPRA.STRIVE
