import ConciseIPRA.PR

/-!
# SCOPE-iPRA structural kernel

Source-level candidate for the small part of SCOPE that is purely structural.
It is written against the current ordinary object-theory interface
`Prf PRAAx`.  It contains no `sorry`, no `axiom`, and no semantic replacement
for an object derivation.  It was source-audited against ProveIt main commit
`58627ed89814ba122e1f0f012f1aba103cda267b`, but it was not elaborated in this
artifact runtime because the ProveIt Lean workspace was not available locally.

The larger compiler is intentionally kept in blueprint files.  This file only
packages natural-deduction operations already present in ConciseIPRA:
substitution, weakening, simultaneous cut, implication discharge, and
existential elimination.
-/

namespace LeanProofs.IPRA.SCOPE

open LeanProofs.ConciseIPRA
open Syn
open scoped Fm

variable {n m : ℕ}
variable {Γ Δ R : List (Fm PTm n)}
variable {A B : Fm PTm n}

/-- Turn a derivation from one explicit boundary into a conditional theorem. -/
theorem boundary (h : B :: Γ ⊢[PRAAx] A) : Γ ⊢[PRAAx] B ⟶ A :=
  .impI h

/-- Discharge one boundary whose producer has already been proved. -/
theorem discharge (hB : Γ ⊢[PRAAx] B) (hA : B :: Γ ⊢[PRAAx] A) :
    Γ ⊢[PRAAx] A :=
  .impE (.impI hA) hB

/-- Replace each assumption by an object-theory derivation of it. -/
theorem replaceContext (h : Γ ⊢[PRAAx] A)
    (supply : ∀ C ∈ Γ, Δ ⊢[PRAAx] C) : Δ ⊢[PRAAx] A :=
  h.trans supply

/-- Specialize all free query parameters by arbitrary iPRA terms. -/
theorem specialize (h : Γ ⊢[PRAAx] A) (σ : Fin n → PTm m) :
    Γ.map (fun C => C.subst σ) ⊢[PRAAx] A.subst σ :=
  h.subst σ

/-- A result with a list of exact producer residuals. -/
structure ResidualResult (n : ℕ) (Γ : List (Fm PTm n)) (goal : Fm PTm n) where
  residuals : List (Fm PTm n)
  derivation : residuals ++ Γ ⊢[PRAAx] goal

namespace ResidualResult

variable {goal : Fm PTm n} (C : ResidualResult n Γ goal)

/-- Close every residual by simultaneous cut. -/
theorem close (supply : ∀ B ∈ C.residuals, Γ ⊢[PRAAx] B) :
    Γ ⊢[PRAAx] goal :=
  C.derivation.trans (by
    intro B hB
    rcases List.mem_append.mp hB with hR | hΓ
    · exact supply B hR
    · exact Prf.hyp hΓ)

/-- Reuse a residual theorem under a larger ambient context. -/
theorem weakenAmbient {Δ : List (Fm PTm n)} (hΓ : Γ ⊆ Δ) :
    C.residuals ++ Δ ⊢[PRAAx] goal :=
  C.derivation.weaken (by
    intro B hB
    rcases List.mem_append.mp hB with hR | hΓmem
    · exact List.mem_append_left _ hR
    · exact List.mem_append_right _ (hΓ hΓmem))

end ResidualResult

/-- A proof-local certificate.  Its witness is scoped under one existential,
while the public goal lives in the outer scope and therefore cannot mention
that witness. -/
structure Contract (n : ℕ) (Γ : List (Fm PTm n)) (goal : Fm PTm n) where
  valid : Fm PTm (n + 1)
  extract : valid :: Γ.map Fm.shift ⊢[PRAAx] goal.shift

namespace Contract

variable {goal : Fm PTm n} (C : Contract n Γ goal)

/-- Seal a producer and consumer.  This is certificate escape mode `private`. -/
theorem close (producer : Γ ⊢[PRAAx] Fm.ex C.valid) : Γ ⊢[PRAAx] goal :=
  .exE producer C.extract

/-- Keep a missing producer visible as an exact residual boundary. -/
theorem conditional : Γ ⊢[PRAAx] (Fm.ex C.valid) ⟶ goal := by
  apply Prf.impI
  apply Prf.exE Prf.hyp0
  exact C.extract.weaken (by simp)

end Contract

/-- Primitive certificate sealing, exposed without the `Contract` wrapper. -/
theorem seal {valid : Fm PTm (n + 1)}
    (producer : Γ ⊢[PRAAx] Fm.ex valid)
    (consumer : valid :: Γ.map Fm.shift ⊢[PRAAx] A.shift) :
    Γ ⊢[PRAAx] A :=
  .exE producer consumer

/-- A closed derivation is reusable under any local contract context. -/
theorem reuseClosed (h : ([] : List (Fm PTm n)) ⊢[PRAAx] A) : Γ ⊢[PRAAx] A :=
  h.ofNil

end LeanProofs.IPRA.SCOPE
