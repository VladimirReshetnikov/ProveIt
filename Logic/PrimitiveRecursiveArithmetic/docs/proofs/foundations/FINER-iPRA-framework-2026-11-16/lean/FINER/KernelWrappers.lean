import IPRADerivations.Core.Search
import IPRADerivations.Core.Pairing

/-!
# FINER kernel wrappers

This file is intentionally tiny.  It records the checked repository interfaces
on which the FINER formalization should be based.  It contains no new generic
compiler theorem; it only packages already available structural rules.

Repository target: VladimirReshetnikov/ProveIt at
64bc0e997df6b8dbdf43f5ac9b3d9f74b4047ee5.
-/

namespace LeanProofs.IPRA.FINER

open LeanProofs.ConciseIPRA
open LeanProofs.IPRA
open Syn
open scoped Fm

variable {n : ℕ} {Γ Δ : List (Fm PTm n)} {φ : Fm PTm n}

/-- The residual hypotheses of a compiled theorem are discharged by the
ordinary simultaneous-cut theorem already present in `ConciseIPRA`. -/
theorem dischargeResiduals
    (h : Γ ⊢[PRAAx] φ)
    (hs : ∀ ψ ∈ Γ, Δ ⊢[PRAAx] ψ) :
    Δ ⊢[PRAAx] φ :=
  Prf.trans h hs

/-- A closed theorem can be used under any local context. -/
theorem reuseClosed (h : ([] : List (Fm PTm n)) ⊢[PRAAx] φ) :
    Γ ⊢[PRAAx] φ :=
  h.ofNil

/-- Specialise a closed derivation at arbitrary object-language terms and place
it under arbitrary hypotheses. -/
theorem specialiseClosed {k : ℕ} {ψ : Fm PTm k}
    (h : ([] : List (Fm PTm k)) ⊢[PRAAx] ψ)
    (σ : Fin k → PTm n) :
    Γ ⊢[PRAAx] ψ.subst σ :=
  LeanProofs.IPRA.inst h σ

end LeanProofs.IPRA.FINER
