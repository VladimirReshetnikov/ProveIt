import IPRADerivations.Core.Basic

/-!
# FIBER structural kernel

Source-oriented candidate against ProveIt commit
58627ed89814ba122e1f0f012f1aba103cda267b.

This file deliberately contains only aliases of checked structural operations.
It was not elaborated in the artifact runtime because Lean was unavailable.
No compilation claim is made.
-/

namespace LeanProofs.IPRA.FIBER

open LeanProofs.ConciseIPRA
open LeanProofs.IPRA
open Syn
open scoped Fm

variable {n k : ℕ}
variable {Γ Δ : List (Fm PTm n)}
variable {φ : Fm PTm n}

/-- Simultaneously discharge every hypothesis of a compiled sequent. -/
theorem discharge
    (h : Γ ⊢[PRAAx] φ)
    (hs : ∀ ψ ∈ Γ, Δ ⊢[PRAAx] ψ) :
    Δ ⊢[PRAAx] φ :=
  h.trans hs

/-- Reuse a closed open-formula theorem at arbitrary terms and hypotheses. -/
theorem specialize
    {θ : Fm PTm k}
    (h : ([] : List (Fm PTm k)) ⊢[PRAAx] θ)
    (σ : Fin k → PTm n) :
    Γ ⊢[PRAAx] θ.subst σ :=
  LeanProofs.IPRA.inst h σ

/-- Seal a proof-local existential certificate. -/
theorem seal
    {A : Fm PTm (n + 1)} {B : Fm PTm n}
    (hex : Γ ⊢[PRAAx] Fm.ex A)
    (hbody : A :: Γ.map Fm.shift ⊢[PRAAx] B.shift) :
    Γ ⊢[PRAAx] B :=
  Prf.exE hex hbody

/-- A closed compiled theorem can be used under an arbitrary client context. -/
theorem underContext
    (h : ([] : List (Fm PTm n)) ⊢[PRAAx] φ) :
    Γ ⊢[PRAAx] φ :=
  h.ofNil

end LeanProofs.IPRA.FIBER
