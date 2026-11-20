import ConciseIPRA.PR

/-!
# Actual object-judgment adapters (uncompiled candidate)

API checked against ProveIt 5f3be02388442f16487d2dc5c2529961dd783d2b.
This file constructs only structural proof adapters.  It does not assert that
any of the new analytic contracts has been proved.  It has not been elaborated
in the delivery environment; run it inside the pinned repository.
-/

namespace ContinuousIPRA

open LeanProofs.ConciseIPRA
open Syn
open scoped Fm

structure CompiledContract (n : Nat) where
  premises : List (Fm PTm n)
  conclusion : Fm PTm n
  derivation : Prf PRAAx premises conclusion

namespace CompiledContract

def specialize {n m : Nat} (c : CompiledContract n)
    (σ : Fin n → PTm m) : CompiledContract m where
  premises := c.premises.map (fun φ => φ.subst σ)
  conclusion := c.conclusion.subst σ
  derivation := c.derivation.subst σ

def discharge {n : Nat} (c : CompiledContract n) (Γ : List (Fm PTm n))
    (supplied : ∀ ψ ∈ c.premises, Prf PRAAx Γ ψ) : CompiledContract n where
  premises := Γ
  conclusion := c.conclusion
  derivation := c.derivation.trans supplied

def closed {n : Nat} (c : CompiledContract n)
    (supplied : ∀ ψ ∈ c.premises, Prf PRAAx [] ψ) :
    Prf PRAAx [] c.conclusion :=
  c.derivation.trans supplied

end CompiledContract

/-- Fixed-function contract composition; both local derivations are required. -/
theorem contract_compose {n : Nat} {Γ : List (Fm PTm n)}
    {input middle output : Fm PTm n}
    (h₁ : Prf PRAAx Γ (input ⟶ middle))
    (h₂ : Prf PRAAx Γ (middle ⟶ output)) :
    Prf PRAAx Γ (input ⟶ output) :=
  Prf.impTrans h₁ h₂

/-- Combining two delivered observations keeps their real proof objects. -/
theorem combine_observations {n : Nat} {Γ : List (Fm PTm n)}
    {φ ψ : Fm PTm n}
    (hφ : Prf PRAAx Γ φ) (hψ : Prf PRAAx Γ ψ) :
    Prf PRAAx Γ (φ ⋏ ψ) :=
  Prf.andI hφ hψ

end ContinuousIPRA
