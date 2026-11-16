import IPRADerivations.Core.Monus

/-! The nonzero signum term and its defining equations in ordinary iPRA. -/

set_option autoImplicit false

namespace LeanProofs.IPRA.Signum

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- `sg x = 1 ∸ (1 ∸ x)`: `0` at `0` and `1` at successors. -/
abbrev sg (x : PTm n) : PTm n := monus (succ zero) (monus (succ zero) x)

theorem sg_zero : Γ ⊢[PRAAx] sg (zero : PTm n) ≐ zero :=
  (congrMonus (.eqRefl _) (monus_zero _)).eqTrans (monus_self _)

theorem sg_succ (x : PTm n) : Γ ⊢[PRAAx] sg (succ x) ≐ succ zero :=
  (congrMonus (.eqRefl _) ((succ_monus_succ _ _).eqTrans (zero_monus _))).eqTrans (monus_zero _)

end LeanProofs.IPRA.Signum
