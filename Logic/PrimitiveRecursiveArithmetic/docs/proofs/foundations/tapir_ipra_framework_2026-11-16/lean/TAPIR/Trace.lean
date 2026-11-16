import IPRADerivations.Foundations.TAPIR.Kernel
import IPRADerivations.Core.Definitions
import IPRADerivations.Foundations.Termination

/-!
# Clocked traces (formalization blueprint)

The checked repository already has the induction and termination theorems.
This file records the thin TAPIR wrappers and suggested state combinators.
-/

namespace LeanProofs.IPRA.TAPIR

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

/-- The generic invariant theorem is the existing open induction wrapper. -/
theorem traceInvariant {k : ℕ} (I : Fm PTm (k + 1)) (hI : I.QF)
    (h0 : ([] : List (Fm PTm k)) ⊢[PRAAx] I.subst (inst zero))
    (hS : [I] ⊢[PRAAx] I.subst (repl (succ (var 0)))) :
    ([] : List (Fm PTm (k + 1))) ⊢[PRAAx] I := by
  exact IPRA.ind I hI h0 hS

/-- Plan-level form of quantifier-free trace induction. -/
def Plan.traceInd {n : ℕ} {Γ : List (Fm PTm n)}
    (I : Fm PTm (n + 1)) (hI : I.QF)
    (p0 : Plan Γ (I.subst (inst zero)))
    (pS : Plan (I :: Γ.map Fm.shift)
      (I.subst (repl (succ (var 0))))) :
    Plan Γ (Fm.all I) :=
  .qfInd I hI p0 pS

/-- A trace symbol from a base term and step term. -/
def traceF {k : ℕ} (base : PTm k) (step : PTm (k + 2)) : PR (k + 1) :=
  recDef base step

/-- Suggested failure-accumulator update.  This definition is intentionally
left theorem-specific until a shared sign/complement API is selected. -/
def failureStep {n : ℕ} (old ok : PTm n) : PTm n :=
  LeanProofs.IPRA.Algebra.CubeRootTwo.sg
    (old + LeanProofs.IPRA.PTm.monus (succ zero) ok)

/-- Target equations and reflection theorem for `failureStep`. -/
theorem failureStep_spec {n : ℕ} {Γ : List (Fm PTm n)}
    (old ok : PTm n) :
    Γ ⊢[PRAAx]
      (failureStep old ok ≐ zero) ⟷
      ((old ≐ zero) ⋏ (ok ≐ succ zero)) := by
  /- The repository's formula language encodes iff as a conjunction of
     implications; use bit cases for `old` and `ok`. -/
  sorry

end LeanProofs.IPRA.TAPIR
