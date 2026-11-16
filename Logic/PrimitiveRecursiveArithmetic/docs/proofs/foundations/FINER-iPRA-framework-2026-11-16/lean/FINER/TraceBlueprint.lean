import FINER.BooleanReflectionBlueprint
import IPRADerivations.Core.Definitions

/-!
# One-induction trace reflection

A theorem-specific iterator first substitutes its state term into a fixed
bounded invariant and Boolean-reflects that invariant.  The resulting formula
`inv : Fm PTm 1` has only the clock variable free and is quantifier-free.
The checked open-induction wrapper then proves it for an arbitrary clock.

This source is intended to be close to the final generic kernel, but it has not
been elaborated in this artifact environment.
-/

namespace LeanProofs.IPRA.FINER

open LeanProofs.ConciseIPRA
open LeanProofs.IPRA
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

/-- The local data needed by ordinary open quantifier-free induction.  Any
state recursor and parameters have already been substituted into `inv`. -/
structure TraceSystem where
  inv : Fm PTm 1
  invQF : inv.QF
  base : ([] : List (Fm PTm 0)) ⊢[PRAAx]
    inv.subst ![(zero : PTm 0)]
  step : [inv] ⊢[PRAAx]
    inv.subst ![succ (var 0)]

/-- Open invariant, retaining the clock as an object-language variable. -/
theorem trace_open (S : TraceSystem) :
    ([] : List (Fm PTm 1)) ⊢[PRAAx] S.inv :=
  ind S.inv S.invQF S.base S.step

/-- Specialise the checked open invariant at an arbitrary clock term and under
an arbitrary local context. -/
theorem trace_at (S : TraceSystem) {n : ℕ}
    {Γ : List (Fm PTm n)} (T : PTm n) :
    Γ ⊢[PRAAx] S.inv.subst ![T] :=
  inst (trace_open S) ![T]

/-- Compose a terminal consequence with trace reflection. -/
theorem trace_finish (S : TraceSystem) {n : ℕ}
    {Γ : List (Fm PTm n)} (T : PTm n) {goal : Fm PTm n}
    (finish : S.inv.subst ![T] :: Γ ⊢[PRAAx] goal) :
    Γ ⊢[PRAAx] goal := by
  apply Prf.trans finish
  intro ψ hψ
  simp only [List.mem_cons] at hψ
  rcases hψ with rfl | htail
  · exact trace_at S T
  · exact Prf.hyp htail

end LeanProofs.IPRA.FINER
