import ConciseIPRA.PR
import ConciseIPRA.NativeBiInterpretation

/-!
# Main application targets for the unified framework

STATUS: declarations and implementation roadmap only.  No theorem below should
be cited as completed until its `sorry` is replaced, built in the pinned
ProveIt workspace, and audited with `#print axioms`.
-/

set_option autoImplicit false

namespace LeanProofs.ConciseIPRA.FinitaryTargets

open Syn
open scoped Fm
open PTm (app zero succ)

/-- A fixed evaluator for a rational name, together with its domain and
regularity formulas.  The concrete rational coding is deliberately postponed
to the shared code module. -/
structure RegularNameSchema where
  params : Nat
  eval : PR (params + 1)
  domFm : Fm PTm params
  regularFm : Fm PTm params

/-- Target: guarded addition of regular names. -/
theorem regularName_add_target : True := by
  /-
  Define a constant-shifted evaluator, instantiate only the four input samples
  needed at a fixed pair of output precisions, prove the rational triangle
  inequality, then universally introduce the precisions.
  -/
  trivial

/-- Target: guarded multiplication with an explicit magnitude certificate. -/
theorem regularName_mul_target : True := by
  trivial

/-- Target: totalized reciprocal under a positive rational apartness bound. -/
theorem regularName_inv_of_apart_target : True := by
  trivial

/-- Target: finite-net transfer from grid inequalities to a represented domain. -/
theorem finiteNet_transfer_target : True := by
  /-
  Inputs: a finite net list, a Boolean coverage certificate, a modulus, and
  pointwise grid checks.  Output: the exact first-order fixed-precision global
  inequality.  The proof uses bounded search for a covering point.
  -/
  trivial

/-- Target: complete bounded enumeration from a height certificate. -/
theorem heightBound_completeList_target : True := by
  trivial

/-- Target: recover a height bound from a complete finite list. -/
theorem completeList_heightBound_target : True := by
  trivial

/-- The final transport pattern; use only after constructing `h`. -/
def exportFinishedProof {n : Nat} {Gamma : List (Fm PTm n)} {phi : Fm PTm n}
    (h : Gamma ⊢[PRAAx] phi) :
    NPrf (Gamma.map NFm.ofPRA) (NFm.ofPRA phi) :=
  (pra_iff_native).mp h

end LeanProofs.ConciseIPRA.FinitaryTargets
