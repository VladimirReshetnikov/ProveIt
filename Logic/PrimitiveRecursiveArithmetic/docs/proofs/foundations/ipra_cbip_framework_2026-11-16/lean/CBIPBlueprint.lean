/-!
# CBIP semantic and object-language blueprint

This file is intentionally a design document in Lean syntax.  It contains
executable host-level data structures and the exact shapes of the object-level
packages to be implemented.  It does not claim to be an object-iPRA proof.
There are no hidden axioms or placeholder theorems: unfinished proof targets
are recorded in comments and in proof-carrying structure fields.
-/

import ConciseIPRA.PR

set_option autoImplicit false

namespace LeanProofs.ConciseIPRA.CBIPBlueprint

open Syn
open scoped Fm

/-! ## Executable semantic layer -/

structure TraceMachine where
  good   : Nat -> Bool
  init   : Nat -> Nat
  bound  : Nat -> Nat
  step   : Nat -> Nat -> Nat -> Nat
  inv    : Nat -> Nat -> Nat -> Bool
  accept : Nat -> Nat -> Bool

def TraceMachine.run (T : TraceMachine) (u : Nat) : Nat -> Nat
  | 0 => T.init u
  | i + 1 => T.step i (T.run u i) u

structure EvidenceMachine where
  start       : Nat -> Nat
  answerBound : Nat -> Nat -> Nat -> Nat
  halt        : Nat -> Nat -> Nat -> Bool
  local       : Nat -> Nat -> Nat -> Nat -> Bool
  next        : Nat -> Nat -> Nat -> Nat -> Nat
  post        : Nat -> Nat -> Nat -> Bool

private def anyBelow (n : Nat) (p : Nat -> Bool) : Bool :=
  (List.range n).any p

/-- Backward finite-horizon viability. -/
def viable (M : EvidenceMachine) (x : Nat) : Nat -> Nat -> Bool
  | 0, s => M.halt x 0 s && M.post x 0 s
  | r + 1, s =>
      if M.halt x (r + 1) s then M.post x (r + 1) s
      else anyBelow (M.answerBound x (r + 1) s) (fun a =>
        M.local x (r + 1) s a && viable M x r (M.next x (r + 1) s a))

inductive BForm where
  | atom   (test : List Nat -> Bool)
  | conj   (p q : BForm)
  | disj   (p q : BForm)
  | exists (bound : List Nat -> Nat) (body : BForm)
  | forall (bound : List Nat -> Nat) (body : BForm)

/-- Boolean game value for a fixed bounded formula. -/
def BForm.value : BForm -> List Nat -> Bool
  | .atom p, env => p env
  | .conj p q, env => p.value env && q.value env
  | .disj p q, env => p.value env || q.value env
  | .exists b p, env => (List.range (b env)).any (fun i => p.value (i :: env))
  | .forall b p, env => (List.range (b env)).all (fun i => p.value (i :: env))

/-! ## Object-language package shapes

The first implementation should not internalize arbitrary host functions.
Each field below is replaced by a concrete fixed `PR` symbol generated for one
fixed program or formula.
-/

/-- Fixed object-language data for a relational finite-horizon machine. -/
structure PRRelMachine where
  start       : PR 1
  answerBound : PR 3   -- input, remaining resource, state
  halt        : PR 3
  local       : PR 4   -- input, resource, state, answer
  next        : PR 4
  post        : PR 3
  stateBound  : PR 2   -- input, horizon

/-- Metadata separating theorem status from proof data.  This structure is not
itself evidence for any theorem. -/
structure PacketStatus where
  fixedEvaluators      : Bool
  finiteBounds         : Bool
  certificateChecker   : Bool
  humanSoundnessProof : Bool
  executableTestsRun   : Bool
  objectDerivation     : Bool
  nativeExport         : Bool
  axiomAuditRun        : Bool
  unresolvedProducer  : Option String

/-!
## Required object-level theorems

Implement these in dependency order, with every conclusion an actual
`Prf PRAAx` derivation.

1. Boolean folds and least search:
   * `allBelow_succ_elim_left`
   * `allBelow_succ_elim_last`
   * `allBelow_succ_intro`
   * dual `anyBelow` lemmas
   * least-success soundness and minimality

2. Fixed bounded game, generated per `BForm`:
   * canonical certificate checks
   * `checkWin -> positiveFormula`
   * `checkLose -> not positiveFormula`

3. Rectangular viability table:
   * row recurrence
   * `viable = 1 <-> boundedSuccessfulTranscript`
   * least viable answer is local and has viable successor
   * forward replay terminates with `post = 1`

4. Stable observation:
   * two successful terminal states imply the requested equivalence or
     diameter inequality
   * selected output satisfies the quotient/approximate conclusion

5. CBIP compiler:
   * structural normalization to `PRTraceSystem`
   * construction of `NormalizedTraceProofs`
   * call `traceReflectionNormalized`

No theorem above should use `pra_iff_native` until the ordinary `Prf PRAAx`
derivation has been completed.
-/

end LeanProofs.ConciseIPRA.CBIPBlueprint
