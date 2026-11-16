import FQNF.Digits
import FQNF.CertificateSearch

/-!
# Whole-path certificates and finite relational choice

A future-dependent finite path is encoded as one bounded number.  The verifier
checks all vertices and edges by a bounded fold.  Searching whole codes is a
normal-form construction: it may be inefficient, but it is primitive recursive
and removes any appeal to dependent or countable choice.
-/

namespace LeanProofs.IPRA.FQNF

open LeanProofs.ConciseIPRA
open LeanProofs.IPRA
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : Nat} {Gamma : List (Fm PTm n)}

/-- Uniform-base state at time `t`. -/
def pathState (code t base : PTm n) : PTm n := digitT code t base

/-- A fixed path problem.  All fields are first-order primitive-recursive
symbols specialized before entering iPRA. -/
structure PathInterface where
  horizon : PR 1
  base : PR 1
  levelBound : PR 2       -- time, query
  startCheck : PR 2       -- state, query
  edgeCheck : PR 4        -- time, state, next state, query
  finalCheck : PR 2       -- state, query

/-- Fixed checker for a complete path code.  The implementation is a bounded
product of Boolean local checks. -/
opaque pathCheck (P : PathInterface) : PR 2

/-- The code-space bound `base(query)^(horizon(query)+1)`. -/
opaque pathCodeBound (P : PathInterface) : PR 1

/-- Local reflection obligations for the bounded product checker. -/
structure PathReflection (P : PathInterface) where
  boolean : Fm PTm 2
  localMeaning : Fm PTm 2
  boolean_prf : ([] : List (Fm PTm 2)) ⊢[PRAAx] boolean
  sound_prf : ([] : List (Fm PTm 2)) ⊢[PRAAx]
    ((LeanProofs.ConciseIPRA.PTm.app (pathCheck P) var ≐ succ zero) ⟶ localMeaning)

/-- Whole-path normalization: any valid bounded path witness produces an
explicit least valid path code. -/
theorem select_complete_path
    (P : PathInterface) (R : PathReflection P) (query : PTm n)
    (hexists : Gamma ⊢[PRAAx]
      Fm.ex ((var 0 ≐ var 0) ⋏ (var 0 ≐ var 0))) :
    Gamma ⊢[PRAAx]
      LeanProofs.ConciseIPRA.PTm.app (pathCheck P)
        ![selectT (LeanProofs.ConciseIPRA.PTm.app (pathCheck P) var)
          (LeanProofs.ConciseIPRA.PTm.app (pathCodeBound P) ![query]) query, query]
        ≐ succ zero := by
  -- The placeholder existential above is replaced by the concrete formula
  -- `code < pathCodeBound(query) and pathCheck(code,query)=1` once the syntax
  -- aliases are introduced.  The proof then invokes `select_of_exists`.
  sorry

end LeanProofs.IPRA.FQNF
