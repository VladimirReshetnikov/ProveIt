import ConciseIPRA.PR

/-!
# Object-language primitive-recursion wrapper

The repository already contains a source-complete theorem named
`primitiveRecursionInvariant`/`primitiveRecursionAt` in a foundation packet.
This file fixes the API to be moved into a shared PFIG library.  The two main
proofs are left as explicit targets rather than silently axiomatized.
-/

namespace LeanProofs.ConciseIPRA.PFIG.ObjectLoop

open Syn
open scoped Fm

/-- State computed by primitive recursion. -/
def runTerm {k n : Nat} (init : PR k) (step : PR (k + 2))
    (time : PTm n) (params : Fin k → PTm n) : PTm n :=
  PTm.app (.prec init step) (Fin.cases time params)

/-- Instantiate an invariant whose variables are state, time, parameters. -/
def instStateTime {k n : Nat} (P : Fm PTm (k + 2))
    (state time : PTm n) (params : Fin k → PTm n) : Fm PTm n :=
  P.subst (Fin.cases state (Fin.cases time params))

/-- Initial invariant formula. -/
def baseFormula {k : Nat} (init : PR k) (P : Fm PTm (k + 2)) :
    Fm PTm k :=
  instStateTime P (PTm.app init var) PTm.zero var

/-- One-step invariant formula; variables are state, time, parameters. -/
def nextFormula {k : Nat} (step : PR (k + 2)) (P : Fm PTm (k + 2)) :
    Fm PTm (k + 2) :=
  instStateTime P
    (PTm.app step
      (Fin.cases (var 1) (Fin.cases (var 0) (fun i => var i.succ.succ))))
    (PTm.succ (var 1)) (fun i => var i.succ.succ)

/-- Invariant at the recursively computed state and variable time. -/
def runInvariant {k : Nat} (init : PR k) (step : PR (k + 2))
    (P : Fm PTm (k + 2)) : Fm PTm (k + 1) :=
  instStateTime P
    (runTerm init step (var 0) (fun i => var i.succ))
    (var 0) (fun i => var i.succ)

/-- Main migration target.  The full proof is present in the inspected
`ipra_local_global/lean/ObjectIteration.lean` source. -/
theorem primitiveRecursionInvariant_target {k : Nat}
    (init : PR k) (step : PR (k + 2))
    (P : Fm PTm (k + 2)) (hP : P.QF)
    (Γ : List (Fm PTm k))
    (base : Γ ⊢[PRAAx] baseFormula init P)
    (preserve : P :: (Γ.map Fm.shift).map Fm.shift
      ⊢[PRAAx] nextFormula step P) :
    Γ ⊢[PRAAx] Fm.all (runInvariant init step P) := by
  sorry

/-- Specialize the invariant at a primitive-recursive fuel. -/
theorem primitiveRecursionAt_target {k : Nat}
    (init : PR k) (step : PR (k + 2))
    (P : Fm PTm (k + 2)) (hP : P.QF)
    (Γ : List (Fm PTm k))
    (base : Γ ⊢[PRAAx] baseFormula init P)
    (preserve : P :: (Γ.map Fm.shift).map Fm.shift
      ⊢[PRAAx] nextFormula step P)
    (fuel : PTm k) :
    Γ ⊢[PRAAx]
      instStateTime P (runTerm init step fuel var) fuel var := by
  sorry

/-- Source-facing loop contract. -/
structure LoopContract {k : Nat}
    (Γ : List (Fm PTm k)) (Post : Fm PTm k) where
  init : PR k
  step : PR (k + 2)
  fuel : PTm k
  invariant : Fm PTm (k + 2)
  qf : invariant.QF
  base : Γ ⊢[PRAAx] baseFormula init invariant
  preserve : invariant :: (Γ.map Fm.shift).map Fm.shift
    ⊢[PRAAx] nextFormula step invariant
  finish : Γ ⊢[PRAAx]
    instStateTime invariant (runTerm init step fuel var) fuel var ⟶ Post

/-- Once the two migration targets are filled, every loop contract produces an
actual object-iPRA theorem. -/
theorem LoopContract.sound {k : Nat}
    {Γ : List (Fm PTm k)} {Post : Fm PTm k}
    (c : LoopContract Γ Post) : Γ ⊢[PRAAx] Post := by
  exact Prf.impE c.finish
    (primitiveRecursionAt_target c.init c.step c.invariant c.qf
      Γ c.base c.preserve c.fuel)

end LeanProofs.ConciseIPRA.PFIG.ObjectLoop
