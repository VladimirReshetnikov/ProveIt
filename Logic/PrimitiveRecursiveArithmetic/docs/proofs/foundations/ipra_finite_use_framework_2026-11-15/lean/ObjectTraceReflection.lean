import ConciseIPRA.NativeBiInterpretation

/-!
# Generic object-iPRA trace-reflection wrapper

This file is written against the inspected ProveIt `ConciseIPRA` API.  It
implements the uniform induction/cut/universal-closure layer once a concrete
trace module supplies already-normalized base, step, and finish derivations.

The artifact environment did not contain Lean or the repository dependency
closure, so this source is NOT claimed compiler-checked.  The likely remaining
work is limited to elaboration of finite argument functions and simp
normalization of the bound substitution; see `FORMALIZATION_PLAN.md`.
-/

namespace LeanProofs.ConciseIPRA.FiniteUse

open Syn
open scoped Fm

/-- Numeral one in the ordinary iPRA term language. -/
def one {n : Nat} : PTm n := PTm.succ PTm.zero

/-- Fixed-arity application helpers. -/
def app1 {n : Nat} (f : PR 1) (x : PTm n) : PTm n :=
  PTm.app f (fun _ : Fin 1 => x)

def app2 {n : Nat} (f : PR 2) (x y : PTm n) : PTm n :=
  PTm.app f (Fin.cases x (fun _ : Fin 1 => y))

def app3 {n : Nat} (f : PR 3) (x y z : PTm n) : PTm n :=
  PTm.app f (Fin.cases x (Fin.cases y (fun _ : Fin 1 => z)))

/-- Fixed primitive-recursive symbols for a one-parameter bounded trace. -/
structure PRTraceSystem where
  good   : PR 1
  init   : PR 1
  bound  : PR 1
  step   : PR 3
  inv    : PR 3
  accept : PR 2

/-- The recursion argument is first; the single ordinary parameter is second. -/
def PRTraceSystem.run (T : PRTraceSystem) : PR 2 :=
  .prec T.init T.step

namespace PRTraceSystem

variable (T : PRTraceSystem)

/-- `Good(u)`. -/
def goodTerm {n : Nat} (u : PTm n) : PTm n := app1 T.good u

/-- `bound(u)`. -/
def boundTerm {n : Nat} (u : PTm n) : PTm n := app1 T.bound u

/-- `Run(i,u)`. -/
def runTerm {n : Nat} (i u : PTm n) : PTm n := app2 T.run i u

/-- `Inv(i,s,u)`. -/
def invTerm {n : Nat} (i s u : PTm n) : PTm n := app3 T.inv i s u

/-- `Accept(s,u)`. -/
def acceptTerm {n : Nat} (s u : PTm n) : PTm n := app2 T.accept s u

/-- Free variable 0 is the induction counter; free variable 1 is the input. -/
def tracePhi : Fm PTm 2 :=
  (T.goodTerm (Syn.var 1) ≐ one) ⟶
    (T.invTerm (Syn.var 0)
      (T.runTerm (Syn.var 0) (Syn.var 1))
      (Syn.var 1) ≐ one)

/-- The trace invariant is syntactically quantifier free. -/
theorem tracePhi_qf : T.tracePhi.QF := by
  trivial

/-- The computed bound, in a context containing only the input variable. -/
def boundAtInput : PTm 1 := T.boundTerm (Syn.var 0)

/-- The induction formula specialized at the computed bound. -/
def phiAtBound : Fm PTm 1 :=
  T.tracePhi.subst (inst T.boundAtInput)

/-- `Good(u) -> Accept(Run(bound(u),u),u)`. -/
def traceGoal : Fm PTm 1 :=
  (T.goodTerm (Syn.var 0) ≐ one) ⟶
    (T.acceptTerm
      (T.runTerm T.boundAtInput (Syn.var 0))
      (Syn.var 0) ≐ one)

end PRTraceSystem

/-- The theorem-specific arithmetic obligations after runner rewrites. -/
structure TraceObligations (T : PRTraceSystem) where
  base : ([] : List (Fm PTm 1)) ⊢[PRAAx]
    T.tracePhi.subst (inst PTm.zero)
  step : [T.tracePhi] ⊢[PRAAx]
    T.tracePhi.subst (repl (PTm.succ (Syn.var 0)))
  finish : [T.phiAtBound] ⊢[PRAAx] T.traceGoal

/-- Generic quantifier-free induction for the invariant. -/
theorem traceInvariant {T : PRTraceSystem} (O : TraceObligations T) :
    ([] : List (Fm PTm 1)) ⊢[PRAAx] Fm.all T.tracePhi :=
  PRA.qfInd T.tracePhi T.tracePhi_qf O.base O.step

/--
The generic reflection wrapper.  A concrete theorem needs only instantiate
`TraceObligations`; native export may then use `pra_iff_native`.
-/
theorem traceReflection {T : PRTraceSystem} (O : TraceObligations T) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] Fm.all T.traceGoal := by
  have hall : ([] : List (Fm PTm 1)) ⊢[PRAAx] Fm.all T.tracePhi :=
    traceInvariant O
  have hbound : ([] : List (Fm PTm 1)) ⊢[PRAAx] T.phiAtBound := by
    simpa [PRTraceSystem.phiAtBound] using
      (Prf.allE T.boundAtInput hall)
  have hgoal : ([] : List (Fm PTm 1)) ⊢[PRAAx] T.traceGoal :=
    Prf.impE (Prf.impI O.finish) hbound
  exact Prf.allI hgoal

end LeanProofs.ConciseIPRA.FiniteUse
