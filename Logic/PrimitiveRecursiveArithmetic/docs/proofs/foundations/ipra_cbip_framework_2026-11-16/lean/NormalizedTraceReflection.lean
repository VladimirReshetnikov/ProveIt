import ConciseIPRA.PR
import ConciseIPRA.NativeBiInterpretation

/-!
# Normalized finite-trace reflection for iPRA

This is a source-oriented candidate against the current ProveIt ConciseIPRA
interfaces.  It intentionally accepts base, step, and terminal derivations in
the exact normalized forms consumed by `PRA.qfInd`.  Thus the small reflection
kernel does not perform theorem-specific run rewrites or de Bruijn transports.

The file contains no `sorry`, `admit`, or added axiom.  It was not compiled in
the artifact runtime because Lean and the repository dependency closure were
unavailable.  No kernel-checked theorem is claimed until it builds in ProveIt.
-/

set_option autoImplicit false

namespace LeanProofs.ConciseIPRA.CBIP

open Syn
open scoped Fm
open PTm (app zero succ)

/-- Numerical one, used as the truth value of Boolean PR symbols. -/
def one {n : Nat} : PTm n := succ zero

/-- Visible helpers for applications of small arity. -/
def app1 {n : Nat} (f : PR 1) (a : PTm n) : PTm n :=
  app f (fun _ => a)

def app2 {n : Nat} (f : PR 2) (a b : PTm n) : PTm n :=
  app f (Fin.cases a (fun _ => b))

def app3 {n : Nat} (f : PR 3) (a b c : PTm n) : PTm n :=
  app f (Fin.cases a (Fin.cases b (fun _ => c)))

/-- A Boolean-valued term is true when it equals one. -/
def IsTrue {n : Nat} (t : PTm n) : Fm PTm n := t ≐ one

/-- Fixed primitive-recursive data of a one-parameter bounded trace. -/
structure PRTraceSystem where
  good   : PR 1
  init   : PR 1
  bound  : PR 1
  step   : PR 3       -- counter, previous state, input
  inv    : PR 3       -- counter, state, input; Boolean-valued
  accept : PR 2       -- final state, input; Boolean-valued

/-- The runner is primitive recursion on the counter with one parameter. -/
def PRTraceSystem.run (T : PRTraceSystem) : PR 2 :=
  .prec T.init T.step

/-- `Good(u)` with one free input variable. -/
def GoodFm (T : PRTraceSystem) : Fm PTm 1 :=
  IsTrue (app1 T.good (var 0))

/-- `Inv(i, run(i,u), u)` with free-variable layout `[i,u]`. -/
def InvRunFm (T : PRTraceSystem) : Fm PTm 2 :=
  IsTrue (app3 T.inv (var 0) (app2 T.run (var 0) (var 1)) (var 1))

/-- `Accept(run(bound(u),u),u)` with one free input variable. -/
def AcceptAtBoundFm (T : PRTraceSystem) : Fm PTm 1 :=
  IsTrue (app2 T.accept
    (app2 T.run (app1 T.bound (var 0)) (var 0)) (var 0))

/-- The closed theorem exported by normalized trace reflection. -/
def ResultFm (T : PRTraceSystem) : Fm PTm 0 :=
  Fm.all (GoodFm T ⟶ AcceptAtBoundFm T)

/-- The induction formula is syntactically quantifier-free. -/
theorem invRun_qf (T : PRTraceSystem) : (InvRunFm T).QF := by
  simp [InvRunFm, IsTrue, Fm.QF]

/--
The local compiler/elaborator has already discharged all theorem-specific
rewriting.  These are exactly the three proof terms needed by the generic
reflection kernel.
-/
structure NormalizedTraceProofs (T : PRTraceSystem) where
  base : [GoodFm T] ⊢[PRAAx]
    (InvRunFm T).subst (inst zero)
  step : InvRunFm T :: [GoodFm T].map Fm.shift ⊢[PRAAx]
    (InvRunFm T).subst (repl (succ (var 0)))
  finish : [GoodFm T] ⊢[PRAAx]
    ((InvRunFm T).subst (inst (app1 T.bound (var 0))) ⟶
      AcceptAtBoundFm T)

/--
A tiny proof-producing reflection kernel: quantifier-free induction,
specialization at the computed bound, terminal extraction, implication
introduction, and universal introduction.
-/
theorem traceReflectionNormalized (T : PRTraceSystem)
    (h : NormalizedTraceProofs T) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] ResultFm T := by
  have hall : [GoodFm T] ⊢[PRAAx] Fm.all (InvRunFm T) :=
    PRA.qfInd (InvRunFm T) (invRun_qf T) h.base h.step
  have hat : [GoodFm T] ⊢[PRAAx]
      (InvRunFm T).subst (inst (app1 T.bound (var 0))) :=
    Prf.allE (app1 T.bound (var 0)) hall
  have hacc : [GoodFm T] ⊢[PRAAx] AcceptAtBoundFm T :=
    Prf.impE h.finish hat
  simpa [ResultFm] using (Prf.allI (Prf.impI hacc))

/-- Optional transport to the native scalar calculus after the PRA proof exists. -/
theorem traceReflectionNormalizedNative (T : PRTraceSystem)
    (h : NormalizedTraceProofs T) :
    NPrf ([] : List (NFm 0)) (NFm.ofPRA (ResultFm T)) := by
  exact (pra_iff_native).mp (traceReflectionNormalized T h)

end LeanProofs.ConciseIPRA.CBIP
