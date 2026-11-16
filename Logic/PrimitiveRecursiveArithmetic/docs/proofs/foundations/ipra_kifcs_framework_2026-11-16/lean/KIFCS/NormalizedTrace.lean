import KIFCS.OpenContract

/-!
# Normalized finite-trace reflection for KIFC-S

The theorem-specific compiler supplies base, step, and terminal derivations in
exactly the forms consumed by `PRA.qfInd`.  The generic kernel performs only
induction, specialization at the computed bound, terminal extraction, and
closure.

No placeholder occurs in this source candidate.  It was not compiled in the
artifact runtime.
-/

set_option autoImplicit false

namespace LeanProofs.ConciseIPRA.KIFCS

open Syn
open scoped Fm
open PTm (app zero succ)

/-- Numerical one, used as Boolean truth. -/
def one {n : Nat} : PTm n := succ zero

def app1 {n : Nat} (f : PR 1) (a : PTm n) : PTm n :=
  app f (fun _ => a)

def app2 {n : Nat} (f : PR 2) (a b : PTm n) : PTm n :=
  app f (Fin.cases a (fun _ => b))

def app3 {n : Nat} (f : PR 3) (a b c : PTm n) : PTm n :=
  app f (Fin.cases a (Fin.cases b (fun _ => c)))

def IsTrue {n : Nat} (t : PTm n) : Fm PTm n := t ≐ one

/-- Fixed primitive-recursive data of a one-input bounded trace. -/
structure PRTraceSystem where
  good   : PR 1
  init   : PR 1
  bound  : PR 1
  step   : PR 3
  inv    : PR 3
  accept : PR 2

/-- The runner recurses on the counter with one parameter. -/
def PRTraceSystem.run (T : PRTraceSystem) : PR 2 :=
  .prec T.init T.step

def GoodFm (T : PRTraceSystem) : Fm PTm 1 :=
  IsTrue (app1 T.good (var 0))

def InvRunFm (T : PRTraceSystem) : Fm PTm 2 :=
  IsTrue (app3 T.inv (var 0) (app2 T.run (var 0) (var 1)) (var 1))

def AcceptAtBoundFm (T : PRTraceSystem) : Fm PTm 1 :=
  IsTrue (app2 T.accept
    (app2 T.run (app1 T.bound (var 0)) (var 0)) (var 0))

def ResultFm (T : PRTraceSystem) : Fm PTm 0 :=
  Fm.all (GoodFm T ⟶ AcceptAtBoundFm T)

theorem invRun_qf (T : PRTraceSystem) : (InvRunFm T).QF := by
  simp [InvRunFm, IsTrue, Fm.QF]

/-- Exactly the normalized local proof terms required by the generic kernel. -/
structure NormalizedTraceProofs (T : PRTraceSystem) where
  base : [GoodFm T] ⊢[PRAAx]
    (InvRunFm T).subst (inst zero)
  step : InvRunFm T :: [GoodFm T].map Fm.shift ⊢[PRAAx]
    (InvRunFm T).subst (repl (succ (var 0)))
  finish : [GoodFm T] ⊢[PRAAx]
    ((InvRunFm T).subst (inst (app1 T.bound (var 0))) ⟶
      AcceptAtBoundFm T)

/-- Quantifier-free induction plus specialization and terminal extraction. -/
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

/-- Contract wrapper for graph compilation. -/
theorem traceReflectionContract (T : PRTraceSystem)
    (h : NormalizedTraceProofs T) : Contract [] (ResultFm T) :=
  Contract.ofPrf (traceReflectionNormalized T h)

/-- Optional transfer after the ordinary theorem has been constructed. -/
theorem traceReflectionNative (T : PRTraceSystem)
    (h : NormalizedTraceProofs T) :
    NPrf ([] : List (NFm 0)) (NFm.ofPRA (ResultFm T)) :=
  (pra_iff_native).mp (traceReflectionNormalized T h)

end LeanProofs.ConciseIPRA.KIFCS
