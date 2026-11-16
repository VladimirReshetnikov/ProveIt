import ConciseIPRA.PR
import ConciseIPRA.NativeBiInterpretation

/-!
# Object-language finite-trace compiler for iPRA

This file is a source-oriented blueprint against the ProveIt API at commit
`9df5cbdf39e6220be823f611987bd584d37711fd`.

Definitions and theorem statements use the repository's actual objects
`PR`, `PTm`, `PRAAx`, `Prf`, `PRA.qfInd`, `NFm.ofPRA`, and
`pra_iff_native`.  The file was not compiled in the artifact environment.
Visible `sorry` terms mark the remaining kernel work; no theorem containing a
`sorry` is claimed to be checked.
-/

set_option autoImplicit false

namespace LeanProofs.ConciseIPRA.FinitaryInterface

open Syn
open scoped Fm
open PTm (app zero succ)

/-- One, used as the truth value of primitive-recursive Boolean symbols. -/
def one {n : Nat} : PTm n := succ zero

/-- Application helpers with the argument order visible in source. -/
def app1 {n : Nat} (f : PR 1) (a : PTm n) : PTm n :=
  app f (fun _ => a)

def app2 {n : Nat} (f : PR 2) (a b : PTm n) : PTm n :=
  app f (Fin.cases a (fun _ => b))

def app3 {n : Nat} (f : PR 3) (a b c : PTm n) : PTm n :=
  app f (Fin.cases a (Fin.cases b (fun _ => c)))

/-- Boolean truth as an object-language equation. -/
def IsTrue {n : Nat} (t : PTm n) : Fm PTm n := t ≐ one

/-- Fixed primitive-recursive data of a one-input bounded trace. -/
structure PRTraceSystem where
  good   : PR 1
  init   : PR 1
  bound  : PR 1
  step   : PR 3       -- index, previous state, input
  inv    : PR 3       -- index, state, input; Boolean-valued
  accept : PR 2       -- final state, input; Boolean-valued

/-- The run is primitive recursion on the first argument with one parameter. -/
def PRTraceSystem.run (T : PRTraceSystem) : PR 2 :=
  .prec T.init T.step

/-- `Good(u)`. -/
def GoodFm (T : PRTraceSystem) : Fm PTm 1 :=
  IsTrue (app1 T.good (var 0))

/-- `Inv(i,s,u)` with variable layout `[i,s,u]`. -/
def InvFm (T : PRTraceSystem) : Fm PTm 3 :=
  IsTrue (app3 T.inv (var 0) (var 1) (var 2))

/-- `Accept(s,u)` with variable layout `[s,u]`. -/
def AcceptFm (T : PRTraceSystem) : Fm PTm 2 :=
  IsTrue (app2 T.accept (var 0) (var 1))

/-- `Good(u) -> Inv(0,init(u),u)`. -/
def BaseFm (T : PRTraceSystem) : Fm PTm 1 :=
  GoodFm T ⟶
    IsTrue (app3 T.inv zero (app1 T.init (var 0)) (var 0))

/-- `Good(u) -> Inv(i,s,u) -> Inv(S i,step(i,s,u),u)`. -/
def StepFm (T : PRTraceSystem) : Fm PTm 3 :=
  IsTrue (app1 T.good (var 2)) ⟶
    IsTrue (app3 T.inv (var 0) (var 1) (var 2)) ⟶
      IsTrue (app3 T.inv (succ (var 0))
        (app3 T.step (var 0) (var 1) (var 2)) (var 2))

/-- `Good(u) -> Inv(bound(u),s,u) -> Accept(s,u)`. -/
def FinalFm (T : PRTraceSystem) : Fm PTm 2 :=
  IsTrue (app1 T.good (var 1)) ⟶
    IsTrue (app3 T.inv (app1 T.bound (var 1)) (var 0) (var 1)) ⟶
      IsTrue (app2 T.accept (var 0) (var 1))

/-- The quantifier-free induction formula `Inv(i,run(i,u),u)` with layout
`[i,u]`. -/
def InvRunFm (T : PRTraceSystem) : Fm PTm 2 :=
  IsTrue (app3 T.inv (var 0) (app2 T.run (var 0) (var 1)) (var 1))

/-- The closed theorem produced by trace reflection. -/
def ResultFm (T : PRTraceSystem) : Fm PTm 0 :=
  Fm.all (
    IsTrue (app1 T.good (var 0)) ⟶
      IsTrue (app2 T.accept
        (app2 T.run (app1 T.bound (var 0)) (var 0)) (var 0)))

/-- The induction formula is syntactically quantifier-free. -/
theorem invRun_qf (T : PRTraceSystem) : (InvRunFm T).QF := by
  simp [InvRunFm, IsTrue, Fm.QF]

/-- The two run equations are direct instances of the existing iPRA primitive
recursion axioms. -/
theorem run_zero {n : Nat} {Γ : List (Fm PTm n)}
    (T : PRTraceSystem) (u : PTm n) :
    Γ ⊢[PRAAx] app2 T.run zero u ≐ app1 T.init u := by
  simpa [PRTraceSystem.run, app1, app2] using
    (PRA.precZero (Γ := Γ) T.init T.step (fun _ : Fin 1 => u))

theorem run_succ {n : Nat} {Γ : List (Fm PTm n)}
    (T : PRTraceSystem) (i u : PTm n) :
    Γ ⊢[PRAAx]
      app2 T.run (succ i) u ≐
        app3 T.step i (app2 T.run i u) u := by
  simpa [PRTraceSystem.run, app2, app3] using
    (PRA.precSucc (Γ := Γ) T.init T.step i (fun _ : Fin 1 => u))

/-- The local contracts are already object-language derivations. -/
structure TraceProofs (T : PRTraceSystem) where
  base  : ([] : List (Fm PTm 1)) ⊢[PRAAx] BaseFm T
  step  : ([] : List (Fm PTm 3)) ⊢[PRAAx] StepFm T
  final : ([] : List (Fm PTm 2)) ⊢[PRAAx] FinalFm T

/-!
The next four lemmas are intentionally small formalization milestones.  They
separate de Bruijn substitution bookkeeping from the mathematical induction.
Each conclusion is exactly what is consumed by `PRA.qfInd` or the final cut.
-/

/-- Base case under the assumption `Good(u)`. -/
theorem trace_base (T : PRTraceSystem) (h : TraceProofs T) :
    [GoodFm T] ⊢[PRAAx] (InvRunFm T).subst (inst zero) := by
  /-
  Instantiate `h.base`, eliminate its implication with `Prf.hyp0`, and
  transport the state argument along `run_zero T (var 0)` using
  `Prf.eqCongr` and `Prf.eqSubst1`.
  -/
  sorry

/-- Successor case under the shifted good-input hypothesis and the induction
hypothesis. -/
theorem trace_step (T : PRTraceSystem) (h : TraceProofs T) :
    InvRunFm T :: [GoodFm T].map Fm.shift ⊢[PRAAx]
      (InvRunFm T).subst (repl (succ (var 0))) := by
  /-
  In the context `[InvRun(i,u), Good(u)]`, substitute
  `(i,run(i,u),u)` into `h.step`, eliminate the two implications, then
  transport along `run_succ T (var 0) (var 1)`.
  -/
  sorry

/-- The invariant holds at every index for a good input. -/
theorem trace_all (T : PRTraceSystem) (h : TraceProofs T) :
    [GoodFm T] ⊢[PRAAx] Fm.all (InvRunFm T) := by
  exact PRA.qfInd (InvRunFm T) (invRun_qf T) (trace_base T h) (trace_step T h)

/-- Specialize the invariant at `bound(u)` and apply the final local contract. -/
theorem trace_final (T : PRTraceSystem) (h : TraceProofs T) :
    [GoodFm T] ⊢[PRAAx]
      IsTrue (app2 T.accept
        (app2 T.run (app1 T.bound (var 0)) (var 0)) (var 0)) := by
  /-
  1. `Prf.allE (app1 T.bound (var 0)) (trace_all T h)`.
  2. Substitute `(run(bound(u),u),u)` into `h.final`.
  3. Eliminate the good-input and invariant implications.
  -/
  sorry

/-- Main proof-producing trace-reflection theorem. -/
theorem traceReflection (T : PRTraceSystem) (h : TraceProofs T) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] ResultFm T := by
  /-
  `Prf.impI (trace_final T h)` discharges `Good(u)` at arity one;
  `Prf.allI` then closes the input variable.  The only remaining work is a
  definitional `simpa [ResultFm, GoodFm]`.
  -/
  sorry

/-- The repository's checked bi-interpretation transports the completed iPRA
proof to the native scalar core. -/
theorem traceReflectionNative (T : PRTraceSystem) (h : TraceProofs T) :
    NPrf ([] : List (NFm 0)) (NFm.ofPRA (ResultFm T)) := by
  exact (pra_iff_native).mp (traceReflection T h)

end LeanProofs.ConciseIPRA.FinitaryInterface
