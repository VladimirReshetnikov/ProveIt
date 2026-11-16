import ConciseIPRA.PR
import ConciseIPRA.NativeBiInterpretation

/-!
# Trace reflection roadmap for ConciseIPRA

STATUS: source-oriented blueprint, not kernel checked in this artifact.

All formula constructors below are explicit. The remaining theorem is intended
to be completed by importing/promoting the already compiled
`primitiveRecursionAt` transformer from
`docs/proofs/foundations/ipra_local_global/lean/ObjectIteration.lean`.
No semantic truth-to-provability principle is intended.
-/

set_option autoImplicit false

namespace LeanProofs.ConciseIPRA.Finitary

open Syn
open scoped Fm
open PTm (app zero succ)

/-- Two explicit arguments in de Bruijn/Fin order. -/
def vec2 {α : Type} (a b : α) : Fin 2 → α :=
  Fin.cases a (Fin.cases b Fin.elim0)

/-- Three explicit arguments in de Bruijn/Fin order. -/
def vec3 {α : Type} (a b c : α) : Fin 3 → α :=
  Fin.cases a (Fin.cases b (Fin.cases c Fin.elim0))

def app1 {n : Nat} (f : PR 1) (a : PTm n) : PTm n :=
  PTm.app f (fun _ => a)

def app2 {n : Nat} (f : PR 2) (a b : PTm n) : PTm n :=
  PTm.app f (vec2 a b)

def app3 {n : Nat} (f : PR 3) (a b c : PTm n) : PTm n :=
  PTm.app f (vec3 a b c)

/-- The object-language assertion that a Boolean-valued term is true. -/
def IsOne {n : Nat} (t : PTm n) : Fm PTm n :=
  t ≐ succ zero

structure PRTraceSystem where
  good   : PR 1
  init   : PR 1
  bound  : PR 1
  step   : PR 3       -- (time, previous state, input)
  inv    : PR 3       -- (time, state, input)
  accept : PR 2       -- (state, input)

/-- The canonical run: recursion argument first, input parameter second. -/
def PRTraceSystem.run (T : PRTraceSystem) : PR 2 :=
  .prec T.init T.step

/-- Free-variable layout: [u]. -/
def BaseFm (T : PRTraceSystem) : Fm PTm 1 :=
  let u : PTm 1 := var 0
  IsOne (app1 T.good u) ⟶
    IsOne (app3 T.inv zero (app1 T.init u) u)

/-- Free-variable layout: [i, s, u]. -/
def StepFm (T : PRTraceSystem) : Fm PTm 3 :=
  let i : PTm 3 := var 0
  let s : PTm 3 := var 1
  let u : PTm 3 := var 2
  IsOne (app1 T.good u) ⟶
    IsOne (app3 T.inv i s u) ⟶
      IsOne (app3 T.inv (succ i) (app3 T.step i s u) u)

/-- Free-variable layout: [s, u]. -/
def FinalFm (T : PRTraceSystem) : Fm PTm 2 :=
  let s : PTm 2 := var 0
  let u : PTm 2 := var 1
  IsOne (app1 T.good u) ⟶
    IsOne (app3 T.inv (app1 T.bound u) s u) ⟶
      IsOne (app2 T.accept s u)

/-- Invariant used by ObjectIteration: layout [state, time, u]. -/
def InvP (T : PRTraceSystem) : Fm PTm 3 :=
  let s : PTm 3 := var 0
  let i : PTm 3 := var 1
  let u : PTm 3 := var 2
  IsOne (app3 T.inv i s u)

/-- Direct induction formula layout [i, u]. -/
def InvRunFm (T : PRTraceSystem) : Fm PTm 2 :=
  let i : PTm 2 := var 0
  let u : PTm 2 := var 1
  IsOne (app3 T.inv i (app2 T.run i u) u)

/-- Closed endpoint. Under `all`, bound variable 0 is `u`. -/
def ResultFm (T : PRTraceSystem) : Fm PTm 0 :=
  Fm.all <|
    let u : PTm 1 := var 0
    IsOne (app1 T.good u) ⟶
      IsOne (app2 T.accept (app2 T.run (app1 T.bound u) u) u)

structure TraceProofs (T : PRTraceSystem) where
  base  : ([] : List (Fm PTm 1)) ⊢[PRAAx] BaseFm T
  step  : ([] : List (Fm PTm 3)) ⊢[PRAAx] StepFm T
  final : ([] : List (Fm PTm 2)) ⊢[PRAAx] FinalFm T

@[simp] theorem invP_qf (T : PRTraceSystem) : (InvP T).QF := by
  trivial

@[simp] theorem invRun_qf (T : PRTraceSystem) : (InvRunFm T).QF := by
  trivial

/--
Main target. Completion path:

1. Let `G : Fm PTm 1 := IsOne (app1 T.good (var 0))` and `Γ := [G]`.
2. From `h.base.ofNil` and `Prf.hyp0`, derive the `baseFormula T.init (InvP T)`
   premise expected by `primitiveRecursionAt`.
3. In context `InvP T :: (Γ.map Fm.shift).map Fm.shift`, use `h.step.ofNil`,
   the shifted good hypothesis, and the invariant hypothesis to derive
   `nextFormula T.step (InvP T)`.
4. Apply the checked `primitiveRecursionAt T.init T.step (InvP T)` at
   `app1 T.bound (var 0)`. The result is the terminal invariant under `Γ`.
5. Instantiate `h.final` by the substitution `[terminalRun, u]`, weaken it to
   `Γ`, and eliminate its two implications using the good hypothesis and the
   terminal invariant.
6. Apply `Prf.impI`, then `Prf.allI`.

The only nontrivial engineering should be `simpa` lemmas equating the explicit
formulas above with `baseFormula`, `nextFormula`, and `instStateTime` from the
promoted ObjectIteration module.
-/
def traceReflection (T : PRTraceSystem) (h : TraceProofs T) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] ResultFm T := by
  sorry

/-- The checked ordinary/native bridge is used only after the ordinary proof. -/
def traceReflectionNative (T : PRTraceSystem) (h : TraceProofs T) :
    NPrf ([] : List (NFm 0)) (NFm.ofPRA (ResultFm T)) := by
  exact (pra_iff_native).mp (traceReflection T h)

/-- Recommended endpoint record for completed packets. -/
structure PacketTarget where
  params      : Nat
  assumptions : List (Fm PTm params)
  conclusion  : Fm PTm params
  derivation  : assumptions ⊢[PRAAx] conclusion

namespace PacketTarget

def toNative (T : PacketTarget) :
    NPrf (T.assumptions.map NFm.ofPRA) (NFm.ofPRA T.conclusion) := by
  exact (pra_iff_native).mp T.derivation

end PacketTarget
end LeanProofs.ConciseIPRA.Finitary
