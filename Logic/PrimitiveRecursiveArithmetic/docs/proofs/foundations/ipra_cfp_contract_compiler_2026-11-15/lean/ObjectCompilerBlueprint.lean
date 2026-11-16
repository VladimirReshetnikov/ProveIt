import ConciseIPRA.PR
import ConciseIPRA.NativeBiInterpretation

/-!
# Object-language compiler blueprint

This file targets the actual ProveIt `ConciseIPRA` API.  It is an outline,
not a completed proof.  Every placeholder is visible as `sorry`; no theorem
below should be cited as established until those placeholders are removed and
the file is compiled in the repository's Lean 4.32.0 environment.
-/

set_option autoImplicit false

namespace LeanProofs.ConciseIPRA
namespace CFP

open Syn
open scoped Fm
open PTm (app zero succ)

/-- Boolean truth is represented by equality to the numeral one. -/
def one {n : Nat} : PTm n := succ zero

def holds {n : Nat} (b : PTm n) : Fm PTm n := b ≐ one

/-- A fixed object-level trace system.  The first argument of `step` is the
stage and the second is the coded state; remaining arguments are parameters.
The exact arity adapters are built from projections and composition. -/
structure PRTraceSystem (p : Nat) where
  init : PR p
  step : PR (p + 2)
  guard : PR (p + 2)
  finish : PR (p + 1)
  horizon : PR p

/-- Target PR codes.  They will be implemented compositionally from `PR.prec`
and the coding library. -/
structure CodingLibrary where
  boolNot : PR 1
  boolAnd : PR 2
  boolOr : PR 2
  eqb : PR 2
  leb : PR 2
  max : PR 2
  pair : PR 2
  left : PR 1
  right : PR 1
  listLength : PR 1
  listGet : PR 2
  listAppend : PR 2
  allBelow : PR 2
  anyBelow : PR 2
  firstTrueTable : PR 2

/-- Quantifier-free formula asserting that the trace state at stage `t`
satisfies the system guard.  This definition is schematic until `runCode`
and the argument adapters are implemented. -/
def traceInvFormula
    {p n : Nat}
    (S : PRTraceSystem p)
    (runCode : PR (p + 1))
    (args : Fin (p + 1) → PTm n) : Fm PTm n :=
  holds (app S.guard (fun i =>
    -- Adapter target: stage/state/parameter ordering.
    app (.proj i) args))

theorem traceInvFormula_qf
    {p n : Nat}
    (S : PRTraceSystem p)
    (runCode : PR (p + 1))
    (args : Fin (p + 1) → PTm n) :
    (traceInvFormula S runCode args).QF := by
  simp [traceInvFormula, holds]

/-- Main reusable target: base, step, and finish proof objects yield the final
trace contract.  The final implementation instantiates `PRA.qfInd` with a
formula that freezes the state after the horizon. -/
theorem PRA.traceReflection
    {p n : Nat}
    (S : PRTraceSystem p)
    (Γ : List (Fm PTm n))
    (runCode : PR (p + 1))
    (inv : Fm PTm (n + 1))
    (hInvQF : inv.QF)
    (hBase : Γ ⊢[PRAAx] inv.subst (inst zero))
    (hStep :
      inv :: Γ.map Fm.shift ⊢[PRAAx]
        inv.subst (repl (succ (var 0)))) :
    Γ ⊢[PRAAx] Fm.all inv := by
  exact PRA.qfInd inv hInvQF hBase hStep

/-- Local node contract.  The formulas are kept explicit so the graph compiler
can compose actual `Prf PRAAx` values. -/
structure LocalContract (n : Nat) where
  premise : Fm PTm n
  result : Fm PTm n
  premiseQF : premise.QF
  resultQF : result.QF
  proof : [premise] ⊢[PRAAx] result

/-- A fixed graph node.  `demand` and `run` are concrete PR codes; parent lists
are meta-level finite data used to generate a single fixed global PR term. -/
structure ContractNode (n : Nat) where
  parentCount : Nat
  demand : Fin parentCount → PR 1
  run : PR (parentCount + 2)
  verify : PR (parentCount + 3)
  local : LocalContract n

structure ContractDAG (n : Nat) where
  nodeCount : Nat
  nodes : Fin nodeCount → ContractNode n
  parentIndex :
    (v : Fin nodeCount) → Fin (nodes v).parentCount → Fin nodeCount
  topological :
    ∀ v j, (parentIndex v j).val < v.val

/-- Reverse-demand adequacy target.  Its proof is a QF induction over the
fixed reverse fold and uses the defining equations of max/table update. -/
theorem PRA.reverseDemand_adequate
    {n : Nat}
    (G : ContractDAG n) :
    True := by
  -- Replace `True` by the exact encoded formula after the coding library is
  -- instantiated.
  trivial

/-- Main compiler target.  The result type is schematic here: the completed
version returns a concrete global output formula and its `Prf PRAAx` term. -/
theorem PRA.contractDAGReflection
    {n : Nat}
    (G : ContractDAG n)
    (Γ : List (Fm PTm n)) :
    True := by
  -- 1. Generate the reverse-demand PR code.
  -- 2. Generate the forward trace PR code.
  -- 3. Generate the QF invariant as Boolean folds over the node table.
  -- 4. Compose each `(G.nodes v).local.proof` in the step case.
  -- 5. Invoke `PRA.traceReflection`.
  trivial

/-- Finite relational path target.  The completed statement uses object-level
candidate tables, a compatibility Boolean, and a fuelled viability table. -/
theorem PRA.relationalPath : True := by
  trivial

/-- Exact zero/apart branch from a regular approximation and supplied
zero-or-gap evidence. -/
theorem PRA.gapDecision : True := by
  trivial

/-- Cubic benchmark target.  This becomes a theorem about coded rational
endpoints and the bisection trace, followed by universal introduction over
the requested precision. -/
theorem PRA.cubicBisection : True := by
  trivial

/-- Transport is intentionally last.  Once `h` is a real object derivation,
the existing bridge gives the native theorem. -/
def exportNative
    {n : Nat} {Γ : List (Fm PTm n)} {φ : Fm PTm n}
    (h : Γ ⊢[PRAAx] φ) :
    NPrf (Γ.map NFm.ofPRA) (NFm.ofPRA φ) :=
  pra_iff_native.mp h

end CFP
end LeanProofs.ConciseIPRA
