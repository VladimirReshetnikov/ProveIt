import KernelCompiler

/-!
# Domain-facing obligation records

This file turns the generic compiler into a precise formalization interface.
It contains no semantic shortcut.  To instantiate a record, a domain packet
must provide the displayed `Prf PRAAx` fields.  The compiler then produces the
advertised theorem mechanically.
-/

set_option autoImplicit false

namespace LeanProofs.ConciseIPRA
namespace KernelFiniteUse

open Syn
open scoped Fm

variable {n : Nat} {Γ : List (Fm PTm n)}

/-- All arithmetic obligations for one finite trace. -/
structure TraceObligations
    (P Q : Fm PTm n) where
  invariant : Fm PTm (n + 1)
  invariantQF : invariant.QF
  fuel : PTm n
  base : P :: Γ ⊢[PRAAx] invariant.subst (inst PTm.zero)
  step : invariant :: (P :: Γ).map Fm.shift ⊢[PRAAx]
    invariant.subst (repl (PTm.succ (var 0)))
  finish : invariant.subst (inst fuel) :: P :: Γ ⊢[PRAAx] Q

/-- Once the fields are filled, the trace contract is an actual object proof. -/
theorem TraceObligations.compile
    {P Q : Fm PTm n}
    (T : TraceObligations (Γ := Γ) P Q) :
    Γ ⊢[PRAAx] P ⟶ Q :=
  loopContract P Q T.invariant T.invariantQF T.fuel
    T.base T.step T.finish

/-- A bounded-search producer with an explicit found witness. -/
structure WitnessObligations
    (R : Fm PTm (n + 1)) where
  witness : PTm n
  witnessCorrect : Γ ⊢[PRAAx] R.subst (inst witness)

/-- Export the witness to an existential without choice. -/
theorem WitnessObligations.compile
    {R : Fm PTm (n + 1)}
    (W : WitnessObligations (Γ := Γ) R) :
    Γ ⊢[PRAAx] Fm.ex R :=
  existsFromWitness R W.witness W.witnessCorrect

/--
A relational producer may retain many possible certificates.  Exact witness
coherence is unnecessary when the requested observable is stable across any
two certified outputs.
-/
structure RelationalObservationObligations
    (C₁ C₂ O : Fm PTm n) where
  first : Γ ⊢[PRAAx] C₁
  second : Γ ⊢[PRAAx] C₂
  comparison : C₁ :: C₂ :: Γ ⊢[PRAAx] O

/-- Compile relational data directly to the stable observable. -/
theorem RelationalObservationObligations.compile
    {C₁ C₂ O : Fm PTm n}
    (R : RelationalObservationObligations (Γ := Γ) C₁ C₂ O) :
    Γ ⊢[PRAAx] O :=
  stableObservable C₁ C₂ O R.first R.second R.comparison

/-- A global mathematical input is a first-class boundary obligation. -/
structure BoundaryObligations
    (Boundary Goal : Fm PTm n) where
  boundary : Γ ⊢[PRAAx] Boundary
  body : Boundary :: Γ ⊢[PRAAx] Goal

/-- Compile a boundary-dependent theorem without misclassifying the boundary
as a primitive-recursive construction. -/
theorem BoundaryObligations.compile
    {Boundary Goal : Fm PTm n}
    (B : BoundaryObligations (Γ := Γ) Boundary Goal) :
    Γ ⊢[PRAAx] Goal :=
  withBoundary Boundary Goal B.boundary B.body

/--
The exactness interface: approximation alone is insufficient; the packet must
also provide a separation/gap theorem and an object proof of branch erasure.
-/
structure ExactnessObligations
    (Approx Gap Exact : Fm PTm n) where
  approximation : Γ ⊢[PRAAx] Approx
  separation : Γ ⊢[PRAAx] Gap
  erasure : Approx :: Gap :: Γ ⊢[PRAAx] Exact

/-- Compile guarded exactness. -/
theorem ExactnessObligations.compile
    {Approx Gap Exact : Fm PTm n}
    (E : ExactnessObligations (Γ := Γ) Approx Gap Exact) :
    Γ ⊢[PRAAx] Exact :=
  exactFromGap Approx Gap Exact E.approximation E.separation E.erasure

end KernelFiniteUse
end LeanProofs.ConciseIPRA
