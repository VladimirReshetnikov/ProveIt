import ObjectKernel

/-!
# A proof-producing compiler from terms to primitive-recursive symbols

The syntax and proof kernel in `ObjectKernel` are copied from the previously
delivered `ipra_coherent_methods_2026-11-15` package.  They preserve the actual
ProveIt `PR`, `PTm`, `PRAAx`, and `Prf` definitions, with `Std` compatibility.

This module is new.  `symbol_correct` concludes an OBJECT-iPRA derivation;
it is not a theorem about truth of arbitrary Lean predicates.
-/

namespace LeanProofs.ConciseIPRA.TermCompiler

open Syn
open scoped Fm

/-- A term over `k` parameters becomes one PR symbol of arity `k`. -/
def symbol {k : Nat} : PTm k → PR k
  | .var i => .proj i
  | .app f ts => .comp f (fun i => symbol (ts i))

/-- The compiler's correctness is proved in the object theory itself, at
arbitrary substituted arguments, and with an arbitrary hypothesis context. -/
theorem symbol_correct {k n : Nat} (t : PTm k) (σ : Fin k → PTm n)
    {Γ : List (Fm PTm n)} :
    Γ ⊢[PRAAx] PTm.app (symbol t) σ ≐ Syn.subst σ t := by
  induction t with
  | var i => exact PRA.proj i σ
  | app f ts ih =>
      apply Prf.eqTrans (PRA.comp f (fun i => symbol (ts i)) σ)
      simpa using (Prf.eqCongr (PTm.app f Syn.var) ih)

/-- Any already-established equation about a term can be transported to its
compiled symbol.  This is an actual proof transformer, without semantic
reflection or any axiom about a checker. -/
theorem transport_equation {k n : Nat} (t : PTm k) (σ : Fin k → PTm n)
    {Γ : List (Fm PTm n)} {u : PTm n}
    (h : Γ ⊢[PRAAx] Syn.subst σ t ≐ u) :
    Γ ⊢[PRAAx] PTm.app (symbol t) σ ≐ u :=
  Prf.eqTrans (symbol_correct t σ) h

end LeanProofs.ConciseIPRA.TermCompiler

#print axioms LeanProofs.ConciseIPRA.TermCompiler.symbol_correct
#print axioms LeanProofs.ConciseIPRA.TermCompiler.transport_equation
