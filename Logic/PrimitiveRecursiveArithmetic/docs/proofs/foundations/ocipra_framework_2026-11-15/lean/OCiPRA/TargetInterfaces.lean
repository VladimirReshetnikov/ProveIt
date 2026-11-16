import OCiPRA.Contracts

/-!
# Target interfaces for the OCiPRA compiler

These structures are *specifications*.  No instances are declared here, so the
file does not assert unfinished theorems.  Each future implementation must fill
its proof fields with actual `Prf PRAAx` derivations.
-/

namespace LeanProofs.ConciseIPRA.OCiPRA

open Syn
open scoped Fm

/-- The bounded-formula Booleanizer to be implemented by recursion on a new
bounded syntax. -/
structure BooleanizerPackage where
  BFm : Nat → Type
  toFm : {n : Nat} → BFm n → Fm PTm n
  test : {n : Nat} → BFm n → PR n
  correct : ∀ {n : Nat} (φ : BFm n),
    [] ⊢[PRAAx] Fm.iff (toFm φ) (accepts (test φ))

/-- Object-level correctness package for least bounded search.  The concrete
implementation will define `least` by primitive recursion and instantiate the
three proof fields using one quantifier-free invariant. -/
structure BoundedSearchPackage (n : Nat) where
  pre : Fm PTm n
  bound : PR n
  relation : Fm PTm (n + 1)
  least : PR n
  withinBound : [pre] ⊢[PRAAx] relation.subst (inst (PTm.app least Syn.var))
  minimality : Fm PTm n
  minimalityProof : [pre] ⊢[PRAAx] minimality

/-- Fixed, compile-time contract DAGs should compile by structural recursion on
their host syntax.  This record states the endpoint without postulating a
universal unclocked evaluator. -/
structure FixedDAGPackage (n : Nat) where
  globalPre : Fm PTm n
  globalProgram : PR n
  globalPost : Fm PTm (n + 1)
  compiled : [globalPre] ⊢[PRAAx]
    globalPost.subst (inst (PTm.app globalProgram Syn.var))

/-- A bounded relational cloud is useful even when no branch-independent exact
selector exists. -/
structure ViabilityPackage (n : Nat) where
  pre : Fm PTm n
  horizon : PR n
  pathCode : PR n
  pathValid : Fm PTm (n + 1)
  compiled : [pre] ⊢[PRAAx]
    pathValid.subst (inst (PTm.app pathCode Syn.var))

/-- Exact elimination of an internal branch requires an explicit stability
proof.  Approximate elimination uses an analogous diameter formula. -/
structure StableObservablePackage (n : Nat) where
  pre : Fm PTm n
  observable : PR (n + 1)
  output : PR n
  stabilityFormula : Fm PTm n
  stability : [pre] ⊢[PRAAx] stabilityFormula

end LeanProofs.ConciseIPRA.OCiPRA
