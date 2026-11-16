import StagedContractKernel.Interfaces

/-!
# Precise blueprint for Booleanization, demand closure, and viability

This file contains executable data definitions and proof-obligation records,
not admitted theorems.  The report gives the full human proofs and the
formalization plan gives the dependency order for replacing each proof field
by a derived `Prf PRAAx` term.
-/

set_option autoImplicit false

namespace LeanProofs.ConciseIPRA
namespace StagedContractKernel

open Syn
open scoped Fm

/-- Host syntax for a fixed bounded formula.  A compiler traverses this finite
syntax at Lean elaboration time and emits a concrete `PR` symbol; there is no
object-language universal evaluator. -/
inductive BForm (n : Nat) where
  | eq (left right : PTm n)
  | lt (left right : PTm n)
  | and (left right : BForm n)
  | or (left right : BForm n)
  | imp (left right : BForm n)
  | boundedAll (bound : PTm n) (body : BForm (n + 1))
  | boundedEx (bound : PTm n) (body : BForm (n + 1))

/-- The two outputs required from Booleanization: a concrete characteristic
term and an actual object-theory reflection proof. -/
structure BooleanizationResult (n : Nat) (Gamma : List (Fm PTm n)) where
  formula : Fm PTm n
  characteristic : PTm n
  qf : formula.QF
  reflectedTrue : Gamma ⊢[PRAAx]
    (characteristic ≐ PTm.succ PTm.zero) ⟶ formula
  reflectedFalse : Gamma ⊢[PRAAx]
    (characteristic ≐ PTm.zero) ⟶ (formula ⟶ Fm.bot)

/-- A finite monotone demand closure.  `state` is a concrete mixed-radix coded
vector.  The invariant must state the cap, inflationarity, and fixed-point
condition at exhaustion. -/
structure DemandClosureObligation
    {n : Nat} (Gamma : List (Fm PTm n)) where
  precondition : Fm PTm n
  conclusion : Fm PTm n
  loop : LoopObligation Gamma precondition conclusion

/-- A finite-horizon relational cloud.  Every field is a concrete term or an
embedded proof obligation; nonemptiness of individual levels is intentionally
not enough--the final field must prove backward viability. -/
structure ViabilityObligation
    {n : Nat} (Gamma : List (Fm PTm n)) where
  precondition : Fm PTm n
  viableAtZero : Fm PTm n
  selectedPathCorrect : precondition :: Gamma ⊢[PRAAx] viableAtZero

/-- A shrinking-cloud name.  Exact coherence is replaced by an explicit
rational diameter or motion budget in `comparison`. -/
structure ShrinkingCloudObligation
    {n : Nat} (Gamma : List (Fm PTm n)) where
  firstCertificate : Fm PTm n
  secondCertificate : Fm PTm n
  requestedAccuracy : Fm PTm n
  comparison : firstCertificate :: secondCertificate :: Gamma ⊢[PRAAx]
    requestedAccuracy

/-!
## Formalization targets (dependency order)

The following signatures are intentionally comments rather than axioms.

```
def compileBForm (B : BForm n) : PR n

theorem compileBForm_reflect_true (B : BForm n) :
  [] ⊢[PRAAx] checked (compileBForm B) PTm.var ⟶ B.toFormula

theorem leastBoundedSearch_correct ... : Prf PRAAx ...

theorem demandClosure_correct ... : Prf PRAAx ...

theorem backwardViability_correct ... : Prf PRAAx ...

theorem leastViablePath_correct ... : Prf PRAAx ...

theorem diameterErasure_correct ... : Prf PRAAx ...
```

Each target is proved by constructing a fixed `PR.prec` symbol, deriving its
zero and successor equations with `PRA.precZero` and `PRA.precSucc`, choosing a
quantifier-free invariant, and invoking `PRA.qfInd`.  Section 12 of the report
spells out the invariant for every target.
-/

end StagedContractKernel
end LeanProofs.ConciseIPRA
