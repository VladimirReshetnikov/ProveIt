import IPRADerivations.Core.Search
import IPRADerivations.Core.Pairing
import IPRADerivations.Core.Definitions

/-!
# Trace reflection, bounded strategies, and relational viability

Implementation blueprint.  Every fixed transition, verifier, and compatibility
predicate is a `PR` code specialized at the Lean meta-level.  No internal
universal evaluator is used.

## Trace reflection

For a fixed state symbol `step`, initial term `init`, invariant bit `inv`, and
trace `run` defined by `recDef`, prove:

```
theorem run_zero ...
theorem run_succ ...
theorem trace_invariant
  (base : Gamma |- inv(init,q)=1)
  (step : inv(s,q)=1 :: Gamma |- inv(next(s,q),q)=1) :
  Gamma |- inv(run(fuel,q),q)=1
```

The induction predicate is literally the equation `inv(run(t,q),q)=1` with
query parameters free, so `IPRA.ind` applies.

## Finite strategy certificates

For each fixed bounded quantifier shape, encode a strategy table in one bounded
code.  Its verifier follows the game tree.  Backward dynamic programming
computes both a winning strategy and a counterstrategy.  The first milestone is
`forall x<B, exists y<C(x), R(x,y)`:

```
structure ForallExistsCertificate ...
def choiceAt ...
def verifyForallExists ...
theorem verify_sound ...
theorem verify_complete ...
```

Completeness uses `Search.mu` separately at each bounded `x`, then a finite
product/table code.  Soundness reads each selected row and invokes bounded
reflection of `R`.

## Relational viability

Given finite levels `A_0,...,A_h`, local validity bits and compatibility bits,
define backward viability:

```
V_h(a) = valid_h(a)
V_i(a) = valid_i(a) and exists b<bound_(i+1),
                       V_(i+1)(b) and compatible_i(a,b).
```

Use least bounded search only after viability has been computed.  This is
essential: the least locally valid answer can be a dead end.  The target
results are:

```
theorem viable_path_sound ...
theorem viable_path_complete ...
theorem least_viable_path ...
theorem no_path_of_not_viable ...
```

The proofs are finite backward/forward inductions on reflected bits; no
infinite-choice principle or infinite branch object is introduced.
-/

namespace LeanProofs.IPRA.SCOPE.TraceAndViability
end LeanProofs.IPRA.SCOPE.TraceAndViability
