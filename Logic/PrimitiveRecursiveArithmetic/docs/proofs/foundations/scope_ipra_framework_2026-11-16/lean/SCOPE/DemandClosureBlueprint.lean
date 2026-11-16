import IPRADerivations.Core.Division
import IPRADerivations.Core.MultiSums
import IPRADerivations.Core.Search

/-!
# Capped cyclic demand closure: implementation blueprint

A fixed finite proof graph may contain cyclic precision/resource dependencies.
SCOPE represents a `k`-vector `d` by mixed-radix digits with bases `cap_i+1`,
defines the inflationary step `H(d)=d join F(d)`, and iterates it from zero.
The rank is `sum_i digit_i(d)`, bounded by `K=sum_i cap_i`.

The central object proof uses the following quantifier-free state invariant:

1. every digit of the current code is within its cap;
2. the current code is the prescribed iterate of `H`;
3. the rank is at most `K`;
4. if the state has not stabilized, the next rank is at least the current rank
   plus one;
5. once stabilized, all later states are equal.

Coordinate bounds and monotonicity are represented by Boolean fold terms, so
the induction matrix is an equation/conjunction of equations, not a formula
with bounded quantifiers.

Required declarations, in dependency order:

```
structure CappedDemand (n k : Nat) where
  cap      : Fin k -> PTm n
  stepCode : PR (n+1)        -- code plus query parameters
  digit    : Fin k -> PR (n+1)
  bounded  : ...             -- object derivations
  monotone : ...             -- object derivation of the reflected relation

def inflate ...
def iterate ...
def rank ...
def totalCap ...

theorem iterate_bounded ...
theorem iterate_mono ...
theorem strict_rank_of_not_fixed ...
theorem fixed_by_totalCap ...
theorem least_prefixed ...
```

`fixed_by_totalCap` is proved by QF induction on the step counter.  If the
state at time `K` were not fixed, then no earlier state could have been fixed;
there would be `K+1` strict rank increases from rank zero, contradicting the
upper bound `K`.  Leastness is a second induction: every iterate is below any
prefixed point, by monotonicity of `H`.
-/

namespace LeanProofs.IPRA.SCOPE.DemandClosure

-- This namespace is intentionally declaration-free until the mixed-radix
-- representation is selected and proved against Core.Division.

end LeanProofs.IPRA.SCOPE.DemandClosure
