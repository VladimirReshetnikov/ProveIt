import Std

/-!
# Finite monotone demand closure

Precision requirements may contain feedback even when proof dependencies are
acyclic.  CIFER resolves such feedback on a finite product of capped natural
orders by inflationary iteration.  A strict step increases the sum of the
coordinates, so the process stabilizes within the explicit rank bound.
-/

set_option autoImplicit false

namespace LeanProofs.ConciseIPRA.CIFER

abbrev Demand (n : Nat) := Fin n -> Nat

namespace Demand

variable {n : Nat}

/-- Componentwise order. -/
def Le (a b : Demand n) : Prop := forall i, a i <= b i

/-- Componentwise maximum. -/
def sup (a b : Demand n) : Demand n := fun i => max (a i) (b i)

/-- Sum rank used as a termination/fuel measure. -/
def rank (a : Demand n) : Nat := Finset.univ.sum a

/-- One inflationary closure step. -/
def step (F : Demand n -> Demand n) (a : Demand n) : Demand n := sup a (F a)

/-- Primitive recursion for exactly `fuel` steps. -/
def iterate (F : Demand n -> Demand n) : Nat -> Demand n -> Demand n
  | 0, a => a
  | k + 1, a => iterate F k (step F a)

/-- A cap certificate for all coordinates. -/
def Under (cap a : Demand n) : Prop := Le a cap

/-!
Formalization targets:

* `le_step`: `Le a (step F a)`.
* `strict_rank`: if `step F a != a`, then `rank a < rank (step F a)`.
* `rank_le_cap`: from `Under cap a`, obtain `rank a <= rank cap`.
* `stabilizes`: if every iterate remains under `cap`, then iteration for
  `rank cap - rank seed + 1` steps reaches a fixed point.
* `least_fixed`: if `F` is monotone, the fixed point is the least prefixed
  point above `seed`.
* `object_trace`: specialize the fixed iteration to a `PR` state transformer
  and prove its equations with `PRA.qfInd`.

The first four are finite arithmetic; the fifth is an induction on the trace;
the final item is the bridge to `ObjectCompiler.loop`.
-/

end Demand
end LeanProofs.ConciseIPRA.CIFER
