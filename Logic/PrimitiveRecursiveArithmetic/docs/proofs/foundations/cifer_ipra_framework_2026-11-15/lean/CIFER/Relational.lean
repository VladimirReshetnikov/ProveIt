import Std

/-!
# Finite relational witnesses and stable observations

A constructive proof often supplies a nonempty finite cloud of acceptable
answers rather than a canonical exact witness.  CIFER preserves that relation,
uses backward viability for finite-horizon compatibility, and collapses it only
through a branch-independent observable or an explicit diameter/gap theorem.
-/

set_option autoImplicit false

namespace LeanProofs.ConciseIPRA.CIFER

structure Cloud (A : Type) where
  values : Array A
  nonempty : values.size > 0

/-- Compatibility between consecutive levels. -/
abbrev Edge (A : Type) := Nat -> A -> A -> Bool

/--
Executable backwards viability.  `levels[k][i]` is viable when it has a
compatible successor at level `k+1` that is itself viable.  The implementation
uses Boolean tables and bounded loops only.
-/
def viableStep {A : Type} (edge : Edge A)
    (k : Nat) (current next : Array A) (nextGood : Array Bool) : Array Bool :=
  current.map fun x =>
    (List.range next.size).any fun j =>
      nextGood.getD j false && edge k x (next.getD j x)

/-- Branch independence of an exact finite observation. -/
def StableOn {A O : Type} [DecidableEq O]
    (obs : A -> O) (xs : Array A) : Prop :=
  forall i (hi : i < xs.size) j (hj : j < xs.size),
    obs (xs[i]'hi) = obs (xs[j]'hj)

/-!
Formalization targets:

* `viable_iff_path`: the backwards table marks precisely the vertices lying on
  a compatible path to the fixed finite horizon.
* `least_path`: bounded least search returns the lexicographically first viable
  path whenever one exists.
* `stable_elim`: a `StableOn` observer gives the same result from every viable
  witness and therefore needs no global selector.
* `diameter_elim`: in a coded rational metric, a cloud of diameter at most
  `2^-q` determines an observation at precision `q`.
* `shrinking_name`: least viable witnesses at changing horizons form a Cauchy
  name under a diameter modulus plus a summable edge-motion budget.
* `gap_collapse`: a positive separation certificate turns an approximate label
  cloud into one exact label; without the gap the relational theorem is kept.

Each object-language version is to use fixed finite codes, Boolean checkers,
bounded search, and `CIFER.loop`; no choice axiom is required.
-/

end LeanProofs.ConciseIPRA.CIFER
