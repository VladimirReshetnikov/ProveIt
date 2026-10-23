# Lean simplification audit and optional bounded scheduler

Repository basis: `cbf94cb552a3b49509e0eee80e7455d4eb5974c6`.

## Recommendation

Adopt the existing Source194 shared scheduler, rebased narrowly onto the current
enumerators, before inventing another scheduler framework. Its `Dynamics` takes
the existing step and run functions and their two equations. Its `Laws` needs
only an index increment at a boundary and a strictly smaller pending pointer
inside a candidate. The lexicographic proof of `reach_or_halt` permits arbitrary
refill sizes and proves completeness from active candidates as well as clean
boundaries. This is already in a repository proposal; it is not a new discovery
of this report.

Current `EnumPerm` still proves `run_inv`, `run_add`, `drain`, and `reach`
separately. Analogues remain in `EnumDom`, `Enum222`, and `Enum254`.
`scheduler_census.json` records 16 declarations, 209 lines and 9,500 bytes.
Those counts measure duplicated proof scope, not net source savings. Charge
the shared module and every adapter when reporting net savings.

The concrete integration hazard is that Source194's proposed `EnumPerm.lean`
still compiles `CDom` using `build (cdom_of_c222 h)`. The current production
file directly compiles `C222` through `build_c222`. Replacing the entire file
with Source194's snapshot would restore a removed intermediate calculus.
Transplant the run/scheduler statements only, keep the present command
definitions and compiler, and use `build_c222` in the completion adapter.

Other tempting proposals are already completed or already represented in
incoming work: final endpoint composition, uniform seed completeness, shared
implication proofs, semantic bundle round-trips, and weak quotient syntax.
The latest public phase15 record is evidence about its selected bytes; it
does not itself certify every later source change at this review's commit.

## A bounded refinement

The supplied optional extension uses the extra K215 fact omitted by the more
general Source194 theorem: after a boundary refill, the residual pointer is
at most the old candidate index. Define T(0)=0 and T(n+1)=T(n)+n+1, and set

    B_N(s) = T(N) - T(index(s)) + pending(s).

Assume `index(s) <= N`. If the target boundary is not already reached, every
successful step preserves this inequality and strictly decreases B_N.

* At an active candidate, the index is unchanged and the pointer decreases.
* At a non-target boundary with index i, the next index is i+1 and the new
  pointer is at most i. Hence the old potential minus the new potential is
  at least T(i+1)-T(i)-i = 1.

Strong induction gives a successful prefix of length `n <= B_N(s)` ending
either at the requested boundary or at a state whose next transition halts.
The halting transition is excluded from n; if it is counted, use n+1.
No condition on the formula/stack payload is needed for this scheduling fact.

The earlier checked-transport Rocq proposal uses the rectangular potential
`(N-index(s))*(N+1)+pending(s)`. The triangular refinement is smaller; at the
K215 seed `(pending,index)=(0,4)`, the bound is `T(N)-10`. This is a bound on
abstract enumerator commands, not on binary Turing-machine steps. It is also
not an unconditional halting bound: reaching a particular candidate boundary
does not assert that candidate proves a contradiction.

The bound is sharp for the class of scheduler laws used here. Consider an
abstract scheduler that decreases a positive pointer by exactly one and, at
pointer zero with index i, refills to pointer i and index i+1. Every successful
non-target transition decreases B_N by exactly one, so this scheduler takes
exactly B_N steps. No sharpness claim is made for the particular Cantor-coded
K215 command decoder.

`K215BoundedScheduler.lean` instantiates the laws using the unchanged current
`EnumPerm.step_eq` and `decode_le`. Its `complete_from` retains the current
direct compiler `build_c222`. As in Source194, a refutation gives halting from
an arbitrary enumerator state because the reset-and-refute candidate works
for every payload reached at its boundary. The converse still needs `Inv`.
The quantifier order is one fixed later candidate working for every reachable
payload, not a different candidate selected separately for each payload.

## Formal status and scope

The standalone `CofinalScheduler.lean` and `BoundedScheduler.lean` compiled
under Lean 4.32.0, commit `8c9756b28d64dab099da31a4c09229a9e6a2ef35`.
The three newly printed profiles are in `BoundedScheduler.log`: monotonicity
uses `propext` and `Quot.sound`; the step and bounded-reach theorems use
`propext`, `Classical.choice`, and `Quot.sound`. They are not advertised as
axiom-free. There is no `sorry` or added axiom declaration.

`evidence/concrete_final_verification.json` records the successful concrete
adapter check, including the exact 14-module production source closure and
all raw compiler outputs. All three concrete profiles report only
`propext`, `Classical.choice`, and `Quot.sound`. The failed first adapter
attempt is retained separately and excluded from acceptance. This component does not rebuild the 215-state TM endpoint,
its source certificate, initialization, runtime sites or set-theoretic
calibration. It does not create an internal ZFC or PA derivation.

Keep the bounded module optional. The practical simplification is the shared
scheduler and current-source adaptation; adding a quantitative theorem by
itself cannot be counted as shortening the accepted endpoint proof.

## Primary source paths

All paths below are relative to the pinned repository.

* `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/EnumPerm.lean`
* `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/EnumDom.lean`
* `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/Enum222.lean`
* `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/Enum254.lean`
* `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/SeedPerm.lean`
* `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KEndpoint215.lean`
* `SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/code/194-scheduler-CofinalScheduler.lean`
* `SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/code/194-scheduler-EnumPerm.lean`
* `Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/simplification/proposals/checked-transport/rocq_seed_rank/refactored/K215F/L1_CompPerm.v`
* `Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/simplification/phase15/README.md`
