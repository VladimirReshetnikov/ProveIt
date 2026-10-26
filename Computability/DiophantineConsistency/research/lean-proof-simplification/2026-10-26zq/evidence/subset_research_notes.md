# A stronger cyclic subset-sum theorem removes the Boolean detour

Review baseline: `9f35798db4a63c25e435fca14d75931144657d7e`.

Late-head scope update: see `LATE_HEAD_SCOPE_ADDENDUM.md` for refresh
`f00ba53b331833c6cb64707bd90e48489e5610f5`. That refresh adds physical
position and one-dummy safety results; the baseline qualifications below
are not assertions that those ingredients are absent from the refresh.

## Primary proposal

Replace the coprime-cardinality interval lemma with the following stronger
statement:

> For every `0 < a < T` and every `u : ZMod T`, there is an `a`-element
> finite subset whose sum is `u`.

This statement holds without assuming `Nat.Coprime a T`, that `T` is a prime
power, or that `ZMod T` is a field. The input group must be cyclic: the result
is not asserted for arbitrary finite abelian groups.

The current proof obtains its subset by translating a consecutive interval.
Such a translation changes the sum by `a*t`, and hence requires `a` to be a
unit modulo `T` to reach every target. The new construction allows one gap
in an interval. That extra shape freedom changes sums by one and removes
the unit condition.

### Explicit witness

Let `sigma = 0 + 1 + ... + (a-1)` and let `d` be the representative of
`u - sigma` in `[0,T)`. Divide `d = a*q + r`, with `0 <= r < a`. Select the
strictly increasing numbers

```
x_i = i + q + (if a-r <= i then 1 else 0),   0 <= i < a.
```

Their sum is `sigma + a*q + r = sigma + d`. The inequality

```
T-1 <= a*(T-a)
```

follows from `(a-1)*(T-a-1) >= 0`, so `d <= a*(T-a)`. Thus `q <= T-a`, and
the boundary case `q = T-a` forces `r = 0`. These facts show every selected
number is strictly below `T`; casting to `ZMod T` therefore preserves
distinctness and cardinality.

### Why the improvement is substantive

For `T=4` and `a=2`, every translated consecutive pair has sum `2*t+1`,
which is odd. The new construction also supplies `{1,3}` for sum zero and
`{0,2}` for sum two. It handles a cardinality which the current interval
method cannot use.

## Consequence for the affine controller

The actual current orbit provides all weights `1+C0*z` modulo `C0*T`.
Assume `0 < C0 < T`. Given a target `t`, choose its least positive
cardinality representative `a` modulo `C0`, so `1 <= a <= C0`.

Use the existing modular-coordinate lift to write

```
t = a + C0*u   in ZMod(C0*T).
```

The new subset-sum theorem supplies an `a`-element subset of `ZMod T`
summing to `u`. Its affine weights sum to `t`. Transporting that subset
through the proved coordinate equivalence preserves cardinality.

This makes the optional Boolean translate unnecessary in the arithmetic
coverage theorem. The prime condition, `p | C0`, prime-power shape
`T = p^n`, nonzero auxiliary weight, and coprimality-selection argument
can disappear from that theorem. They remain where independently needed
for the actual power orbit and rank-unit proofs.

The new output bound **must** be `a <= C0`, not the old strict `a < C0`:
a nonzero target with zero projection to `ZMod C0` requires a positive
multiple of `C0` as its selected cardinality. Since `C0 < T`, the enlarged
bound still meets `a < T`. This is a deliberate interface improvement,
not an unchanged-signature replacement.

The result is not a proof that every arithmetic subset is a safe physical
dummy placement. The existing physical safety and rank-variation bridges
must still be composed. It also does not claim a reduction in the number
of variables of the printed Diophantine equation.

## Exact source targets

- `ControllerIntervalSums.lean`: `interval_sum`, `startFor`,
  `startFor_equation`, `targetInterval`, and its sum/cardinality interface.
- `ControllerAuxiliaryChoice.lean`: `exists_boolean_sub_ne_zero` and
  `exists_coprime_cardinality` become unnecessary in the new arithmetic
  coverage path.
- `ControllerResidueLift.lean`: replace `exists_subset_boolean_sum` with
  the Boolean-free endpoint; retain or extract `exists_coordinate`.
- `ControllerOrbitTransport.lean`: use the new finite subset instead of
  `targetInterval` in its image construction. Its generic affine finite
  sum calculation remains useful.
- `CurrentPowerCoordinates2011.lean`: the already-proved actual orbit is
  the concrete input to the new theorem, with `C0 = d*auxiliary` and
  `T = auxiliary^k` when `C0 < T` has been established.

The only non-check production client of `targetInterval` found by exact
symbol search is `ControllerOrbitTransport`. Retaining every historical
interval helper as a public compatibility API will reduce the net source
deletion; no global line-saving figure is asserted in these notes.

## Boundary conditions

- `a=0` fails in any nontrivial cyclic group for a nonzero target.
- `a=T` has only the complete group as a subset, hence only one possible
  sum; for example `T=3,a=3` cannot realize target one.
- `T=1` has no cardinality satisfying `0<a<T`; the generic theorem does
  not incorrectly claim a nontrivial sum range at that endpoint.
- The natural interval theorem permits `a=T,d=0`, exactly as it should.
- The affine bound `C0<T` is necessary for the stated uniform result.
  If `C0=T=2`, the affine weights are `{1,3}` modulo four, whose subset
  sums are `{0,1,3}` and miss two.

## Novelty decision

Agent `/root/novelty_audit` screened 1,295 textual members in all 23 placed
packets and the five incoming ZIPs, and cleared this proposal. Nearby old
ideas concern inverse-invariance of finite sets, additive aligned-cell
equivalences, coefficient fibers, sparse physical placements, and native
rank scalar coordinates. None proves noncoprime fixed-cardinality cyclic
subset-sum surjectivity or removes the optional Boolean arithmetic term.
The mathematics is elementary and no claim of literature-wide novelty is
made; the novel contribution here is the proof architecture relative to
the specified audited corpus.

## Supporting weaker abstraction

`SubsetTranslation.lean` proves that any finite seed realizes every sum
through translations when multiplication by its cardinality is surjective.
It includes a `ZMod` specialization from coprimality and preserves any
translation-invariant property of the seed. This is independently checked,
but the stronger theorem above is the principal proposal. Do not count the
weaker abstraction as a second removal of the same controller complexity.

## Validation

`RestrictedSubsetSums.lean` compiled successfully with Lean 4.32.0 and the
existing mathlib v4.32.0 cache. The compiler exit code is zero. Both printed
endpoint axiom reports list exactly `propext`, `Classical.choice`, and
`Quot.sound`; there is no `sorryAx`, new axiom, or native-decide dependency.
The file contains generic theorems for every allowed modulus and
cardinality, not just bounded examples. `RestrictedSubsetSums.log` is the
retained compiler output. An object file was produced for checking the
affine composition; source and log, rather than platform-specific objects,
are the intended portable deliverables.

The final proof does not use `nlinarith`. Its two nonlinear-looking bounds
use exact natural multiplication cancellation and a successor-product
identity, followed by `omega`. Imports are restricted to `ZMod.Basic`,
finite-sum interval/ring lemmas, and `SplitIfs`. This avoids loading the
entire tactic umbrella merely to establish the subset theorem.
