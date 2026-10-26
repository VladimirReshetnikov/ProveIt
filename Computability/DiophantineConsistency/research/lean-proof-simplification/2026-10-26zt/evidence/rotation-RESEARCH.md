# Exact rotation congruence without Boolean hypotheses

## Target and source contract

Pinned source: `f00ba53b331833c6cb64707bd90e48489e5610f5`.
`Computability/DiophantineConsistency/Lean/DiophantineConsistency/CurrentWordRephase2011.lean`,
especially `rotation_eq` (lines 67–74), `normalization_rephase` (77–86),
and its production caller `marked_packing_rephase` (104).

The current proof invokes `NativeBooleanRotation.rotation_zero_phase` twice.
That theorem needs `∀ i, c i ≤ 1` because it identifies an individual
binary rotation with a plain permutation of its original digits.
The rephase theorem needs only equality of two binary rotations. Both
rotations run the same digit-normalization operation, so its digit bounds
are irrelevant to their equality.

## Mathematical mechanism

The literal definition is

```
binaryRotation v W c =
  rotate (shiftDigits (2^v) (2^(W%v)) c) (W/v : ZMod n).
```

It depends on W only through the pair
`(W % v, (W / v : ZMod n))`. Consequently

```
hphase : W % v = W' % v
hshift : (W/v : ZMod n) = (W'/v : ZMod n)
------------------------------------------------
binaryRotation v W c = binaryRotation v W' c
```

for every numeric function c. No Boolean, digit-size, carry, word-bound,
or matching premise is used. The proof is `unfold binaryRotation; rw
[hphase, hshift]`.

For current strides `W = 47*(2011*s)`, both phases are zero and the already
proved `physical_shift_eq` supplies the quotient-residue equality. The
patched proof thus simplifies the definition directly. It deletes `hc`
from `rotation_eq` and `hd` from `normalization_rephase`; the latter now
transfers any supplied normalization of arbitrary natural dummy controls.
The same carry and digit functions are retained.

The complete `marked_packing_rephase` and `packing_rephase` statements
retain `hd`: scalar and mask reconstruction still need that bound. This
proposal does not weaken those proofs by silently dropping it.

## Second-order extension: exact period normal form

The identities

```
(W % (v*n)) % v = W % v
(W % (v*n)) / v = (W/v) % n
```

give

```
binaryRotation v (W % (v*n)) c = binaryRotation v W c.
```

Therefore congruent displacements modulo the complete binary period `v*n`
produce *equal digit functions*, even at nonzero partial phases and for
unbounded digits. This is stronger than equality of the associated packed
words modulo `2^(v*n)-1`. It provides a canonical displacement parameter
for generic normalization transport. It never asserts equality of the
ordinary multipliers `2^W` and `2^W'`.

This extension belongs to the same proposal; it should not be counted as a
second independent novelty claim.

## Why the premise removal matters

For radix eight and a constant digit word c=8, `binaryRotation 3 0 c` is
the constant word one, not c. Thus generalizing the Boolean lemma itself
would be false. Nevertheless shifts differing by 3*n still give identical
normalized words. The supplied control example checks both facts.

## Novelty audit

The independent novelty reviewer retained this after scanning all a–zj
proposal prose. Closest prior items were:

* Packet a, `source_notes/digits-review.md`:139–165, half-radix and scaled
  rotation interfaces.
* Packet i, deriving `word_rotate` from point-mass convolution.
* Packet p, arbitrary bit-phase sparse temporal support.

Those concern digit values, scalar convolution, or sparse support. The
new delta is exact equality from the definition's two control coordinates,
and removal of the unrelated Boolean prerequisites in the newly added
rephase client. Prior carry-record and normalization-coherence ideas are
assumed available; no saving is claimed from recreating them.

## Artifacts and validation scope

* `RotationCongruence.lean`: compiled with Lean 4.32.0 against freshly compiled pinned
  `NativeCyclicConvolution` and `NativeCyclicRotation` modules. All three
  reported theorem axioms are `[propext, Quot.sound]`. The exact numeric
  47/2011 proof-body specialization and arbitrary-large-digit controls passed.
* `RotationPeriod.lean`: compiled successfully (exit 0) with Lean 4.32.0.
  The stronger period-normalization theorem and its congruence/periodicity
  corollaries report only `[propext, Classical.choice, Quot.sound]`.
  The base coordinate congruence uses `[propext, Quot.sound]`.
* `rephase-assumptions.patch`: concrete API-changing proposal, including the
  one production call and one focused check call. The main source shrinks
  from 122 to 120 physical lines. This tiny line reduction is secondary to
  the two weakened theorem interfaces. The full production-module patch
  has not been compiled in this run unless later validation says otherwise.
* `patched/`: complete candidate versions of the two modified files.
* `patch-metadata.json`: baseline digest, line counts, and validation scope.

The two pinned current rotation/convolution source modules were freshly
compiled in an isolated object overlay before the final kernel replays.
Their direct project dependency `Diophantine.Paper1982.Master2` was fetched
through GitHub at the same pin and its Git blob exactly matches the cached
source (`2fa05bcc59fdc466875b792930f92f398d0dfc71`). Deeper project and
Mathlib dependencies were reused from existing Lean 4.32.0 caches. This is
a focused current-definition check, not a clean rebuild of the entire project.

## Adoption

Apply the patch only together with its caller change. Compile the two
modules and search all callers of the two changed theorem names. Retain
the current noncongruent-shift negative control. Add a normalization
transport check with an arbitrary numeric dummy map, conditional on its
existing `Facts`; do not assert that bounded normalization exists for
arbitrary unbounded inputs. A compatibility wrapper may retain an unused
old Boolean premise if preserving the old public signature is preferred.

## Final validation and exact boundary

All four final compiler invocations returned exit code zero: pinned
NativeCyclicConvolution, pinned NativeCyclicRotation, RotationCongruence,
and RotationPeriod. `fresh-validation.json` records direct subprocess
return codes, source/output hashes, timings, and every axiom report.
The generic coordinate and period kernels require no `NeZero n` instance:
the three rotation definitions only apply functions and totalized natural
arithmetic, with no finite sum. At n=0 or v=0 the proposed period is zero;
the theorem remains an ordinary reflexive-period statement. No least-period
claim is made. The current production theorem keeps its existing positive
cell-modulus context because `physical_shift_eq` supplies its source bridge.
