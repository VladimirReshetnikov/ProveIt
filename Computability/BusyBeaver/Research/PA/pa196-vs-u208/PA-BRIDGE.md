# PA196: a route to the missing internal implication

This note identifies possible reuse and outstanding obligations. It proves no
new PA sentence. Let `H` be the **exact literal blank-tape halting sentence**
`PA196.Arithmetic.haltingSentence`, and let `N` be its negation. The upstream
[`Independence.lean`](../jamesyc-upstream/pa196/PA196/Independence.lean)
proves `PA ⊢ N → Con(PA)`; the other half needed for the desired biconditional
is `PA ⊢ H → ¬Con(PA)`. In classical PA this is equivalent to
`PA ⊢ Con(PA) → N`. Standard-model nonhalting does not supply it.

## An intermediate checker interface

Write `Ref(c)` for the formula in
[`RefutationGraph.lean`](../jamesyc-upstream/pa196/PA196/Arithmetic/RefutationGraph.lean).
Its all-model graph theorem identifies `Ref(c)` with
`Checker.verifyValue c = 2`; the checker encodes an accepted proof of code 1.
The following two **proposed**, not established, all-model theorems would be
sufficient, for every model `V` of ordinary PA:

1. If `V ⊧ H`, there is `c : V` with `Checker.verifyValue c = 2`.
2. If `Checker.verifyValue c = 2`, then `Provable theory (qqFalsum : V)`.

Together they imply `H → ¬Con(PA)` in every PA model; with the existing
formula representations and arithmetic completeness, they would yield the
corresponding syntactic PA theorem. One may instead use a different coded
native proof predicate, but its equivalence to the machine-generated proof
objects must then be demonstrated for **nonstandard** model elements too.
The two steps isolate machine-run extraction from proof-theoretic soundness.

The existing directions are the reverse of those needed above:

* [`RefutationMachine.lean`](../jamesyc-upstream/pa196/PA196/Arithmetic/RefutationMachine.lean)
  proves `refutation_implies_literal` in every PA model, from an accepted
  `c` to `V ⊧ H`, and packages that as a PA theorem.
* [`FoundationNativeRefutationTransport.lean`](../jamesyc-upstream/pa196/PA196/Arithmetic/Transport/FoundationNativeRefutationTransport.lean)
  proves that an internal PA refutation supplies an accepted checker code.
  [`InternalConsistency.lean`](../jamesyc-upstream/pa196/PA196/Arithmetic/Transport/InternalConsistency.lean)
  packages the contrapositive as `noRefutationSentence → Con(PA)`. This is
  **not** checker soundness in PA.
* [`Logic/CommandSoundness.lean`](../jamesyc-upstream/pa196/PA196/Logic/CommandSoundness.lean)
  maintains ordinary-Nat derivability of the live store and stack, while
  [`Logic/Soundness.lean`](../jamesyc-upstream/pa196/PA196/Logic/Soundness.lean)
  proves code 1 false using a concrete external hereditarily finite model.
  The source explicitly describes that soundness proof as external; it is not
  a uniform internal translation of arbitrary proof codes to PA proofs.

## Reusing the physical execution machinery

The imported arithmetic development already contains useful all-model pieces:

* [`InternalCodedSourceTrace.lean`](../jamesyc-upstream/pa196/PA196/Arithmetic/Machine/InternalCodedSourceTrace.lean)
  proves totality of model-length coded source traces, including a PA theorem.
* [`EndpointInternalCodedSourcePhysicalStep.lean`](../jamesyc-upstream/pa196/PA196/Arithmetic/Machine/EndpointInternalCodedSourcePhysicalStep.lean)
  binds a source frame to a positive physical segment using `physical_step`.
  Its disjunction allows either a physical halt segment or a successor frame.
* [`EndpointInternalCodedSourcePhysicalTrace.lean`](../jamesyc-upstream/pa196/PA196/Arithmetic/Machine/EndpointInternalCodedSourcePhysicalTrace.lean)
  iterates the refinement by internal PA induction and proves
  `trace_halt_physical`: a coded **source** halt gives a physical halt.
* [`StartupLiteralTransport.lean`](../jamesyc-upstream/pa196/PA196/Arithmetic/Machine/StartupLiteralTransport.lean)
  connects source halting after the fixed startup to the literal arithmetic
  halting sentence, and
  [`StateMapProjection.lean`](../jamesyc-upstream/pa196/PA196/Arithmetic/Machine/StateMapProjection.lean)
  handles the internal sparse-to-literal control projection.

A plausible reverse theorem would show that a literal halt trace of internal
length `t` forces a source halt within a bounded model-length source trace.
One way to investigate it is to strengthen the physical-step/lift invariant
so that, when the current source instruction is not halt, its positive segment
ends at a nonhalt frame, then use model-internal trace determinism and the
fact that each simulated source instruction consumes at least one physical
step. An induction through `t+1` source steps would then preclude a physical
halt by time `t` unless a source halt had already occurred. This is a proof
plan, not a theorem supplied by the present files: the existing `Lifted`
disjunction by itself does not identify an early physical halt with a source
halt, and arithmetic representation, determinism, halted-source behavior and
partial final segments must all be checked. The exact sparse halt encoding
`215` and the literal table's halt label `196` must not be conflated.

After obtaining a source halt, another missing all-model invariant must turn
its command/stack history into a PA196 checker proof of code 1. Merely replaying
standard-Nat `SoundStore` or compiling a pre-existing checker proof in the
forward direction is insufficient.

## Recoding and freshness

The original-code freshness fact already exists externally:
[`Logic/Decode.lean`](../jamesyc-upstream/pa196/PA196/Logic/Decode.lean)
proves `NumericDecode.fuel_names_bound`, `NumericDecode.self_fresh` and
`Named.eval_fresh` for standard `Nat` and the imported named syntax. To use
this in an arbitrary PA model, a represented numeric decoding/occurrence
predicate and a uniform internal boundedness/freshness argument are still
needed. In particular, the PA196 gate uses the same number `c` as the
property's original code and as its bound-variable label; after code recoding,
the label remains `c` while the new code need not equal `c`. A rule that only
accepts a binder equal to the *new* property code cannot be applied directly.

There is also a distinct decoder issue. PA196's decoder treats nonzero
implication-tagged codes uniformly as `.imp`. The imported earlier
[`M6/Logic/NativeDecode.lean`](../jamesyc-upstream/pa196/M6/Logic/NativeDecode.lean)
treats such a code with consequent `1` as primitive `.neg`. For example,
`4 * pair(0,1) = 8` decodes in PA196 as truth implying `mem(0,0)`, but in
that M6 decoder as the negation of truth. These have the same truth value in
an irreflexive interpretation, where `mem(0,0)` is false; they are not the
same named syntax and can differ in a structure with reflexive membership.
A recoder or proof translation must handle this convention explicitly rather
than assert a syntactic identity after swapping quantifier components.
This observation concerns the cited imported M6 decoder; an independently
chosen target decoder needs its own checked specification.

For the guarded gate, with equality vacuity `Δ`, membership vacuity `V` and
quantified separation component `Q`, the old and new propositions are
`G = ¬(V → Q)` and `F = ¬(Δ → (V → Q))`; classical logic gives
`F ↔ (Δ ∧ G)`. This does not itself build a uniform W+irreflexivity proof of
`F`, solve the original-binder/recoded-property mismatch, or translate arbitrary
checker derivations. See [COMPARISON.md](COMPARISON.md) for the machine and
source comparison and the remaining proof obligations.
