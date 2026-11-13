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

## Review of the incoming direct translation, 13 November 2026

The later incoming [PA-TM research archive](../../../../../docs/incoming/pa_tm_research_2026-11-13.zip),
member `pa_tm_research_2026-11-13/report/pa_reverse_translation.tex`, proposes
a more direct route than recoding PA196 into the older native syntax. It
interprets PA196 membership as arithmetic bit membership `B(u,v)` and
its equality as arithmetic equality, while translating the *transposed*
quantifier directly. Thus neither the older decoder's primitive-negation
convention nor its property-code/binder interface has to be reproduced by this
particular route. The report presents an ordinary mathematical argument and
states a conditional transfer theorem; it explicitly does **not** contain
an implemented proof compiler or a new kernel-checked PA biconditional.

The written argument addresses several substantive cases:

* PA proves `B(u,v) → v < u`, hence `¬B(u,u)`. Code 1 translates to
  `B(x₀,x₀)`, so implication to code 1 is provably ordinary negation, and
  the final translated refutation yields PA falsity. Code 0 is a truth alias:
  because `I(0,0)=0`, the translation of that degenerate implication needs a
  fixed proof of `⊤ ↔ (⊤ → ⊤)` rather than a literal syntax equality.
* For a formula `φ` not containing the output label `c`, and distinct source
  labels `a,b`, bounded bit comprehension supplies a set with bits
  `((B(A,z) ∨ z=b) ∧ φ[z/x_b])`. This simultaneously supplies the separation
  and distinguished-point clauses. When **the labels** `a,b` coincide, the
  first antecedent becomes `B(z,z)` under the binder and is false; a singleton
  at the original value of `x_b`, included only when `φ` holds there,
  supplies the remaining clauses. The guard `c≠a,b` and freshness of `c` in
  the property are both used. The equality- and membership-vacuity parts
  then combine with that witness via the propositional gate identity above.
  This collision argument is about equal labels, not merely equal assigned
  numeric values.
* The proposed comprehension proof is a fixed classical PA induction template
  with the input formula substituted into the induction instance. The report
  proposes primitive-recursive proof construction and syntactic proof
  checking, avoiding a uniform truth predicate or a PA reflection principle.
  This is the right kind of uniformity needed for nonstandard proof codes;
  the manuscript does not implement the constructor or check its PA proof.

These checks make the direct route a concrete proof plan; they do **not**
validate all its uniformity and machine-binding claims. In particular, the
report leaves open (1) the exact PA196-checker and Foundation-PA proof-code
conversions, total proof-producing substitution/fresh-variable/comprehension
templates and their PA-internal correctness, and (2) extraction of a native
refutation from an **arbitrary model-length literal halting trace**, including
startup, totalized halting behavior, nonhalting intermediate macro states and
coded sequence bounds. That extraction must also handle the non-injective
stack convention `pair(0,0)=0`: a zero stack and a pushed zero with zero tail
share a numeric code. The external `SoundStack.pop` already handles both
cases, but the proposed internal parallel proof-stack encoding and updates
still need a corresponding all-model argument. The conditional theorem
assumes the machine contracts in PA-verifiable form. The existing forward
physical refinement and external HF soundness do not automatically discharge
those hypotheses. A finite test
of the gate or selected machine traces is not an all-model proof. No concrete
logical counterexample to the written gate cases was found in this review;
that is not a verification of the full claimed primitive-recursive translation
or its connection to the literal machine.

## A bounded invariant for the zero-alias stack

[The certificate-stack note](reverse-cert-stack/README.md) proves an ordinary-natural-number
parallel-certificate invariant that accommodates `pair(0,0)=0`. It checks
certificates only while the numeric stack is nonzero, treats later certificate
cells as ghosts, and returns a fixed proof of truth on underflow. Push and pop
preserve the invariant; for the exact Cantor pair, checking indices less than
the numeric stack code suffices. This gives a concrete finite invariant for a
potential arithmetization, but it is not yet a PA-internal proof or a link to
the PA196 checker and does not discharge the reverse implication.

[The command-extraction note](reverse-cert-stack/COMMAND-EXTRACTION.md) spells
out a conditional proof-producing update for every exact PA196 store command.
It identifies the concrete syntactic constructors and PA-internal induction
that remain to be implemented; it does not bind a literal halting trace.

[The literal-halt extraction note](reverse-cert-stack/LITERAL-HALT-EXTRACTION.md)
spells out how forward projection, positive nonhalt segments, and a bounded
trace comparison could avoid constructing an inverse state map. Its required
all-model induction and determinism lemmas remain unproved here.
