# The smallest next syntactic bridge

This record concerns the PA proof-code comparison, not machine minimization.
The same-language lemma below passed its first narrow kernel check; its C254/ZFC
applications remain unproved.

## Checked all-internal axiom-proof substitution

[`InternalAxiomProofTransport`](../../../../Logic/PeanoArithmetic/BoundedConsistency/Lean/BoundedPAConsistency/InternalAxiomProofTransport.lean) proves, in any IΣ1 model V, for any fixed
encodable/arithmetically definable language L and Delta1 theories T,U:

```text
(∀ p : V, IsFormula L p → p ∈ T.Δ₁Class → Provable U p)
  → ∀ f : V, Provable T f → Provable U f.
```

The hypothesis is restricted to well-formed formulas because a source axiom
leaf already contains that check. An arbitrary Delta1 recognizer is not assumed
to reject every malformed nonstandard raw code. The audit also checks the
stronger unrestricted axiom-premise variant as an immediate caller.

The proof uses Foundation's `Derivation.induction1` with the Sigma1 predicate
`Derivable U (fstIdx d)`. Logical rules reconstruct a target derivation of the
same exact coded end sequent. The explicit shift case uses `Derivable.shift`.
The source axiom case obtains a target singleton-sequent proof from the supplied
represented provability witness and weakens it to the source end sequent.
No target-proof size bound, single uniform proof selector, standardness premise,
or recursion on an external Lean proof is required. Existential target proof
codes suffice for consistency transfer.

The exact upstream APIs are in pinned Foundation
`Foundation/FirstOrder/Bootstrapping/Syntax/Proof/Basic.lean`:
`Derivation.induction1` line551, the weaker axiom-inclusion `of_ss` line656,
`Derivable` constructors lines686–735, and the represented singleton/provability
bridge lines830–837. This extension is a small internal counterpart of
substituting proofs for axiom leaves; it is not an interpretation theorem.

The [fresh check](results/internal-axiom-proof-transport-verification.json) and
[independent review](results/internal-axiom-proof-transport-review.json) record the exact source and audit.
Source2.159s and audit1.959s; three theorem reports, seven generic callers,
zero warnings; all reports contain only Lean's standard three axioms. The
checker builds no local prerequisite modules: its sole source import is the
cached Foundation Proof.Basic. Provider source/object identities, dependency
pins/clean tracked trees and compiler identity are recorded and rechecked;
no whole external dependency-cache attestation is asserted.

## Why this is useful, and its exact limitation

This implements the PA plan's weaker sufficient proof-transport interface: an
internally total *selected output proof code* for every valid source proof is
unnecessary.
For a same-language step, all-internal provability of its axiom families is
sufficient, and Sigma1 induction composes those existential witnesses through
nonstandard derivations. ModelCodedCoreCompiler still has a different useful
scope: its source proof is a fixed standard finite proof, specialized at an
arbitrary internal matrix. Neither interface replaces the other.

The new lemma does not itself compare different formula presentations or
relativize formulas. It therefore does not consume NativeTheory254,
WFTheory, or ChoiceCalibration254 directly. Those current results use
external semantic transfer. Their ordinary hypotheses are not the displayed
all-internal axiom-provability hypothesis.

## Concrete next leaf: represented set-schema axiom constructors

The smallest specific set-theoretic client is to supply the existing
Separation/Replacement recognizers with literal witnesses, initially for
shift-fixed internal matrices:

```text
(K : Semiformula V ℒₛₑₜ 1) → K.shift = K →
  (sepBody K).val ∈ (𝗭𝗙 : SetTheory).Δ₁Class
(K : Semiformula V ℒₛₑₜ 2) → K.shift = K →
  (repBody K).val ∈ (𝗭𝗙 : SetTheory).Δ₁Class.
```

Then `TProof.byAxm` produces actual represented ZF/ZFC proof carriers. This
is proposed/unbuilt. It can copy the exact *pattern*, not the arithmetic
axiom, of `ModelCodedInductionAxiom.indBody_mem_peano_of_shift_fixed` (line39).
The witnesses are m=0, b=the typed closed schema body, and the supplied raw K;
existing code-growth and empty-substitution lemmas discharge the recognizer's
bounds and recovery condition. The required bodies and raw graphs already
exist in ZFCinPA/SeparationDelta1.lean and ReplacementDelta1.lean. Their final
Theory.Δ₁ instances provide recognizers, but their `mem_iff` proofs ultimately
use `SchemaClosure.schemaRecognizer_quote_iff` line179, whose theorem is
explicitly over Nat quotations. That is not yet the stated all-internal
constructor.

This initial closed-matrix client deliberately retains its shift-fixedness
premise. Arbitrary free parameters still require a represented closure/rebind
adapter or an explicit internally indexed bound-variable context. It must not
be sold as arbitrary-matrix schema transport. Foundation's
Incompleteness/InductionSchemeDelta1.lean lines33–36 explicitly says that the
free-to-bound `fixitr` half of universal closure is still open there.

## Shortest route around unnecessary internal model construction

For the direction C254-refutation → ZFC-refutation, a direct represented
soundness compiler can avoid both WF and L: ZFC proves CP, full native GIC,
and IR. It still needs a represented *all-code* named/base4 decoder (including
truth0, F1, arbitrary named binders and both bundle inequalities), plus uniform
ZF proofs of the actual decoded bundle instance. Numeric arithmetic and
C254 checker history alone do not supply this syntax map.

The Collection proof can be handled by a fixed standard derivation in a
placeholder-extended set language **with its finite used schematic axioms
explicitly supplied**. Merely lifting ordinary ZF/ZFC into the extended
language does not grant Separation/Replacement for the opaque new predicate.
Thus a generic placeholder theorem cannot silently erase that leaf obligation.
The new set-schema constructors would discharge those actual instantiated
axiom leaves after syntax/coherence checks. A set-language version of the
heterogeneous core compiler can reuse the existing ZFCinPA/SetPlaceholders
translation equations; its old compiler currently requires shift-fixed Ks.

The reverse ZFC-refutation → C254-refutation still requires the actual
syntax-sensitive L and WF/quotient interpretations (or another proved finite
interpretation), then a represented logical-presentation compiler. In
particular, L-Separation and L-Replacement use the recursively relativized
*source set-language formula*, not an arbitrary predicate whose amenability
can be assumed. A finite checked Choice-in-L proof handles the fixed Choice
axiom, but cannot replace those schema selectors.

There is no established shortcut from the current external equiconsistency
alone to this internal statement. A computable search may terminate on every
standard valid input while its termination on valid codes is unprovable in PA.
Likewise all fixed standard templates do not quantify over nonstandard proof
codes. The checked all-internal leaf-substitution lemma narrows the remaining
work to actual axiom/proof-translation interfaces without claiming them.

A portable narrow check is available:

```sh
python -B Computability/BusyBeaver/Research/ZFC/check_internal_axiom_proof_transport.py \
  --repo /path/to/Proofs --dependency-root /path/to/built/dependency-checkout \
  --output /outside/new-empty-internal-axiom-transport-check
```

The maintained-default preflight is recorded separately and invokes no Lean
process. Its source/audit bytes are identical to the successful first check.
