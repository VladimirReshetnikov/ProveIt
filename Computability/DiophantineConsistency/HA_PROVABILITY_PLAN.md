# HA provability of the current consistency equations

The owner strengthened the goal on26 October2026: prove in Lean both the
current Diophantine equivalence and that the equivalence is provable in
intuitionistic Heyting Arithmetic (HA). The owner then clarified that a
Lean proof that an HA proof EXISTS is sufficient. There is no requirement
to print, normalize, serialize or enumerate a literal HA proof certificate.
This supersedes encoded ZFC derivation as the primary remaining target.
Equation-size reduction, frequent detailed commits and normal fast-forward
synchronization with origin/main continue.

## Exact target and established results

For each selected literal polynomial P, the intended endpoint is a Lean
theorem asserting `HA.Proves equivalenceSentence`, with `HA.Proves` meaning
existence of a finite derivation using intuitionistic first-order logic,
the usual arithmetic axioms and the full first-order induction schema.
`HA.Proves` is now defined in [HAProofs](Lean/DiophantineConsistency/HAProofs.lean)
and independently checked. The particular `equivalenceSentence` and its
completed provability theorem remain targets.

The sentence must express, in arithmetic, that P has no positive integer
solution iff the actual sealed-ZFC proof predicate has no refutation.
Use P(x+1) on natural variables, represented as equality of two natural
polynomials, for the positive-domain side. The ZFC side must be an actual
arithmetization of the repository's proof convention, not an uninterpreted
atom named ConZFC. A primitive-recursive function-language extension would
need a proved conservative elimination into conventional HA.

The external Lean equivalence is already closed for the maintained
14-positive/65-operation/degree150 equation and the three accepted
13-positive forms, in
[CurrentPositiveZero2011](Lean/DiophantineConsistency/CurrentPositiveZero2011.lean).
The current scaled auxiliary replacement is also covered by
[CarrierScaledAuxiliary118](Lean/DiophantineConsistency/CarrierScaledAuxiliary118.lean).
Their independent endpoint replays and axiom reports are documented in
the [formalization plan](LEAN_EQUIVALENCE_PLAN.md). A source-authenticated
361-module custom dependency validation has passed at the pinned09eaa
snapshot:191 fresh and170 authenticated reuses. A separate15-command
post-merge refresh also passed; see the
[original replay](reviews/current-positive-zero2011-closure-replay.md) and
[limited refresh](reviews/current-positive-zero2011-refresh-replay.md).
Neither is an HA proof-existence theorem.

[ObjectCurrentEquation2011](Lean/DiophantineConsistency/ObjectCurrentEquation2011.lean)
supplies a set-theory-language no-solution sentence with exact arbitrary-model
positive-domain semantics. That work is retained, but the new HA target
needs an arithmetic sentence and intuitionistic derivability. No further
ZF-model-only completion is required merely to satisfy the new goal.

The arithmetic equation sentence is now supplied by
[ArithmeticCurrentEquation2011](Lean/DiophantineConsistency/ArithmeticCurrentEquation2011.lean).
Its `unsolvabilitySentence` compiles the exact current fourteen-variable
successor-shifted expression into the ordinary `0,S,+,*` language. All four
complete coefficient ports are actual compact binary numerals, not free
symbols. Exactly fourteen universal binders close the no-zero formula.
The generic compiler has exact semantics over every commutative semiring;
its natural-number interpretation is precisely no positive integral zero
of the displayed polynomial. Three fresh leaves and ten standard-only
axiom reports passed [independent review/replay](reviews/arithmetic-expression-lean-peer.md).
This binds the equation side. The arithmetic ZFC-checker sentence and the
HA equivalence derivation remain open.

[HADeduction](Lean/DiophantineConsistency/HADeduction.lean) now composes
actual finite HA proofs by concatenating their supporting axiom lists.
[HANegativeStability](Lean/DiophantineConsistency/HANegativeStability.lean)
constructs intuitionistic stability proofs for negations, conjunctions and
universals, with the full context shifted at universal introduction.
Four leaves passed [independent replay](reviews/ha-deduction-stability-lean-peer.md)
and sixteen reports using only `propext` and `Quot.sound`.

[HAEquationStability2011](Lean/DiophantineConsistency/HAEquationStability2011.lean)
binds this to the literal current sentence: HA proves `¬¬NoZero → NoZero`.
Its derivation has an empty context and an empty arithmetic axiom list.
Both leaves passed [independent replay](reviews/ha-equation-stability2011-lean-peer.md)
and four standard-only reports. This proves a particular logical property
inside HA. It does not prove NoZero itself or the consistency equivalence.
In particular, double-negation stability alone does not identify a formula
with its full Gödel–Gentzen translation. The translation comparison for
the complete no-zero/consistency equivalence remains to be proved.

## Two viable proof routes to audit

One route proves, within HA, both positive-witness implications:

```text
an actual coded ZFC refutation -> a positive zero of P;
a positive zero of P -> an actual coded ZFC refutation.
```

Negating these implications yields the requested consistency equivalence
intuitionistically. There is no need to extract a refutation from a double
negation of consistency. A new external witness interface can first expose
the existing arithmetic constructions directly from a supplied refutation,
avoiding the current convenience wrapper's classical double-negation step.
That interface alone will not constitute an HA formalization.

A second route proves existence of a PA derivation and applies a verified
Gödel–Gentzen translation plus HA equivalence to the original sentence.
This may avoid reconstructing every external proof in intuitionistic form.
The desired no-witness statements suggest a negative arithmetic formulation,
but the exact translation/stability obligations must be proved for the
chosen proof-checker formula and equation sentence. A standard-number Lean
iff does not itself provide the required PA derivation. Classical Tarski
validity alone likewise does not establish intuitionistic derivability.

The Foundation library already has the first-order Gödel–Gentzen theorem
in Lean, as well as the Coq port. The small
[FoundationTheoryGG](Lean/DiophantineConsistency/FoundationTheoryGG.lean)
adapter now lifts it to finite theory assumptions, preserving the actual
translated axiom list. Both leaves passed an
[independent fresh replay](reviews/foundation-theory-gg-root.md), with59
prerequisite modules authenticated against their v4.32 build traces.
Arithmetic axiom and induction preservation, syntax interoperability and
the particular target's stability remain separate obligations. See the
[existing API audit](reviews/ha-existing-foundation-api-audit.md).
An existence theorem via general proof translation is acceptable: no
expanded derivation for the enormous fixed integers must be displayed.

## Concrete foundational checks

- `PAHF.PASyntax` has reusable arithmetic syntax and induction axioms, but
  its proof calculus has unrestricted excluded middle. It is PA, not HA.
  The existing type-valued bounded-PA proof trees likewise contain LEM.
  Removing LEM must be explicit in a genuine new derivability relation;
  erasure into PA is only a one-way validation.
- `HAProofs` now supplies that relation: sixteen intuitionistic deduction
  rules with capture-avoiding quantifier side conditions, a finite list of
  conventional arithmetic axioms, and full formula induction. Its
  [author receipt](reviews/ha-proofs-author.md) and
  [independent replay](reviews/ha-proofs-lean-peer.md) record ten axiom
  reports and authenticated reuse of five prerequisite modules. This
  defines genuine HA theoremhood; it is not yet the desired HA theorem.
- The shallow `PA.Model` has induction for every Lean predicate. An
  argument using that stronger semantic bundle must not be mislabeled
  validity in every first-order PA model. Formula-instance induction and
  ordinary external induction are different interfaces.
- `PAHF.PASyntax` is a large monolithic dependency. Any reused object must
  have authenticated source/toolchain provenance. A small independently
  namespaced arithmetic calculus is preferable to pretending a partial
  source extraction is that accepted module.
- Standard Lean axioms in an external audit do not identify which HA
  induction instances or proof rules justify the arithmetic argument.
  Conversely, classical reasoning in the Lean METATHEORY is allowed when
  proving existence of a genuine HA derivation; it must not be silently
  inserted as an HA object-language rule.

## The machine calibration needs its own arithmetic audit

The literal715-digit machine is linked to refutations through
[KEndpoint215](../BusyBeaver/Lean/BusyBeaver/ZFC/KEndpoint215.lean) and
[KEndpoint](../BusyBeaver/Lean/BusyBeaver/ZFC/KEndpoint.lean).
The current lower chain is not presented as a direct ZFC proof checker:
`c222_of_zf_refutation` uses C222 semantic completeness, the seed/model
construction and `zf_consistent_of_formSeed`. The final ZF/ZFC transfer
uses `ConstructibleChoice.zf_refutation_iff_zfc_refutation`.

These are valid external Lean interfaces at their recorded scope. Their
proofs do not automatically establish arithmetic provability of this
calibration. There is, however, substantial completed internal arithmetic
machinery: `ZFCinPA.ValidatorConsistencyEquivalence` proves the validator
consistency equivalence in IΣ₂ and PA; `LSchema` already supplies internal
ZF/ZFC Choice transport; and `BinaryConsistencyRotation240` proves the
consistency equivalence for the exact represented Rotation240 binary
machine in IΣ₂ and PA. Reuse these results rather than reconstructing them.

The remaining comparison concerns the actual215 table and boot seed,
the changed C222 calculus, and the distinct coded proof conventions.
The user-specified `k225-formal/verification/k215/README.md` explicitly
separates its external endpoint from an internal PA theorem. Its215
candidate counter starts at4; the represented240 validator uses different
startup data and the older254 calculus. No definitional rewrite between
these has been found in the inspected sources. Existing represented
lookup and positive-clock simulation frameworks are useful interfaces,
but their exact215 contracts must be proved. The
[constructive/source audit](research/ha-current-equation-constructive-audit-20261026.md)
records these concrete differences and the searched scope. This is an
open comparison obligation, not a claim of unprovability in HA.

[CurrentWitnessEquivalence2011](Lean/DiophantineConsistency/CurrentWitnessEquivalence2011.lean)
now proves the external direct equivalence between positive zeros and
the literal `BProv ZFCax_s [] Form.fBot`. Its final negation composition
uses no double-negation elimination; imported calibration and arithmetic
are not thereby internalized. See the
[root replay](reviews/current-witness-equivalence2011-root.md).

Two bounded arithmetic prerequisites are now checked:
[NativeFiniteCarry](Lean/DiophantineConsistency/NativeFiniteCarry.lean)
constructs the actual quotient carries by at most `57*card(ι)` iterations
in the current radix47 setting, retaining wraparound and reset identities;
[BoundedPellDivisibility](Lean/DiophantineConsistency/BoundedPellDivisibility.lean)
finds a positive divisible Pell ordinate at index at most m², including
the actual fresh-seed shape. Both main/check pairs passed independent
[root replay](reviews/finite-carry-bounded-pell-root.md), with21 standard-only
axiom reports. Their bounded algorithms are standard-arithmetic results,
not yet HA derivations. The frozen current witnesses were not replaced.

Remaining arithmetic refactorings include replacing real-valued Pell
estimates by denominator-cleared integer inequalities. Under the
PA/negative-translation route, each
refactoring should be justified by its contribution to PA formalization;
surface elimination of `Classical.choice` is not the goal by itself.

## Next reviewable checkpoints

1. Authentic HA derivability and basic arithmetic/induction interfaces are
   checked, with one-way classical embedding and focused binder checks.
2. The literal arithmetic equation sentence is checked. Supply the exact
   arithmetized ZFC-refutation sentence and its coding comparison, retaining
   the actual proof convention.
3. Establish the applicable proof-translation/stability theorem or the two
   direct internal witness transformations. Record which remaining native,
   Pell and machine lemmas need PA/HA proof-existence witnesses.
4. Compose a CLOSED Lean theorem asserting existence of an HA derivation
   of the actual equivalence. A desired-provability hypothesis is not a
   completed endpoint.

No HA equivalence proof-existence theorem is claimed at this checkpoint.
The decimal equation page and all14 distinct unsubscripted unknowns are
preserved. The goal remains active.
