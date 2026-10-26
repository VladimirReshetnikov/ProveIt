# The object-language ZFC obligation

`ExplicitZFC.noSyntaxZero_iff_conZFC` is an external Lean theorem about the
actual predicate `BProv ZFCax_s [] Form.fBot`. It is not a derivation in that
calculus of a sentence expressing the same equivalence. The requested
“provably equivalent in ZFC” claim therefore remains a separate obligation.
No theorem in this research promotes the external equivalence to an internal
one. The maintained14-variable polynomial and all three accepted13-variable
forms now also have closed external Lean equivalences, in
[`CurrentPositiveZero2011`](Lean/DiophantineConsistency/CurrentPositiveZero2011.lean).
Its source, standard axiom audit and independent fresh endpoint replay are
recorded in the [author](reviews/current-positive-zero2011-root.md) and
[peer](reviews/current-positive-zero2011-lean-peer.md) receipts. This progress
does not discharge the object-language obligation described here.

Both sides of the internal target are now actual `SetTheory.Form` sentences:
a consistency sentence for sealed ZFC axiom codes and a sentence saying that
the fixed nine-variable polynomial has no internal natural zero. The remaining
required conclusion is

```
BProv ZFCax_s [] (fIff ObjectCodeSeal.consistencySentence
  ObjectEquation.unsolvabilitySentence).
```

The polynomial-side target is now supplied by
`ObjectEquation.unsolvabilitySentence`. Its satisfaction theorem includes
all internal natural tuples. `ObjectCodeSeal.consistencySentence` quantifies
over internal refutations from the sealed axiom-code predicate and quotes the
actual external `ZFCax_s` convention. The equivalence between these two
sentences is still open. The separate unsealed consistency sentence remains
available for the canonical bounded-consistency development.

That displayed target concerns the older nine-variable equation. The
maintained14-variable equation now has its own checked target:

```lean
BProv ZFCax_s [] (fIff ObjectCodeSeal.consistencySentence
  ObjectCurrentEquation2011.unsolvabilitySentence)
```

[`ObjectCurrentEquation2011`](Lean/DiophantineConsistency/ObjectCurrentEquation2011.lean)
defines the literal expression with the actual current four ports and
proves equality with the entire maintained multivariate polynomial. Its
natural encoding is P(x+1)=0, so all14 original unknowns are strictly
positive. The closed no-zero sentence has checked satisfaction exactly
when every strictly positive internal-natural tuple fails the original
signed expression. This includes nonstandard tuples and uses their
internal predecessors; it is not restricted to external numerals. The
[author record](reviews/object-current-equation2011-author.md) and
[independent root replay](reviews/object-current-equation2011-root.md)
record ten standard-only axiom audits and precise dependency-reuse scope.
The native current-source closure refresh remains separately in progress.
The displayed `BProv` equivalence itself is still OPEN. The
[current-expression/internal-bridge audit](research/current-equivalence-next-bridge-20261026.md)
identifies the exact API and remaining sealed-refutation/machine/native
interpretation work. The new external theorem does not identify the older
`ObjectEquation.unsolvabilitySentence` with this current equation.

## Verified reusable interfaces

* [`FirstOrder.Completeness`](../../Logic/FirstOrder/Lean/FirstOrder/Completeness.lean)
  defines `BProv` as a derivation with finite axiom support. Its
  `completeness_inf_context` proves actual `BProv` from validity in every
  model of a sentence theory. This includes nonstandard models; truth only
  in the external natural numbers is insufficient.
* [`ZF.Zf`](../../SetTheory/ZF/Lean/ZF/Zf.lean) supplies the `ZFAxioms`
  semantic bundle, the model's own `omegaV`, successor, formula macros with
  satisfaction specifications, and definable internal induction `omega_ind`.
* [`BoundedZFCConsistency.OmegaRecursion`](../../SetTheory/BoundedConsistency/Lean/BoundedZFCConsistency/OmegaRecursion.lean)
  supplies `fThetaG_spec`, `thetaG_total`, `thetaG_unique`, and
  `omega_recursion` for a supplied definable operation. Its stage index
  ranges over the model's own omega.
* [`CodedDerivation`](../../SetTheory/BoundedConsistency/Lean/BoundedZFCConsistency/CodedDerivation.lean)
  supplies the actual formula `fDerivesF`, its arbitrary-model specification
  `fDerivesF_spec`, and quotation soundness `derives_of_prov`. The converse
  from every internal derivation to an external Lean derivation is false
  in nonstandard models and is not supplied.
* [`AxiomCode`](../../SetTheory/BoundedConsistency/Lean/BoundedZFCConsistency/AxiomCode.lean)
  supplies `fZFCAxiomCodeF`, `fCtxZFCAxiomsF` and their arbitrary-model
  specifications. These encode the unsealed axiom predicate `ZFCax`.
  The external consistency endpoint uses the sealed sentence theory
  `ZFCax_s`; `ObjectCodeSeal` now supplies its internal sealed axiom-code
  predicate using checked bound computation and universal closure.
* [`Endpoint.zfc_proves_conZFC_unfolded`](../../SetTheory/BoundedConsistency/Lean/BoundedZFCConsistency/Endpoint.lean)
  proves `BProv ZFCax_s [] (conZFCForm n)` for each external numeral `n`.
  This is bounded consistency. The external family does not give a single
  proof of its universal closure or unrestricted consistency.

The canonical source search found no generic theorem translating arbitrary
Lean natural-number theorems or the current MRDP/Jones compiler correctness
proof into the `Form` calculus. The reusable bridge is first-order
completeness after an arbitrary-model interpretation has been proved.

## Concrete progress: internal addition

[`ObjectArithmetic.lean`](Lean/DiophantineConsistency/ObjectArithmetic.lean)
now supplies `addForm z x y : Form`, by iterating successor with the existing
internal omega-recursion machinery. It proves:

* `addForm_spec`, an exact satisfaction specification in every `ZFAxioms`
  model, including nonstandard inputs;
* totality, uniqueness, zero and successor equations, and closure of the
  result in the internal omega;
* `addRel_numerals_iff`, agreement on every pair of external numerals;
* `zfc_proves_addition_total` and `zfc_proves_addition_unique`, actual
  `BProv ZFCax_s []` derivations of the supplied closed totality and
  functionality sentences.

The output-closure proof uses `omega_ind` with a supplied `Form`, rather
than an unrestricted external induction assumption about the model.
The module and its independent axiom audit pass with only `propext`,
`Classical.choice`, and `Quot.sound`.

[`ObjectAdditionLaws.lean`](Lean/DiophantineConsistency/ObjectAdditionLaws.lean)
now proves left zero, left successor, commutativity and associativity over
the entire internal omega. Every induction supplies an actual formula.
The closed commutativity and associativity sentences have actual ZFC
derivations; see [OBJECT_ADDITION_LAWS.md](OBJECT_ADDITION_LAWS.md). These
laws support internal arithmetic compiler proofs, without transferring
arbitrary external natural-number theorems to nonstandard models.
`ObjectAdditionCancellation` further checks left/right cancellation and the
zero-sum criterion, with an actual closed ZFC cancellation proof.

## Multiplication, supplied expressions, and the actual equation sentence

[`ObjectMultiplication.lean`](Lean/DiophantineConsistency/ObjectMultiplication.lean)
builds multiplication by iterating internal addition. Its exact model
semantics, natural output closure, zero/successor laws, and numeral agreement
are checked. `zfc_proves_multiplication_total` and
`zfc_proves_multiplication_unique` are actual `BProv ZFCax_s []` derivations.

[`ObjectMultiplicationLaws.lean`](Lean/DiophantineConsistency/ObjectMultiplicationLaws.lean)
adds left zero, left successor and commutativity for all internal naturals,
using explicit formula predicates for induction and the checked addition
laws. Its closed commutativity sentence has an actual ZFC derivation; see
[OBJECT_MULTIPLICATION_LAWS.md](OBJECT_MULTIPLICATION_LAWS.md).
`ObjectDistributivity` adds both distributive laws and multiplication
associativity on every internal natural, including actual closed ZFC
derivations of the associated sentences.

[`ObjectNaturalExpression.lean`](Lean/DiophantineConsistency/ObjectNaturalExpression.lean)
recursively interprets every supplied `NatExpr`, with arbitrary maps of its
finite coordinates to free-variable slots. It supplies exact arbitrary-model
semantics and actual ZFC proofs of totality and functionality. The output
closure proofs use definable internal induction, including nonstandard inputs.

[`ObjectPolynomial.lean`](Lean/DiophantineConsistency/ObjectPolynomial.lean)
splits an integer expression into its two natural expressions and supplies
the actual closed sentence `noZeroForm e`. `sat_noZeroForm_iff` quantifies
over every internal natural tuple. Numeralwise equation agreement is proved;
external no-zero truth is not promoted to all-model satisfaction.

[`ObjectOmegaSemiring.lean`](Lean/DiophantineConsistency/ObjectOmegaSemiring.lean)
now packages the entire internal omega as a nontrivial commutative semiring,
with exact graph and numeral-cast identities. `ObjectNaturalSemiring`
identifies expression, equation and no-zero formula semantics with
evaluation in that semiring for every internal tuple. This supports finite
polynomial identities on nonstandard inputs; it is not a transfer principle
for arbitrary external arithmetic theorems. See
[OBJECT_OMEGA_SEMIRING.md](OBJECT_OMEGA_SEMIRING.md).

`ObjectNaturalOrder` and `ObjectNaturalZero` add internal difference witnesses,
canonical linear order, additive cancellation and absence of zero divisors.
Using these, `ObjectResidualSquares.zfc_proves_residual_conjunction` is an
actual ZFC derivation equating a supplied sum of residual squares with the
conjunction of its residual equations, under the internal-natural guard.
This closes the algebraic sum-of-squares compiler step; see
[OBJECT_RESIDUAL_SQUARES.md](OBJECT_RESIDUAL_SQUARES.md). Correctness of the
complete arithmetic checker/representation on nonstandard inputs remains open.

[`ObjectEquation.lean`](Lean/DiophantineConsistency/ObjectEquation.lean)
instantiates this construction at the closed nine-variable equation:
`unsolvabilitySentence := ObjectPolynomial.noZeroForm ExplicitZFC.expression`.
Sentencehood and exact arbitrary-model satisfaction are checked. The
additional external implication `conZFC_of_sat` uses only that satisfaction
excludes every external numeral zero. It is not the requested internal iff.

## Unbounded consistency and internal universal closure

[`ObjectConsistency.lean`](Lean/DiophantineConsistency/ObjectConsistency.lean)
removes the numerical certificate bound from the canonical consistency
formula. Its `unsealedConsistencySentence` quantifies over every internal
formula, axiom context, and refutation certificate. Exact arbitrary-model
semantics and quotation of external unsealed refutations are checked. For
each external numeral `n`, `zfc_proves_unbounded_implies_bounded` is an
actual derivation of the implication to `conZFCForm n`; it does not assert
either consistency sentence. External proofs from unsealed axioms transfer
to the sealed theory, but this does not supply the required transformation
of internal proof certificates.

[`ObjectCodeClosure.lean`](Lean/DiophantineConsistency/ObjectCodeClosure.lean)
defines iteration of the universal-quantifier code constructor. Totality,
uniqueness, and formula-code preservation hold for every internal natural
iteration count, by definable internal induction. Its quotation theorem
agrees exactly with `closeN`, and with `sealF` when supplied the numeral
`bound f`. Closed totality and functionality sentences have actual ZFC
derivations.

[`ObjectCodeBound.lean`](Lean/DiophantineConsistency/ObjectCodeBound.lean)
computes that bound on every internal formula code. Its explicit local
constructor certificates, exact formula semantics, natural-valuedness,
totality, and functionality are checked. The proofs use definable
formula-code induction, including nonstandard codes; quotation agrees
exactly with `SetTheory.bound`. Totality and functionality have actual
ZFC derivations.

[`ObjectCodeSeal.lean`](Lean/DiophantineConsistency/ObjectCodeSeal.lean)
combines the two operations, with exact `sealF` quotation and actual ZFC
totality/functionality proofs. Its sealed axiom-code predicate quotes every
actual `ZFCax_s` axiom. The associated `consistencySentence` has exact
arbitrary-model semantics: no internal coded refutation from these sealed
axiom contexts. Every external sealed refutation quotes internally, so
satisfaction implies the external `ConZFC`; the reverse is not asserted
uniformly for nonstandard models. An internal transformation between sealed
and unsealed proof certificates remains optional work if the older unsealed
coding is used; it is not needed merely to state the sealed target.

## Shortest concrete route still missing

1. Relate the supplied unbounded consistency sentence internally to a concrete arithmetic
   refutation test. The present `KEndpoint`/constructible-choice bridge is
   external; it is not already this internal interpretation. A new direct
   verifier for sealed ZFC proof codes could avoid internalizing that entire
   model-theoretic bridge.
2. Prove the arithmetic representation and Jones correctness for the
   internal natural numbers of every ZFC model, or produce object-language
   derivations of those correctness statements. Numeral agreement alone
   leaves nonstandard witnesses untreated. There is currently no automatic
   transfer of the existing Mathlib `Nat` proofs to this setting.
3. Apply the existing sentence-theory completeness theorem to that
   arbitrary-model equivalence, yielding the displayed `BProv` endpoint.

This route needs no assumption that ZFC is consistent. It needs considerably
more formalization than the external iff; bounded consistency reflection and
quotation soundness do not discharge those remaining obligations.

The [literal tree-to-quartic compiler](OBJECT_QUARTIC_COMPILER.md) now also
has an unconditional proof in the actual sealed ZFC calculus. It identifies
the source and compiled no-zero sentences on the entire internal omega.
It does not internalize an arbitrary external representation theorem or
close the full checker-to-consistency calibration.
