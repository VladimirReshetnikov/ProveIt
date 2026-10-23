# The object-language ZFC obligation

`ExplicitZFC.noSyntaxZero_iff_conZFC` is an external Lean theorem about the
actual predicate `BProv ZFCax_s [] Form.fBot`. It is not a derivation in that
calculus of a sentence expressing the same equivalence. The requested
“provably equivalent in ZFC” claim therefore remains a separate obligation.
No theorem in this research promotes the external equivalence to an internal
one.

A fully internal endpoint must supply two actual `SetTheory.Form` sentences:
a consistency sentence for the chosen coded ZFC proof system, and a sentence
saying that the fixed nine-variable polynomial has no natural zero. The
required conclusion then has the shape

```
BProv ZFCax_s [] (fIff consistencySentence unsolvabilitySentence).
```

The polynomial-side target is now supplied by
`ObjectEquation.unsolvabilitySentence`. Its satisfaction theorem includes
all internal natural tuples. `ObjectConsistency.unsealedConsistencySentence`
supplies the consistency-side sentence for the canonical unsealed axiom
coding. Relating that coding internally to the sealed theory used by the
external endpoint, and deriving the full equivalence, remain open.

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
  `ZFCax_s`; a common internal proof coding or an internal sealing bridge
  must be specified explicitly.
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

## Multiplication, supplied expressions, and the actual equation sentence

[`ObjectMultiplication.lean`](Lean/DiophantineConsistency/ObjectMultiplication.lean)
builds multiplication by iterating internal addition. Its exact model
semantics, natural output closure, zero/successor laws, and numeral agreement
are checked. `zfc_proves_multiplication_total` and
`zfc_proves_multiplication_unique` are actual `BProv ZFCax_s []` derivations.

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
derivations. Computing the bound on arbitrary internal formula codes and
transforming sealed/unsealed refutation certificates remain open.

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
