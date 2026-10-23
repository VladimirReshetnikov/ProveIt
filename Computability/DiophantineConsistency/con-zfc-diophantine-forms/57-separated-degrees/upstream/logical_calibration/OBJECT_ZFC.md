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

Neither target sentence, nor this derivation, is currently assembled here.

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

## Shortest concrete route still missing

1. Build multiplication from the definable addition iterator, then compile
   supplied natural expression syntax to `Form` with arbitrary-model graph
   semantics. Splitting the integer syntax by `Expr.splitNatural` permits
   equality of two natural values and avoids an initial integer-model layer.
2. State the unbounded internal consistency sentence with an explicit
   proof/axiom coding. Relate that coding internally to a concrete arithmetic
   refutation test. The present `KEndpoint`/constructible-choice bridge is
   external; it is not already this internal interpretation. A new direct
   verifier for sealed ZFC proof codes could avoid internalizing that entire
   model-theoretic bridge.
3. Prove the arithmetic representation and Jones correctness for the
   internal natural numbers of every ZFC model, or produce object-language
   derivations of those correctness statements. Numeral agreement alone
   leaves nonstandard witnesses untreated. There is currently no automatic
   transfer of the existing Mathlib `Nat` proofs to this setting.
4. Apply the existing sentence-theory completeness theorem to that
   arbitrary-model equivalence, yielding the displayed `BProv` endpoint.

This route needs no assumption that ZFC is consistent. It needs considerably
more formalization than the external iff; bounded consistency reflection and
quotation soundness do not discharge those remaining obligations.
