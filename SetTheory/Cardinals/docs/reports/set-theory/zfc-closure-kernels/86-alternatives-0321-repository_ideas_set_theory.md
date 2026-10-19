# Existing set-theory machinery useful for the small-machine project

Source inspection, 16 October 2026. This note covers the existing Closure,
first-order ZF, PA/HF, bounded-consistency and ZFC-in-PA developments. It adds
no formal theorem and records no new build. New formal work for this project
uses Lean. The immediate opportunity is to reuse proved syntax, proof
transport and weak-theory recursion while comparing the new closure kernels;
the repository search does not reveal a previously proved smaller ZFC
consistency-search machine.

## Recommendations

1. Start the new kernel's reference formalization with the repository's small
   `SetTheory.Form` language and its calculus. Add explicit formula
   constructors and matrix certificates for the selected closure schema.
   Keep the runtime encoding separate: the existing language has more
   connectives than a small final verifier may want.
2. Prove the kernel's set constructions in dependency order, then instantiate
   the existing first-order recursion theorem for its converse hull
   construction. Avoid copying another specialized closure iteration.
3. Give the refutation checker a data-valued certificate type with structural
   recursion or strictly earlier proof references. Prove soundness and
   enumeration completeness before minimizing its runtime representation.
4. Retain a PA-strength theory as a diagnostic control. Replacing the
   power-bounding container by mere transitive containment can lose the
   required strength even though substantial syntax and recursion machinery
   still works.

The following findings distinguish existing Lean results from adaptations
that remain to be implemented.

## Closure already has a useful dependency audit

The established alternative axiomatization is genuinely formalized. In
`SetTheory/ClosureAxiomatization/Lean/ClosureAxiomatization/Equivalence.lean:624`,
`T_iff_ZF` proves deductive equivalence between the sentence theory `Tax_s`
and the repository's ZF theory. This is a theorem about its stated Closure
presentation, not about the incoming BIC, positive seeded, exact-fiber, or
Mira container theories.

There is a concrete weakening worth reusing in proofs. In
`SetTheory/ClosureAxiomatization/Lean/ClosureAxiomatization/Forward.lean:87`,
`HostAx` says every object belongs to some set. At line 150,
`powerset_gives_hosting` derives it from Power Set; the shallow forward
proofs then use hosting directly:

| Existing declaration | Exact source | What it saves |
|---|---|---|
| `Pairing` | `SetTheory/ClosureAxiomatization/Lean/ClosureAxiomatization/Forward.lean:285` | Separation, Hosting and Closure suffice; no Power Set premise. |
| `Union` | `SetTheory/ClosureAxiomatization/Lean/ClosureAxiomatization/Forward.lean:318` | Separation and Closure suffice. |
| `Replacement` | `SetTheory/ClosureAxiomatization/Lean/ClosureAxiomatization/Forward.lean:338` | Separation, Hosting and Closure suffice. |

This is a bootstrap technique: prove the precise hosting fact needed by an
image argument instead of assuming a power set solely to obtain a host.
These shallow declarations quantify over Lean predicates. For first-order
schema claims, follow the separate deep construction: `Closure_form` at
`SetTheory/ClosureAxiomatization/Lean/ClosureAxiomatization/Equivalence.lean:439`
has explicit fresh-variable renamings, and the actual first-order theory is
defined at line 506. A shallow proof alone is not a proof that the needed
matrix has been expressed in the permitted language.

The reverse construction is stronger evidence for omitting unnecessary
axioms from the *proof layer*. In
`SetTheory/ZF/Lean/ZF/Zf.lean:334`, `ZFAxioms` contains exactly
Extensionality, Separation, Pairing, Union, Infinity and functional
Replacement. It has no Power Set, Foundation or Choice. At line 1336,
`ClosureFO_of_ZF` constructs closure for every definable member-bounded
relation in every such model. Thus the repository already handles the
Foundation-free internal iteration needed by much of our converse proof.

This does **not** justify deleting all power-set strength from the searched
theory. It shows that a particular proof engine works over a weaker bundle.
The target still needs a separate calibration to ordinary ZFC.

## Reuse the general recursion theorem

`SetTheory/ZF/Lean/ZF/Zf.lean` specializes its finite-approximation
construction to the closure step `gstep`. The general version already
exists elsewhere:

- `defOp_functional`,
  `SetTheory/BoundedConsistency/Lean/BoundedZFCConsistency/OmegaRecursion.lean:224`,
  turns a formula defining a function into the functionality premise
  Replacement needs.
- `omega_recursion`, same file line 853, constructs an internal function
  on the model's **internal** omega for a definable step and arbitrary seed.
- `omega_recursion_unique`, same file line 931, proves uniqueness as a set.

The theorem requires a graph formula `fG`, its parameter environment `eG`,
and a proof that it defines the operation `G`. It is not recursion for an
arbitrary Lean function. For exact-fiber or seeded closure, first define
the unique exact fiber and the corresponding set-valued step, then supply
its graph. This keeps the no-Choice argument explicit: Replacement collects
unique outputs rather than an arbitrary selected bound for each input.

A second useful construction avoids a common closure error.
`exists_pairClosed` at
`SetTheory/BoundedConsistency/Lean/BoundedZFCConsistency/FormulaClosedSet.lean:436`
constructs a set containing internal omega and closed under Kuratowski
pairing. It obtains an ambient unary closure, cuts out the least step-closed
part, proves directedness, and only then takes its union. At line 457,
`exists_formulaClosed` turns that into a formula-code universe. Arbitrary
closure junk need not be directed; taking its union prematurely does not
establish closure under a binary constructor. This is directly useful for
our coded syntax, not a new ZFC-strength axiom.

## Syntax and proof certificates are substantially reusable

The lightweight logic does not require adopting the large-cardinal
development or a new set-theory metatheory.

| Existing component | Exact source | Use and remaining boundary |
|---|---|---|
| `Form`, `rename`, `Free` | `Logic/FirstOrder/Lean/FirstOrder/Fol.lean:89`, `:110`, `:127` | De Bruijn binders and freshness/substitution infrastructure. The language contains logical equality and eight constructors. |
| `sealF`, `Sentence_seal` | `Logic/FirstOrder/Lean/FirstOrder/Fol.lean:361`, `:363` | Universally close arbitrary parameter tuples without an informal closure convention. |
| `code`, `decode`, `decode_code` | `Logic/FirstOrder/Lean/FirstOrder/Fol.lean:371`, `:381`, `:396` | Executable total, fuelled formula decoding and coverage of every encoded formula. Malformed/fuel-exhausted inputs default to falsity; a proof checker must still reject invalid certificates instead of accepting that fallback as a refutation. |
| `BProv_lift` | `Logic/FirstOrder/Lean/FirstOrder/Completeness.lean:373` | Transfer a finite proof once every used source axiom and context assumption has a target proof. Useful for local axiom templates. |
| `completeness_inf_context`, `theory_transfer` | `Logic/FirstOrder/Lean/FirstOrder/Completeness.lean:1082`, `:1105` | Turn semantic consequence into the repository's derivability relation. These are formal mathematical transport theorems, not an extracted small proof compiler. |

`BProv` is explicitly an existential over a finite axiom list plus a
`Prop`-valued derivation
(`Logic/FirstOrder/Lean/FirstOrder/Completeness.lean:308`). The data layer
needed for inspection also exists: `ProvTree` at
`SetTheory/BoundedConsistency/Lean/BoundedZFCConsistency/Basic.lean:201`
is a `Type`-valued mirror of the seventeen inference rules. `ProvTree.erase`
at line 227 and `provTree_complete` at line 317 connect it to `Prov`.
This is a useful starting certificate specification; it is not yet a
serialized untyped certificate decoder or a minimal TM verifier.

For internal proof predicates, the repository already avoids circular
certificates. `DerClosed` at
`SetTheory/BoundedConsistency/Lean/BoundedZFCConsistency/CodedDerivation.lean:924`
requires judgements at internal natural ranks with premises at smaller
ranks; `Derives` is defined at line 960. A mere set closed under inference
rules is unsound: conjunction introduction and elimination can justify a
cycle with no derivation from assumptions. Our checker should retain an
equivalent descent argument even if its certificate representation changes.

## Equality elimination and uniform matrix templates

The `ZFCinPA` branch has a more general compiler architecture, using the
vendored Foundation library's syntax rather than `SetTheory.Form`.
`compileSetTemplate` at
`Logic/Interpretability/ZFCinPA/Lean/ZFCinPA/SetPlaceholders.lean:559`
specializes a fixed proof with relation placeholders into an internal ZFC
proof; `compileSetTemplate_isZFCProof` at line 570 verifies the represented
proof predicate. Placeholder matrices may have nonstandard internal codes.

This provides a concrete model for uniform schema proofs: treat the matrix
as an opaque relation of fixed arity and prove its wrapper once. It does
not already compile our kernels or emit their TM programs, and directly
mixing the two formula languages would require a proved translation.

Congruence is essential at this boundary. In
`Logic/Interpretability/ZFCinPA/Lean/ZFCinPA/SetPlaceholderQuotient.lean:99`,
`models_fullEquality` requires congruence for the added placeholders.
`complete_underSetPlaceholderCongruence` at line 160 explicitly retains
that antecedent while quotienting interpreted equality. This supports our
EC-controlled profile interpretation and warns against deleting EC merely
because the formulas contain no logical equality. It does not prove the
raw congruence-free kernel equiconsistent with ZFC.

## PA/HF supplies a real weaker control

There is more here than a standard-model demonstration. The current source
has the unconditional concrete
`paHFFinDeductiveBiInterpretation` and
`PA_biinterpretable_with_HFFin` at
`Logic/Interpretability/PAHF/Lean/PAHF/HFRoundTrip.lean:4536` and `:4544`.
The source also gives the composable `TheoryInterpretation` record at
`Logic/Interpretability/PAHF/Lean/PAHF/Interpretation.lean:8208` and
`TheoryInterpretation.comp` at line 8226: sentence preservation,
axiom translation and theorem translation are separate obligations.

Its target is specifically `HFFinAx_s`:
`Logic/Interpretability/PAHF/Lean/PAHF/AckermannHFCore.lean:1521` adds
finite-generation induction to the empty/extensionality/adjunction and
Foundation-style induction theory at line 1502. Therefore it is a useful
PA-strength control for the Mira transitive-container branch, but cannot
replace a ZFC-strength kernel. A bridge from the new container axioms to
these exact axioms remains to be formalized; the existence of this
bi-interpretation does not discharge that bridge automatically.

## Bounded consistency gives design lessons, not a shortcut to the target

`zfc_proves_conZFC` at
`SetTheory/BoundedConsistency/Lean/BoundedZFCConsistency/Endpoint.lean:40`
proves an object-level ZFC derivation for every **external Lean natural**
`n`. It does not produce one ZFC proof of unrestricted consistency. Its
bound covers every formula occurrence, including contexts and rule
parameters. `conclusionRestrictedProv_bot_iff` at
`SetTheory/BoundedConsistency/Lean/BoundedZFCConsistency/Basic.lean:449`
formally shows why bounding only the final contradiction is ineffective.
This project's hierarchy also charges bounded set quantifiers after
expansion; it is not the Levy hierarchy.

Three distinctions matter for our proof-predicate implementation:

1. External quotation is only sound into internal syntax.
   `formCode_isFormCodeSem` at
   `SetTheory/BoundedConsistency/Lean/BoundedZFCConsistency/CodePredicate.lean:207`
   proves that direction. Nonstandard models contain further internal
   codes. `IsZFCAxiomCode` at
   `SetTheory/BoundedConsistency/Lean/BoundedZFCConsistency/AxiomCode.lean:1054`
   quantifies over those internal matrix codes for its two schemas. It is
   not restricted to an external list of quoted instances.
2. Truth levels are external formula-building parameters, not object
   variables: see `levelSatF`'s stated type and explanation at
   `SetTheory/BoundedConsistency/Lean/BoundedZFCConsistency/UniverseTruthLevel.lean:14`.
   Likewise `natV` at
   `SetTheory/BoundedConsistency/Lean/BoundedZFCConsistency/Coding.lean:86`
   produces a numeral for each external natural; it is not automatically
   a function defined at every internal natural.
3. The attempted PA-internal uniformization is still conditional.
   `peano_proves_uniformZFCProvability_of_successorImplications` at
   `Logic/Interpretability/ZFCinPA/Lean/ZFCinPA/Endpoint.lean:127`
   requires `ZFCSuccessorImplicationsInAllModels`, defined at line 80 with
   an arbitrary model element `n : V`. Do not replace that premise with
   a family of proofs only at standard numerals. A failed weaker
   certificate is documented by the actual countermodel theorem
   `exclusivity_not_step_transferable` at
   `Logic/Interpretability/ZFCinPA/Lean/ZFCinPA/LocalStepDerivation.lean:255`.

One positive proof technique is worth copying immediately: `TotalOn` at
`SetTheory/BoundedConsistency/Lean/BoundedZFCConsistency/InternalSatTotality.lean:463`
strengthens certificate existence to **one certificate for an entire set
of environments**. This avoids choosing a separate witness at every
environment. `certificate_total` at line 632 then handles arbitrary internal
codes. The same technique can avoid accidental Choice assumptions in our
uniform matrix and substitution arguments.

Finally, an ambient Lean proof of a model of ZFC is not the requested
object-level ZFC proof of the machine equivalence. The distinction is
explicit in
`SetTheory/BoundedConsistency/Lean/BoundedZFCConsistency/Consistency.lean:42`:
`not_restrictedBProv_bot_of_hasModel` retains a model as a hypothesis.
Neither importing a universe model nor adding inaccessible-cardinal or
large-cardinal assumptions is an acceptable compression of the target.

## What this changes in the work plan

The repository already removes much of the mathematical infrastructure
cost of a new Lean kernel proof. The next concrete theorem should connect
the selected equality-free closure schema, with all parameter and freshness
conditions explicit, to the existing first-order ZF syntax and a fixed
refutation predicate. Use the general recursion and proof-transport
interfaces above; then prove a terminating executable checker and complete
enumerator against that predicate. A later low-connective or shared-matrix
encoding can be compared against this reference implementation.

This is a proposal for reuse, not a state-count result. Neither fewer named
axioms nor one infinite schema determines the size of the resulting machine.
For example `Tax_s` has three fixed sentences and **two infinite schemas**
at `SetTheory/ClosureAxiomatization/Lean/ClosureAxiomatization/Equivalence.lean:506`;
the Lean quantifier over `Form` does not turn those schemas into a finite
first-order axiom list. Any new kernel still needs its exact consistency
calibration, including the Foundation/Choice bridge, and an actual backend
before a claim of beating 254 states is justified.

