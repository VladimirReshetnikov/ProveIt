# Scoped audit: C222 calibration and provability in ZFC

Audit target: ProveIt commit `e0c98c629bf10d30b695884f6b1d2ab361bdf513`.
This note inspects the relevant declarations and the mathematical structure
of their proofs. It is not a fresh build of their full Lean dependency
closure, nor an exported derivation in the repository's object-language ZFC.

## Conclusion

The inspected C222/ZF calibration admits an ordinary proof formalizable in
ZFC. The semantic lower-bound argument does **not** require an externally
well-founded model, an omega-standard model, or a transitive set model of ZF.
The potentially troublesome phrase "well-founded part" is resolved explicitly
by the source definitions: it means an **internally** well-founded,
first-order definable part of a set model. Quotient formation, this definable
substructure, first-order completeness for a set of sentences, and the
constructible-model argument all use set constructions available in ZFC.

This supports a theorem stated as a mathematical ZFC-provable equivalence,
composed with the retained calibration. It does not support the additional
claim that the new complete equation has been checked by Lean/Rocq, or that
an actual object-language `BProv ZFCax_s []` derivation of its consistency
equivalence has been emitted. That remains a separate formalization task.

## Exact interfaces inspected

All paths below are relative to
`Computability/BusyBeaver/Lean/BusyBeaver/ZFC/` at the pinned commit.

* `KEndpoint.lean`, `c222_of_zf_refutation` and
  `c222_iff_zf_refutation`:

      KCode222.C222 Code254.F <-> BProv ZFax_s [] Form.fBot.

  The lower direction uses `KEind222.c222_complete`,
  `fullSeed_direct_of_derivable`, `formSeed_of_fullSeed`, and
  `KLower.zf_consistent_of_formSeed`.

* `KCode222.lean` defines C222 as an inductively generated relation on natural
  numbers, with truth, modus ponens, generalization, eight row families and
  a guarded bundle. Thus its derivability relation has the usual finite
  arithmetic proof-certificate presentation. `c222_sound` is induction on
  these finite derivations, relative to an irreflexive model of the bundles.

* `KEind222.lean`, `c222_complete`, applies first-order completeness to the
  named theory `T` plus an irreflexivity sentence. It then explicitly
  interprets named equality by the `Eind` formula, transports derivations
  through `thm_th`, and embeds them through `c222_of_thmK`.

* `KSeedDirect222.lean`, `seed_direct` and
  `fullSeed_direct_of_derivable`, obtain the seed property for every named
  formula. The fresh label is the code of its interpreted double negation;
  `free_lt_enc` and `free_th` prove that label does not occur free. This is
  a uniform construction on formula codes, not a separate assumption for
  each externally standard formula.

* `KLowerQHyp.lean`, `zf_consistent_of_formSeed`, constructs a tagged domain
  and supplies `KQHyp.QHyp` to `KQ1ZF.zf_consistent`.

* `KQ1Model.lean` forms the quotient by its coded bisimilarity relation and
  proves `sat_quotient`. The membership and equality interpretations are
  displayed first-order formulas (`memberForm`, `eqvForm`); `translate` is
  recursion on actual formula syntax.

* `KQ1Collect.lean`, `quotient_fullGIC`, transports formula-indexed
  collection, including equality. The premise is a schema over actual
  formulas; it is not collection for every arbitrary external relation.

* `WellFoundedPartCore.lean` contains the decisive definitions:

      InternallyWellFounded mem t :=
        forall s, Sub mem s t -> NonemptySet mem s ->
          exists m, Minimal mem m s
      TW mem t := Transitive mem t /\ InternallyWellFounded mem t
      WF mem x := exists t, TW mem t /\ mem x t.

  Here `s` ranges over the structure's domain. The file gives literal
  formulas `wellFoundedForm`, `twForm`, `wfForm` and proves their satisfaction
  equivalences. Its `wf_closure` uses one displayed collection instance
  `gicForm witnessForm`, rather than an external predicate schema. This
  distinction prevents the invalid inference to a transitive model of ZF.

* `WFRelativization.lean` translates universal quantifiers to
  `forall x (WF(x) -> ...)` and existential quantifiers to
  `exists x (WF(x) /\ ...)`, using the ambient `wfForm` as guard.
  `sat_translate` proves the uniform satisfaction correspondence.

* `WFModelCore.lean`, `domain_models_ZF`, proves all the sealed ZF axioms,
  including Foundation and the Separation and Replacement schemas, in the
  internally well-founded domain. For schema instances it uses the actual
  recursive formula translation. `KQ1ZF.lean`, `zf_consistent`, then uses
  soundness to exclude a finite ZF refutation.

* `KUpper222.lean`, `zf_refutation_of_c222`, proves the other calibration
  direction. Assuming a set model of ZF, its constructible inner model
  satisfies every seed instance. `seed_in_VL` uses reflection for a finite
  list of formula bodies, including the power-set formula, and Separation
  to build the required container. C222 soundness excludes a refutation;
  first-order completeness converts the semantic consequence to a ZF proof.

* `ConstructibleChoice.lean`, `zf_refutation_iff_zfc_refutation`, is the
  separate Choice transport. A set model of ZF has a constructible inner
  model of ZFC; soundness and completeness yield the equivalence of the
  two refutation-existence statements.

## Ordinary proof inside ZFC

Work in ZFC with all formulas and finite proof objects represented by
natural numbers and finite sequences. Satisfaction for a **set** structure
is definable uniformly by recursion on formula codes.

If C222 does not derive 1, the named-theory completeness theorem provides
a nonempty irreflexive set model of the named formulas whose interpreted
codes are derivable. This theory is a set: it is a definable subset of the
countable set of formula codes. The fresh-label argument supplies its full
formula-indexed seed property. Form the tagged structure, quotient it by
the displayed equivalence relation, and restrict to the domain defined by
the displayed `wfForm`. The source's uniform interpretations prove that
this set structure satisfies ZF. Soundness then excludes a ZF refutation.

Conversely, if ZF has no refutation, completeness supplies a set model of
ZF. Its constructible submodel satisfies the seed instances by the
finite-formula reflection argument. Induction on a hypothetical C222
derivation of 1 contradicts soundness in that model. Hence C222 does not
derive 1. Finally compose with the constructible-model Choice transport.

This establishes, in ZFC, the equivalence between C222 refutation existence
and ZFC refutation existence. In particular the proof need not extract a
primitive-recursive function transforming refutations: first-order
completeness is itself a ZFC theorem and proves the required existence
statements. A primitive-recursive translator is a stronger implementation
claim not established by merely quoting this semantic proof.

## Nonstandard-model uniformity

For any model M of ZFC, the same proof is read using its own omega,
internally finite syntax, set structures and set-model satisfaction. A
formula or finite certificate that M regards as finite need not be
externally standard. The induction and recursive syntax translations are
performed inside M. The restriction defined by `wfForm` is also internal;
its membership relation can be externally ill-founded. No step replaces
M's arithmetic by the external standard natural numbers.

This is why the ordinary proof is suitable for a ZFC-provability claim,
rather than only a statement about standard solutions in the metatheory.
The full machine-checked object-level statement would additionally require
reifying these constructions and the arithmetic compiler into the sealed
object calculus. The present source interfaces do not by themselves do
that reification.

## Recommended report wording

"The ordinary mathematical proof is formalizable in ZFC. It composes the
new polynomial zero-set equivalence with the retained C222/ZF calibration
and the constructible-model equivalence of ZF and ZFC refutability. Thus
ZFC proves that the displayed equation has no integer zero if and only if
Con(ZFC). The release does not contain a newly completed Lean/Rocq proof
of that endpoint or a newly emitted derivation in the encoded object
calculus. Its executable checks certify the stated finite algebra and
certificates; the unbounded arithmetic and logical facts are the proved
mathematical dependencies identified here."

Do not describe the entire calibration as "only finite arithmetic". The
polynomial compiler and local reduction may be arithmetical, but the
retained semantic calibration explicitly uses completeness, quotient and
definable-submodel constructions, and the constructible-model theorem.
