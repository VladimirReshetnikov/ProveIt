(**
  Identify the Sigma/Or row production with the canonical rank-zero target.

  The two formulae are not definitionally equal.  The shared append row uses
  three pieces of data selected by the ambient template translation: named
  parameter two for the row mode, and the two opaque shared successor-row
  codes.  The canonical target instead contains the literal numeral zero and
  two completely embedded PA rows.  This file records the exact three
  carrier equalities under which constructor congruence closes that gap.

  The mode equality has an additional proof-producing benefit: equality
  reflexivity constructs the mode-zero root directly in any represented
  context.  Consequently the final adapter needs only the domain, Or-code,
  and selected-state roots from a Boolean client; it does not ask that client
  to manufacture a separate proof of the translated parameter equality.
*)

From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors
  RawCodedRestrictedPAProof
  RawCodedPALocalProofExistential
  RawCodedPALocalProofEquality
  RawCodedTemplateSyntax
  RawCodedTemplateProofCompiler
  RawCodedTemplateProofCompilerSelfShiftTail
  RawCodedFourStateTableAppendRowLtSuccCases
  RawCodedFourStateTableAppendGlobalTraversalAssembly
  RawCodedDynamicTruthSuccessorRowsAppendNormalization
  RawCodedDynamicTruthSigmaOrFixedProductionTemplate
  RawCodedDynamicTruthSigmaOrFixedProductionAppendIntegration.

Module
  PABoundedRawCodedDynamicTruthSigmaOrCanonicalProductionIdentification.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPALocalProofEquality.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedTemplateProofCompilerSelfShiftTail.
Import PABoundedRawCodedFourStateTableAppendRowLtSuccCases.
Import PABoundedRawCodedFourStateTableAppendGlobalTraversalAssembly.
Import PABoundedRawCodedDynamicTruthSuccessorRowsAppendNormalization.
Import PABoundedRawCodedDynamicTruthSigmaOrFixedProductionTemplate.
Import
  PABoundedRawCodedDynamicTruthSigmaOrFixedProductionAppendIntegration.

(** Constructor congruence reduces the formerly monolithic production-code
    equality to its three genuinely translation-dependent leaves.  Notice
    that the Pi equality remains necessary even at root mode zero: formula
    coding retains the unused right disjunct syntactically. *)
Theorem rawTemplateFormula_dynamicTruthSigmaOr_named_zeroCanonical_eq :
  forall (M : RawPAModel)
    (translation : RawCodedTemplateTranslation M),
  rawTemplateTerm translation
      (ttParameter coqFourStateTableAppendRowModeParameterName) =
    rawTemplateTerm translation (embedPATerm (Term.numeral 0)) ->
  rawTemplateFormula translation
      coqDynamicTruthSharedSigmaSuccessorRowTemplate =
    rawTemplateFormula translation
      (embedPAFormula
        coqDynamicTruthSigmaOrZeroCanonicalSigmaRowFormula) ->
  rawTemplateFormula translation
      coqDynamicTruthSharedPiSuccessorRowTemplate =
    rawTemplateFormula translation
      (embedPAFormula
        coqDynamicTruthSigmaOrZeroCanonicalPiRowFormula) ->
  rawTemplateFormula translation
      (coqFourStateTableAppendNamedClosedRowProductionTemplate
        coqDynamicTruthSharedSigmaSuccessorRowTemplate
        coqDynamicTruthSharedPiSuccessorRowTemplate) =
    rawTemplateFormula translation
      (templateFormulaOpen (embedPATerm (Term.numeral 0))
        (coqFourStateTableAppendEmbeddedModeProductionMotive
          coqDynamicTruthSigmaOrZeroCanonicalSigmaRowFormula
          coqDynamicTruthSigmaOrZeroCanonicalPiRowFormula)).
Proof.
  intros M translation hmode hsigma hpi.
  rewrite coqFourStateTableAppendEmbeddedModeProductionMotive_open.
  unfold coqFourStateTableAppendNamedClosedRowProductionTemplate.
  rewrite !rawTemplateFormula_or, !rawTemplateFormula_and,
    !rawTemplateFormula_eq.
  rewrite hmode, hsigma, hpi.
  reflexivity.
Qed.

(** A translated parameter whose term code is zero proves its own mode-zero
    formula by represented equality reflexivity.  No context assumption and
    no PA helper witness is consumed. *)
Theorem raw_codedPALocalProofOf_dynamicTruthSigmaOr_mode_zero_of_term_eq :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M) context,
  rawTemplateTerm translation
      (ttParameter coqFourStateTableAppendRowModeParameterName) =
    rawTemplateTerm translation (embedPATerm (Term.numeral 0)) ->
  exists modeRoot,
    RawCodedPALocalProofOf M context
      (rawTemplateFormula translation
        coqDynamicTruthSigmaOrModeZeroTemplate) modeRoot.
Proof.
  intros M hPA translation context hmode.
  unfold coqDynamicTruthSigmaOrModeZeroTemplate.
  rewrite rawTemplateFormula_eq, hmode.
  eexists.
  apply raw_codedPALocalProofOf_eqRefl.
  exact hPA.
Qed.

(** The direct canonical-root adapter.  Relative to the previous four-root
    handoff, [modeRoot] has disappeared: [hmode] constructs it internally.
    The two row-code identifications are kept as plain equalities, rather
    than hidden inside a callback or a purported proof compiler. *)
Theorem
    raw_dynamicTruthZeroCanonicalFixedProductionRoot_of_sigma_or_three_roots_and_atomic_identifications :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M)
    sourceWitnessList sourceContext tail
    witness7 witness6 witness5 witness4
    witness3 witness2 witness1 witness0
    domainRoot codeRoot leftStateRoot,
  RawCodedPAAxiomWitnessContext M sourceWitnessList sourceContext ->
  rawTemplateTerm translation
      (ttParameter coqFourStateTableAppendRowModeParameterName) =
    rawTemplateTerm translation (embedPATerm (Term.numeral 0)) ->
  rawTemplateFormula translation
      coqDynamicTruthSharedSigmaSuccessorRowTemplate =
    rawTemplateFormula translation
      (embedPAFormula
        coqDynamicTruthSigmaOrZeroCanonicalSigmaRowFormula) ->
  rawTemplateFormula translation
      coqDynamicTruthSharedPiSuccessorRowTemplate =
    rawTemplateFormula translation
      (embedPAFormula
        coqDynamicTruthSigmaOrZeroCanonicalPiRowFormula) ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail translation sourceContext tail)
    (rawTemplateFormula translation
      (coqDynamicTruthSigmaOrOpenedDomainAt
        witness7 witness6 witness5 witness4
        witness3 witness2 witness1 witness0)) domainRoot ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail translation sourceContext tail)
    (rawTemplateFormula translation
      (coqDynamicTruthSigmaOrOpenedCodeAt
        witness7 witness6 witness5 witness4
        witness3 witness2 witness1 witness0)) codeRoot ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail translation sourceContext tail)
    (rawTemplateFormula translation
      (coqDynamicTruthSigmaOrOpenedLeftStateAt
        witness7 witness6 witness5 witness4
        witness3 witness2 witness1 witness0)) leftStateRoot ->
  exists fixedProductionRoot,
    RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation sourceContext tail)
      (rawTemplateFormula translation
        (templateFormulaOpen (embedPATerm (Term.numeral 0))
          (coqFourStateTableAppendEmbeddedModeProductionMotive
            coqDynamicTruthSigmaOrZeroCanonicalSigmaRowFormula
            coqDynamicTruthSigmaOrZeroCanonicalPiRowFormula)))
      fixedProductionRoot.
Proof.
  intros M hPA translation sourceWitnessList sourceContext tail
    witness7 witness6 witness5 witness4
    witness3 witness2 witness1 witness0
    domainRoot codeRoot leftStateRoot hbase
    hmode hsigma hpi hdomain hcode hleftState.
  destruct
    (raw_codedPALocalProofOf_dynamicTruthSigmaOr_mode_zero_of_term_eq
      M hPA translation
      (rawTemplateContextCodeOnTail translation sourceContext tail)
      hmode) as [modeRoot hmodeRoot].
  destruct
    (raw_codedPALocalProofOf_dynamic_truth_sigma_or_fixed_production_of_four_roots
      M hPA translation sourceWitnessList sourceContext tail
      witness7 witness6 witness5 witness4
      witness3 witness2 witness1 witness0
      modeRoot domainRoot codeRoot leftStateRoot
      hbase hmodeRoot hdomain hcode hleftState) as
    [fixedProductionRoot hfixed].
  exists fixedProductionRoot.
  rewrite <-
    (rawTemplateFormula_dynamicTruthSigmaOr_named_zeroCanonical_eq
      M translation hmode hsigma hpi).
  exact hfixed.
Qed.

End
  PABoundedRawCodedDynamicTruthSigmaOrCanonicalProductionIdentification.
