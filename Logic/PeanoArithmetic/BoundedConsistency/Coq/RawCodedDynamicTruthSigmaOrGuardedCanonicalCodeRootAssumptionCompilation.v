(**
  Isolate the exact parent-code residual of the guarded Sigma/Or row.

  The synchronized fixed-production consumer leaves three independent
  obligations.  The syntactically smallest one is the parent Or-code atom

      FormulaOrCode(rowFormula, leftFormula, rightFormula).

  It is important not to confuse this atom with one of the append
  extension's lookup projections.  The mode-zero append prefix describes
  the four freshly extended beta tables; it does not assert which formula
  constructor the later row eigenvariable denotes.  Consequently this file
  makes the exact missing assumption explicit instead of claiming an
  unsound unconditional producer.

  The main reusable result is a general compiler for a literal member of a
  temporary template prefix.  It adds no PA-axiom witnesses: the represented
  proof is the assumption leaf over the existing witnessed tail.  Its
  specialization to the exact guarded Sigma/Or code root reduces the
  independent three-root interface to two genuine proof producers plus one
  transparent prefix-membership obligation.
*)

From Stdlib Require Import List.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors
  RawCodedProofAssumptionLeaf
  RawCodedPALocalProofUniversalIntroductionChain
  RawCodedPAAxiomWitnessPrefix
  RawCodedPALocalProofWitnessedContextMerge
  RawCodedTemplateSyntax
  RawCodedTemplateProofCompiler
  RawCodedTemplateProofCompilerSelfShiftTail
  RawCodedTemplateDirectStructuralTranslation
  RawCodedDynamicTruthSigmaSuccessorRowGraph
  RawCodedDynamicTruthSuccessorRowsAppendNormalization
  RawCodedFourStateTableAppendExistentialElimination
  RawCodedDynamicTruthSigmaOrGuardedCanonicalConsumerIntegration
  RawCodedDynamicTruthSigmaOrGuardedCanonicalThreeRootCompilation.

Module
  PABoundedRawCodedDynamicTruthSigmaOrGuardedCanonicalCodeRootAssumptionCompilation.

Import ListNotations.
Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedProofAssumptionLeaf.
Import PABoundedRawCodedPALocalProofUniversalIntroductionChain.
Import PABoundedRawCodedPAAxiomWitnessPrefix.
Import PABoundedRawCodedPALocalProofWitnessedContextMerge.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedTemplateProofCompilerSelfShiftTail.
Import PABoundedRawCodedTemplateDirectStructuralTranslation.
Import PABoundedRawCodedDynamicTruthSigmaSuccessorRowGraph.
Import PABoundedRawCodedDynamicTruthSuccessorRowsAppendNormalization.
Import PABoundedRawCodedFourStateTableAppendExistentialElimination.
Import
  PABoundedRawCodedDynamicTruthSigmaOrGuardedCanonicalConsumerIntegration.
Import
  PABoundedRawCodedDynamicTruthSigmaOrGuardedCanonicalThreeRootCompilation.

(** Opening the eight local-row witnesses lowers the ambient parent formula
    from slot ten to slot two.  The selected left and unused right child
    codes are literally witnesses six and four.  [reflexivity] here is a
    deliberate audit of all eight de Bruijn substitutions. *)
Lemma coqDynamicTruthSigmaOrGuardedCanonicalCodeRootTemplate_shape :
  coqDynamicTruthSigmaOrGuardedCanonicalCodeRootTemplate =
  embedPAFormula
    (formulaOrCodeTermAt (tVar 2) (tVar 6) (tVar 4)).
Proof. reflexivity. Qed.

(** The complete prefix is affine in the caller tail.  In particular, the
    only finite assumptions before that tail are the append-extension facts;
    the formula-constructor atom displayed above is not inserted by this
    definition. *)
Lemma coqDynamicTruthSigmaOrGuardedCanonicalModeZeroRowPrefix_affine :
  forall outerPrefix,
  coqDynamicTruthSigmaOrGuardedCanonicalModeZeroRowPrefix outerPrefix =
  coqFourStateTableAppendRowPrefix
    (ttVar 7) (ttVar 6) (ttVar 5) (ttVar 4)
    (ttVar 3) (ttVar 2) (ttVar 1) (ttVar 0)
    (ttParameter coqDynamicTruthAppendRowBoundParameterName)
    (embedPATerm (Term.numeral 0))
    (ttVar 2) (ttVar 6) (ttVar 5) ++
  templateContextShiftMany 13 outerPrefix.
Proof.
  intros outerPrefix.
  unfold coqDynamicTruthSigmaOrGuardedCanonicalModeZeroRowPrefix.
  apply coqFourStateTableAppendRowContext_affine.
Qed.

(** Any literal member of a temporary prefix has a growing compiler with the
    empty standard-witness extension.  The proof root is reconstructed over
    the whole encoded prefix, so membership—not list position—is the exact
    side condition needed by the represented assumption rule. *)
Theorem raw_codedPAStandardWitnessGrowingTemplateFormulaCompilerAt_of_member :
  forall (M : RawPAModel) (hPA : RawPASatisfies M)
    (translation : RawCodedTemplateTranslation M) prefix formula,
  In formula prefix ->
  RawCodedPAStandardWitnessGrowingTemplateFormulaCompilerAt M
    translation prefix formula.
Proof.
  intros M hPA translation prefix formula hmember
    sourceWitnessList sourceContext hsource.
  set (encodedPrefix :=
    rawTemplateContextCodeOnTail translation sourceContext prefix).
  set (encodedFormula := rawTemplateFormula translation formula).
  exists [],
    (rawProofAssumptionRoot M encodedPrefix encodedFormula).
  cbn [rawStandardPAAxiomWitnessPrefixWitnessListCode
    rawStandardPAAxiomWitnessPrefixContextCode].
  split; [exact hsource |].
  split.
  - apply (raw_proofAssumption_ruleCoverage M hPA).
    unfold encodedPrefix, encodedFormula.
    apply (raw_templateContextOnTail_member M hPA).
    + exact (raw_codedPAAxiomWitnessContext_context_realizable
        M sourceWitnessList sourceContext hsource).
    + exact hmember.
  - apply raw_proofAssumption_endpoint.
Qed.

(** Exact specialization.  This is intentionally conditional on literal
    membership in the *actual* mode-zero prefix; the affine equation above
    records why append lookup projections alone cannot discharge it. *)
Theorem
    raw_dynamicTruthSigmaOrGuardedCanonical_codeRootGrowingCompilerUnderPrefixAt_of_member :
  forall (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M) outerPrefix,
  In coqDynamicTruthSigmaOrGuardedCanonicalCodeRootTemplate
    (coqDynamicTruthSigmaOrGuardedCanonicalModeZeroRowPrefix outerPrefix) ->
  RawCodedPAStandardWitnessGrowingTemplateFormulaCompilerAt M
    (rawDirectStructuralTemplateTranslation M hPA inputs)
    (coqDynamicTruthSigmaOrGuardedCanonicalModeZeroRowPrefix outerPrefix)
    coqDynamicTruthSigmaOrGuardedCanonicalCodeRootTemplate.
Proof.
  intros M hPA inputs outerPrefix hmember.
  exact
    (raw_codedPAStandardWitnessGrowingTemplateFormulaCompilerAt_of_member
      M hPA (rawDirectStructuralTemplateTranslation M hPA inputs)
      (coqDynamicTruthSigmaOrGuardedCanonicalModeZeroRowPrefix outerPrefix)
      coqDynamicTruthSigmaOrGuardedCanonicalCodeRootTemplate hmember).
Qed.

(** A positive compiler is, trivially, a formula-or-refutation compiler. *)
Theorem
    raw_dynamicTruthSigmaOrGuardedCanonical_codeRootGrowingOrRefutationCompilerUnderPrefixAt_of_member :
  forall (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M) outerPrefix,
  In coqDynamicTruthSigmaOrGuardedCanonicalCodeRootTemplate
    (coqDynamicTruthSigmaOrGuardedCanonicalModeZeroRowPrefix outerPrefix) ->
  RawCodedPAStandardWitnessGrowingTemplateFormulaOrRefutationCompilerAt M
    (rawDirectStructuralTemplateTranslation M hPA inputs)
    (coqDynamicTruthSigmaOrGuardedCanonicalModeZeroRowPrefix outerPrefix)
    coqDynamicTruthSigmaOrGuardedCanonicalCodeRootTemplate.
Proof.
  intros M hPA inputs outerPrefix hmember
    sourceWitnessList sourceContext hsource.
  destruct
    (raw_dynamicTruthSigmaOrGuardedCanonical_codeRootGrowingCompilerUnderPrefixAt_of_member
      M hPA inputs outerPrefix hmember
      sourceWitnessList sourceContext hsource) as
    (witnesses & root & hwitnessed & hcode).
  exists witnesses, root. split; [exact hwitnessed |].
  left. exact hcode.
Qed.

(** Conditional two-producer form of the exact three-root residual.  The
    domain and selected-state roots remain independent; the parent-code root
    is supplied solely by the audited literal membership above. *)
Theorem
    raw_dynamicTruthSigmaOrGuardedCanonical_independentGrowingThreeRootOrRefutationCompilersUnderPrefixAt_of_code_member :
  forall (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M) outerPrefix,
  In coqDynamicTruthSigmaOrGuardedCanonicalCodeRootTemplate
    (coqDynamicTruthSigmaOrGuardedCanonicalModeZeroRowPrefix outerPrefix) ->
  RawCodedPAStandardWitnessGrowingTemplateFormulaOrRefutationCompilerAt M
    (rawDirectStructuralTemplateTranslation M hPA inputs)
    (coqDynamicTruthSigmaOrGuardedCanonicalModeZeroRowPrefix outerPrefix)
    coqDynamicTruthSigmaOrGuardedCanonicalDomainRootTemplate ->
  RawCodedPAStandardWitnessGrowingTemplateFormulaOrRefutationCompilerAt M
    (rawDirectStructuralTemplateTranslation M hPA inputs)
    (coqDynamicTruthSigmaOrGuardedCanonicalModeZeroRowPrefix outerPrefix)
    coqDynamicTruthSigmaOrGuardedCanonicalLeftStateRootTemplate ->
  RawDynamicTruthSigmaOrGuardedCanonicalIndependentGrowingThreeRootOrRefutationCompilersUnderPrefixAt
    M hPA inputs outerPrefix.
Proof.
  intros M hPA inputs outerPrefix hmember hdomain hleftState.
  constructor.
  - exact hdomain.
  - exact
      (raw_dynamicTruthSigmaOrGuardedCanonical_codeRootGrowingOrRefutationCompilerUnderPrefixAt_of_member
        M hPA inputs outerPrefix hmember).
  - exact hleftState.
Qed.

End
  PABoundedRawCodedDynamicTruthSigmaOrGuardedCanonicalCodeRootAssumptionCompilation.
