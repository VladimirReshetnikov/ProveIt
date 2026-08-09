(**
  Synchronize the two positive Imp-I bodies at their literal ready contexts.

  The append traversal proves a *global source applied to three root terms*.
  At the Imp-I endpoint those terms are not the standalone variables
  [#2,#1,#0]: the eight rule witnesses have moved the outer conclusion and
  assignment arguments to their literal endpoint positions.  This file
  names the three applications needed by the two branches:

  - Pi evidence for the antecedent at [#6,#9,#8];
  - Sigma evidence for the consequent at [#5,#9,#8]; and
  - Sigma evidence for the parent implication at the shifted outer
    conclusion and [#9,#8].

  A branch compiler may allocate its own finite batch of standard PA-axiom
  witnesses.  The false-left compiler is run first and the true-right
  compiler is run on its extension.  The false body and the already compiled
  evidence decision are then transported to the second extension.  Thus the
  public theorem consumes both positive-body compilers, and hence supplies
  the existing fixed-row split, on one explicit standard witness prefix.

  The remaining proof-producing boundary is exactly those two standard-tail
  compilers.  In addition, three carrier-code identifications say that the
  two applied predecessor sources and the applied parent Sigma source are
  the direct truth codes selected by the soundness inputs.  No semantic truth
  law and no simultaneous proof of the exclusive Sigma/Pi predecessor states
  is assumed here.
*)

From Stdlib Require Import List.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  CodedProof
  RawCodedSyntaxConstructors
  RawCodedContextLists
  RawCodedRestrictedPAProof
  RawCodedPAAxiomWitnessPrefix
  RawCodedPALocalProofExistential
  RawCodedTemplateSyntax
  RawCodedTemplateProofCompiler
  RawCodedTemplateProofCompilerSelfShiftTail
  RawCodedTemplateDirectStructuralTranslation
  RawCodedPALocalProofWitnessedContextMerge
  RawCodedTemplateLocalProofWitnessedTailTransport
  RawCodedTemplateLocalProofStandardWitnessTailTransport
  RawCodedFixedLevelTruthTotality
  RawCodedFourStateTableAppendPermutedTemplateGlobalTraversalAssembly
  RawCodedDynamicTruthSuccessorRowsAppendNormalization
  RawCodedDynamicTruthSigmaImpFixedProductionAppendIntegration
  RawCodedRestrictedPADerivationSoundnessDirectAssumptionCase
  RawCodedRestrictedPADerivationSoundnessDirectImpIntroductionCase
  RawCodedRestrictedPADerivationSoundnessDirectRuleCasesAfterImpIntroductionRecursive
  RawCodedRestrictedPADerivationSoundnessDirectRuleCasesAfterImpIntroductionTruth
  RawCodedRestrictedPADirectImpIntroductionStandardReadySplitCompilation.

Import ListNotations.

Module
  PABoundedRawCodedRestrictedPADirectImpIntroductionPositiveBodyCompilation.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedCodedProof.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedContextLists.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedPAAxiomWitnessPrefix.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedTemplateProofCompilerSelfShiftTail.
Import PABoundedRawCodedTemplateDirectStructuralTranslation.
Import PABoundedRawCodedPALocalProofWitnessedContextMerge.
Import PABoundedRawCodedTemplateLocalProofWitnessedTailTransport.
Import PABoundedRawCodedTemplateLocalProofStandardWitnessTailTransport.
Import PABoundedRawCodedFixedLevelTruthTotality.
Import
  PABoundedRawCodedFourStateTableAppendPermutedTemplateGlobalTraversalAssembly.
Import PABoundedRawCodedDynamicTruthSuccessorRowsAppendNormalization.
Import
  PABoundedRawCodedDynamicTruthSigmaImpFixedProductionAppendIntegration.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectAssumptionCase.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectImpIntroductionCase.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectRuleCasesAfterImpIntroductionRecursive.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectRuleCasesAfterImpIntroductionTruth.
Import
  PABoundedRawCodedRestrictedPADirectImpIntroductionStandardReadySplitCompilation.

(** The predecessor evidence assumed by the false-left implication row.
    The root formula is witness [#6], while [#9] and [#8] are the assignment
    code and assignment step inherited from before the eight rule witnesses
    were opened. *)
Definition coqRestrictedPADirectImpIntroductionFalseLeftPiEvidenceTemplate
    : TemplateFormula :=
  coqFourStateTableAppendTemplateGlobalSourceAtRootTerms 1
    coqDynamicTruthSharedSigmaSuccessorRowTemplate
    coqDynamicTruthSharedPiSuccessorRowTemplate
    (ttVar 6) (ttVar 9) (ttVar 8).

(** The predecessor evidence assumed by the true-right implication row. *)
Definition coqRestrictedPADirectImpIntroductionTrueRightSigmaEvidenceTemplate
    : TemplateFormula :=
  coqFourStateTableAppendTemplateGlobalSourceAtRootTerms 0
    coqDynamicTruthSharedSigmaSuccessorRowTemplate
    coqDynamicTruthSharedPiSuccessorRowTemplate
    (ttVar 5) (ttVar 9) (ttVar 8).

(** The positive conclusion common to both rows.  Using the named outer
    conclusion term avoids silently replacing its eight-variable lift by an
    unrelated low de Bruijn index. *)
Definition coqRestrictedPADirectImpIntroductionParentSigmaEvidenceTemplate
    : TemplateFormula :=
  coqFourStateTableAppendTemplateGlobalSourceAtRootTerms 0
    coqDynamicTruthSharedSigmaSuccessorRowTemplate
    coqDynamicTruthSharedPiSuccessorRowTemplate
    coqRestrictedPADirectAssumptionOuterConclusionTerm
    (ttVar 9) (ttVar 8).

Definition coqRestrictedPADirectImpIntroductionFalsePositiveBodyPrefix
    : TemplateContext :=
  coqRestrictedPADirectImpIntroductionFalseLeftPiEvidenceTemplate ::
  coqRestrictedPADirectImpIntroductionFormulaCodeTemplate ::
  coqRestrictedPADirectStrongStepImpIntroductionReadyContext [].

Definition coqRestrictedPADirectImpIntroductionTruePositiveBodyPrefix
    : TemplateContext :=
  coqRestrictedPADirectImpIntroductionTrueRightSigmaEvidenceTemplate ::
  coqRestrictedPADirectImpIntroductionFormulaCodeTemplate ::
  coqRestrictedPADirectStrongStepImpIntroductionReadyContext [].

(** Standard-tail form of one append/application producer.  This is the
    exact strengthening of a bare [RawCodedPAGrowingTemplateLocalProofAt]
    needed by the direct soundness continuation: the selected target remains
    visibly a meta-level finite prefix of standard PA-axiom witnesses. *)
Definition RawCoqRestrictedPADirectImpIntroductionPositiveBodyCompilerAt
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    (prefix : TemplateContext) : Prop :=
  forall sourceWitnessList sourceContext,
  RawCodedPAAxiomWitnessContext M sourceWitnessList sourceContext ->
  exists (witnesses : StandardPAAxiomWitnessPrefix) (root : M),
    RawCodedPAAxiomWitnessContext M
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        witnesses sourceWitnessList)
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses sourceContext) /\
    RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        (rawStandardPAAxiomWitnessPrefixContextCode M
          witnesses sourceContext)
        prefix)
      (rawDirectTemplateFormula inputs
        coqRestrictedPADirectImpIntroductionParentSigmaEvidenceTemplate)
      root.

Arguments RawCoqRestrictedPADirectImpIntroductionPositiveBodyCompilerAt
  M hPA inputs prefix : clear implicits.

(** Keep the branch indices selected by the finite Sigma implication
    compiler visible in the producer package.  The two fields have different
    prefix types, so exchanging false-left and true-right is rejected by the
    kernel even though their output formula is shared. *)
Record RawCoqRestrictedPADirectImpIntroductionPositiveBodyCompilers
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M) : Prop := {
  rawCoqRestrictedPADirectImpIntroduction_falseLeftBodyCompiler :
    RawCoqRestrictedPADirectImpIntroductionPositiveBodyCompilerAt
      M hPA inputs
      coqRestrictedPADirectImpIntroductionFalsePositiveBodyPrefix;
  rawCoqRestrictedPADirectImpIntroduction_trueRightBodyCompiler :
    RawCoqRestrictedPADirectImpIntroductionPositiveBodyCompilerAt
      M hPA inputs
      coqRestrictedPADirectImpIntroductionTruePositiveBodyPrefix
}.

Arguments RawCoqRestrictedPADirectImpIntroductionPositiveBodyCompilers
  M hPA inputs : clear implicits.

(** Synchronize two supplied applied-global-source compilers and immediately
    consume their results as the positive bodies of the verified ready split.
    The theorem performs all witness/context synchronization itself; it does
    not claim that the two compiler fields have already been constructed. *)
Theorem
    raw_selectedImpIntroductionFixedRowSplitTail_of_ready_decision_and_positive_body_compilers :
  forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    (baseWitnesses : StandardPAAxiomWitnessPrefix)
    piLeft decisionRoot,
  let translation := rawDirectStructuralTemplateTranslation M hPA inputs in
  let baseContext := rawStandardPAAxiomWitnessPrefixContextCode M
    baseWitnesses (raw_zero M) in
  let readyPrefix :=
    coqRestrictedPADirectStrongStepImpIntroductionReadyContext [] in
  let readyContext := rawTemplateContextCodeOnTail translation
    baseContext readyPrefix in
  let formulaRelation := rawDirectTemplateFormula inputs
    coqRestrictedPADirectImpIntroductionFormulaCodeTemplate in
  let sigmaLeft := rawDirectTemplateFormula inputs
    coqRestrictedPADirectImpIntroductionAntecedentTruthTemplate in
  let sigmaRight := rawDirectTemplateFormula inputs
    coqRestrictedPADirectImpIntroductionConsequentTruthTemplate in
  let sigmaImp := rawDirectTemplateFormula inputs
    coqRestrictedPADirectAssumptionOuterConclusionTruthTemplate in
  RawCodedPAAxiomWitnessContext M
    (rawStandardPAAxiomWitnessPrefixWitnessListCode M
      baseWitnesses (raw_zero M)) baseContext ->
  RawCodedFormulaAtomicallyAdequate M piLeft ->
  RawCodedPALocalProofOf M readyContext
    (rawFormulaOrCode M sigmaLeft piLeft) decisionRoot ->
  rawDirectTemplateFormula inputs
      coqRestrictedPADirectImpIntroductionFalseLeftPiEvidenceTemplate =
    piLeft ->
  rawDirectTemplateFormula inputs
      coqRestrictedPADirectImpIntroductionTrueRightSigmaEvidenceTemplate =
    sigmaRight ->
  rawDirectTemplateFormula inputs
      coqRestrictedPADirectImpIntroductionParentSigmaEvidenceTemplate =
    sigmaImp ->
  RawCoqRestrictedPADirectImpIntroductionPositiveBodyCompilers
    M hPA inputs ->
  RawCoqRestrictedPADirectSelectedImpIntroductionFixedRowSplitTail
    M hPA inputs.
Proof.
  intros M hPA inputs baseWitnesses piLeft decisionRoot
    translation baseContext readyPrefix readyContext
    formulaRelation sigmaLeft sigmaRight sigmaImp
    hbase hpiAdequate hdecision
    hfalseEvidence htrueEvidence hparentEvidence
    [hfalseCompiler htrueCompiler].
  cbn zeta in *.

  destruct
    (hfalseCompiler
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        baseWitnesses (raw_zero M))
      baseContext hbase) as
    (falseWitnesses & falseRoot & hfalseWitnessed & hfalse).
  set (falseWitnessList :=
    rawStandardPAAxiomWitnessPrefixWitnessListCode M falseWitnesses
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        baseWitnesses (raw_zero M))).
  set (falseContext :=
    rawStandardPAAxiomWitnessPrefixContextCode M falseWitnesses
      baseContext).

  destruct
    (htrueCompiler falseWitnessList falseContext hfalseWitnessed) as
    (trueWitnesses & trueRoot & hfinalWitnessed & htrue).
  set (finalWitnessList :=
    rawStandardPAAxiomWitnessPrefixWitnessListCode M trueWitnesses
      falseWitnessList).
  set (finalContext :=
    rawStandardPAAxiomWitnessPrefixContextCode M trueWitnesses
      falseContext).
  fold finalContext in htrue.
  fold translation in htrue.

  assert (hfalseFinalIncluded : RawContextListIncluded M
      falseContext finalContext).
  {
    unfold finalContext.
    exact
      (raw_standardPAAxiomWitnessPrefixContextCode_target_included
        M hPA trueWitnesses falseContext).
  }
  destruct
    (raw_codedPALocalProof_sameTemplatePrefix_witnessedTail_transport
      M hPA translation
      falseWitnessList falseContext
      finalWitnessList finalContext
      coqRestrictedPADirectImpIntroductionFalsePositiveBodyPrefix
      (rawDirectTemplateFormula inputs
        coqRestrictedPADirectImpIntroductionParentSigmaEvidenceTemplate)
      falseRoot hfalseWitnessed hfinalWitnessed
      hfalseFinalIncluded hfalse) as
    [falseFinalRoot hfalseFinal].

  assert (hbaseFalseIncluded : RawContextListIncluded M
      baseContext falseContext).
  {
    unfold falseContext.
    exact
      (raw_standardPAAxiomWitnessPrefixContextCode_target_included
        M hPA falseWitnesses baseContext).
  }
  assert (hbaseFinalIncluded : RawContextListIncluded M
      baseContext finalContext).
  {
    intros member hmember.
    exact (hfalseFinalIncluded member
      (hbaseFalseIncluded member hmember)).
  }
  destruct
    (raw_codedPALocalProof_sameTemplatePrefix_witnessedTail_transport
      M hPA translation
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        baseWitnesses (raw_zero M))
      baseContext finalWitnessList finalContext readyPrefix
      (rawFormulaOrCode M sigmaLeft piLeft) decisionRoot
      hbase hfinalWitnessed hbaseFinalIncluded hdecision) as
    [decisionFinalRoot hdecisionFinal].

  assert (hfalseContextCode :
      rawTemplateContextCodeOnTail translation finalContext
        coqRestrictedPADirectImpIntroductionFalsePositiveBodyPrefix =
      rawListNode M piLeft
        (rawListNode M formulaRelation
          (rawTemplateContextCodeOnTail translation finalContext
            readyPrefix))).
  {
    unfold
      coqRestrictedPADirectImpIntroductionFalsePositiveBodyPrefix.
    change
      (rawListNode M
        (rawDirectTemplateFormula inputs
          coqRestrictedPADirectImpIntroductionFalseLeftPiEvidenceTemplate)
        (rawListNode M formulaRelation
          (rawTemplateContextCodeOnTail translation finalContext
            readyPrefix)) =
       rawListNode M piLeft
        (rawListNode M formulaRelation
          (rawTemplateContextCodeOnTail translation finalContext
            readyPrefix))).
    rewrite hfalseEvidence.
    reflexivity.
  }
  assert (htrueContextCode :
      rawTemplateContextCodeOnTail translation finalContext
        coqRestrictedPADirectImpIntroductionTruePositiveBodyPrefix =
      rawListNode M sigmaRight
        (rawListNode M formulaRelation
          (rawTemplateContextCodeOnTail translation finalContext
            readyPrefix))).
  {
    unfold
      coqRestrictedPADirectImpIntroductionTruePositiveBodyPrefix.
    change
      (rawListNode M
        (rawDirectTemplateFormula inputs
          coqRestrictedPADirectImpIntroductionTrueRightSigmaEvidenceTemplate)
        (rawListNode M formulaRelation
          (rawTemplateContextCodeOnTail translation finalContext
            readyPrefix)) =
       rawListNode M sigmaRight
        (rawListNode M formulaRelation
          (rawTemplateContextCodeOnTail translation finalContext
            readyPrefix))).
    rewrite htrueEvidence.
    reflexivity.
  }
  rewrite hfalseContextCode, hparentEvidence in hfalseFinal.
  rewrite htrueContextCode, hparentEvidence in htrue.

  set (allWitnesses := trueWitnesses ++
    (falseWitnesses ++ baseWitnesses)).
  assert (hfinalWitnessedStandard : RawCodedPAAxiomWitnessContext M
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        allWitnesses (raw_zero M))
      (rawStandardPAAxiomWitnessPrefixContextCode M
        allWitnesses (raw_zero M))).
  {
    unfold allWitnesses, finalWitnessList, finalContext,
      falseWitnessList, falseContext in hfinalWitnessed |- *.
    rewrite !rawStandardPAAxiomWitnessPrefixWitnessListCode_app.
    rewrite !rawStandardPAAxiomWitnessPrefixContextCode_app.
    exact hfinalWitnessed.
  }
  assert (hfinalContextStandard :
      finalContext =
      rawStandardPAAxiomWitnessPrefixContextCode M
        allWitnesses (raw_zero M)).
  {
    unfold allWitnesses, finalContext, falseContext, baseContext.
    rewrite !rawStandardPAAxiomWitnessPrefixContextCode_app.
    reflexivity.
  }
  rewrite hfinalContextStandard in
    hdecisionFinal, hfalseFinal, htrue.

  exact
    (raw_selectedImpIntroductionFixedRowSplitTail_of_standard_ready_decision_and_positive_bodies
      M hPA inputs allWitnesses piLeft
      decisionFinalRoot falseFinalRoot trueRoot
      hfinalWitnessedStandard hpiAdequate
      hdecisionFinal hfalseFinal htrue).
Qed.

End
  PABoundedRawCodedRestrictedPADirectImpIntroductionPositiveBodyCompilation.
