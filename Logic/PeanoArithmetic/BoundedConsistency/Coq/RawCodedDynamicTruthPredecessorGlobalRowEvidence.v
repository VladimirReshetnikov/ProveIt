(** Turn a selected opened global row into predecessor evidence. *)

From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedContextLists
  RawCodedRestrictedPAProof
  RawCodedPAAxiomWitnessPrefix
  RawCodedPALocalProofExistential
  RawCodedPALocalProofExistentialEliminationChain
  RawCodedPALocalProofWitnessedContextMerge
  RawCodedTemplateSyntax
  RawCodedTemplateProofCompiler
  RawCodedTemplateProofCompilerSelfShiftTail
  RawCodedTemplatePAEmbedding
  RawCodedTemplateLocalProofWitnessedTailTransport
  RawCodedDynamicTruthPredecessorStateExclusivityCompilation
  RawCodedDynamicTruthPredecessorGlobalExistentialElimination
  RawCodedDynamicTruthGlobalOpenedRowSelection.

Module PABoundedRawCodedDynamicTruthPredecessorGlobalRowEvidence.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedContextLists.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedPAAxiomWitnessPrefix.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPALocalProofExistentialEliminationChain.
Import PABoundedRawCodedPALocalProofWitnessedContextMerge.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedTemplateProofCompilerSelfShiftTail.
Import PABoundedRawCodedTemplatePAEmbedding.
Import PABoundedRawCodedTemplateLocalProofWitnessedTailTransport.
Import
  PABoundedRawCodedDynamicTruthPredecessorStateExclusivityCompilation.
Import
  PABoundedRawCodedDynamicTruthPredecessorGlobalExistentialElimination.
Import PABoundedRawCodedDynamicTruthGlobalOpenedRowSelection.

(** This theorem isolates the sole remaining formula-specific obligation:
    the selected row payload must be the tenfold shift of the conclusion to
    be retained after existential elimination.  Everything else—arithmetic
    tag selection, witnessed-tail growth, binder-safe source weakening, and
    all ten represented [Ex-E] nodes—is discharged here. *)
Theorem
    raw_codedPALocalProofOf_dynamicTruthPredecessor_global_row_evidence :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall witnessList baseContext rootMode localSigma localPi
      conclusion sourceRoot,
  RawCodedPAAxiomWitnessContext M witnessList baseContext ->
  rootMode = 0 \/ rootMode = 1 ->
  rawTemplateFormula translation
      (coqDynamicTruthGlobalOpenedRootRowSelectedPayload
        rootMode localSigma localPi) =
    rawTemplateFormula translation
      (templateFormulaShiftMany 10 conclusion) ->
  RawCodedPALocalProofOf M
    (rawDynamicTruthPredecessorJointStateContext M baseContext)
    (rawTemplateFormula translation
      (coqDynamicTruthGlobalExistentialSource
        rootMode localSigma localPi)) sourceRoot ->
  exists witnesses evidenceRoot,
    RawCodedPAAxiomWitnessContext M
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        witnesses witnessList)
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses baseContext) /\
    RawContextListIncluded M baseContext
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses baseContext) /\
    RawCodedPALocalProofOf M
      (rawDynamicTruthPredecessorJointStateContext M
        (rawStandardPAAxiomWitnessPrefixContextCode M
          witnesses baseContext))
      (rawTemplateFormula translation conclusion) evidenceRoot.
Proof.
  intros M hPA translation hagreement witnessList baseContext
    rootMode localSigma localPi conclusion sourceRoot
    hwitnessed hrootMode halignment hsource.
  destruct
    (raw_codedPALocalProofOf_dynamicTruthGlobal_opened_root_row_selected
      M hPA translation hagreement witnessList baseContext
      rootMode localSigma localPi hwitnessed hrootMode)
    as (witnesses & selectedRoot & hextended & hincluded & hselected).
  set (extendedWitnessList :=
    rawStandardPAAxiomWitnessPrefixWitnessListCode M
      witnesses witnessList).
  set (extendedContext :=
    rawStandardPAAxiomWitnessPrefixContextCode M
      witnesses baseContext).
  assert (hsourceOnTemplatePrefix : RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation baseContext
        coqDynamicTruthPredecessorStateTemplateContext)
      (rawTemplateFormula translation
        (coqDynamicTruthGlobalExistentialSource
          rootMode localSigma localPi)) sourceRoot).
  {
    rewrite (raw_dynamicTruthPredecessorStateTemplateContextCode
      M translation hagreement baseContext).
    exact hsource.
  }
  destruct
    (raw_codedPALocalProof_sameTemplatePrefix_witnessedTail_transport
      M hPA translation witnessList baseContext
      extendedWitnessList extendedContext
      coqDynamicTruthPredecessorStateTemplateContext
      (rawTemplateFormula translation
        (coqDynamicTruthGlobalExistentialSource
          rootMode localSigma localPi))
      sourceRoot hwitnessed hextended hincluded hsourceOnTemplatePrefix)
    as [transportedSourceRoot htransportedSource].
  assert (htransportedSourceJoint : RawCodedPALocalProofOf M
      (rawDynamicTruthPredecessorJointStateContext M extendedContext)
      (rawTemplateFormula translation
        (coqDynamicTruthGlobalExistentialSource
          rootMode localSigma localPi)) transportedSourceRoot).
  {
    rewrite <- (raw_dynamicTruthPredecessorStateTemplateContextCode
      M translation hagreement extendedContext).
    exact htransportedSource.
  }
  assert (hselectedShifted : RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation extendedContext
        (coqDynamicTruthGlobalExistentialDeepContext
          rootMode localSigma localPi))
      (rawTemplateFormula translation
        (templateFormulaShiftMany 10 conclusion)) selectedRoot).
  {
    rewrite <- halignment.
    exact hselected.
  }
  destruct
    (raw_codedPALocalProofOf_dynamicTruthGlobal_existential_elimination_on_predecessor_state_context
      M hPA translation hagreement extendedWitnessList extendedContext
      rootMode localSigma localPi conclusion transportedSourceRoot
      selectedRoot hextended htransportedSourceJoint hselectedShifted)
    as [evidenceRoot hevidence].
  exists witnesses, evidenceRoot.
  split; [exact hextended |].
  split; [exact hincluded | exact hevidence].
Qed.

(** Ordinary-PA syntax remains a convenient specialization when the desired
    evidence is standard.  Native nonstandard evidence instead uses the
    weaker translated-code premise of the generic theorem above. *)
Corollary
    raw_codedPALocalProofOf_dynamicTruthPredecessor_global_row_PA_evidence :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall witnessList baseContext rootMode localSigma localPi
      evidenceFormula sourceRoot,
  RawCodedPAAxiomWitnessContext M witnessList baseContext ->
  rootMode = 0 \/ rootMode = 1 ->
  paDynamicTruthGlobalOpenedRootRowSelectedPayload
      rootMode localSigma localPi =
    paFormulaShiftMany 10 evidenceFormula ->
  RawCodedPALocalProofOf M
    (rawDynamicTruthPredecessorJointStateContext M baseContext)
    (rawTemplateFormula translation
      (coqDynamicTruthGlobalExistentialSource
        rootMode localSigma localPi)) sourceRoot ->
  exists witnesses evidenceRoot,
    RawCodedPAAxiomWitnessContext M
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        witnesses witnessList)
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses baseContext) /\
    RawContextListIncluded M baseContext
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses baseContext) /\
    RawCodedPALocalProofOf M
      (rawDynamicTruthPredecessorJointStateContext M
        (rawStandardPAAxiomWitnessPrefixContextCode M
          witnesses baseContext))
      (rawTemplateFormula translation
        (embedPAFormula evidenceFormula)) evidenceRoot.
Proof.
  intros M hPA translation hagreement witnessList baseContext
    rootMode localSigma localPi evidenceFormula sourceRoot
    hwitnessed hrootMode halignment hsource.
  apply
    (raw_codedPALocalProofOf_dynamicTruthPredecessor_global_row_evidence
      M hPA translation hagreement witnessList baseContext
      rootMode localSigma localPi (embedPAFormula evidenceFormula)
      sourceRoot hwitnessed hrootMode).
  - rewrite coqDynamicTruthGlobalOpenedRootRowSelectedPayload_embedPA,
      <- embedPAFormula_paFormulaShiftMany, halignment.
    reflexivity.
  - exact hsource.
Qed.

(** Compile both polarity payloads into one final witnessed context.  The
    second selection may grow the PA tail again, so the first evidence root
    is transported across that inclusion after the Pi elimination closes. *)
Theorem
    raw_codedPALocalProofOf_dynamicTruthPredecessor_global_row_evidence_pair :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall witnessList baseContext localSigma localPi
      sigmaConclusion piConclusion sigmaSourceRoot piSourceRoot,
  RawCodedPAAxiomWitnessContext M witnessList baseContext ->
  rawTemplateFormula translation
      (coqDynamicTruthGlobalOpenedRootRowSelectedPayload
        0 localSigma localPi) =
    rawTemplateFormula translation
      (templateFormulaShiftMany 10 sigmaConclusion) ->
  rawTemplateFormula translation
      (coqDynamicTruthGlobalOpenedRootRowSelectedPayload
        1 localSigma localPi) =
    rawTemplateFormula translation
      (templateFormulaShiftMany 10 piConclusion) ->
  RawCodedPALocalProofOf M
    (rawDynamicTruthPredecessorJointStateContext M baseContext)
    (rawTemplateFormula translation
      (coqDynamicTruthGlobalExistentialSource 0 localSigma localPi))
    sigmaSourceRoot ->
  RawCodedPALocalProofOf M
    (rawDynamicTruthPredecessorJointStateContext M baseContext)
    (rawTemplateFormula translation
      (coqDynamicTruthGlobalExistentialSource 1 localSigma localPi))
    piSourceRoot ->
  exists targetWitnessList targetContext sigmaRoot piRoot,
    RawCodedPAAxiomWitnessContext M targetWitnessList targetContext /\
    RawContextListIncluded M baseContext targetContext /\
    RawCodedPALocalProofOf M
      (rawDynamicTruthPredecessorJointStateContext M targetContext)
      (rawTemplateFormula translation sigmaConclusion) sigmaRoot /\
    RawCodedPALocalProofOf M
      (rawDynamicTruthPredecessorJointStateContext M targetContext)
      (rawTemplateFormula translation piConclusion) piRoot.
Proof.
  intros M hPA translation hagreement witnessList baseContext
    localSigma localPi sigmaConclusion piConclusion
    sigmaSourceRoot piSourceRoot hwitnessed
    hsigmaAlignment hpiAlignment hsigmaSource hpiSource.
  destruct
    (raw_codedPALocalProofOf_dynamicTruthPredecessor_global_row_evidence
      M hPA translation hagreement witnessList baseContext
      0 localSigma localPi sigmaConclusion sigmaSourceRoot
      hwitnessed (or_introl eq_refl) hsigmaAlignment hsigmaSource)
    as (sigmaWitnesses & sigmaRoot & hsigmaWitnessed &
      hsigmaIncluded & hsigma).
  set (sigmaWitnessList :=
    rawStandardPAAxiomWitnessPrefixWitnessListCode M
      sigmaWitnesses witnessList).
  set (sigmaContext :=
    rawStandardPAAxiomWitnessPrefixContextCode M
      sigmaWitnesses baseContext).
  assert (hpiSourceOnTemplatePrefix : RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation baseContext
        coqDynamicTruthPredecessorStateTemplateContext)
      (rawTemplateFormula translation
        (coqDynamicTruthGlobalExistentialSource
          1 localSigma localPi)) piSourceRoot).
  {
    rewrite (raw_dynamicTruthPredecessorStateTemplateContextCode
      M translation hagreement baseContext).
    exact hpiSource.
  }
  destruct
    (raw_codedPALocalProof_sameTemplatePrefix_witnessedTail_transport
      M hPA translation witnessList baseContext
      sigmaWitnessList sigmaContext
      coqDynamicTruthPredecessorStateTemplateContext
      (rawTemplateFormula translation
        (coqDynamicTruthGlobalExistentialSource
          1 localSigma localPi))
      piSourceRoot hwitnessed hsigmaWitnessed hsigmaIncluded
      hpiSourceOnTemplatePrefix)
    as [transportedPiSourceRoot htransportedPiSource].
  assert (htransportedPiSourceJoint : RawCodedPALocalProofOf M
      (rawDynamicTruthPredecessorJointStateContext M sigmaContext)
      (rawTemplateFormula translation
        (coqDynamicTruthGlobalExistentialSource
          1 localSigma localPi)) transportedPiSourceRoot).
  {
    rewrite <- (raw_dynamicTruthPredecessorStateTemplateContextCode
      M translation hagreement sigmaContext).
    exact htransportedPiSource.
  }
  destruct
    (raw_codedPALocalProofOf_dynamicTruthPredecessor_global_row_evidence
      M hPA translation hagreement sigmaWitnessList sigmaContext
      1 localSigma localPi piConclusion transportedPiSourceRoot
      hsigmaWitnessed (or_intror eq_refl) hpiAlignment
      htransportedPiSourceJoint)
    as (piWitnesses & piRoot & hpiWitnessed & hpiIncluded & hpi).
  set (piWitnessList :=
    rawStandardPAAxiomWitnessPrefixWitnessListCode M
      piWitnesses sigmaWitnessList).
  set (piContext :=
    rawStandardPAAxiomWitnessPrefixContextCode M
      piWitnesses sigmaContext).
  assert (hsigmaOnTemplatePrefix : RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation sigmaContext
        coqDynamicTruthPredecessorStateTemplateContext)
      (rawTemplateFormula translation sigmaConclusion) sigmaRoot).
  {
    rewrite (raw_dynamicTruthPredecessorStateTemplateContextCode
      M translation hagreement sigmaContext).
    exact hsigma.
  }
  destruct
    (raw_codedPALocalProof_sameTemplatePrefix_witnessedTail_transport
      M hPA translation sigmaWitnessList sigmaContext
      piWitnessList piContext
      coqDynamicTruthPredecessorStateTemplateContext
      (rawTemplateFormula translation sigmaConclusion) sigmaRoot
      hsigmaWitnessed hpiWitnessed hpiIncluded hsigmaOnTemplatePrefix)
    as [transportedSigmaRoot htransportedSigma].
  assert (htransportedSigmaJoint : RawCodedPALocalProofOf M
      (rawDynamicTruthPredecessorJointStateContext M piContext)
      (rawTemplateFormula translation sigmaConclusion)
      transportedSigmaRoot).
  {
    rewrite <- (raw_dynamicTruthPredecessorStateTemplateContextCode
      M translation hagreement piContext).
    exact htransportedSigma.
  }
  exists piWitnessList, piContext, transportedSigmaRoot, piRoot.
  split; [exact hpiWitnessed |].
  split.
  - intros member hmember.
    exact (hpiIncluded member (hsigmaIncluded member hmember)).
  - split; assumption.
Qed.

End PABoundedRawCodedDynamicTruthPredecessorGlobalRowEvidence.
