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
  coqDynamicTruthGlobalOpenedRootRowSelectedPayload
      rootMode localSigma localPi =
    templateFormulaShiftMany 10 conclusion ->
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

End PABoundedRawCodedDynamicTruthPredecessorGlobalRowEvidence.
