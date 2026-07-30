(** Turn a selected opened global row into predecessor evidence. *)

From Stdlib Require Import List.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors
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
  RawCodedTemplateLocalProofStandardWitnessTailTransport
  RawCodedDynamicTruthNativeLocalPositiveGraph
  RawCodedDynamicTruthLocalAdmissibilityCompilation
  RawCodedDynamicTruthPredecessorAdmissibilityAssignmentCompilation
  RawCodedDynamicTruthPredecessorStateExclusivityCompilation
  RawCodedDynamicTruthPredecessorGlobalExistentialElimination
  RawCodedDynamicTruthGlobalOpenedRowSelection.

Module PABoundedRawCodedDynamicTruthPredecessorGlobalRowEvidence.

Import ListNotations.
Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedSyntaxConstructors.
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
Import PABoundedRawCodedTemplateLocalProofStandardWitnessTailTransport.
Import PABoundedRawCodedDynamicTruthNativeLocalPositiveGraph.
Import PABoundedRawCodedDynamicTruthLocalAdmissibilityCompilation.
Import
  PABoundedRawCodedDynamicTruthPredecessorAdmissibilityAssignmentCompilation.
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
    raw_codedPALocalProofOf_dynamicTruthPredecessor_global_row_evidence_under_prefix :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall witnessList baseContext prefix rootMode localSigma localPi
      conclusion sourceRoot,
  RawCodedPAAxiomWitnessContext M witnessList baseContext ->
  rootMode = 0 \/ rootMode = 1 ->
  rawTemplateFormula translation
      (coqDynamicTruthGlobalOpenedRootRowSelectedPayload
        rootMode localSigma localPi) =
    rawTemplateFormula translation
      (templateFormulaShiftMany 10 conclusion) ->
  RawCodedPALocalProofOf M
    (rawDynamicTruthPredecessorJointStateContext M
      (rawTemplateContextCodeOnTail translation baseContext prefix))
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
        (rawTemplateContextCodeOnTail translation
          (rawStandardPAAxiomWitnessPrefixContextCode M
            witnesses baseContext) prefix))
      (rawTemplateFormula translation conclusion) evidenceRoot.
Proof.
  intros M hPA translation hagreement witnessList baseContext
    prefix rootMode localSigma localPi conclusion sourceRoot
    hwitnessed hrootMode halignment hsource.
  destruct
    (raw_codedPALocalProofOf_dynamicTruthGlobal_opened_root_row_selected_under_prefix
      M hPA translation hagreement witnessList baseContext
      prefix rootMode localSigma localPi hwitnessed hrootMode)
    as (witnesses & selectedRoot & hextended & hincluded & hselected).
  set (extendedWitnessList :=
    rawStandardPAAxiomWitnessPrefixWitnessListCode M
      witnesses witnessList).
  set (extendedContext :=
    rawStandardPAAxiomWitnessPrefixContextCode M
      witnesses baseContext).
  assert (hsourceOnTemplatePrefix : RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation baseContext
        (coqDynamicTruthPredecessorStateTemplateContext ++ prefix))
      (rawTemplateFormula translation
        (coqDynamicTruthGlobalExistentialSource
          rootMode localSigma localPi)) sourceRoot).
  {
    rewrite (raw_dynamicTruthPredecessorStateTemplateContext_app_code
      M translation hagreement baseContext prefix).
    exact hsource.
  }
  destruct
    (raw_codedPALocalProof_sameTemplatePrefix_witnessedTail_transport
      M hPA translation witnessList baseContext
      extendedWitnessList extendedContext
      (coqDynamicTruthPredecessorStateTemplateContext ++ prefix)
      (rawTemplateFormula translation
        (coqDynamicTruthGlobalExistentialSource
          rootMode localSigma localPi))
      sourceRoot hwitnessed hextended hincluded hsourceOnTemplatePrefix)
    as [transportedSourceRoot htransportedSource].
  assert (htransportedSourceJoint : RawCodedPALocalProofOf M
      (rawDynamicTruthPredecessorJointStateContext M
        (rawTemplateContextCodeOnTail translation extendedContext prefix))
      (rawTemplateFormula translation
        (coqDynamicTruthGlobalExistentialSource
          rootMode localSigma localPi)) transportedSourceRoot).
  {
    rewrite <- (raw_dynamicTruthPredecessorStateTemplateContext_app_code
      M translation hagreement extendedContext prefix).
    exact htransportedSource.
  }
  assert (hselectedShifted : RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation extendedContext
        (coqDynamicTruthGlobalExistentialDeepContextUnderPrefix
          rootMode localSigma localPi prefix))
      (rawTemplateFormula translation
        (templateFormulaShiftMany 10 conclusion)) selectedRoot).
  {
    rewrite <- halignment.
    exact hselected.
  }
  destruct
    (raw_codedPALocalProofOf_dynamicTruthGlobal_existential_elimination_on_predecessor_state_context_under_prefix
      M hPA translation hagreement extendedWitnessList extendedContext
      prefix rootMode localSigma localPi conclusion transportedSourceRoot
      selectedRoot hextended htransportedSourceJoint hselectedShifted)
    as [evidenceRoot hevidence].
  exists witnesses, evidenceRoot.
  split; [exact hextended |].
  split; [exact hincluded | exact hevidence].
Qed.

(** State-only compatibility endpoint. *)
Corollary
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
  pose proof
    (raw_codedPALocalProofOf_dynamicTruthPredecessor_global_row_evidence_under_prefix
      M hPA translation hagreement witnessList baseContext []
      rootMode localSigma localPi conclusion sourceRoot
      hwitnessed hrootMode halignment hsource) as hresult.
  cbn [rawTemplateContextCodeOnTail] in hresult.
  exact hresult.
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
    raw_codedPALocalProofOf_dynamicTruthPredecessor_global_row_evidence_pair_under_prefix :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall witnessList baseContext prefix localSigma localPi
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
    (rawDynamicTruthPredecessorJointStateContext M
      (rawTemplateContextCodeOnTail translation baseContext prefix))
    (rawTemplateFormula translation
      (coqDynamicTruthGlobalExistentialSource 0 localSigma localPi))
    sigmaSourceRoot ->
  RawCodedPALocalProofOf M
    (rawDynamicTruthPredecessorJointStateContext M
      (rawTemplateContextCodeOnTail translation baseContext prefix))
    (rawTemplateFormula translation
      (coqDynamicTruthGlobalExistentialSource 1 localSigma localPi))
    piSourceRoot ->
  exists targetWitnessList targetContext sigmaRoot piRoot,
    RawCodedPAAxiomWitnessContext M targetWitnessList targetContext /\
    RawContextListIncluded M baseContext targetContext /\
    RawCodedPALocalProofOf M
      (rawDynamicTruthPredecessorJointStateContext M
        (rawTemplateContextCodeOnTail translation targetContext prefix))
      (rawTemplateFormula translation sigmaConclusion) sigmaRoot /\
    RawCodedPALocalProofOf M
      (rawDynamicTruthPredecessorJointStateContext M
        (rawTemplateContextCodeOnTail translation targetContext prefix))
      (rawTemplateFormula translation piConclusion) piRoot.
Proof.
  intros M hPA translation hagreement witnessList baseContext
    prefix localSigma localPi sigmaConclusion piConclusion
    sigmaSourceRoot piSourceRoot hwitnessed
    hsigmaAlignment hpiAlignment hsigmaSource hpiSource.
  destruct
    (raw_codedPALocalProofOf_dynamicTruthPredecessor_global_row_evidence_under_prefix
      M hPA translation hagreement witnessList baseContext
      prefix 0 localSigma localPi sigmaConclusion sigmaSourceRoot
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
        (coqDynamicTruthPredecessorStateTemplateContext ++ prefix))
      (rawTemplateFormula translation
        (coqDynamicTruthGlobalExistentialSource
          1 localSigma localPi)) piSourceRoot).
  {
    rewrite (raw_dynamicTruthPredecessorStateTemplateContext_app_code
      M translation hagreement baseContext prefix).
    exact hpiSource.
  }
  destruct
    (raw_codedPALocalProof_sameTemplatePrefix_witnessedTail_transport
      M hPA translation witnessList baseContext
      sigmaWitnessList sigmaContext
      (coqDynamicTruthPredecessorStateTemplateContext ++ prefix)
      (rawTemplateFormula translation
        (coqDynamicTruthGlobalExistentialSource
          1 localSigma localPi))
      piSourceRoot hwitnessed hsigmaWitnessed hsigmaIncluded
      hpiSourceOnTemplatePrefix)
    as [transportedPiSourceRoot htransportedPiSource].
  assert (htransportedPiSourceJoint : RawCodedPALocalProofOf M
      (rawDynamicTruthPredecessorJointStateContext M
        (rawTemplateContextCodeOnTail translation sigmaContext prefix))
      (rawTemplateFormula translation
        (coqDynamicTruthGlobalExistentialSource
          1 localSigma localPi)) transportedPiSourceRoot).
  {
    rewrite <- (raw_dynamicTruthPredecessorStateTemplateContext_app_code
      M translation hagreement sigmaContext prefix).
    exact htransportedPiSource.
  }
  destruct
    (raw_codedPALocalProofOf_dynamicTruthPredecessor_global_row_evidence_under_prefix
      M hPA translation hagreement sigmaWitnessList sigmaContext
      prefix 1 localSigma localPi piConclusion transportedPiSourceRoot
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
        (coqDynamicTruthPredecessorStateTemplateContext ++ prefix))
      (rawTemplateFormula translation sigmaConclusion) sigmaRoot).
  {
    rewrite (raw_dynamicTruthPredecessorStateTemplateContext_app_code
      M translation hagreement sigmaContext prefix).
    exact hsigma.
  }
  destruct
    (raw_codedPALocalProof_sameTemplatePrefix_witnessedTail_transport
      M hPA translation sigmaWitnessList sigmaContext
      piWitnessList piContext
      (coqDynamicTruthPredecessorStateTemplateContext ++ prefix)
      (rawTemplateFormula translation sigmaConclusion) sigmaRoot
      hsigmaWitnessed hpiWitnessed hpiIncluded hsigmaOnTemplatePrefix)
    as [transportedSigmaRoot htransportedSigma].
  assert (htransportedSigmaJoint : RawCodedPALocalProofOf M
      (rawDynamicTruthPredecessorJointStateContext M
        (rawTemplateContextCodeOnTail translation piContext prefix))
      (rawTemplateFormula translation sigmaConclusion)
      transportedSigmaRoot).
  {
    rewrite <- (raw_dynamicTruthPredecessorStateTemplateContext_app_code
      M translation hagreement piContext prefix).
    exact htransportedSigma.
  }
  exists piWitnessList, piContext, transportedSigmaRoot, piRoot.
  split; [exact hpiWitnessed |].
  split.
  - intros member hmember.
    exact (hpiIncluded member (hsigmaIncluded member hmember)).
  - split; assumption.
Qed.

(** State-only paired endpoint. *)
Corollary
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
  pose proof
    (raw_codedPALocalProofOf_dynamicTruthPredecessor_global_row_evidence_pair_under_prefix
      M hPA translation hagreement witnessList baseContext []
      localSigma localPi sigmaConclusion piConclusion
      sigmaSourceRoot piSourceRoot hwitnessed
      hsigmaAlignment hpiAlignment hsigmaSource hpiSource) as hresult.
  cbn [rawTemplateContextCodeOnTail] in hresult.
  exact hresult.
Qed.

(** Package a caller-supplied admissibility root with the two newly derived
    evidence roots.  The admissibility proof is transported only after both
    polarity compilers have selected their final common witnessed tail. *)
Corollary
    raw_dynamicTruthPredecessorStateLogicalRootsAt_of_global_row_pair_under_prefix :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall witnessList baseContext prefix localSigma localPi
      sigmaDomain piDomain sigmaConclusion piConclusion
      sigmaSourceRoot piSourceRoot,
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
    (rawDynamicTruthPredecessorJointStateContext M
      (rawTemplateContextCodeOnTail translation baseContext prefix))
    (rawTemplateFormula translation
      (coqDynamicTruthGlobalExistentialSource 0 localSigma localPi))
    sigmaSourceRoot ->
  RawCodedPALocalProofOf M
    (rawDynamicTruthPredecessorJointStateContext M
      (rawTemplateContextCodeOnTail translation baseContext prefix))
    (rawTemplateFormula translation
      (coqDynamicTruthGlobalExistentialSource 1 localSigma localPi))
    piSourceRoot ->
  (exists admissibleRoot,
    RawCodedPALocalProofOf M
      (rawDynamicTruthPredecessorJointStateContext M
        (rawTemplateContextCodeOnTail translation baseContext prefix))
      (rawDynamicTruthLocalAdmissibleCode M sigmaDomain piDomain)
      admissibleRoot) ->
  exists targetWitnessList targetContext,
    RawCodedPAAxiomWitnessContext M targetWitnessList targetContext /\
    RawContextListIncluded M baseContext targetContext /\
    RawDynamicTruthPredecessorStateLogicalRootsAt M
      (rawTemplateContextCodeOnTail translation targetContext prefix)
      sigmaDomain piDomain
      (rawTemplateFormula translation sigmaConclusion)
      (rawTemplateFormula translation piConclusion).
Proof.
  intros M hPA translation hagreement witnessList baseContext
    prefix localSigma localPi sigmaDomain piDomain
    sigmaConclusion piConclusion
    sigmaSourceRoot piSourceRoot hwitnessed hsigmaAlignment hpiAlignment
    hsigmaSource hpiSource [admissibleRoot hadmissible].
  destruct
    (raw_codedPALocalProofOf_dynamicTruthPredecessor_global_row_evidence_pair_under_prefix
      M hPA translation hagreement witnessList baseContext
      prefix localSigma localPi sigmaConclusion piConclusion
      sigmaSourceRoot piSourceRoot hwitnessed
      hsigmaAlignment hpiAlignment hsigmaSource hpiSource)
    as (targetWitnessList & targetContext & sigmaRoot & piRoot &
      htargetWitnessed & hincluded & hsigma & hpi).
  assert (hadmissibleOnTemplatePrefix : RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation baseContext
        (coqDynamicTruthPredecessorStateTemplateContext ++ prefix))
      (rawDynamicTruthLocalAdmissibleCode M sigmaDomain piDomain)
      admissibleRoot).
  {
    rewrite (raw_dynamicTruthPredecessorStateTemplateContext_app_code
      M translation hagreement baseContext prefix).
    exact hadmissible.
  }
  destruct
    (raw_codedPALocalProof_sameTemplatePrefix_witnessedTail_transport
      M hPA translation witnessList baseContext
      targetWitnessList targetContext
      (coqDynamicTruthPredecessorStateTemplateContext ++ prefix)
      (rawDynamicTruthLocalAdmissibleCode M sigmaDomain piDomain)
      admissibleRoot hwitnessed htargetWitnessed hincluded
      hadmissibleOnTemplatePrefix)
    as [transportedAdmissibleRoot htransportedAdmissible].
  assert (htransportedAdmissibleJoint : RawCodedPALocalProofOf M
      (rawDynamicTruthPredecessorJointStateContext M
        (rawTemplateContextCodeOnTail translation targetContext prefix))
      (rawDynamicTruthLocalAdmissibleCode M sigmaDomain piDomain)
      transportedAdmissibleRoot).
  {
    rewrite <- (raw_dynamicTruthPredecessorStateTemplateContext_app_code
      M translation hagreement targetContext prefix).
    exact htransportedAdmissible.
  }
  exists targetWitnessList, targetContext.
  split; [exact htargetWitnessed |].
  split; [exact hincluded |].
  constructor.
  - exists transportedAdmissibleRoot. exact htransportedAdmissibleJoint.
  - exists sigmaRoot. exact hsigma.
  - exists piRoot. exact hpi.
Qed.

(** State-only compatibility package. *)
Corollary
    raw_dynamicTruthPredecessorStateLogicalRootsAt_of_global_row_pair :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall witnessList baseContext localSigma localPi
      sigmaDomain piDomain sigmaConclusion piConclusion
      sigmaSourceRoot piSourceRoot,
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
  (exists admissibleRoot,
    RawCodedPALocalProofOf M
      (rawDynamicTruthPredecessorJointStateContext M baseContext)
      (rawDynamicTruthLocalAdmissibleCode M sigmaDomain piDomain)
      admissibleRoot) ->
  exists targetWitnessList targetContext,
    RawCodedPAAxiomWitnessContext M targetWitnessList targetContext /\
    RawContextListIncluded M baseContext targetContext /\
    RawDynamicTruthPredecessorStateLogicalRootsAt M targetContext
      sigmaDomain piDomain
      (rawTemplateFormula translation sigmaConclusion)
      (rawTemplateFormula translation piConclusion).
Proof.
  intros M hPA translation hagreement witnessList baseContext
    localSigma localPi sigmaDomain piDomain sigmaConclusion piConclusion
    sigmaSourceRoot piSourceRoot hwitnessed hsigmaAlignment hpiAlignment
    hsigmaSource hpiSource hadmissible.
  pose proof
    (raw_dynamicTruthPredecessorStateLogicalRootsAt_of_global_row_pair_under_prefix
      M hPA translation hagreement witnessList baseContext []
      localSigma localPi sigmaDomain piDomain sigmaConclusion piConclusion
      sigmaSourceRoot piSourceRoot hwitnessed hsigmaAlignment hpiAlignment
      hsigmaSource hpiSource hadmissible) as hresult.
  cbn [rawTemplateContextCodeOnTail] in hresult.
  exact hresult.
Qed.

(** Component-facing form of the complete package.  It deliberately asks
    for the three independently sourced admissibility facts in the original
    joint-state context; their conjunction is compiled before the paired
    evidence eliminator chooses its final witnessed extension. *)
Corollary
    raw_dynamicTruthPredecessorStateLogicalRootsAt_of_global_row_pair_components :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall witnessList baseContext localSigma localPi
      sigmaDomain piDomain sigmaConclusion piConclusion
      sigmaSourceRoot piSourceRoot,
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
  RawDynamicTruthLocalAdmissibilityComponentsAt M
    (rawDynamicTruthPredecessorJointStateContext M baseContext)
    sigmaDomain piDomain ->
  exists targetWitnessList targetContext,
    RawCodedPAAxiomWitnessContext M targetWitnessList targetContext /\
    RawContextListIncluded M baseContext targetContext /\
    RawDynamicTruthPredecessorStateLogicalRootsAt M targetContext
      sigmaDomain piDomain
      (rawTemplateFormula translation sigmaConclusion)
      (rawTemplateFormula translation piConclusion).
Proof.
  intros M hPA translation hagreement witnessList baseContext
    localSigma localPi sigmaDomain piDomain sigmaConclusion piConclusion
    sigmaSourceRoot piSourceRoot hwitnessed hsigmaAlignment hpiAlignment
    hsigmaSource hpiSource hcomponents.
  apply
    (raw_dynamicTruthPredecessorStateLogicalRootsAt_of_global_row_pair
      M hPA translation hagreement witnessList baseContext
      localSigma localPi sigmaDomain piDomain sigmaConclusion piConclusion
      sigmaSourceRoot piSourceRoot hwitnessed
      hsigmaAlignment hpiAlignment hsigmaSource hpiSource).
  exact
    (raw_codedPALocalProofOf_dynamicTruthLocalAdmissible_of_components
      M hPA
      (rawDynamicTruthPredecessorJointStateContext M baseContext)
      sigmaDomain piDomain hcomponents).
Qed.

(** End-to-end logical-root composition with the honest admissibility
    boundary.  Assignment coverage and every intermediate context transport
    are internal; callers retain only the two restricted-proof invariants and
    the two opened global-row sources. *)
Corollary
    raw_dynamicTruthPredecessorStateLogicalRootsAt_of_global_row_pair_under_prefix_atomic_and_domain :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall witnessList baseContext prefix localSigma localPi
      sigmaDomain piDomain sigmaConclusion piConclusion
      sigmaSourceRoot piSourceRoot atomicRoot domainRoot,
  RawCodedTemplatePrefixAtomicallyAdequate M translation prefix ->
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
    (rawDynamicTruthPredecessorJointStateContext M
      (rawTemplateContextCodeOnTail translation baseContext prefix))
    (rawTemplateFormula translation
      (coqDynamicTruthGlobalExistentialSource 0 localSigma localPi))
    sigmaSourceRoot ->
  RawCodedPALocalProofOf M
    (rawDynamicTruthPredecessorJointStateContext M
      (rawTemplateContextCodeOnTail translation baseContext prefix))
    (rawTemplateFormula translation
      (coqDynamicTruthGlobalExistentialSource 1 localSigma localPi))
    piSourceRoot ->
  RawCodedPALocalProofOf M
    (rawDynamicTruthPredecessorJointStateContext M
      (rawTemplateContextCodeOnTail translation baseContext prefix))
    (rawDynamicTruthLocalAtomicAdequacyCode M) atomicRoot ->
  RawCodedPALocalProofOf M
    (rawDynamicTruthPredecessorJointStateContext M
      (rawTemplateContextCodeOnTail translation baseContext prefix))
    (rawFormulaOrCode M sigmaDomain piDomain) domainRoot ->
  exists targetWitnessList targetContext,
    RawCodedPAAxiomWitnessContext M targetWitnessList targetContext /\
    RawContextListIncluded M baseContext targetContext /\
    RawDynamicTruthPredecessorStateLogicalRootsAt M
      (rawTemplateContextCodeOnTail translation targetContext prefix)
      sigmaDomain piDomain
      (rawTemplateFormula translation sigmaConclusion)
      (rawTemplateFormula translation piConclusion).
Proof.
  intros M hPA translation hagreement witnessList baseContext
    prefix localSigma localPi sigmaDomain piDomain
    sigmaConclusion piConclusion
    sigmaSourceRoot piSourceRoot atomicRoot domainRoot hprefix hwitnessed
    hsigmaAlignment hpiAlignment hsigmaSource hpiSource hatomic hdomain.
  destruct
    (raw_dynamicTruthPredecessorLocalAdmissibility_on_witnessed_extension_under_prefix_of_atomic_and_domain
      M hPA translation hagreement witnessList baseContext prefix
      sigmaDomain piDomain atomicRoot domainRoot hprefix
      hwitnessed hatomic hdomain)
    as (admissibilityWitnesses & admissibleRoot & hadmissibilityWitnessed &
      hadmissible).
  set (admissibilityWitnessList :=
    rawStandardPAAxiomWitnessPrefixWitnessListCode M
      admissibilityWitnesses witnessList).
  set (admissibilityContext :=
    rawStandardPAAxiomWitnessPrefixContextCode M
      admissibilityWitnesses baseContext).
  assert (hadmissibilityIncluded : RawContextListIncluded M
      baseContext admissibilityContext).
  {
    unfold admissibilityContext.
    exact (raw_standardPAAxiomWitnessPrefixContextCode_target_included
      M hPA admissibilityWitnesses baseContext).
  }
  assert (hsigmaSourceTemplate : RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation baseContext
        (coqDynamicTruthPredecessorStateTemplateContext ++ prefix))
      (rawTemplateFormula translation
        (coqDynamicTruthGlobalExistentialSource 0 localSigma localPi))
      sigmaSourceRoot).
  {
    rewrite (raw_dynamicTruthPredecessorStateTemplateContext_app_code
      M translation hagreement baseContext prefix).
    exact hsigmaSource.
  }
  destruct
    (raw_codedPALocalProof_sameTemplatePrefix_witnessedTail_transport
      M hPA translation witnessList baseContext
      admissibilityWitnessList admissibilityContext
      (coqDynamicTruthPredecessorStateTemplateContext ++ prefix)
      (rawTemplateFormula translation
        (coqDynamicTruthGlobalExistentialSource 0 localSigma localPi))
      sigmaSourceRoot hwitnessed hadmissibilityWitnessed
      hadmissibilityIncluded hsigmaSourceTemplate)
    as [transportedSigmaSourceRoot htransportedSigmaSource].
  assert (htransportedSigmaSourceJoint : RawCodedPALocalProofOf M
      (rawDynamicTruthPredecessorJointStateContext M
        (rawTemplateContextCodeOnTail translation
          admissibilityContext prefix))
      (rawTemplateFormula translation
        (coqDynamicTruthGlobalExistentialSource 0 localSigma localPi))
      transportedSigmaSourceRoot).
  {
    rewrite <- (raw_dynamicTruthPredecessorStateTemplateContext_app_code
      M translation hagreement admissibilityContext prefix).
    exact htransportedSigmaSource.
  }
  assert (hpiSourceTemplate : RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation baseContext
        (coqDynamicTruthPredecessorStateTemplateContext ++ prefix))
      (rawTemplateFormula translation
        (coqDynamicTruthGlobalExistentialSource 1 localSigma localPi))
      piSourceRoot).
  {
    rewrite (raw_dynamicTruthPredecessorStateTemplateContext_app_code
      M translation hagreement baseContext prefix).
    exact hpiSource.
  }
  destruct
    (raw_codedPALocalProof_sameTemplatePrefix_witnessedTail_transport
      M hPA translation witnessList baseContext
      admissibilityWitnessList admissibilityContext
      (coqDynamicTruthPredecessorStateTemplateContext ++ prefix)
      (rawTemplateFormula translation
        (coqDynamicTruthGlobalExistentialSource 1 localSigma localPi))
      piSourceRoot hwitnessed hadmissibilityWitnessed
      hadmissibilityIncluded hpiSourceTemplate)
    as [transportedPiSourceRoot htransportedPiSource].
  assert (htransportedPiSourceJoint : RawCodedPALocalProofOf M
      (rawDynamicTruthPredecessorJointStateContext M
        (rawTemplateContextCodeOnTail translation
          admissibilityContext prefix))
      (rawTemplateFormula translation
        (coqDynamicTruthGlobalExistentialSource 1 localSigma localPi))
      transportedPiSourceRoot).
  {
    rewrite <- (raw_dynamicTruthPredecessorStateTemplateContext_app_code
      M translation hagreement admissibilityContext prefix).
    exact htransportedPiSource.
  }
  destruct
    (raw_dynamicTruthPredecessorStateLogicalRootsAt_of_global_row_pair_under_prefix
      M hPA translation hagreement
      admissibilityWitnessList admissibilityContext
      prefix localSigma localPi sigmaDomain piDomain
      sigmaConclusion piConclusion
      transportedSigmaSourceRoot transportedPiSourceRoot
      hadmissibilityWitnessed hsigmaAlignment hpiAlignment
      htransportedSigmaSourceJoint htransportedPiSourceJoint
      (ex_intro _ admissibleRoot hadmissible))
    as (targetWitnessList & targetContext & htargetWitnessed &
      htargetIncluded & hroots).
  exists targetWitnessList, targetContext.
  split; [exact htargetWitnessed |].
  split.
  - intros member hmember.
    exact (htargetIncluded member
      (hadmissibilityIncluded member hmember)).
  - exact hroots.
Qed.

(** State-only compatibility endpoint for the complete atomic/domain
    handoff. *)
Corollary
    raw_dynamicTruthPredecessorStateLogicalRootsAt_of_global_row_pair_atomic_and_domain :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall witnessList baseContext localSigma localPi
      sigmaDomain piDomain sigmaConclusion piConclusion
      sigmaSourceRoot piSourceRoot atomicRoot domainRoot,
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
  RawCodedPALocalProofOf M
    (rawDynamicTruthPredecessorJointStateContext M baseContext)
    (rawDynamicTruthLocalAtomicAdequacyCode M) atomicRoot ->
  RawCodedPALocalProofOf M
    (rawDynamicTruthPredecessorJointStateContext M baseContext)
    (rawFormulaOrCode M sigmaDomain piDomain) domainRoot ->
  exists targetWitnessList targetContext,
    RawCodedPAAxiomWitnessContext M targetWitnessList targetContext /\
    RawContextListIncluded M baseContext targetContext /\
    RawDynamicTruthPredecessorStateLogicalRootsAt M targetContext
      sigmaDomain piDomain
      (rawTemplateFormula translation sigmaConclusion)
      (rawTemplateFormula translation piConclusion).
Proof.
  intros M hPA translation hagreement witnessList baseContext
    localSigma localPi sigmaDomain piDomain sigmaConclusion piConclusion
    sigmaSourceRoot piSourceRoot atomicRoot domainRoot hwitnessed
    hsigmaAlignment hpiAlignment hsigmaSource hpiSource hatomic hdomain.
  pose proof
    (raw_dynamicTruthPredecessorStateLogicalRootsAt_of_global_row_pair_under_prefix_atomic_and_domain
      M hPA translation hagreement witnessList baseContext []
      localSigma localPi sigmaDomain piDomain sigmaConclusion piConclusion
      sigmaSourceRoot piSourceRoot atomicRoot domainRoot
      (fun formula hformula => match hformula with end)
      hwitnessed hsigmaAlignment hpiAlignment hsigmaSource hpiSource
      hatomic hdomain) as hresult.
  cbn [rawTemplateContextCodeOnTail] in hresult.
  exact hresult.
Qed.

End PABoundedRawCodedDynamicTruthPredecessorGlobalRowEvidence.
