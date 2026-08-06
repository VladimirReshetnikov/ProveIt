(**
  Integrate guarded rank-zero append payloads with guarded branch evidence.

  The canonical append compiler is root-term parametric, so its guarded
  specialization produces the two global applications at
  [formula, assignmentCode, assignmentStep] = [#2,#6,#5].  Those applications
  are exactly the canonical rank-zero application formulas under the guarded
  evidence renaming.  This module records that finite syntax calculation and
  then performs the represented proof transport on one witnessed extension.

  The selected direct inputs are kept explicit throughout.  In particular,
  the append payloads, the renamed native evidence roots, and the guarded
  branch records all use the same direct translation.  Payload production is
  deliberately left as a premise; no bottom translation or model-global
  payload producer is selected here.
*)

From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  CodedSyntax
  RawCodedSyntaxConstructors
  RawCodedContextLists
  RawCodedRestrictedPAProof
  RawCodedTemplateSyntax
  RawCodedTemplateProofCompiler
  RawCodedTemplateProofCompilerSelfShiftTail
  RawCodedTemplatePAEmbedding
  RawCodedTemplateDirectStructuralTranslation
  RawCodedTemplateDirectStructuralPAAgreement
  RawCodedPAAxiomWitnessPrefix
  RawCodedPALocalProofExistential
  RawCodedPALocalProofWitnessedContextMerge
  RawCodedPAGrowingTemplateConjunction
  RawCodedFourStateTableAppendPermutedTemplateGlobalTraversalAssembly
  RawCodedDynamicTruthNativeZeroCanonicalTraceExactification
  RawCodedDynamicTruthNativeZeroCanonicalAppendSourceIdentification
  RawCodedDynamicTruthNativeZeroCanonicalApplicationProofTransport
  RawCodedDynamicTruthImpGuardedPredecessorExclusivityCompilation
  RawCodedDynamicTruthZeroLocalExclusiveTemplateIdentification
  RawCodedDynamicTruthNativeZeroGuardedEvidenceIdentification
  RawCodedDynamicTruthNativeZeroGuardedPredecessorCompilation.

Module
  PABoundedRawCodedDynamicTruthNativeZeroGuardedCanonicalAppendIntegration.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedCodedSyntax.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedContextLists.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedTemplateProofCompilerSelfShiftTail.
Import PABoundedRawCodedTemplatePAEmbedding.
Import PABoundedRawCodedTemplateDirectStructuralTranslation.
Import PABoundedRawCodedTemplateDirectStructuralPAAgreement.
Import PABoundedRawCodedPAAxiomWitnessPrefix.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPALocalProofWitnessedContextMerge.
Import PABoundedRawCodedPAGrowingTemplateConjunction.
Import
  PABoundedRawCodedFourStateTableAppendPermutedTemplateGlobalTraversalAssembly.
Import
  PABoundedRawCodedDynamicTruthNativeZeroCanonicalTraceExactification.
Import
  PABoundedRawCodedDynamicTruthNativeZeroCanonicalAppendSourceIdentification.
Import
  PABoundedRawCodedDynamicTruthNativeZeroCanonicalApplicationProofTransport.
Import
  PABoundedRawCodedDynamicTruthImpGuardedPredecessorExclusivityCompilation.
Import
  PABoundedRawCodedDynamicTruthZeroLocalExclusiveTemplateIdentification.
Import
  PABoundedRawCodedDynamicTruthNativeZeroGuardedEvidenceIdentification.
Import
  PABoundedRawCodedDynamicTruthNativeZeroGuardedPredecessorCompilation.

(** The two guarded root-term sources are literally the corresponding
    canonical applications under the evidence-coordinate renaming.  These
    computations cross all ten global existential binders, so keeping them
    explicit audits the complete capture-safe substitution. *)
Lemma coqFourStateTableAppendAtGuardedRootTerms_zero_sigma :
  coqFourStateTableAppendTemplateGlobalSourceAtRootTerms 0
      (embedPAFormula dynamicTruthZeroCanonicalSigmaRowFormula)
      (embedPAFormula dynamicTruthZeroCanonicalPiRowFormula)
      (ttVar 2) (ttVar 6) (ttVar 5) =
  embedPAFormula
    (Formula.rename dynamicTruthZeroGuardedEvidenceRenaming
      dynamicTruthZeroInputGlobalSigmaApplicationFormula).
Proof. vm_compute. reflexivity. Qed.

Lemma coqFourStateTableAppendAtGuardedRootTerms_zero_pi :
  coqFourStateTableAppendTemplateGlobalSourceAtRootTerms 1
      (embedPAFormula dynamicTruthZeroCanonicalSigmaRowFormula)
      (embedPAFormula dynamicTruthZeroCanonicalPiRowFormula)
      (ttVar 2) (ttVar 6) (ttVar 5) =
  embedPAFormula
    (Formula.rename dynamicTruthZeroGuardedEvidenceRenaming
      dynamicTruthZeroInputGlobalPiApplicationFormula).
Proof. vm_compute. reflexivity. Qed.

(** Carrier-facing forms for every PA-agreeing translation. *)
Theorem rawTemplateFormula_zeroCanonicalGuardedGlobalSource_sigma : forall
    (M : RawPAModel) (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  rawTemplateFormula translation
      (coqFourStateTableAppendTemplateGlobalSourceAtRootTerms 0
        (embedPAFormula dynamicTruthZeroCanonicalSigmaRowFormula)
        (embedPAFormula dynamicTruthZeroCanonicalPiRowFormula)
        (ttVar 2) (ttVar 6) (ttVar 5)) =
  rawQuotedFormulaCode M
    (Formula.rename dynamicTruthZeroGuardedEvidenceRenaming
      dynamicTruthZeroInputGlobalSigmaApplicationFormula).
Proof.
  intros M translation hagreement.
  rewrite coqFourStateTableAppendAtGuardedRootTerms_zero_sigma.
  exact (rawTemplateFormula_embedPA hagreement
    (Formula.rename dynamicTruthZeroGuardedEvidenceRenaming
      dynamicTruthZeroInputGlobalSigmaApplicationFormula)).
Qed.

Theorem rawTemplateFormula_zeroCanonicalGuardedGlobalSource_pi : forall
    (M : RawPAModel) (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  rawTemplateFormula translation
      (coqFourStateTableAppendTemplateGlobalSourceAtRootTerms 1
        (embedPAFormula dynamicTruthZeroCanonicalSigmaRowFormula)
        (embedPAFormula dynamicTruthZeroCanonicalPiRowFormula)
        (ttVar 2) (ttVar 6) (ttVar 5)) =
  rawQuotedFormulaCode M
    (Formula.rename dynamicTruthZeroGuardedEvidenceRenaming
      dynamicTruthZeroInputGlobalPiApplicationFormula).
Proof.
  intros M translation hagreement.
  rewrite coqFourStateTableAppendAtGuardedRootTerms_zero_pi.
  exact (rawTemplateFormula_embedPA hagreement
    (Formula.rename dynamicTruthZeroGuardedEvidenceRenaming
      dynamicTruthZeroInputGlobalPiApplicationFormula)).
Qed.

(** Compile both synchronized guarded payloads, merge the independently
    growing conclusions, and rebase the resulting pair onto an arbitrary
    witnessed caller tail.  Nothing in this construction inspects the
    surrounding assumptions, so the strongest reusable statement keeps the
    entire prefix abstract. *)
Theorem
    raw_dynamicTruthZeroCanonicalGuardedGlobalApplicationRoots_on_witnessed_extension_of_kernel_payload_pair_under_prefix :
    forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
      (inputs : RawCodedTemplateDirectStructuralInputs M)
      sourceWitnessList sourceContext prefix,
  RawCodedPAAxiomWitnessContext M sourceWitnessList sourceContext ->
  RawDynamicTruthZeroCanonicalGuardedAppendRowKernelPayloadPairUnderPrefix
    M (rawDirectStructuralTemplateTranslation M hPA inputs) prefix ->
  exists targetWitnessList targetContext sigmaApplicationRoot
      piApplicationRoot,
    RawCodedPAAxiomWitnessContext M targetWitnessList targetContext /\
    RawContextListIncluded M sourceContext targetContext /\
    RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        targetContext prefix)
      (rawQuotedFormulaCode M
        (Formula.rename dynamicTruthZeroGuardedEvidenceRenaming
          dynamicTruthZeroInputGlobalSigmaApplicationFormula))
      sigmaApplicationRoot /\
    RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        targetContext prefix)
      (rawQuotedFormulaCode M
        (Formula.rename dynamicTruthZeroGuardedEvidenceRenaming
          dynamicTruthZeroInputGlobalPiApplicationFormula))
      piApplicationRoot.
Proof.
  intros M hPA inputs sourceWitnessList sourceContext prefix
    hsource (appendWitnesses & hsigmaPayload & hpiPayload).
  set (translation := rawDirectStructuralTemplateTranslation M hPA inputs).
  pose proof
    (raw_codedPAGrowingTemplateLocalProofAt_dynamic_truth_zero_canonical_guarded_global_of_kernel_payload_under_prefix
      M hPA translation (rawDirectStructuralTemplatePAAgreement M hPA inputs)
      0 prefix appendWitnesses (or_introl eq_refl)
      (raw_guardedDirectStructuralTemplatePrefix_atomically_adequate
        M hPA inputs prefix) hsigmaPayload) as hsigmaGrowing.
  pose proof
    (raw_codedPAGrowingTemplateLocalProofAt_dynamic_truth_zero_canonical_guarded_global_of_kernel_payload_under_prefix
      M hPA translation (rawDirectStructuralTemplatePAAgreement M hPA inputs)
      1 prefix appendWitnesses (or_intror eq_refl)
      (raw_guardedDirectStructuralTemplatePrefix_atomically_adequate
        M hPA inputs prefix) hpiPayload) as hpiGrowing.
  pose proof
    (raw_codedPAGrowingTemplateLocalProofAt_pair_at_prefix
      M hPA translation
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        appendWitnesses (raw_zero M))
      (rawStandardPAAxiomWitnessPrefixContextCode M
        appendWitnesses (raw_zero M)) prefix
      (rawTemplateFormula translation
        (coqFourStateTableAppendTemplateGlobalSourceAtRootTerms 0
          (embedPAFormula dynamicTruthZeroCanonicalSigmaRowFormula)
          (embedPAFormula dynamicTruthZeroCanonicalPiRowFormula)
          (ttVar 2) (ttVar 6) (ttVar 5)))
      (rawTemplateFormula translation
        (coqFourStateTableAppendTemplateGlobalSourceAtRootTerms 1
          (embedPAFormula dynamicTruthZeroCanonicalSigmaRowFormula)
          (embedPAFormula dynamicTruthZeroCanonicalPiRowFormula)
          (ttVar 2) (ttVar 6) (ttVar 5)))
      hsigmaGrowing hpiGrowing) as happlications.
  pose proof
    (raw_codedPAGrowingTemplateLocalProofPairAt_rebase
      M hPA translation
      (rawStandardPAAxiomWitnessPrefixContextCode M
        appendWitnesses (raw_zero M)) prefix
      (rawTemplateFormula translation
        (coqFourStateTableAppendTemplateGlobalSourceAtRootTerms 0
          (embedPAFormula dynamicTruthZeroCanonicalSigmaRowFormula)
          (embedPAFormula dynamicTruthZeroCanonicalPiRowFormula)
          (ttVar 2) (ttVar 6) (ttVar 5)))
      (rawTemplateFormula translation
        (coqFourStateTableAppendTemplateGlobalSourceAtRootTerms 1
          (embedPAFormula dynamicTruthZeroCanonicalSigmaRowFormula)
          (embedPAFormula dynamicTruthZeroCanonicalPiRowFormula)
          (ttVar 2) (ttVar 6) (ttVar 5)))
      sourceWitnessList sourceContext hsource happlications) as hrebased.
  destruct hrebased as
    (targetWitnessList & targetContext & sigmaApplicationRoot &
      piApplicationRoot & htargetWitnessed & hincluded &
      hsigmaApplication & hpiApplication).
  unfold translation in hsigmaApplication, hpiApplication.
  rewrite (rawTemplateFormula_zeroCanonicalGuardedGlobalSource_sigma
    M (rawDirectStructuralTemplateTranslation M hPA inputs)
    (rawDirectStructuralTemplatePAAgreement M hPA inputs))
    in hsigmaApplication.
  rewrite (rawTemplateFormula_zeroCanonicalGuardedGlobalSource_pi
    M (rawDirectStructuralTemplateTranslation M hPA inputs)
    (rawDirectStructuralTemplatePAAgreement M hPA inputs))
    in hpiApplication.
  exists targetWitnessList, targetContext,
    sigmaApplicationRoot, piApplicationRoot.
  split; [exact htargetWitnessed |].
  split; [exact hincluded |].
  split; assumption.
Qed.

(** Implication-specific compatibility wrapper.  The abstract-prefix theorem
    above is also used by the Boolean guarded branches. *)
Theorem
    raw_dynamicTruthZeroCanonicalGuardedGlobalApplicationRoots_on_witnessed_extension_of_kernel_payload_pair :
    forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
      (inputs : RawCodedTemplateDirectStructuralInputs M)
      sourceWitnessList sourceContext callerPrefix,
  RawCodedPAAxiomWitnessContext M sourceWitnessList sourceContext ->
  RawDynamicTruthZeroCanonicalGuardedAppendRowKernelPayloadPairUnderPrefix
    M (rawDirectStructuralTemplateTranslation M hPA inputs)
      (coqDynamicTruthImpGuardedDeepPrefix callerPrefix) ->
  exists targetWitnessList targetContext sigmaApplicationRoot
      piApplicationRoot,
    RawCodedPAAxiomWitnessContext M targetWitnessList targetContext /\
    RawContextListIncluded M sourceContext targetContext /\
    RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        targetContext (coqDynamicTruthImpGuardedDeepPrefix callerPrefix))
      (rawQuotedFormulaCode M
        (Formula.rename dynamicTruthZeroGuardedEvidenceRenaming
          dynamicTruthZeroInputGlobalSigmaApplicationFormula))
      sigmaApplicationRoot /\
    RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        targetContext (coqDynamicTruthImpGuardedDeepPrefix callerPrefix))
      (rawQuotedFormulaCode M
        (Formula.rename dynamicTruthZeroGuardedEvidenceRenaming
          dynamicTruthZeroInputGlobalPiApplicationFormula))
      piApplicationRoot.
Proof.
  intros M hPA inputs sourceWitnessList sourceContext callerPrefix
    hsource hpayloads.
  exact
    (raw_dynamicTruthZeroCanonicalGuardedGlobalApplicationRoots_on_witnessed_extension_of_kernel_payload_pair_under_prefix
      M hPA inputs sourceWitnessList sourceContext
      (coqDynamicTruthImpGuardedDeepPrefix callerPrefix)
      hsource hpayloads).
Qed.

(** The two native evidence roots under a caller-selected prefix.  Separating
    this prefix-generic record from the implication branch record lets the
    same append compiler feed conjunction and disjunction. *)
Record RawDynamicTruthGuardedEvidenceRootsUnderPrefixAt
    (M : RawPAModel) (translation : RawCodedTemplateTranslation M)
    (baseContext : M) (prefix : TemplateContext) : Prop := {
  rawDynamicTruthGuardedEvidenceUnderPrefix_sigma : exists sigmaRoot,
    RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation baseContext prefix)
      (rawTemplateFormula translation
        coqDynamicTruthImpGuardedLocalSigmaEvidenceTemplate) sigmaRoot;
  rawDynamicTruthGuardedEvidenceUnderPrefix_pi : exists piRoot,
    RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation baseContext prefix)
      (rawTemplateFormula translation
        coqDynamicTruthImpGuardedLocalPiEvidenceTemplate) piRoot
}.

Arguments RawDynamicTruthGuardedEvidenceRootsUnderPrefixAt
  M translation baseContext prefix : clear implicits.

(** Transport common guarded applications to the two renamed native evidence
    formulas and identify those formulas with the guarded templates of the
    same selected direct inputs.  The prefix remains completely abstract. *)
Theorem
    raw_dynamicTruthGuardedEvidenceRootsUnderPrefix_on_witnessed_extension_of_canonical_append_kernel_payload_pair :
    forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
      (inputs : RawCodedTemplateDirectStructuralInputs M)
      sourceWitnessList sourceContext prefix,
  RawDynamicTruthZeroGuardedEvidenceIdentification M inputs ->
  RawCodedPAAxiomWitnessContext M sourceWitnessList sourceContext ->
  RawDynamicTruthZeroCanonicalGuardedAppendRowKernelPayloadPairUnderPrefix
    M (rawDirectStructuralTemplateTranslation M hPA inputs) prefix ->
  exists targetWitnessList targetContext,
    RawCodedPAAxiomWitnessContext M targetWitnessList targetContext /\
    RawContextListIncluded M sourceContext targetContext /\
    RawDynamicTruthGuardedEvidenceRootsUnderPrefixAt M
      (rawDirectStructuralTemplateTranslation M hPA inputs)
      targetContext prefix.
Proof.
  intros M hPA inputs sourceWitnessList sourceContext prefix
    hidentification hsource hpayloads.
  set (translation := rawDirectStructuralTemplateTranslation M hPA inputs).
  destruct
    (raw_dynamicTruthZeroCanonicalGuardedGlobalApplicationRoots_on_witnessed_extension_of_kernel_payload_pair_under_prefix
      M hPA inputs sourceWitnessList sourceContext prefix
      hsource hpayloads) as
    (applicationWitnessList & applicationContext & sigmaApplicationRoot &
      piApplicationRoot & happlicationWitnessed & hsourceApplicationIncluded &
      hsigmaApplication & hpiApplication).
  destruct
    (raw_dynamicTruthZeroNativeEvidenceRoots_of_renamed_canonicalApplicationRoots_under_prefix
      M hPA translation (rawDirectStructuralTemplatePAAgreement M hPA inputs)
      dynamicTruthZeroGuardedEvidenceRenaming
      applicationWitnessList applicationContext prefix
      sigmaApplicationRoot piApplicationRoot
      (raw_guardedDirectStructuralTemplatePrefix_atomically_adequate
        M hPA inputs prefix)
      happlicationWitnessed hsigmaApplication hpiApplication) as
    (evidenceWitnessList & evidenceContext & sigmaEvidenceRoot &
      piEvidenceRoot & hevidenceWitnessed &
      happlicationEvidenceIncluded & hsigmaEvidence & hpiEvidence).
  assert (hsourceEvidenceIncluded :
      RawContextListIncluded M sourceContext evidenceContext).
  {
    intros member hmember.
    exact (happlicationEvidenceIncluded member
      (hsourceApplicationIncluded member hmember)).
  }
  assert (hsigmaIdentification :
      rawTemplateFormula translation
          coqDynamicTruthImpGuardedLocalSigmaEvidenceTemplate =
      rawQuotedFormulaCode M
        (Formula.rename dynamicTruthZeroGuardedEvidenceRenaming
          dynamicTruthZeroSigmaEvidenceFormula)).
  {
    unfold translation, rawDirectStructuralTemplateTranslation.
    exact (rawDynamicTruthZeroGuardedEvidence_sigma
      M inputs hidentification).
  }
  assert (hpiIdentification :
      rawTemplateFormula translation
          coqDynamicTruthImpGuardedLocalPiEvidenceTemplate =
      rawQuotedFormulaCode M
        (Formula.rename dynamicTruthZeroGuardedEvidenceRenaming
          dynamicTruthZeroPiEvidenceFormula)).
  {
    unfold translation, rawDirectStructuralTemplateTranslation.
    exact (rawDynamicTruthZeroGuardedEvidence_pi
      M inputs hidentification).
  }
  exists evidenceWitnessList, evidenceContext.
  split; [exact hevidenceWitnessed |].
  split; [exact hsourceEvidenceIncluded |].
  constructor.
  - exists sigmaEvidenceRoot.
    rewrite hsigmaIdentification.
    exact hsigmaEvidence.
  - exists piEvidenceRoot.
    rewrite hpiIdentification.
    exact hpiEvidence.
Qed.

(** Implication-specific compatibility wrapper around the abstract-prefix
    evidence compiler. *)
Theorem
    raw_dynamicTruthImpGuardedEvidenceRoots_on_witnessed_extension_of_canonical_append_kernel_payload_pair :
    forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
      (inputs : RawCodedTemplateDirectStructuralInputs M)
      sourceWitnessList sourceContext callerPrefix,
  RawDynamicTruthZeroGuardedEvidenceIdentification M inputs ->
  RawCodedPAAxiomWitnessContext M sourceWitnessList sourceContext ->
  RawDynamicTruthZeroCanonicalGuardedAppendRowKernelPayloadPairUnderPrefix
    M (rawDirectStructuralTemplateTranslation M hPA inputs)
      (coqDynamicTruthImpGuardedDeepPrefix callerPrefix) ->
  exists targetWitnessList targetContext,
    RawCodedPAAxiomWitnessContext M targetWitnessList targetContext /\
    RawContextListIncluded M sourceContext targetContext /\
    RawDynamicTruthImpGuardedEvidenceRootsAt M
      (rawDirectStructuralTemplateTranslation M hPA inputs)
      targetContext callerPrefix.
Proof.
  intros M hPA inputs sourceWitnessList sourceContext callerPrefix
    hidentification hsource hpayloads.
  destruct
    (raw_dynamicTruthGuardedEvidenceRootsUnderPrefix_on_witnessed_extension_of_canonical_append_kernel_payload_pair
      M hPA inputs sourceWitnessList sourceContext
      (coqDynamicTruthImpGuardedDeepPrefix callerPrefix)
      hidentification hsource hpayloads) as
    (targetWitnessList & targetContext & htargetWitnessed & hincluded &
      hevidence).
  destruct hevidence as
    [(sigmaEvidenceRoot & hsigmaEvidence)
      (piEvidenceRoot & hpiEvidence)].
  exists targetWitnessList, targetContext.
  split; [exact htargetWitnessed |].
  split; [exact hincluded |].
  constructor.
  - exists sigmaEvidenceRoot. exact hsigmaEvidence.
  - exists piEvidenceRoot. exact hpiEvidence.
Qed.

(** Attach the guarded evidence pair to an already synchronized parent
    package.  The existing branch adapter transports the three parent roots
    across the evidence-producing witnessed extension, so all five roots end
    in one exact guarded deep context. *)
Theorem
    raw_dynamicTruthImpGuardedBranchRoots_on_witnessed_extension_of_parent_and_canonical_append_kernel_payload_pair :
    forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
      (inputs : RawCodedTemplateDirectStructuralInputs M)
      sourceWitnessList sourceContext callerPrefix,
  RawDynamicTruthZeroGuardedEvidenceIdentification M inputs ->
  RawCodedPAAxiomWitnessContext M sourceWitnessList sourceContext ->
  RawDynamicTruthImpGuardedParentBranchRootsAt M
    (rawDirectStructuralTemplateTranslation M hPA inputs)
    sourceContext callerPrefix ->
  RawDynamicTruthZeroCanonicalGuardedAppendRowKernelPayloadPairUnderPrefix
    M (rawDirectStructuralTemplateTranslation M hPA inputs)
      (coqDynamicTruthImpGuardedDeepPrefix callerPrefix) ->
  exists targetWitnessList targetContext,
    RawCodedPAAxiomWitnessContext M targetWitnessList targetContext /\
    RawContextListIncluded M sourceContext targetContext /\
    RawDynamicTruthImpGuardedBranchRootsAt M
      (rawDirectStructuralTemplateTranslation M hPA inputs)
      targetContext callerPrefix.
Proof.
  intros M hPA inputs sourceWitnessList sourceContext callerPrefix
    hidentification hsource hparent hpayloads.
  destruct
    (raw_dynamicTruthImpGuardedEvidenceRoots_on_witnessed_extension_of_canonical_append_kernel_payload_pair
      M hPA inputs sourceWitnessList sourceContext callerPrefix
      hidentification hsource hpayloads) as
    (targetWitnessList & targetContext & htargetWitnessed &
      hincluded & hevidence).
  exists targetWitnessList, targetContext.
  split; [exact htargetWitnessed |].
  split; [exact hincluded |].
  exact
    (raw_dynamicTruthImpGuardedBranchRoots_of_parent_and_evidence_on_witnessed_extension
      M hPA (rawDirectStructuralTemplateTranslation M hPA inputs)
      sourceWitnessList sourceContext targetWitnessList targetContext
      callerPrefix hsource htargetWitnessed hincluded hparent hevidence).
Qed.

End
  PABoundedRawCodedDynamicTruthNativeZeroGuardedCanonicalAppendIntegration.
