(**
  Guarded predecessor compilation at the normalized rank-zero boundary.

  The guarded implication theorem needs five roots in its real branch after
  the predecessor and constructor binders have been introduced.  This file
  packages those exact roots, closes the guarded predecessor formula, and
  exposes the remaining traversal producer as one sharply typed interface.
  Fixed helper compilation and zero-field normalization are no longer part
  of that residual.
*)

From Stdlib Require Import List.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedContextLists
  RawCodedRestrictedPAProof
  RawCodedRestrictedPAConsistencyFormulaCode
  RawCodedRestrictedPAConsistencyFromUniversalSoundness
  RawCodedRestrictedTargetTemplateContext
  RawCodedPALocalProofExistential
  RawCodedPALocalProofExistentialEliminationChain
  RawCodedPALocalProofUniversalIntroductionChain
  RawCodedPALocalProofWitnessedContextMerge
  RawCodedTemplateSyntax
  RawCodedTemplateProofCompiler
  RawCodedTemplateProofCompilerSelfShiftTail
  RawCodedTemplateLocalProofWitnessedTailTransport
  RawCodedTemplatePAEmbedding
  RawCodedTemplateDirectStructuralTranslation
  RawCodedTemplateDirectStructuralPAAgreement
  RawCodedTemplateFormulaAtomicAdequacy
  RawCodedTemplateBottomDirectStructuralInputs
  RawCodedDynamicTruthNativeLocalPositiveGraph
  RawCodedDynamicTruthLocalFieldProjectionCompilation
  RawCodedDynamicTruthLocalExclusiveTemplateDirectInputs
  RawCodedDynamicTruthImpDirectChildAdmissibilityProofCompilation
  RawCodedDynamicTruthImpGuardedBranchExclusivity
  RawCodedDynamicTruthPredecessorGlobalExistentialElimination
  RawCodedDynamicTruthPredecessorGlobalRowEvidence
  RawCodedDynamicTruthLocalCollisionMatrixAssembly
  RawCodedDynamicTruthImpGuardedPredecessorExclusivityCompilation
  RawCodedDynamicTruthNativeZeroPredecessorLogicalRootsCompilation
  RawCodedDynamicTruthNativeZeroGuardedNormalization
  RawCodedDynamicTruthZeroLocalExclusiveTemplateIdentification
  RawCodedStrongStepProofEndpointAtomicAdequacyProofCompilation
  RawCodedProofEndpointQuantifierBoundedProofCompilation
  RawCodedStrongStepProofEndpointQuantifierBoundedProofCompilation
  RawCodedStrongStepProofEndpointEvidenceCompilation.

Import ListNotations.

Module
  PABoundedRawCodedDynamicTruthNativeZeroGuardedPredecessorCompilation.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedContextLists.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedRestrictedPAConsistencyFormulaCode.
Import PABoundedRawCodedRestrictedPAConsistencyFromUniversalSoundness.
Import PABoundedRawCodedRestrictedTargetTemplateContext.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPALocalProofExistentialEliminationChain.
Import PABoundedRawCodedPALocalProofUniversalIntroductionChain.
Import PABoundedRawCodedPALocalProofWitnessedContextMerge.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedTemplateProofCompilerSelfShiftTail.
Import PABoundedRawCodedTemplateLocalProofWitnessedTailTransport.
Import PABoundedRawCodedTemplatePAEmbedding.
Import PABoundedRawCodedTemplateDirectStructuralTranslation.
Import PABoundedRawCodedTemplateDirectStructuralPAAgreement.
Import PABoundedRawCodedTemplateFormulaAtomicAdequacy.
Import PABoundedRawCodedTemplateBottomDirectStructuralInputs.
Import PABoundedRawCodedDynamicTruthNativeLocalPositiveGraph.
Import PABoundedRawCodedDynamicTruthLocalFieldProjectionCompilation.
Import PABoundedRawCodedDynamicTruthLocalExclusiveTemplateDirectInputs.
Import
  PABoundedRawCodedDynamicTruthImpDirectChildAdmissibilityProofCompilation.
Import PABoundedRawCodedDynamicTruthImpGuardedBranchExclusivity.
Import
  PABoundedRawCodedDynamicTruthPredecessorGlobalExistentialElimination.
Import PABoundedRawCodedDynamicTruthPredecessorGlobalRowEvidence.
Import PABoundedRawCodedDynamicTruthLocalCollisionMatrixAssembly.
Import
  PABoundedRawCodedDynamicTruthImpGuardedPredecessorExclusivityCompilation.
Import
  PABoundedRawCodedDynamicTruthNativeZeroPredecessorLogicalRootsCompilation.
Import PABoundedRawCodedDynamicTruthNativeZeroGuardedNormalization.
Import
  PABoundedRawCodedDynamicTruthZeroLocalExclusiveTemplateIdentification.
Import PABoundedRawCodedStrongStepProofEndpointAtomicAdequacyProofCompilation.
Import PABoundedRawCodedProofEndpointQuantifierBoundedProofCompilation.
Import
  PABoundedRawCodedStrongStepProofEndpointQuantifierBoundedProofCompilation.
Import PABoundedRawCodedStrongStepProofEndpointEvidenceCompilation.

(** Local direct-translation adequacy avoids importing the substantially
    stronger global-row compiler merely for this elementary consequence of
    the translation contract. *)
Lemma raw_guardedDirectStructuralTemplatePrefix_atomically_adequate : forall
    (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (inputs : RawCodedTemplateDirectStructuralInputs M) prefix,
  RawCodedTemplatePrefixAtomicallyAdequate M
    (rawDirectStructuralTemplateTranslation M hPA inputs) prefix.
Proof.
  intros M hPA inputs prefix formula _.
  exact (raw_codedTemplateFormula_atomically_adequate_core M hPA
    (rawDirectStructuralTemplateTranslation M hPA inputs) formula).
Qed.

(** Five introduced variables move the endpoint formula coordinate [#2] to
    the guarded parent coordinate [#7]. *)
Lemma coqDynamicTruthImpGuardedParentAtomicTemplate_eq_endpoint_shift5 :
  coqDynamicTruthImpDirectChildAtomicPremiseTemplate
    coqDynamicTruthImpGuardedLevelTerm
    coqDynamicTruthImpGuardedParentTerm
    coqDynamicTruthImpGuardedLeftTerm
    coqDynamicTruthImpGuardedRightTerm
    coqDynamicTruthImpGuardedChildTerm =
  templateFormulaRename (templateShiftRenamingMany 5)
    coqStrongStepProofEndpointAtomicAdequacyConclusion.
Proof. vm_compute. reflexivity. Qed.

(** Unlike atomic adequacy, the domain endpoint is not literally the same
    template after five shifts: the generic endpoint names the lower-level
    parameter, whereas the guarded predecessor domain names the upper-level
    parameter.  Direct inputs for the local collision law identify those two
    translated numeral terms.  Stating the bridge on translated formula
    codes therefore captures the actual reusable hypothesis without claiming
    a false syntactic identity. *)
Lemma coqDynamicTruthImpGuardedParentDomainTemplate_view :
  coqDynamicTruthImpDirectChildDomainPremiseTemplate
    coqDynamicTruthImpGuardedLevelTerm
    coqDynamicTruthImpGuardedParentTerm
    coqDynamicTruthImpGuardedLeftTerm
    coqDynamicTruthImpGuardedRightTerm
    coqDynamicTruthImpGuardedChildTerm =
  restrictedTargetTemplateFormulaContext
    coqRestrictedPASoundnessUpperLevelTerm
    (restrictedTargetFormulaQuantifierBoundedContext (tVar 7)).
Proof. vm_compute. reflexivity. Qed.

Lemma coqStrongStepProofEndpointQuantifierBoundedConclusion_shift5_view :
  templateFormulaRename (templateShiftRenamingMany 5)
    coqStrongStepProofEndpointQuantifierBoundedConclusion =
  restrictedTargetTemplateFormulaContext
    coqRestrictedPASoundnessLowerLevelTerm
    (restrictedTargetFormulaQuantifierBoundedContext (tVar 7)).
Proof.
  rewrite coqStrongStepProofEndpointQuantifierBoundedConclusion_view.
  vm_compute. reflexivity.
Qed.

Lemma raw_coqDynamicTruthImpGuardedParentDomain_eq_endpoint_shift5 :
    forall (M : RawPAModel)
      (inputs : RawCodedTemplateDirectStructuralInputs M)
      sigmaDomain piDomain sigmaEvidence piEvidence,
  RawCoqDynamicTruthLocalExclusiveTemplateIdentification M inputs
    sigmaDomain piDomain sigmaEvidence piEvidence ->
  rawDirectTemplateFormula inputs
      (coqDynamicTruthImpDirectChildDomainPremiseTemplate
        coqDynamicTruthImpGuardedLevelTerm
        coqDynamicTruthImpGuardedParentTerm
        coqDynamicTruthImpGuardedLeftTerm
        coqDynamicTruthImpGuardedRightTerm
        coqDynamicTruthImpGuardedChildTerm) =
  rawDirectTemplateFormula inputs
      (templateFormulaRename (templateShiftRenamingMany 5)
        coqStrongStepProofEndpointQuantifierBoundedConclusion).
Proof.
  intros M inputs sigmaDomain piDomain sigmaEvidence piEvidence
    hidentification.
  pose proof
    (rawCoqDynamicTruthLocalExclusive_levelAlignment
      M inputs sigmaDomain piDomain sigmaEvidence piEvidence
      hidentification) as hlevel.
  rewrite coqDynamicTruthImpGuardedParentDomainTemplate_view.
  rewrite coqStrongStepProofEndpointQuantifierBoundedConclusion_shift5_view.
  unfold rawDirectTemplateFormula.
  rewrite !rawStructuralWith_restrictedTargetTemplateFormulaContext.
  change
    (rawDirectTemplateTerm inputs
       coqRestrictedPASoundnessLowerLevelTerm =
     rawDirectTemplateTerm inputs
       coqRestrictedPASoundnessUpperLevelTerm) in hlevel.
  fold (rawDirectTemplateTerm inputs).
  now rewrite hlevel.
Qed.

(** Normalize the real guarded branch context into the fixed branch-local
    prefix followed by the caller assumptions shifted through all five
    binders.  Keeping this equality explicit prevents later proof transport
    from depending on reductions of nested context maps. *)
Definition coqDynamicTruthImpGuardedFixedDeepPrefix : TemplateContext :=
  [coqDynamicTruthImpGuardedDirectChildTemplate;
   coqDynamicTruthImpGuardedShapeTemplate] ++
  templateContextShiftMany 2
    coqDynamicTruthPredecessorStateTemplateContext.

Lemma coqDynamicTruthImpGuardedDeepPrefix_split : forall callerPrefix,
  coqDynamicTruthImpGuardedDeepPrefix callerPrefix =
  coqDynamicTruthImpGuardedFixedDeepPrefix ++
  templateContextShiftMany 5 callerPrefix.
Proof.
  intro callerPrefix.
  unfold coqDynamicTruthImpGuardedDeepPrefix,
    coqDynamicTruthImpGuardedFixedDeepPrefix.
  cbn [templateContextShiftMany templateContextShift
    templateContextRename].
  reflexivity.
Qed.

(** Folding an outer translated prefix over an already folded inner prefix
    is just folding their concatenation over the original raw tail.  This
    small structural lemma is independent of guarded truth and is stated
    here to factor both endpoint-root transports below. *)
Lemma rawTemplateContextCodeOnTail_app_finite : forall
    (M : RawPAModel) (translation : RawCodedTemplateTranslation M)
    baseContext outer inner,
  rawTemplateContextCodeOnTail translation baseContext (outer ++ inner) =
  rawTemplateContextCodeOnTail translation
    (rawTemplateContextCodeOnTail translation baseContext inner) outer.
Proof.
  intros M translation baseContext outer.
  induction outer as [|formula tail ih]; intro inner.
  - reflexivity.
  - simpl (rawTemplateContextCodeOnTail translation baseContext
      ((formula :: tail) ++ inner)).
    simpl (rawTemplateContextCodeOnTail translation
      (rawTemplateContextCodeOnTail translation baseContext inner)
      (formula :: tail)).
    f_equal. apply ih.
Qed.

(** Compile the two parent invariants directly from the caller's restricted
    proof and endpoint-rule assumptions, then retain the literal guard and
    predecessor-state prefix.  The theorem is prefix-general and grows the
    witnessed PA tail only through the two reusable endpoint compilers. *)
Theorem raw_dynamicTruthImpGuardedParentEndpointRoots_of_template_assumptions :
    forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
      (inputs : RawCodedTemplateDirectStructuralInputs M)
      sigmaDomain piDomain sigmaEvidence piEvidence
      baseWitnessList baseContext callerPrefix,
  RawCoqDynamicTruthLocalExclusiveTemplateIdentification M inputs
    sigmaDomain piDomain sigmaEvidence piEvidence ->
  RawCodedPAAxiomWitnessContext M baseWitnessList baseContext ->
  In coqRestrictedPADerivationSoundnessRestrictedProofTemplate
    callerPrefix ->
  In coqStrongStepProofEndpointAtomicAdequacyRulePremise callerPrefix ->
  exists targetWitnessList targetContext atomicRoot domainRoot,
    RawCodedPAAxiomWitnessContext M targetWitnessList targetContext /\
    RawContextListIncluded M baseContext targetContext /\
    RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        targetContext
        (coqDynamicTruthImpGuardedDeepPrefix callerPrefix))
      (rawDirectTemplateFormula inputs
        (coqDynamicTruthImpDirectChildAtomicPremiseTemplate
          coqDynamicTruthImpGuardedLevelTerm
          coqDynamicTruthImpGuardedParentTerm
          coqDynamicTruthImpGuardedLeftTerm
          coqDynamicTruthImpGuardedRightTerm
          coqDynamicTruthImpGuardedChildTerm)) atomicRoot /\
    RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        targetContext
        (coqDynamicTruthImpGuardedDeepPrefix callerPrefix))
      (rawDirectTemplateFormula inputs
        (coqDynamicTruthImpDirectChildDomainPremiseTemplate
          coqDynamicTruthImpGuardedLevelTerm
          coqDynamicTruthImpGuardedParentTerm
          coqDynamicTruthImpGuardedLeftTerm
          coqDynamicTruthImpGuardedRightTerm
          coqDynamicTruthImpGuardedChildTerm)) domainRoot.
Proof.
  intros M hPA inputs sigmaDomain piDomain sigmaEvidence piEvidence
    baseWitnessList baseContext callerPrefix hidentification hbase
    hrestrictedIn hruleIn.
  set (translation :=
    rawDirectStructuralTemplateTranslation M hPA inputs).
  set (shiftedCaller := templateContextShiftMany 5 callerPrefix).
  destruct
    (raw_codedPALocalProof_strongStepEndpointEvidence_of_template_assumptions_after_binders_on_witnessed_tail
      M hPA inputs 5 baseWitnessList baseContext callerPrefix
      (raw_guardedDirectStructuralTemplatePrefix_atomically_adequate
        M hPA inputs shiftedCaller)
      hbase hrestrictedIn hruleIn)
    as (targetWitnessList & targetContext & atomicRoot & domainRoot &
      htarget & hincluded & hatomic & hdomain).
  assert (htargetRealizable : RawContextListRealizable M targetContext).
  {
    exact (raw_codedPAAxiomWitnessContext_context_realizable
      M targetWitnessList targetContext htarget).
  }
  assert (hshiftedRealizable : RawContextListRealizable M
      (rawTemplateContextCodeOnTail translation targetContext
        shiftedCaller)).
  {
    exact (raw_templateContextOnTail_realizable M hPA translation
      targetContext shiftedCaller htargetRealizable).
  }
  destruct (raw_codedPALocalProof_templatePrefix M hPA translation
    (rawTemplateContextCodeOnTail translation targetContext shiftedCaller)
    coqDynamicTruthImpGuardedFixedDeepPrefix
    (rawDirectTemplateFormula inputs
      (templateFormulaRename (templateShiftRenamingMany 5)
        coqStrongStepProofEndpointAtomicAdequacyConclusion))
    atomicRoot hshiftedRealizable
    (raw_guardedDirectStructuralTemplatePrefix_atomically_adequate
      M hPA inputs coqDynamicTruthImpGuardedFixedDeepPrefix)
    hatomic) as [atomicDeepRoot hatomicDeep].
  destruct (raw_codedPALocalProof_templatePrefix M hPA translation
    (rawTemplateContextCodeOnTail translation targetContext shiftedCaller)
    coqDynamicTruthImpGuardedFixedDeepPrefix
    (rawDirectTemplateFormula inputs
      (templateFormulaRename (templateShiftRenamingMany 5)
        coqStrongStepProofEndpointQuantifierBoundedConclusion))
    domainRoot hshiftedRealizable
    (raw_guardedDirectStructuralTemplatePrefix_atomically_adequate
      M hPA inputs coqDynamicTruthImpGuardedFixedDeepPrefix)
    hdomain) as [domainDeepRoot hdomainDeep].
  assert (hcontext :
      rawTemplateContextCodeOnTail translation targetContext
        (coqDynamicTruthImpGuardedDeepPrefix callerPrefix) =
      rawTemplateContextCodeOnTail translation
        (rawTemplateContextCodeOnTail translation targetContext
          shiftedCaller)
        coqDynamicTruthImpGuardedFixedDeepPrefix).
  {
    unfold shiftedCaller.
    rewrite coqDynamicTruthImpGuardedDeepPrefix_split.
    apply rawTemplateContextCodeOnTail_app_finite.
  }
  change (RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail translation
      (rawTemplateContextCodeOnTail translation targetContext shiftedCaller)
      coqDynamicTruthImpGuardedFixedDeepPrefix)
    (rawDirectTemplateFormula inputs
      (templateFormulaRename (templateShiftRenamingMany 5)
        coqStrongStepProofEndpointAtomicAdequacyConclusion))
    atomicDeepRoot) in hatomicDeep.
  rewrite <- hcontext in hatomicDeep.
  rewrite <- coqDynamicTruthImpGuardedParentAtomicTemplate_eq_endpoint_shift5
    in hatomicDeep.
  change (RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail translation
      (rawTemplateContextCodeOnTail translation targetContext shiftedCaller)
      coqDynamicTruthImpGuardedFixedDeepPrefix)
    (rawDirectTemplateFormula inputs
      (templateFormulaRename (templateShiftRenamingMany 5)
        coqStrongStepProofEndpointQuantifierBoundedConclusion))
    domainDeepRoot) in hdomainDeep.
  rewrite <- hcontext in hdomainDeep.
  rewrite <- (raw_coqDynamicTruthImpGuardedParentDomain_eq_endpoint_shift5
    M inputs sigmaDomain piDomain sigmaEvidence piEvidence
    hidentification) in hdomainDeep.
  exists targetWitnessList, targetContext, atomicDeepRoot, domainDeepRoot.
  split; [exact htarget |].
  split; [exact hincluded |].
  split; assumption.
Qed.

(** The local source and the two parent invariants form the traversal-free
    part of the guarded branch.  Separating this triple from selected row
    evidence lets endpoint compilation grow and synchronize its witnessed
    PA tail before the two polarity-specific traversal roots are attached. *)
Record RawDynamicTruthImpGuardedParentBranchRootsAt
    (M : RawPAModel) (translation : RawCodedTemplateTranslation M)
    (baseContext : M) (callerPrefix : TemplateContext) : Prop := {
  rawDynamicTruthImpGuardedBranch_source : exists sourceRoot,
    RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation baseContext
        (coqDynamicTruthImpGuardedDeepPrefix callerPrefix))
      (rawTemplateFormula translation
        (tfAll (tfAll (tfAll
          coqDynamicTruthLocalExclusiveBodyTemplate)))) sourceRoot;
  rawDynamicTruthImpGuardedBranch_parentAtomic : exists atomicRoot,
    RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation baseContext
        (coqDynamicTruthImpGuardedDeepPrefix callerPrefix))
      (rawTemplateFormula translation
        (coqDynamicTruthImpDirectChildAtomicPremiseTemplate
          coqDynamicTruthImpGuardedLevelTerm
          coqDynamicTruthImpGuardedParentTerm
          coqDynamicTruthImpGuardedLeftTerm
          coqDynamicTruthImpGuardedRightTerm
          coqDynamicTruthImpGuardedChildTerm)) atomicRoot;
  rawDynamicTruthImpGuardedBranch_parentDomain : exists domainRoot,
    RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation baseContext
        (coqDynamicTruthImpGuardedDeepPrefix callerPrefix))
      (rawTemplateFormula translation
        (coqDynamicTruthImpDirectChildDomainPremiseTemplate
          coqDynamicTruthImpGuardedLevelTerm
          coqDynamicTruthImpGuardedParentTerm
          coqDynamicTruthImpGuardedLeftTerm
          coqDynamicTruthImpGuardedRightTerm
          coqDynamicTruthImpGuardedChildTerm)) domainRoot
}.

Arguments RawDynamicTruthImpGuardedParentBranchRootsAt
  M translation baseContext callerPrefix : clear implicits.

(** The traversal-specific half of a guarded branch.  Both global sources,
    both payload callbacks, and both conclusions use the literal guarded
    deep prefix.  The local row templates remain parameters so this adapter
    applies beyond rank zero and does not bake a particular traversal syntax
    into the guarded logical closure. *)
Record RawDynamicTruthImpGuardedSelectedEvidenceTraversalAt
    (M : RawPAModel) (translation : RawCodedTemplateTranslation M)
    (baseContext : M) (callerPrefix : TemplateContext)
    (localSigma localPi : TemplateFormula) : Prop := {
  rawDynamicTruthImpGuardedTraversal_sigmaSource : exists root,
    RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation baseContext
        (coqDynamicTruthImpGuardedDeepPrefix callerPrefix))
      (rawTemplateFormula translation
        (coqDynamicTruthGlobalExistentialSource
          0 localSigma localPi)) root;
  rawDynamicTruthImpGuardedTraversal_piSource : exists root,
    RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation baseContext
        (coqDynamicTruthImpGuardedDeepPrefix callerPrefix))
      (rawTemplateFormula translation
        (coqDynamicTruthGlobalExistentialSource
          1 localSigma localPi)) root;
  rawDynamicTruthImpGuardedTraversal_sigmaCompiler :
    RawCodedDynamicTruthSelectedPayloadShiftCompilerOnWitnessedExtensionsOnTemplatePrefix
      M translation baseContext
      (coqDynamicTruthImpGuardedDeepPrefix callerPrefix) 0
      localSigma localPi
      coqDynamicTruthImpGuardedLocalSigmaEvidenceTemplate;
  rawDynamicTruthImpGuardedTraversal_piCompiler :
    RawCodedDynamicTruthSelectedPayloadShiftCompilerOnWitnessedExtensionsOnTemplatePrefix
      M translation baseContext
      (coqDynamicTruthImpGuardedDeepPrefix callerPrefix) 1
      localSigma localPi
      coqDynamicTruthImpGuardedLocalPiEvidenceTemplate
}.

Arguments RawDynamicTruthImpGuardedSelectedEvidenceTraversalAt
  M translation baseContext callerPrefix localSigma localPi
  : clear implicits.

Record RawDynamicTruthImpGuardedEvidenceRootsAt
    (M : RawPAModel) (translation : RawCodedTemplateTranslation M)
    (baseContext : M) (callerPrefix : TemplateContext) : Prop := {
  rawDynamicTruthImpGuardedEvidenceRoots_sigma : exists sigmaRoot,
    RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation baseContext
        (coqDynamicTruthImpGuardedDeepPrefix callerPrefix))
      (rawTemplateFormula translation
        coqDynamicTruthImpGuardedLocalSigmaEvidenceTemplate) sigmaRoot;
  rawDynamicTruthImpGuardedEvidenceRoots_pi : exists piRoot,
    RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation baseContext
        (coqDynamicTruthImpGuardedDeepPrefix callerPrefix))
      (rawTemplateFormula translation
        coqDynamicTruthImpGuardedLocalPiEvidenceTemplate) piRoot
}.

Arguments RawDynamicTruthImpGuardedEvidenceRootsAt
  M translation baseContext callerPrefix : clear implicits.

(** Run both selected rows and retain their common witnessed extension. *)
Theorem
    raw_dynamicTruthImpGuardedEvidenceRoots_on_witnessed_extension_of_traversal :
    forall (M : RawPAModel), RawPASatisfies M -> forall
      translation baseWitnessList baseContext callerPrefix
      localSigma localPi,
  RawCodedTemplatePAAgreement M translation ->
  RawCodedPAAxiomWitnessContext M baseWitnessList baseContext ->
  RawDynamicTruthImpGuardedSelectedEvidenceTraversalAt M translation
    baseContext callerPrefix localSigma localPi ->
  exists targetWitnessList targetContext,
    RawCodedPAAxiomWitnessContext M targetWitnessList targetContext /\
    RawContextListIncluded M baseContext targetContext /\
    RawDynamicTruthImpGuardedEvidenceRootsAt M translation
      targetContext callerPrefix.
Proof.
  intros M hPA translation baseWitnessList baseContext callerPrefix
    localSigma localPi hagreement hbase htraversal.
  destruct htraversal as
    [(sigmaSourceRoot & hsigmaSource) (piSourceRoot & hpiSource)
      hsigmaCompiler hpiCompiler].
  destruct
    (raw_codedPALocalProofOf_dynamicTruthGlobal_row_evidence_pair_of_selected_compiler_families_on_template_prefix
      M hPA translation hagreement baseWitnessList baseContext
      (coqDynamicTruthImpGuardedDeepPrefix callerPrefix)
      localSigma localPi
      coqDynamicTruthImpGuardedLocalSigmaEvidenceTemplate
      coqDynamicTruthImpGuardedLocalPiEvidenceTemplate
      sigmaSourceRoot piSourceRoot hbase
      hsigmaCompiler hpiCompiler hsigmaSource hpiSource)
    as (targetWitnessList & targetContext & sigmaRoot & piRoot &
      htargetWitnessed & hincluded & hsigma & hpi).
  exists targetWitnessList, targetContext.
  split; [exact htargetWitnessed |].
  split; [exact hincluded |].
  constructor.
  - exists sigmaRoot. exact hsigma.
  - exists piRoot. exact hpi.
Qed.

(** All five roots inhabit the same deepest branch context.  Existential
    root codes stay in [Prop], so the interface commits to no computational
    choice and can be transported or merged by ordinary witnessed-context
    machinery. *)
Record RawDynamicTruthImpGuardedBranchRootsAt
    (M : RawPAModel) (translation : RawCodedTemplateTranslation M)
    (baseContext : M) (callerPrefix : TemplateContext) : Prop := {
  rawDynamicTruthImpGuardedBranch_parent :
    RawDynamicTruthImpGuardedParentBranchRootsAt M translation
      baseContext callerPrefix;
  rawDynamicTruthImpGuardedBranch_sigmaEvidence : exists sigmaRoot,
    RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation baseContext
        (coqDynamicTruthImpGuardedDeepPrefix callerPrefix))
      (rawTemplateFormula translation
        coqDynamicTruthImpGuardedLocalSigmaEvidenceTemplate) sigmaRoot;
  rawDynamicTruthImpGuardedBranch_piEvidence : exists piRoot,
    RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation baseContext
        (coqDynamicTruthImpGuardedDeepPrefix callerPrefix))
      (rawTemplateFormula translation
        coqDynamicTruthImpGuardedLocalPiEvidenceTemplate) piRoot
}.

Arguments RawDynamicTruthImpGuardedBranchRootsAt
  M translation baseContext callerPrefix : clear implicits.

(** Merge the traversal result with the already synchronized parent triple.
    Only the witnessed PA tail changes; all five roots preserve the same
    literal guarded template prefix. *)
Theorem
    raw_dynamicTruthImpGuardedBranchRoots_on_witnessed_extension_of_parent_and_traversal :
    forall (M : RawPAModel), RawPASatisfies M -> forall
      translation baseWitnessList baseContext callerPrefix
      localSigma localPi,
  RawCodedTemplatePAAgreement M translation ->
  RawCodedPAAxiomWitnessContext M baseWitnessList baseContext ->
  RawDynamicTruthImpGuardedParentBranchRootsAt M translation
    baseContext callerPrefix ->
  RawDynamicTruthImpGuardedSelectedEvidenceTraversalAt M translation
    baseContext callerPrefix localSigma localPi ->
  exists targetWitnessList targetContext,
    RawCodedPAAxiomWitnessContext M targetWitnessList targetContext /\
    RawContextListIncluded M baseContext targetContext /\
    RawDynamicTruthImpGuardedBranchRootsAt M translation
      targetContext callerPrefix.
Proof.
  intros M hPA translation baseWitnessList baseContext callerPrefix
    localSigma localPi hagreement hbase hparent htraversal.
  destruct hparent as
    [(sourceRoot & hsource) (atomicRoot & hatomic)
      (domainRoot & hdomain)].
  destruct
    (raw_dynamicTruthImpGuardedEvidenceRoots_on_witnessed_extension_of_traversal
      M hPA translation baseWitnessList baseContext callerPrefix
      localSigma localPi hagreement hbase htraversal)
    as (targetWitnessList & targetContext & htargetWitnessed &
      hincluded & hevidence).
  destruct hevidence as
    [(sigmaRoot & hsigma) (piRoot & hpi)].
  destruct
    (raw_codedPALocalProof_sameTemplatePrefix_witnessedTail_transport
      M hPA translation baseWitnessList baseContext
      targetWitnessList targetContext
      (coqDynamicTruthImpGuardedDeepPrefix callerPrefix)
      (rawTemplateFormula translation
        (tfAll (tfAll (tfAll
          coqDynamicTruthLocalExclusiveBodyTemplate))))
      sourceRoot hbase htargetWitnessed hincluded hsource)
    as [transportedSourceRoot htransportedSource].
  destruct
    (raw_codedPALocalProof_sameTemplatePrefix_witnessedTail_transport
      M hPA translation baseWitnessList baseContext
      targetWitnessList targetContext
      (coqDynamicTruthImpGuardedDeepPrefix callerPrefix)
      (rawTemplateFormula translation
        (coqDynamicTruthImpDirectChildAtomicPremiseTemplate
          coqDynamicTruthImpGuardedLevelTerm
          coqDynamicTruthImpGuardedParentTerm
          coqDynamicTruthImpGuardedLeftTerm
          coqDynamicTruthImpGuardedRightTerm
          coqDynamicTruthImpGuardedChildTerm))
      atomicRoot hbase htargetWitnessed hincluded hatomic)
    as [transportedAtomicRoot htransportedAtomic].
  destruct
    (raw_codedPALocalProof_sameTemplatePrefix_witnessedTail_transport
      M hPA translation baseWitnessList baseContext
      targetWitnessList targetContext
      (coqDynamicTruthImpGuardedDeepPrefix callerPrefix)
      (rawTemplateFormula translation
        (coqDynamicTruthImpDirectChildDomainPremiseTemplate
          coqDynamicTruthImpGuardedLevelTerm
          coqDynamicTruthImpGuardedParentTerm
          coqDynamicTruthImpGuardedLeftTerm
          coqDynamicTruthImpGuardedRightTerm
          coqDynamicTruthImpGuardedChildTerm))
      domainRoot hbase htargetWitnessed hincluded hdomain)
    as [transportedDomainRoot htransportedDomain].
  exists targetWitnessList, targetContext.
  split; [exact htargetWitnessed |].
  split; [exact hincluded |].
  constructor.
  - constructor.
    + exists transportedSourceRoot. exact htransportedSource.
    + exists transportedAtomicRoot. exact htransportedAtomic.
    + exists transportedDomainRoot. exact htransportedDomain.
  - exists sigmaRoot. exact hsigma.
  - exists piRoot. exact hpi.
Qed.

(** General closure adapter.  It is independent of rank zero and accepts any
    agreeing translation whose concrete deep prefix is atomically adequate. *)
Theorem
    raw_dynamicTruthImpGuardedPredecessorRoot_on_witnessed_extension_of_branch_roots :
    forall (M : RawPAModel), RawPASatisfies M -> forall
      translation baseWitnessList baseContext callerPrefix,
  RawCodedTemplatePAAgreement M translation ->
  RawCodedTemplatePrefixAtomicallyAdequate M translation
    (coqDynamicTruthImpGuardedDeepPrefix callerPrefix) ->
  RawCodedPAAxiomWitnessContext M baseWitnessList baseContext ->
  RawDynamicTruthImpGuardedBranchRootsAt M translation
    baseContext callerPrefix ->
  exists targetWitnessList targetContext predecessorRoot,
    RawCodedPAAxiomWitnessContext M targetWitnessList targetContext /\
    RawContextListIncluded M baseContext targetContext /\
    RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation targetContext callerPrefix)
      (rawDynamicTruthImpGuardedPredecessorStateExclusivityCode M)
      predecessorRoot.
Proof.
  intros M hPA translation baseWitnessList baseContext callerPrefix
    hagreement hadequate hbase hroots.
  destruct hroots as
    [hparent (sigmaRoot & hsigma) (piRoot & hpi)].
  destruct hparent as
    [(sourceRoot & hsource) (atomicRoot & hatomic)
      (domainRoot & hdomain)].
  exact
    (raw_dynamicTruthImpGuardedPredecessorStateExclusivityRoot_of_branch_roots_under_template_prefix
      M hPA translation hagreement baseWitnessList baseContext callerPrefix
      sourceRoot atomicRoot domainRoot sigmaRoot piRoot
      hadequate hbase hsource hatomic hdomain hsigma hpi).
Qed.

(** The local-exclusivity member of the branch package is already present in
    normalized resources.  Identify its concrete rank-zero body with the
    chosen direct translation, then insert the entire deep branch prefix by
    represented adequate-cons transplantation. *)
Theorem raw_dynamicTruthImpGuardedBranchSource_of_zero_normalized : forall
    (M : RawPAModel) (hPA : RawPASatisfies M), forall
      (inputs : RawCodedTemplateDirectStructuralInputs M)
      normalizedTranslation witnessList baseContext helperRoots callerPrefix,
  RawCoqDynamicTruthLocalExclusiveTemplateIdentification M inputs
    (rawDynamicTruthZeroSigmaDomainCode M)
    (rawDynamicTruthZeroPiDomainCode M)
    (rawDynamicTruthZeroSigmaEvidenceCode M)
    (rawDynamicTruthZeroPiEvidenceCode M) ->
  RawDynamicTruthNativeLocalZeroGuardedNormalizedResourcesAt M
    normalizedTranslation witnessList baseContext helperRoots ->
  exists sourceRoot,
    RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        baseContext (coqDynamicTruthImpGuardedDeepPrefix callerPrefix))
      (rawTemplateFormula
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        (tfAll (tfAll (tfAll
          coqDynamicTruthLocalExclusiveBodyTemplate)))) sourceRoot.
Proof.
  intros M hPA inputs normalizedTranslation witnessList baseContext
    helperRoots callerPrefix hidentification hnormalized.
  destruct
    (rawDynamicTruthNativeLocalZeroGuardedNormalized_localProjections
      M normalizedTranslation witnessList baseContext helperRoots
      hnormalized) as [fieldRoot hprojected].
  pose proof (rawDynamicTruthLocalProjected_exclusive M baseContext
    (rawDynamicTruthZeroSigmaDomainCode M)
    (rawDynamicTruthZeroPiDomainCode M)
    (rawDynamicTruthZeroSigmaEvidenceCode M)
    (rawDynamicTruthZeroPiEvidenceCode M) fieldRoot hprojected)
    as hexclusive.
  assert (hsourceCode :
      rawTemplateFormula
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        (tfAll (tfAll (tfAll
          coqDynamicTruthLocalExclusiveBodyTemplate))) =
      rawDynamicTruthLocalFormulaAll3Code M
        (rawDynamicTruthLocalExclusiveCode M
          (rawDynamicTruthZeroSigmaDomainCode M)
          (rawDynamicTruthZeroPiDomainCode M)
          (rawDynamicTruthZeroSigmaEvidenceCode M)
          (rawDynamicTruthZeroPiEvidenceCode M))).
  {
    unfold rawDynamicTruthLocalFormulaAll3Code.
    rewrite !rawTemplateFormula_all.
    repeat f_equal.
    change (rawDirectTemplateFormula inputs
      coqDynamicTruthLocalExclusiveBodyTemplate =
      rawDynamicTruthLocalExclusiveCode M
        (rawDynamicTruthZeroSigmaDomainCode M)
        (rawDynamicTruthZeroPiDomainCode M)
        (rawDynamicTruthZeroSigmaEvidenceCode M)
        (rawDynamicTruthZeroPiEvidenceCode M)).
    exact (rawCoqDynamicTruthLocalExclusiveBodyTemplate_identified
      M hPA inputs
      (rawDynamicTruthZeroSigmaDomainCode M)
      (rawDynamicTruthZeroPiDomainCode M)
      (rawDynamicTruthZeroSigmaEvidenceCode M)
      (rawDynamicTruthZeroPiEvidenceCode M) hidentification).
  }
  destruct (rawDynamicTruthNativeLocalZeroGuardedNormalized_fields
    M normalizedTranslation witnessList baseContext helperRoots
    hnormalized) as [hbaseWitnessed _].
  destruct (raw_codedPALocalProof_templatePrefix M hPA
    (rawDirectStructuralTemplateTranslation M hPA inputs)
    baseContext (coqDynamicTruthImpGuardedDeepPrefix callerPrefix)
    (rawDynamicTruthLocalFormulaAll3Code M
      (rawDynamicTruthLocalExclusiveCode M
        (rawDynamicTruthZeroSigmaDomainCode M)
        (rawDynamicTruthZeroPiDomainCode M)
        (rawDynamicTruthZeroSigmaEvidenceCode M)
        (rawDynamicTruthZeroPiEvidenceCode M)))
    (rawDynamicTruthLocalExclusiveProjectionRoot M baseContext
      (rawDynamicTruthZeroSigmaDomainCode M)
      (rawDynamicTruthZeroPiDomainCode M)
      (rawDynamicTruthZeroSigmaEvidenceCode M)
      (rawDynamicTruthZeroPiEvidenceCode M) fieldRoot)
    (raw_codedPAAxiomWitnessContext_context_realizable
      M witnessList baseContext hbaseWitnessed)
    (raw_guardedDirectStructuralTemplatePrefix_atomically_adequate M hPA
      inputs (coqDynamicTruthImpGuardedDeepPrefix callerPrefix))
    hexclusive) as [sourceRoot hsource].
  exists sourceRoot. rewrite hsourceCode. exact hsource.
Qed.

(** Synchronize the normalized local-exclusivity source with both guarded
    parent endpoints.  Endpoint compilation may append standard PA witnesses;
    the source proof is transported once across that literal tail inclusion,
    so the resulting three-root package has one exact deep context. *)
Theorem
    raw_dynamicTruthImpGuardedParentBranchRoots_exists_of_zero_normalized_and_template_assumptions :
    forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
      normalizedTranslation witnessList baseContext helperRoots callerPrefix,
  RawDynamicTruthNativeLocalZeroGuardedNormalizedResourcesAt M
    normalizedTranslation witnessList baseContext helperRoots ->
  In coqRestrictedPADerivationSoundnessRestrictedProofTemplate
    callerPrefix ->
  In coqStrongStepProofEndpointAtomicAdequacyRulePremise callerPrefix ->
  exists inputs : RawCodedTemplateDirectStructuralInputs M,
  exists targetWitnessList targetContext,
    RawCoqDynamicTruthLocalExclusiveTemplateIdentification M inputs
      (rawDynamicTruthZeroSigmaDomainCode M)
      (rawDynamicTruthZeroPiDomainCode M)
      (rawDynamicTruthZeroSigmaEvidenceCode M)
      (rawDynamicTruthZeroPiEvidenceCode M) /\
    RawCodedPAAxiomWitnessContext M targetWitnessList targetContext /\
    RawContextListIncluded M baseContext targetContext /\
    RawDynamicTruthImpGuardedParentBranchRootsAt M
      (rawDirectStructuralTemplateTranslation M hPA inputs)
      targetContext callerPrefix.
Proof.
  intros M hPA normalizedTranslation witnessList baseContext helperRoots
    callerPrefix hnormalized hrestrictedIn hruleIn.
  destruct
    (raw_dynamicTruthZeroLocalExclusiveTemplateIdentification_exists M hPA)
    as [inputs hidentification].
  destruct
    (rawDynamicTruthNativeLocalZeroGuardedNormalized_fields
      M normalizedTranslation witnessList baseContext helperRoots
      hnormalized) as [hbaseWitnessed _].
  destruct
    (raw_dynamicTruthImpGuardedBranchSource_of_zero_normalized
      M hPA inputs normalizedTranslation witnessList baseContext
      helperRoots callerPrefix hidentification hnormalized)
    as [sourceRoot hsource].
  destruct
    (raw_dynamicTruthImpGuardedParentEndpointRoots_of_template_assumptions
      M hPA inputs
      (rawDynamicTruthZeroSigmaDomainCode M)
      (rawDynamicTruthZeroPiDomainCode M)
      (rawDynamicTruthZeroSigmaEvidenceCode M)
      (rawDynamicTruthZeroPiEvidenceCode M)
      witnessList baseContext callerPrefix hidentification hbaseWitnessed
      hrestrictedIn hruleIn)
    as (targetWitnessList & targetContext & atomicRoot & domainRoot &
      htargetWitnessed & hincluded & hatomic & hdomain).
  destruct
    (raw_codedPALocalProof_sameTemplatePrefix_witnessedTail_transport
      M hPA (rawDirectStructuralTemplateTranslation M hPA inputs)
      witnessList baseContext targetWitnessList targetContext
      (coqDynamicTruthImpGuardedDeepPrefix callerPrefix)
      (rawTemplateFormula
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        (tfAll (tfAll (tfAll
          coqDynamicTruthLocalExclusiveBodyTemplate))))
      sourceRoot hbaseWitnessed htargetWitnessed hincluded hsource)
    as [transportedSourceRoot htransportedSource].
  exists inputs, targetWitnessList, targetContext.
  split; [exact hidentification |].
  split; [exact htargetWitnessed |].
  split; [exact hincluded |].
  constructor.
  - exists transportedSourceRoot. exact htransportedSource.
  - exists atomicRoot. exact hatomic.
  - exists domainRoot. exact hdomain.
Qed.

(** Canonical rank-zero identification chooses direct inputs whose local
    coordinates agree with the normalized field.  Because the conclusion is
    propositional, the selected structural record remains an honest
    existential witness rather than a global choice. *)
Corollary
    raw_dynamicTruthImpGuardedBranchSource_exists_of_zero_normalized : forall
    (M : RawPAModel) (hPA : RawPASatisfies M), forall
      normalizedTranslation witnessList baseContext helperRoots callerPrefix,
  RawDynamicTruthNativeLocalZeroGuardedNormalizedResourcesAt M
    normalizedTranslation witnessList baseContext helperRoots ->
  exists inputs : RawCodedTemplateDirectStructuralInputs M,
  exists sourceRoot,
    RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        baseContext (coqDynamicTruthImpGuardedDeepPrefix callerPrefix))
      (rawTemplateFormula
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        (tfAll (tfAll (tfAll
          coqDynamicTruthLocalExclusiveBodyTemplate)))) sourceRoot.
Proof.
  intros M hPA normalizedTranslation witnessList baseContext helperRoots
    callerPrefix hnormalized.
  destruct
    (raw_dynamicTruthZeroLocalExclusiveTemplateIdentification_exists M hPA)
    as [inputs hidentification].
  exists inputs.
  exact (raw_dynamicTruthImpGuardedBranchSource_of_zero_normalized
    M hPA inputs normalizedTranslation witnessList baseContext helperRoots
    callerPrefix hidentification hnormalized).
Qed.

(** The only remaining normalized rank-zero producer: select the five branch
    roots on one witnessed extension.  The helper cells and all normalized
    local data are already carried by [resources]. *)
Definition
    RawDynamicTruthNativeLocalZeroGrowingGuardedBranchRootsCompilerOnNormalizedResources
    (M : RawPAModel) (hPA : RawPASatisfies M) : Prop :=
  forall (tail : nat -> M) witnessList baseContext (helperRoots : list M)
      sigmaDomain piDomain sigmaEvidence piEvidence,
    RawDynamicTruthNativeLocalZeroGuardedNormalizedResourcesAt M
      (rawBottomDirectStructuralTemplateTranslation M hPA)
      witnessList baseContext helperRoots ->
    RawDynamicTruthNativeLocalZeroCanonicalFullTraceAt M tail
      sigmaDomain piDomain sigmaEvidence piEvidence ->
    exists inputs : RawCodedTemplateDirectStructuralInputs M,
    exists branchWitnessList branchContext,
      RawCodedPAAxiomWitnessContext M branchWitnessList branchContext /\
      RawContextListIncluded M baseContext branchContext /\
      RawDynamicTruthImpGuardedBranchRootsAt M
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        branchContext [].

Arguments
  RawDynamicTruthNativeLocalZeroGrowingGuardedBranchRootsCompilerOnNormalizedResources
  M hPA : clear implicits.

Definition
    RawDynamicTruthNativeLocalZeroGrowingGuardedPredecessorRootCompilerOnNormalizedResources
    (M : RawPAModel) (hPA : RawPASatisfies M) : Prop :=
  forall (tail : nat -> M) witnessList baseContext (helperRoots : list M)
      sigmaDomain piDomain sigmaEvidence piEvidence,
    RawDynamicTruthNativeLocalZeroGuardedNormalizedResourcesAt M
      (rawBottomDirectStructuralTemplateTranslation M hPA)
      witnessList baseContext helperRoots ->
    RawDynamicTruthNativeLocalZeroCanonicalFullTraceAt M tail
      sigmaDomain piDomain sigmaEvidence piEvidence ->
    exists targetWitnessList targetContext,
      RawCodedPAAxiomWitnessContext M targetWitnessList targetContext /\
      RawContextListIncluded M baseContext targetContext /\
      RawDynamicTruthLocalRootAt M targetContext
        (rawDynamicTruthImpGuardedPredecessorStateExclusivityCode M).

Arguments
  RawDynamicTruthNativeLocalZeroGrowingGuardedPredecessorRootCompilerOnNormalizedResources
  M hPA : clear implicits.

(** Close the guarded predecessor and compose the producer's context growth
    with the finite PA extension selected by child-admissibility compilation. *)
Theorem
    raw_dynamicTruthNativeLocalZeroGrowingGuardedPredecessorRootCompilerOnNormalizedResources_of_branch_roots :
    forall (M : RawPAModel) (hPA : RawPASatisfies M),
  RawDynamicTruthNativeLocalZeroGrowingGuardedBranchRootsCompilerOnNormalizedResources
    M hPA ->
  RawDynamicTruthNativeLocalZeroGrowingGuardedPredecessorRootCompilerOnNormalizedResources
    M hPA.
Proof.
  intros M hPA hcompiler tail witnessList baseContext helperRoots
    sigmaDomain piDomain sigmaEvidence piEvidence hresources htrace.
  destruct (hcompiler tail witnessList baseContext helperRoots
    sigmaDomain piDomain sigmaEvidence piEvidence hresources htrace) as
    (inputs & branchWitnessList & branchContext & hbranchWitnessed &
      hbaseBranchIncluded & hbranchRoots).
  destruct
    (raw_dynamicTruthImpGuardedPredecessorRoot_on_witnessed_extension_of_branch_roots
      M hPA (rawDirectStructuralTemplateTranslation M hPA inputs)
      branchWitnessList branchContext []
      (rawDirectStructuralTemplatePAAgreement M hPA inputs)
      (raw_guardedDirectStructuralTemplatePrefix_atomically_adequate M hPA
        inputs
        (coqDynamicTruthImpGuardedDeepPrefix []))
      hbranchWitnessed hbranchRoots) as
    (targetWitnessList & targetContext & predecessorRoot &
      htargetWitnessed & hbranchTargetIncluded & hpredecessor).
  exists targetWitnessList, targetContext.
  split; [exact htargetWitnessed |].
  split.
  - intros member hmember.
    exact (hbranchTargetIncluded member
      (hbaseBranchIncluded member hmember)).
  - exists predecessorRoot.
    cbn [rawTemplateContextCodeOnTail].
    exact hpredecessor.
Qed.

End
  PABoundedRawCodedDynamicTruthNativeZeroGuardedPredecessorCompilation.
