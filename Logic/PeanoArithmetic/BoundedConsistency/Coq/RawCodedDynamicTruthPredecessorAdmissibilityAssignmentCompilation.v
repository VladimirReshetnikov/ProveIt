(**
  The assignment-definedness component of predecessor admissibility.

  The universal beta-assignment theorem is compiled beneath the literal Pi,
  Sigma predecessor-state prefix.  This module discharges prefix adequacy
  from standard PA quotation and rewrites the template context to the exact
  raw joint-state context used by the predecessor logical-roots package.
*)

From Stdlib Require Import List.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  CodedSyntax
  RawCodedAssignment
  RawCodedFixedLevelTruthTotality
  RawCodedSyntaxConstructors
  RawCodedContextLists
  RawCodedRestrictedPAProof
  RawCodedPAAxiomWitnessPrefix
  RawCodedPALocalProofWitnessedContextMerge
  RawCodedProofAtomicAdequacyStandard
  RawCodedPALocalProofExistential
  RawCodedTemplateSyntax
  RawCodedTemplateProofCompiler
  RawCodedTemplateProofCompilerSelfShiftTail
  RawCodedTemplatePAEmbedding
  RawCodedTemplateLocalProofWitnessedTailTransport
  RawCodedTemplateLocalProofStandardWitnessTailTransport
  RawCodedAssignmentUniversalDefinednessProofCompilation
  RawCodedDynamicTruthNativeLocalPositiveGraph
  RawCodedDynamicTruthLocalAdmissibilityCompilation
  RawCodedDynamicTruthPredecessorStateExclusivityCompilation
  RawCodedDynamicTruthPredecessorGlobalExistentialElimination.

Module
  PABoundedRawCodedDynamicTruthPredecessorAdmissibilityAssignmentCompilation.

Import ListNotations.
Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedCodedSyntax.
Import PABoundedRawCodedAssignment.
Import PABoundedRawCodedFixedLevelTruthTotality.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedContextLists.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedPAAxiomWitnessPrefix.
Import PABoundedRawCodedPALocalProofWitnessedContextMerge.
Import PABoundedRawCodedProofAtomicAdequacyStandard.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedTemplateProofCompilerSelfShiftTail.
Import PABoundedRawCodedTemplatePAEmbedding.
Import PABoundedRawCodedTemplateLocalProofWitnessedTailTransport.
Import PABoundedRawCodedTemplateLocalProofStandardWitnessTailTransport.
Import PABoundedRawCodedAssignmentUniversalDefinednessProofCompilation.
Import PABoundedRawCodedDynamicTruthNativeLocalPositiveGraph.
Import PABoundedRawCodedDynamicTruthLocalAdmissibilityCompilation.
Import
  PABoundedRawCodedDynamicTruthPredecessorStateExclusivityCompilation.
Import
  PABoundedRawCodedDynamicTruthPredecessorGlobalExistentialElimination.

(** Exact fixed leaves after the local formula/assignment theorem is opened
    inside the predecessor body's Sigma-index, Pi-index, and child binders. *)
Definition rawDynamicTruthPredecessorLocalAtomicAdequacyCode
    (M : RawPAModel) : M :=
  rawNumeralValue M
    (formulaCode (codedFormulaAtomicallyAdequateTermAt (tVar 0))).

Definition rawDynamicTruthPredecessorLocalAssignmentDefinedCode
    (M : RawPAModel) : M :=
  rawNumeralValue M
    (formulaCode
      (codedAssignmentDefinedThroughTermAt
        (tVar 4) (tVar 3) (tVar 0))).

Definition rawDynamicTruthPredecessorLocalAdmissibleCode
    (M : RawPAModel) (sigmaDomain piDomain : M) : M :=
  rawDynamicTruthAdmissibleCodeOf M
    (rawDynamicTruthPredecessorLocalAtomicAdequacyCode M)
    (rawDynamicTruthPredecessorLocalAssignmentDefinedCode M)
    sigmaDomain piDomain.

Arguments rawDynamicTruthPredecessorLocalAtomicAdequacyCode M
  : clear implicits.
Arguments rawDynamicTruthPredecessorLocalAssignmentDefinedCode M
  : clear implicits.
Arguments rawDynamicTruthPredecessorLocalAdmissibleCode
  M sigmaDomain piDomain : clear implicits.

(** Both temporary assumptions are embedded ordinary PA formulae, so PA
    agreement turns their translated codes into standard quotation and the
    generic quotation theorem supplies atomic adequacy. *)
Lemma raw_dynamicTruthPredecessorStateTemplateContext_atomically_adequate :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  RawCodedTemplatePrefixAtomicallyAdequate M translation
    coqDynamicTruthPredecessorStateTemplateContext.
Proof.
  intros M hPA translation hagreement formula hformula.
  unfold coqDynamicTruthPredecessorStateTemplateContext in hformula.
  destruct hformula as [<- | [<- | []]].
  - rewrite (rawTemplateFormula_embedPA hagreement
      dynamicTruthPredecessorPiStateMemberBodyFormula).
    exact (raw_quotedFormula_atomically_adequate M hPA
      dynamicTruthPredecessorPiStateMemberBodyFormula).
  - rewrite (rawTemplateFormula_embedPA hagreement
      dynamicTruthPredecessorSigmaStateMemberBodyFormula).
    exact (raw_quotedFormula_atomically_adequate M hPA
      dynamicTruthPredecessorSigmaStateMemberBodyFormula).
Qed.

(** Predecessor state assumptions may sit in front of an arbitrary caller
    prefix.  Separating this small closure lemma from the proof compiler
    avoids forcing every strong-step client to repeat the same [in_app_iff]
    argument. *)
Lemma raw_dynamicTruthPredecessorStateTemplateContext_app_atomically_adequate :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall prefix,
  RawCodedTemplatePrefixAtomicallyAdequate M translation prefix ->
  RawCodedTemplatePrefixAtomicallyAdequate M translation
    (coqDynamicTruthPredecessorStateTemplateContext ++ prefix).
Proof.
  intros M hPA translation hagreement prefix hprefix formula hformula.
  apply in_app_iff in hformula.
  destruct hformula as [hstate | hcaller].
  - exact
      (raw_dynamicTruthPredecessorStateTemplateContext_atomically_adequate
        M hPA translation hagreement formula hstate).
  - exact (hprefix formula hcaller).
Qed.

(** Prefix-general assignment component.  The caller prefix stays outside
    the witnessed PA tail and is therefore preserved literally while the
    closed assignment theorem selects its finite standard-axiom extension. *)
Theorem
    raw_dynamicTruthPredecessorLocalAssignmentRoot_on_witnessed_extension_under_prefix :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall baseWitnessList baseContext prefix,
  RawCodedTemplatePrefixAtomicallyAdequate M translation prefix ->
  RawCodedPAAxiomWitnessContext M baseWitnessList baseContext ->
  exists (witnesses : StandardPAAxiomWitnessPrefix) root,
    RawCodedPAAxiomWitnessContext M
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        witnesses baseWitnessList)
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses baseContext) /\
    RawCodedPALocalProofOf M
      (rawDynamicTruthPredecessorJointStateContext M
        (rawTemplateContextCodeOnTail translation
          (rawStandardPAAxiomWitnessPrefixContextCode M
            witnesses baseContext) prefix))
      (rawDynamicTruthLocalAssignmentDefinedCode M) root.
Proof.
  intros M hPA translation hagreement baseWitnessList baseContext
    prefix hprefix hbase.
  destruct
    (raw_codedPALocalProofOf_assignmentDefinedThrough_local_numeral_on_witnessed_tail_under_prefix
      M hPA translation hagreement baseWitnessList baseContext
      (coqDynamicTruthPredecessorStateTemplateContext ++ prefix)
      (raw_dynamicTruthPredecessorStateTemplateContext_app_atomically_adequate
        M hPA translation hagreement prefix hprefix)
      hbase)
    as (witnesses & root & hextended & hproof).
  exists witnesses, root. split; [exact hextended |].
  rewrite (raw_dynamicTruthPredecessorStateTemplateContext_app_code
    M translation hagreement
    (rawStandardPAAxiomWitnessPrefixContextCode M
      witnesses baseContext) prefix) in hproof.
  unfold rawDynamicTruthLocalAssignmentDefinedCode.
  exact hproof.
Qed.

(** Correct child-coordinate form of the preceding compiler.  It is kept as
    a separate endpoint while downstream predecessor bridges migrate away
    from the historical local-field layout. *)
Theorem
    raw_dynamicTruthPredecessorChildAssignmentRoot_on_witnessed_extension_under_prefix :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall baseWitnessList baseContext prefix,
  RawCodedTemplatePrefixAtomicallyAdequate M translation prefix ->
  RawCodedPAAxiomWitnessContext M baseWitnessList baseContext ->
  exists (witnesses : StandardPAAxiomWitnessPrefix) root,
    RawCodedPAAxiomWitnessContext M
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        witnesses baseWitnessList)
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses baseContext) /\
    RawCodedPALocalProofOf M
      (rawDynamicTruthPredecessorJointStateContext M
        (rawTemplateContextCodeOnTail translation
          (rawStandardPAAxiomWitnessPrefixContextCode M
            witnesses baseContext) prefix))
      (rawDynamicTruthPredecessorLocalAssignmentDefinedCode M) root.
Proof.
  intros M hPA translation hagreement baseWitnessList baseContext
    prefix hprefix hbase.
  destruct
    (raw_codedPALocalProofOf_assignmentDefinedThrough_predecessor_child_numeral_on_witnessed_tail_under_prefix
      M hPA translation hagreement baseWitnessList baseContext
      (coqDynamicTruthPredecessorStateTemplateContext ++ prefix)
      (raw_dynamicTruthPredecessorStateTemplateContext_app_atomically_adequate
        M hPA translation hagreement prefix hprefix)
      hbase)
    as (witnesses & root & hextended & hproof).
  exists witnesses, root. split; [exact hextended |].
  rewrite (raw_dynamicTruthPredecessorStateTemplateContext_app_code
    M translation hagreement
    (rawStandardPAAxiomWitnessPrefixContextCode M
      witnesses baseContext) prefix) in hproof.
  unfold rawDynamicTruthPredecessorLocalAssignmentDefinedCode.
  exact hproof.
Qed.

(** Produce the exact assignment component under the literal predecessor
    state assumptions.  The returned standard prefix is retained so the
    atomic-adequacy and domain components can later be transported into this
    same extension before the three roots are conjoined. *)
Theorem
    raw_dynamicTruthPredecessorLocalAssignmentRoot_on_witnessed_extension :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall baseWitnessList baseContext,
  RawCodedPAAxiomWitnessContext M baseWitnessList baseContext ->
  exists (witnesses : StandardPAAxiomWitnessPrefix) root,
    RawCodedPAAxiomWitnessContext M
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        witnesses baseWitnessList)
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses baseContext) /\
    RawCodedPALocalProofOf M
      (rawDynamicTruthPredecessorJointStateContext M
        (rawStandardPAAxiomWitnessPrefixContextCode M
          witnesses baseContext))
      (rawDynamicTruthLocalAssignmentDefinedCode M) root.
Proof.
  intros M hPA translation hagreement
    baseWitnessList baseContext hbase.
  destruct
    (raw_dynamicTruthPredecessorLocalAssignmentRoot_on_witnessed_extension_under_prefix
      M hPA translation hagreement baseWitnessList baseContext []
      (fun formula hformula => match hformula with end) hbase)
    as (witnesses & root & hextended & hproof).
  exists witnesses, root. split; [exact hextended |].
  cbn [rawTemplateContextCodeOnTail] in hproof.
  exact hproof.
Qed.

(** Prefix-general predecessor admissibility.  State membership alone does
    not imply that an arbitrary table row is syntactically adequate or lies
    in the requested rank union.  Callers therefore supply exactly those two
    restricted-proof invariants beneath the state assumptions and their own
    temporary prefix.  Assignment coverage is generated here, and all three
    roots are synchronized in the one retained witnessed extension. *)
Theorem
    raw_dynamicTruthPredecessorLocalAdmissibility_on_witnessed_extension_under_prefix_of_atomic_and_domain :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall baseWitnessList baseContext prefix sigmaDomain piDomain
      atomicRoot domainRoot,
  RawCodedTemplatePrefixAtomicallyAdequate M translation prefix ->
  RawCodedPAAxiomWitnessContext M baseWitnessList baseContext ->
  RawCodedPALocalProofOf M
    (rawDynamicTruthPredecessorJointStateContext M
      (rawTemplateContextCodeOnTail translation baseContext prefix))
    (rawDynamicTruthLocalAtomicAdequacyCode M) atomicRoot ->
  RawCodedPALocalProofOf M
    (rawDynamicTruthPredecessorJointStateContext M
      (rawTemplateContextCodeOnTail translation baseContext prefix))
    (rawFormulaOrCode M sigmaDomain piDomain) domainRoot ->
  exists (witnesses : StandardPAAxiomWitnessPrefix) admissibleRoot,
    RawCodedPAAxiomWitnessContext M
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        witnesses baseWitnessList)
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses baseContext) /\
    RawCodedPALocalProofOf M
      (rawDynamicTruthPredecessorJointStateContext M
        (rawTemplateContextCodeOnTail translation
          (rawStandardPAAxiomWitnessPrefixContextCode M
            witnesses baseContext) prefix))
      (rawDynamicTruthLocalAdmissibleCode M sigmaDomain piDomain)
      admissibleRoot.
Proof.
  intros M hPA translation hagreement baseWitnessList baseContext
    prefix sigmaDomain piDomain atomicRoot domainRoot
    hprefix hbase hatomic hdomain.
  destruct
    (raw_dynamicTruthPredecessorLocalAssignmentRoot_on_witnessed_extension_under_prefix
      M hPA translation hagreement baseWitnessList baseContext prefix
      hprefix hbase)
    as (witnesses & assignmentRoot & hextended & hassignment).
  set (extendedWitnessList :=
    rawStandardPAAxiomWitnessPrefixWitnessListCode M
      witnesses baseWitnessList).
  set (extendedContext :=
    rawStandardPAAxiomWitnessPrefixContextCode M
      witnesses baseContext).
  assert (hincluded : RawContextListIncluded M baseContext extendedContext).
  {
    unfold extendedContext.
    exact (raw_standardPAAxiomWitnessPrefixContextCode_target_included
      M hPA witnesses baseContext).
  }
  assert (hatomicTemplate : RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation baseContext
        (coqDynamicTruthPredecessorStateTemplateContext ++ prefix))
      (rawDynamicTruthLocalAtomicAdequacyCode M) atomicRoot).
  {
    rewrite (raw_dynamicTruthPredecessorStateTemplateContext_app_code
      M translation hagreement baseContext prefix).
    exact hatomic.
  }
  destruct
    (raw_codedPALocalProof_sameTemplatePrefix_witnessedTail_transport
      M hPA translation baseWitnessList baseContext
      extendedWitnessList extendedContext
      (coqDynamicTruthPredecessorStateTemplateContext ++ prefix)
      (rawDynamicTruthLocalAtomicAdequacyCode M) atomicRoot
      hbase hextended hincluded hatomicTemplate)
    as [transportedAtomicRoot htransportedAtomic].
  assert (htransportedAtomicJoint : RawCodedPALocalProofOf M
      (rawDynamicTruthPredecessorJointStateContext M
        (rawTemplateContextCodeOnTail translation extendedContext prefix))
      (rawDynamicTruthLocalAtomicAdequacyCode M)
      transportedAtomicRoot).
  {
    rewrite <- (raw_dynamicTruthPredecessorStateTemplateContext_app_code
      M translation hagreement extendedContext prefix).
    exact htransportedAtomic.
  }
  assert (hdomainTemplate : RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation baseContext
        (coqDynamicTruthPredecessorStateTemplateContext ++ prefix))
      (rawFormulaOrCode M sigmaDomain piDomain) domainRoot).
  {
    rewrite (raw_dynamicTruthPredecessorStateTemplateContext_app_code
      M translation hagreement baseContext prefix).
    exact hdomain.
  }
  destruct
    (raw_codedPALocalProof_sameTemplatePrefix_witnessedTail_transport
      M hPA translation baseWitnessList baseContext
      extendedWitnessList extendedContext
      (coqDynamicTruthPredecessorStateTemplateContext ++ prefix)
      (rawFormulaOrCode M sigmaDomain piDomain) domainRoot
      hbase hextended hincluded hdomainTemplate)
    as [transportedDomainRoot htransportedDomain].
  assert (htransportedDomainJoint : RawCodedPALocalProofOf M
      (rawDynamicTruthPredecessorJointStateContext M
        (rawTemplateContextCodeOnTail translation extendedContext prefix))
      (rawFormulaOrCode M sigmaDomain piDomain)
      transportedDomainRoot).
  {
    rewrite <- (raw_dynamicTruthPredecessorStateTemplateContext_app_code
      M translation hagreement extendedContext prefix).
    exact htransportedDomain.
  }
  assert (hcomponents : RawDynamicTruthLocalAdmissibilityComponentsAt M
      (rawDynamicTruthPredecessorJointStateContext M
        (rawTemplateContextCodeOnTail translation extendedContext prefix))
      sigmaDomain piDomain).
  {
    constructor.
    - exists transportedAtomicRoot. exact htransportedAtomicJoint.
    - exists assignmentRoot. exact hassignment.
    - exists transportedDomainRoot. exact htransportedDomainJoint.
  }
  destruct
    (raw_codedPALocalProofOf_dynamicTruthLocalAdmissible_of_components
      M hPA (rawDynamicTruthPredecessorJointStateContext M
        (rawTemplateContextCodeOnTail translation extendedContext prefix))
      sigmaDomain piDomain hcomponents)
    as [admissibleRoot hadmissible].
  exists witnesses, admissibleRoot. split; assumption.
Qed.

(** Historical state-only endpoint, now an empty-prefix specialization of
    the stronger theorem above. *)
Corollary
    raw_dynamicTruthPredecessorLocalAdmissibility_on_witnessed_extension_of_atomic_and_domain :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall baseWitnessList baseContext sigmaDomain piDomain
      atomicRoot domainRoot,
  RawCodedPAAxiomWitnessContext M baseWitnessList baseContext ->
  RawCodedPALocalProofOf M
    (rawDynamicTruthPredecessorJointStateContext M baseContext)
    (rawDynamicTruthLocalAtomicAdequacyCode M) atomicRoot ->
  RawCodedPALocalProofOf M
    (rawDynamicTruthPredecessorJointStateContext M baseContext)
    (rawFormulaOrCode M sigmaDomain piDomain) domainRoot ->
  exists (witnesses : StandardPAAxiomWitnessPrefix) admissibleRoot,
    RawCodedPAAxiomWitnessContext M
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        witnesses baseWitnessList)
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses baseContext) /\
    RawCodedPALocalProofOf M
      (rawDynamicTruthPredecessorJointStateContext M
        (rawStandardPAAxiomWitnessPrefixContextCode M
          witnesses baseContext))
      (rawDynamicTruthLocalAdmissibleCode M sigmaDomain piDomain)
      admissibleRoot.
Proof.
  intros M hPA translation hagreement baseWitnessList baseContext
    sigmaDomain piDomain atomicRoot domainRoot hbase hatomic hdomain.
  pose proof
    (raw_dynamicTruthPredecessorLocalAdmissibility_on_witnessed_extension_under_prefix_of_atomic_and_domain
      M hPA translation hagreement baseWitnessList baseContext []
      sigmaDomain piDomain atomicRoot domainRoot
      (fun formula hformula => match hformula with end)
      hbase hatomic hdomain) as hresult.
  cbn [rawTemplateContextCodeOnTail] in hresult.
  exact hresult.
Qed.

End
  PABoundedRawCodedDynamicTruthPredecessorAdmissibilityAssignmentCompilation.
