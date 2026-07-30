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
    (raw_codedPALocalProofOf_assignmentDefinedThrough_local_numeral_on_witnessed_tail_under_prefix
      M hPA translation hagreement baseWitnessList baseContext
      coqDynamicTruthPredecessorStateTemplateContext
      (raw_dynamicTruthPredecessorStateTemplateContext_atomically_adequate
        M hPA translation hagreement)
      hbase)
    as (witnesses & root & hextended & hproof).
  exists witnesses, root. split; [exact hextended |].
  rewrite (raw_dynamicTruthPredecessorStateTemplateContextCode
    M translation hagreement
    (rawStandardPAAxiomWitnessPrefixContextCode M
      witnesses baseContext)) in hproof.
  unfold rawDynamicTruthLocalAssignmentDefinedCode.
  exact hproof.
Qed.

(** Honest predecessor-admissibility boundary.  State membership alone does
    not imply that an arbitrary table row is syntactically adequate or lies
    in the requested rank union.  Callers therefore supply exactly those two
    restricted-proof invariants.  Assignment coverage is generated here,
    and the two incoming roots are transported through that compiler's one
    retained witness extension before all three components are conjoined. *)
Theorem
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
  destruct
    (raw_dynamicTruthPredecessorLocalAssignmentRoot_on_witnessed_extension
      M hPA translation hagreement baseWitnessList baseContext hbase)
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
        coqDynamicTruthPredecessorStateTemplateContext)
      (rawDynamicTruthLocalAtomicAdequacyCode M) atomicRoot).
  {
    rewrite (raw_dynamicTruthPredecessorStateTemplateContextCode
      M translation hagreement baseContext).
    exact hatomic.
  }
  destruct
    (raw_codedPALocalProof_sameTemplatePrefix_witnessedTail_transport
      M hPA translation baseWitnessList baseContext
      extendedWitnessList extendedContext
      coqDynamicTruthPredecessorStateTemplateContext
      (rawDynamicTruthLocalAtomicAdequacyCode M) atomicRoot
      hbase hextended hincluded hatomicTemplate)
    as [transportedAtomicRoot htransportedAtomic].
  assert (htransportedAtomicJoint : RawCodedPALocalProofOf M
      (rawDynamicTruthPredecessorJointStateContext M extendedContext)
      (rawDynamicTruthLocalAtomicAdequacyCode M)
      transportedAtomicRoot).
  {
    rewrite <- (raw_dynamicTruthPredecessorStateTemplateContextCode
      M translation hagreement extendedContext).
    exact htransportedAtomic.
  }
  assert (hdomainTemplate : RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation baseContext
        coqDynamicTruthPredecessorStateTemplateContext)
      (rawFormulaOrCode M sigmaDomain piDomain) domainRoot).
  {
    rewrite (raw_dynamicTruthPredecessorStateTemplateContextCode
      M translation hagreement baseContext).
    exact hdomain.
  }
  destruct
    (raw_codedPALocalProof_sameTemplatePrefix_witnessedTail_transport
      M hPA translation baseWitnessList baseContext
      extendedWitnessList extendedContext
      coqDynamicTruthPredecessorStateTemplateContext
      (rawFormulaOrCode M sigmaDomain piDomain) domainRoot
      hbase hextended hincluded hdomainTemplate)
    as [transportedDomainRoot htransportedDomain].
  assert (htransportedDomainJoint : RawCodedPALocalProofOf M
      (rawDynamicTruthPredecessorJointStateContext M extendedContext)
      (rawFormulaOrCode M sigmaDomain piDomain)
      transportedDomainRoot).
  {
    rewrite <- (raw_dynamicTruthPredecessorStateTemplateContextCode
      M translation hagreement extendedContext).
    exact htransportedDomain.
  }
  assert (hcomponents : RawDynamicTruthLocalAdmissibilityComponentsAt M
      (rawDynamicTruthPredecessorJointStateContext M extendedContext)
      sigmaDomain piDomain).
  {
    constructor.
    - exists transportedAtomicRoot. exact htransportedAtomicJoint.
    - exists assignmentRoot. exact hassignment.
    - exists transportedDomainRoot. exact htransportedDomainJoint.
  }
  destruct
    (raw_codedPALocalProofOf_dynamicTruthLocalAdmissible_of_components
      M hPA (rawDynamicTruthPredecessorJointStateContext M extendedContext)
      sigmaDomain piDomain hcomponents)
    as [admissibleRoot hadmissible].
  exists witnesses, admissibleRoot. split; assumption.
Qed.

End
  PABoundedRawCodedDynamicTruthPredecessorAdmissibilityAssignmentCompilation.
