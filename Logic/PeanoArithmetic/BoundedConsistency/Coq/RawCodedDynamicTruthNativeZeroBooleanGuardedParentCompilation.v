(**
  Prefix-generic parent roots for guarded Boolean predecessors.

  The first guarded endpoint compiler was specialized to the implication
  branch prefix.  Its arithmetic content, however, only depends on the two
  assumptions already present in the surrounding strong-step rule case.
  The five newly opened binders may be preceded by any atomically adequate
  fixed prefix.  Factoring that observation here avoids copying the endpoint
  compilers for conjunction and disjunction and, more importantly, keeps the
  real caller assumptions visible instead of pretending that the caller
  prefix is empty.

  The second half of the module inserts the normalized rank-zero local-
  exclusivity source under the same Boolean prefix.  The resulting parent
  package contains exactly the first three fields needed by the guarded
  Boolean diagonal compiler; selected Sigma/Pi evidence is intentionally
  left to the append-row producer.
*)

From Stdlib Require Import List.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedContextLists
  RawCodedRestrictedPAProof
  RawCodedRestrictedPAConsistencyFromUniversalSoundness
  RawCodedPALocalProofExistential
  RawCodedPALocalProofExistentialEliminationChain
  RawCodedPALocalProofUniversalIntroductionChain
  RawCodedPALocalProofWitnessedContextMerge
  RawCodedTemplateSyntax
  RawCodedTemplateProofCompiler
  RawCodedTemplateProofCompilerSelfShiftTail
  RawCodedTemplateLocalProofWitnessedTailTransport
  RawCodedLtSuccCasesProofCompilation
  RawCodedPAGrowingTemplateConjunction
  RawCodedTemplateDirectStructuralTranslation
  RawCodedTemplateDirectStructuralPAAgreement
  RawCodedDynamicTruthLocalFieldProjectionCompilation
  RawCodedDynamicTruthNativeLocalPositiveGraph
  RawCodedDynamicTruthLocalExclusiveTemplateDirectInputs
  RawCodedDynamicTruthPredecessorStateExclusivityCompilation
  RawCodedDynamicTruthPredecessorGlobalExistentialElimination
  RawCodedDynamicTruthImpGuardedPredecessorExclusivityCompilation
  RawCodedDynamicTruthZeroLocalExclusiveTemplateIdentification
  RawCodedDynamicTruthNativeZeroPredecessorLogicalRootsCompilation
  RawCodedDynamicTruthNativeZeroGuardedNormalization
  RawCodedStrongStepProofEndpointAtomicAdequacyProofCompilation
  RawCodedProofEndpointQuantifierBoundedProofCompilation
  RawCodedStrongStepProofEndpointQuantifierBoundedProofCompilation
  RawCodedStrongStepProofEndpointEvidenceCompilation
  RawCodedDynamicTruthNativeZeroGuardedPredecessorCompilation
  RawCodedDynamicTruthBooleanGuardedBranchExclusivity
  RawCodedDynamicTruthBooleanDirectChildAdmissibilityProofCompilation
  RawCodedDynamicTruthBooleanGuardedDiagonalCompilation.

Module
  PABoundedRawCodedDynamicTruthNativeZeroBooleanGuardedParentCompilation.

Import ListNotations.
Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedContextLists.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedRestrictedPAConsistencyFromUniversalSoundness.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPALocalProofExistentialEliminationChain.
Import PABoundedRawCodedPALocalProofUniversalIntroductionChain.
Import PABoundedRawCodedPALocalProofWitnessedContextMerge.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedTemplateProofCompilerSelfShiftTail.
Import PABoundedRawCodedTemplateLocalProofWitnessedTailTransport.
Import PABoundedRawCodedLtSuccCasesProofCompilation.
Import PABoundedRawCodedPAGrowingTemplateConjunction.
Import PABoundedRawCodedTemplateDirectStructuralTranslation.
Import PABoundedRawCodedTemplateDirectStructuralPAAgreement.
Import PABoundedRawCodedDynamicTruthLocalFieldProjectionCompilation.
Import PABoundedRawCodedDynamicTruthNativeLocalPositiveGraph.
Import PABoundedRawCodedDynamicTruthLocalExclusiveTemplateDirectInputs.
Import PABoundedRawCodedDynamicTruthPredecessorStateExclusivityCompilation.
Import
  PABoundedRawCodedDynamicTruthPredecessorGlobalExistentialElimination.
Import
  PABoundedRawCodedDynamicTruthImpGuardedPredecessorExclusivityCompilation.
Import
  PABoundedRawCodedDynamicTruthZeroLocalExclusiveTemplateIdentification.
Import
  PABoundedRawCodedDynamicTruthNativeZeroPredecessorLogicalRootsCompilation.
Import PABoundedRawCodedDynamicTruthNativeZeroGuardedNormalization.
Import PABoundedRawCodedStrongStepProofEndpointAtomicAdequacyProofCompilation.
Import PABoundedRawCodedProofEndpointQuantifierBoundedProofCompilation.
Import
  PABoundedRawCodedStrongStepProofEndpointQuantifierBoundedProofCompilation.
Import PABoundedRawCodedStrongStepProofEndpointEvidenceCompilation.
Import
  PABoundedRawCodedDynamicTruthNativeZeroGuardedPredecessorCompilation.
Import PABoundedRawCodedDynamicTruthBooleanGuardedBranchExclusivity.
Import
  PABoundedRawCodedDynamicTruthBooleanDirectChildAdmissibilityProofCompilation.
Import PABoundedRawCodedDynamicTruthBooleanGuardedDiagonalCompilation.

(** The constructor-specific fixed prefix consists of the direct-child and
    shape guards followed by the two predecessor-state assumptions.  The
    caller is shifted through all five variables opened by those layers. *)
Definition coqDynamicTruthBooleanGuardedFixedDeepPrefix
    (constructor : DynamicTruthBooleanConstructor) : TemplateContext :=
  [coqDynamicTruthBooleanGuardedDirectChildTemplate constructor;
   coqDynamicTruthBooleanGuardedShapeTemplate constructor] ++
  templateContextShiftMany 2
    coqDynamicTruthPredecessorStateTemplateContext.

Lemma coqDynamicTruthBooleanGuardedDeepPrefix_split : forall
    constructor callerPrefix,
  coqDynamicTruthBooleanGuardedDeepPrefix constructor callerPrefix =
  coqDynamicTruthBooleanGuardedFixedDeepPrefix constructor ++
    templateContextShiftMany 5 callerPrefix.
Proof.
  intros constructor callerPrefix.
  unfold coqDynamicTruthBooleanGuardedDeepPrefix,
    coqDynamicTruthBooleanGuardedFixedDeepPrefix.
  cbn [templateContextShiftMany templateContextShift
    templateContextRename].
  reflexivity.
Qed.

(** Endpoint evidence after five binders can be retained under an arbitrary
    fixed prefix.  This is the connective-independent core that had
    previously been embedded in the implication specialization. *)
Theorem
    raw_guardedParentEndpointShift5Roots_under_fixed_prefix_of_template_assumptions :
    forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
      (inputs : RawCodedTemplateDirectStructuralInputs M)
      baseWitnessList baseContext callerPrefix fixedPrefix,
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
        (fixedPrefix ++ templateContextShiftMany 5 callerPrefix))
      (rawDirectTemplateFormula inputs
        (templateFormulaRename (templateShiftRenamingMany 5)
          coqStrongStepProofEndpointAtomicAdequacyConclusion)) atomicRoot /\
    RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        targetContext
        (fixedPrefix ++ templateContextShiftMany 5 callerPrefix))
      (rawDirectTemplateFormula inputs
        (templateFormulaRename (templateShiftRenamingMany 5)
          coqStrongStepProofEndpointQuantifierBoundedConclusion)) domainRoot.
Proof.
  intros M hPA inputs baseWitnessList baseContext callerPrefix fixedPrefix
    hbase hrestrictedIn hruleIn.
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
    fixedPrefix
    (rawDirectTemplateFormula inputs
      (templateFormulaRename (templateShiftRenamingMany 5)
        coqStrongStepProofEndpointAtomicAdequacyConclusion))
    atomicRoot hshiftedRealizable
    (raw_guardedDirectStructuralTemplatePrefix_atomically_adequate
      M hPA inputs fixedPrefix)
    hatomic) as [atomicDeepRoot hatomicDeep].
  destruct (raw_codedPALocalProof_templatePrefix M hPA translation
    (rawTemplateContextCodeOnTail translation targetContext shiftedCaller)
    fixedPrefix
    (rawDirectTemplateFormula inputs
      (templateFormulaRename (templateShiftRenamingMany 5)
        coqStrongStepProofEndpointQuantifierBoundedConclusion))
    domainRoot hshiftedRealizable
    (raw_guardedDirectStructuralTemplatePrefix_atomically_adequate
      M hPA inputs fixedPrefix)
    hdomain) as [domainDeepRoot hdomainDeep].
  assert (hcontext :
      rawTemplateContextCodeOnTail translation targetContext
        (fixedPrefix ++ shiftedCaller) =
      rawTemplateContextCodeOnTail translation
        (rawTemplateContextCodeOnTail translation targetContext
          shiftedCaller) fixedPrefix).
  {
    apply rawTemplateContextCodeOnTail_app_finite.
  }
  assert (hatomicFinal : RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation targetContext
        (fixedPrefix ++ shiftedCaller))
      (rawDirectTemplateFormula inputs
        (templateFormulaRename (templateShiftRenamingMany 5)
          coqStrongStepProofEndpointAtomicAdequacyConclusion))
      atomicDeepRoot).
  {
    rewrite hcontext. exact hatomicDeep.
  }
  assert (hdomainFinal : RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation targetContext
        (fixedPrefix ++ shiftedCaller))
      (rawDirectTemplateFormula inputs
        (templateFormulaRename (templateShiftRenamingMany 5)
          coqStrongStepProofEndpointQuantifierBoundedConclusion))
      domainDeepRoot).
  {
    rewrite hcontext. exact hdomainDeep.
  }
  exists targetWitnessList, targetContext, atomicDeepRoot, domainDeepRoot.
  split; [exact htarget |].
  split; [exact hincluded |].
  unfold translation, shiftedCaller in hatomicFinal, hdomainFinal.
  split; assumption.
Qed.

(** Proof-root counterpart of the preceding endpoint assembly.  The two
    shell premises have already been renamed through the five constructor
    binders and proved under an arbitrary adequate prefix.  Their endpoint
    laws may grow independent finite PA witness tails; the synchronized
    renaming-natural compiler merges those tails internally. *)
Theorem
    raw_guardedParentEndpointShift5Roots_under_prefix_of_renamed_roots :
    forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
      (inputs : RawCodedTemplateDirectStructuralInputs M)
      baseWitnessList baseContext prefix restrictedRoot ruleRoot,
  RawCodedTemplatePrefixAtomicallyAdequate M
    (rawDirectStructuralTemplateTranslation M hPA inputs) prefix ->
  RawCodedPAAxiomWitnessContext M baseWitnessList baseContext ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail
      (rawDirectStructuralTemplateTranslation M hPA inputs)
      baseContext prefix)
    (rawDirectTemplateFormula inputs
      (templateFormulaRename (templateShiftRenamingMany 5)
        coqRestrictedPADerivationSoundnessRestrictedProofTemplate))
    restrictedRoot ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail
      (rawDirectStructuralTemplateTranslation M hPA inputs)
      baseContext prefix)
    (rawDirectTemplateFormula inputs
      (templateFormulaRename (templateShiftRenamingMany 5)
        coqStrongStepProofEndpointAtomicAdequacyRulePremise))
    ruleRoot ->
  exists targetWitnessList targetContext atomicRoot domainRoot,
    RawCodedPAAxiomWitnessContext M targetWitnessList targetContext /\
    RawContextListIncluded M baseContext targetContext /\
    RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        targetContext prefix)
      (rawDirectTemplateFormula inputs
        (templateFormulaRename (templateShiftRenamingMany 5)
          coqStrongStepProofEndpointAtomicAdequacyConclusion)) atomicRoot /\
    RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        targetContext prefix)
      (rawDirectTemplateFormula inputs
        (templateFormulaRename (templateShiftRenamingMany 5)
          coqStrongStepProofEndpointQuantifierBoundedConclusion)) domainRoot.
Proof.
  intros M hPA inputs baseWitnessList baseContext prefix
    restrictedRoot ruleRoot hprefix hbase hrestricted hrule.
  exact
    (raw_codedPALocalProof_strongStepEndpointEvidence_renamed_of_restricted_and_rule_roots_on_witnessed_tail_under_prefix
      M hPA inputs (templateShiftRenamingMany 5)
      baseWitnessList baseContext prefix restrictedRoot ruleRoot
      hprefix hbase hrestricted hrule).
Qed.

(** The Boolean parent formulas are the implication parent formulas at the
    same coordinates.  Only the two guard assumptions in the context differ. *)
Theorem raw_dynamicTruthBooleanGuardedParentEndpointRoots_of_template_assumptions :
    forall constructor (M : RawPAModel) (hPA : RawPASatisfies M), forall
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
        (coqDynamicTruthBooleanGuardedDeepPrefix constructor callerPrefix))
      (rawDirectTemplateFormula inputs
        (coqDynamicTruthBooleanDirectChildAtomicPremiseTemplate constructor
          coqDynamicTruthBooleanGuardedLevelTerm
          coqDynamicTruthBooleanGuardedParentTerm
          coqDynamicTruthBooleanGuardedLeftTerm
          coqDynamicTruthBooleanGuardedRightTerm
          coqDynamicTruthBooleanGuardedChildTerm)) atomicRoot /\
    RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        targetContext
        (coqDynamicTruthBooleanGuardedDeepPrefix constructor callerPrefix))
      (rawDirectTemplateFormula inputs
        (coqDynamicTruthBooleanDirectChildDomainPremiseTemplate constructor
          coqDynamicTruthBooleanGuardedLevelTerm
          coqDynamicTruthBooleanGuardedParentTerm
          coqDynamicTruthBooleanGuardedLeftTerm
          coqDynamicTruthBooleanGuardedRightTerm
          coqDynamicTruthBooleanGuardedChildTerm)) domainRoot.
Proof.
  intros constructor M hPA inputs sigmaDomain piDomain sigmaEvidence
    piEvidence baseWitnessList baseContext callerPrefix hidentification
    hbase hrestrictedIn hruleIn.
  destruct
    (raw_guardedParentEndpointShift5Roots_under_fixed_prefix_of_template_assumptions
      M hPA inputs baseWitnessList baseContext callerPrefix
      (coqDynamicTruthBooleanGuardedFixedDeepPrefix constructor)
      hbase hrestrictedIn hruleIn)
    as (targetWitnessList & targetContext & atomicRoot & domainRoot &
      htarget & hincluded & hatomic & hdomain).
  rewrite <- coqDynamicTruthBooleanGuardedDeepPrefix_split
    in hatomic, hdomain.
  rewrite
    (coqDynamicTruthBooleanDirectChildAtomicPremiseTemplate_eq_imp
      constructor
      coqDynamicTruthBooleanGuardedLevelTerm
      coqDynamicTruthBooleanGuardedParentTerm
      coqDynamicTruthBooleanGuardedLeftTerm
      coqDynamicTruthBooleanGuardedRightTerm
      coqDynamicTruthBooleanGuardedChildTerm).
  unfold coqDynamicTruthBooleanGuardedLevelTerm,
    coqDynamicTruthBooleanGuardedParentTerm,
    coqDynamicTruthBooleanGuardedLeftTerm,
    coqDynamicTruthBooleanGuardedRightTerm,
    coqDynamicTruthBooleanGuardedChildTerm.
  rewrite coqDynamicTruthImpGuardedParentAtomicTemplate_eq_endpoint_shift5.
  exists targetWitnessList, targetContext, atomicRoot, domainRoot.
  split; [exact htarget |].
  split; [exact hincluded |].
  split; [exact hatomic |].
  rewrite
    (coqDynamicTruthBooleanDirectChildDomainPremiseTemplate_eq_imp
      constructor
      coqDynamicTruthImpGuardedLevelTerm
      coqDynamicTruthImpGuardedParentTerm
      coqDynamicTruthImpGuardedLeftTerm
      coqDynamicTruthImpGuardedRightTerm
      coqDynamicTruthImpGuardedChildTerm).
  rewrite
    (raw_coqDynamicTruthImpGuardedParentDomain_eq_endpoint_shift5
      M inputs sigmaDomain piDomain sigmaEvidence piEvidence
      hidentification).
  exact hdomain.
Qed.

(** Boolean specialization of the renamed proof-root endpoint.  Unlike the
    assumption-membership wrapper, this theorem remains valid after the
    surrounding direct shell has projected and transported its premise roots
    through the five constructor binders. *)
Theorem
    raw_dynamicTruthBooleanGuardedParentEndpointRoots_of_renamed_restricted_and_rule_roots :
    forall constructor (M : RawPAModel) (hPA : RawPASatisfies M), forall
      (inputs : RawCodedTemplateDirectStructuralInputs M)
      sigmaDomain piDomain sigmaEvidence piEvidence
      baseWitnessList baseContext callerPrefix restrictedRoot ruleRoot,
  RawCoqDynamicTruthLocalExclusiveTemplateIdentification M inputs
    sigmaDomain piDomain sigmaEvidence piEvidence ->
  RawCodedPAAxiomWitnessContext M baseWitnessList baseContext ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail
      (rawDirectStructuralTemplateTranslation M hPA inputs)
      baseContext
      (coqDynamicTruthBooleanGuardedDeepPrefix constructor callerPrefix))
    (rawDirectTemplateFormula inputs
      (templateFormulaRename (templateShiftRenamingMany 5)
        coqRestrictedPADerivationSoundnessRestrictedProofTemplate))
    restrictedRoot ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail
      (rawDirectStructuralTemplateTranslation M hPA inputs)
      baseContext
      (coqDynamicTruthBooleanGuardedDeepPrefix constructor callerPrefix))
    (rawDirectTemplateFormula inputs
      (templateFormulaRename (templateShiftRenamingMany 5)
        coqStrongStepProofEndpointAtomicAdequacyRulePremise))
    ruleRoot ->
  exists targetWitnessList targetContext atomicRoot domainRoot,
    RawCodedPAAxiomWitnessContext M targetWitnessList targetContext /\
    RawContextListIncluded M baseContext targetContext /\
    RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        targetContext
        (coqDynamicTruthBooleanGuardedDeepPrefix constructor callerPrefix))
      (rawDirectTemplateFormula inputs
        (coqDynamicTruthBooleanDirectChildAtomicPremiseTemplate constructor
          coqDynamicTruthBooleanGuardedLevelTerm
          coqDynamicTruthBooleanGuardedParentTerm
          coqDynamicTruthBooleanGuardedLeftTerm
          coqDynamicTruthBooleanGuardedRightTerm
          coqDynamicTruthBooleanGuardedChildTerm)) atomicRoot /\
    RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        targetContext
        (coqDynamicTruthBooleanGuardedDeepPrefix constructor callerPrefix))
      (rawDirectTemplateFormula inputs
        (coqDynamicTruthBooleanDirectChildDomainPremiseTemplate constructor
          coqDynamicTruthBooleanGuardedLevelTerm
          coqDynamicTruthBooleanGuardedParentTerm
          coqDynamicTruthBooleanGuardedLeftTerm
          coqDynamicTruthBooleanGuardedRightTerm
          coqDynamicTruthBooleanGuardedChildTerm)) domainRoot.
Proof.
  intros constructor M hPA inputs sigmaDomain piDomain sigmaEvidence
    piEvidence baseWitnessList baseContext callerPrefix restrictedRoot ruleRoot
    hidentification hbase hrestricted hrule.
  destruct
    (raw_guardedParentEndpointShift5Roots_under_prefix_of_renamed_roots
      M hPA inputs baseWitnessList baseContext
      (coqDynamicTruthBooleanGuardedDeepPrefix constructor callerPrefix)
      restrictedRoot ruleRoot
      (raw_guardedDirectStructuralTemplatePrefix_atomically_adequate
        M hPA inputs
        (coqDynamicTruthBooleanGuardedDeepPrefix constructor callerPrefix))
      hbase hrestricted hrule) as
    (targetWitnessList & targetContext & atomicRoot & domainRoot &
      htarget & hincluded & hatomic & hdomain).
  rewrite
    (coqDynamicTruthBooleanDirectChildAtomicPremiseTemplate_eq_imp
      constructor
      coqDynamicTruthBooleanGuardedLevelTerm
      coqDynamicTruthBooleanGuardedParentTerm
      coqDynamicTruthBooleanGuardedLeftTerm
      coqDynamicTruthBooleanGuardedRightTerm
      coqDynamicTruthBooleanGuardedChildTerm).
  unfold coqDynamicTruthBooleanGuardedLevelTerm,
    coqDynamicTruthBooleanGuardedParentTerm,
    coqDynamicTruthBooleanGuardedLeftTerm,
    coqDynamicTruthBooleanGuardedRightTerm,
    coqDynamicTruthBooleanGuardedChildTerm.
  rewrite coqDynamicTruthImpGuardedParentAtomicTemplate_eq_endpoint_shift5.
  exists targetWitnessList, targetContext, atomicRoot, domainRoot.
  split; [exact htarget |].
  split; [exact hincluded |].
  split; [exact hatomic |].
  rewrite
    (coqDynamicTruthBooleanDirectChildDomainPremiseTemplate_eq_imp
      constructor
      coqDynamicTruthImpGuardedLevelTerm
      coqDynamicTruthImpGuardedParentTerm
      coqDynamicTruthImpGuardedLeftTerm
      coqDynamicTruthImpGuardedRightTerm
      coqDynamicTruthImpGuardedChildTerm).
  rewrite
    (raw_coqDynamicTruthImpGuardedParentDomain_eq_endpoint_shift5
      M inputs sigmaDomain piDomain sigmaEvidence piEvidence
      hidentification).
  exact hdomain.
Qed.

(** Prefix-parametric form of the normalized local-exclusivity projection.
    The proof uses no assumption from [prefix]; adequate-cons insertion is
    therefore the exact structural operation. *)
Theorem raw_dynamicTruthGuardedBranchSource_of_zero_normalized_under_prefix :
    forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
      (inputs : RawCodedTemplateDirectStructuralInputs M)
      normalizedTranslation witnessList baseContext helperRoots prefix,
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
        baseContext prefix)
      (rawTemplateFormula
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        (tfAll (tfAll (tfAll
          coqDynamicTruthLocalExclusiveBodyTemplate)))) sourceRoot.
Proof.
  intros M hPA inputs normalizedTranslation witnessList baseContext
    helperRoots prefix hidentification hnormalized.
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
    baseContext prefix
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
    (raw_guardedDirectStructuralTemplatePrefix_atomically_adequate
      M hPA inputs prefix)
    hexclusive) as [sourceRoot hsource].
  exists sourceRoot. rewrite hsourceCode. exact hsource.
Qed.

(** Parent-only Boolean package, separated from the two selected evidence
    roots so each producer may grow its witnessed tail independently. *)
Record RawDynamicTruthBooleanGuardedParentBranchRootsAt
    (constructor : DynamicTruthBooleanConstructor)
    (M : RawPAModel) (translation : RawCodedTemplateTranslation M)
    (baseContext : M) (callerPrefix : TemplateContext) : Prop := {
  rawDynamicTruthBooleanGuardedParent_source : exists sourceRoot,
    RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation baseContext
        (coqDynamicTruthBooleanGuardedDeepPrefix
          constructor callerPrefix))
      (rawTemplateFormula translation
        (tfAll (tfAll (tfAll
          coqDynamicTruthLocalExclusiveBodyTemplate)))) sourceRoot;
  rawDynamicTruthBooleanGuardedParent_atomic : exists atomicRoot,
    RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation baseContext
        (coqDynamicTruthBooleanGuardedDeepPrefix
          constructor callerPrefix))
      (rawTemplateFormula translation
        (coqDynamicTruthBooleanDirectChildAtomicPremiseTemplate constructor
          coqDynamicTruthBooleanGuardedLevelTerm
          coqDynamicTruthBooleanGuardedParentTerm
          coqDynamicTruthBooleanGuardedLeftTerm
          coqDynamicTruthBooleanGuardedRightTerm
          coqDynamicTruthBooleanGuardedChildTerm)) atomicRoot;
  rawDynamicTruthBooleanGuardedParent_domain : exists domainRoot,
    RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation baseContext
        (coqDynamicTruthBooleanGuardedDeepPrefix
          constructor callerPrefix))
      (rawTemplateFormula translation
        (coqDynamicTruthBooleanDirectChildDomainPremiseTemplate constructor
          coqDynamicTruthBooleanGuardedLevelTerm
          coqDynamicTruthBooleanGuardedParentTerm
          coqDynamicTruthBooleanGuardedLeftTerm
          coqDynamicTruthBooleanGuardedRightTerm
          coqDynamicTruthBooleanGuardedChildTerm)) domainRoot
}.

Arguments RawDynamicTruthBooleanGuardedParentBranchRootsAt
  constructor M translation baseContext callerPrefix : clear implicits.

(** Join a local-exclusive source already proved on one witnessed PA tail
    with renamed restricted/rule roots proved on a possibly larger tail.
    Endpoint compilation may itself select further finite PA witnesses; the
    source is transported only once, directly to that final tail.  Factoring
    this asymmetric merge keeps both the fixed-root and independently growing
    clients free of duplicated context bookkeeping. *)
Theorem
    raw_dynamicTruthBooleanGuardedParentBranchRoots_of_source_and_renamed_roots_on_witnessed_extension :
    forall constructor (M : RawPAModel) (hPA : RawPASatisfies M), forall
      (inputs : RawCodedTemplateDirectStructuralInputs M)
      sigmaDomain piDomain sigmaEvidence piEvidence
      sourceWitnessList sourceContext endpointWitnessList endpointContext
      callerPrefix sourceRoot restrictedRoot ruleRoot,
  RawCoqDynamicTruthLocalExclusiveTemplateIdentification M inputs
    sigmaDomain piDomain sigmaEvidence piEvidence ->
  RawCodedPAAxiomWitnessContext M sourceWitnessList sourceContext ->
  RawCodedPAAxiomWitnessContext M endpointWitnessList endpointContext ->
  RawContextListIncluded M sourceContext endpointContext ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail
      (rawDirectStructuralTemplateTranslation M hPA inputs)
      sourceContext
      (coqDynamicTruthBooleanGuardedDeepPrefix constructor callerPrefix))
    (rawTemplateFormula
      (rawDirectStructuralTemplateTranslation M hPA inputs)
      (tfAll (tfAll (tfAll coqDynamicTruthLocalExclusiveBodyTemplate))))
    sourceRoot ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail
      (rawDirectStructuralTemplateTranslation M hPA inputs)
      endpointContext
      (coqDynamicTruthBooleanGuardedDeepPrefix constructor callerPrefix))
    (rawDirectTemplateFormula inputs
      (templateFormulaRename (templateShiftRenamingMany 5)
        coqRestrictedPADerivationSoundnessRestrictedProofTemplate))
    restrictedRoot ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail
      (rawDirectStructuralTemplateTranslation M hPA inputs)
      endpointContext
      (coqDynamicTruthBooleanGuardedDeepPrefix constructor callerPrefix))
    (rawDirectTemplateFormula inputs
      (templateFormulaRename (templateShiftRenamingMany 5)
        coqStrongStepProofEndpointAtomicAdequacyRulePremise))
    ruleRoot ->
  exists targetWitnessList targetContext,
    RawCodedPAAxiomWitnessContext M targetWitnessList targetContext /\
    RawContextListIncluded M sourceContext targetContext /\
    RawDynamicTruthBooleanGuardedParentBranchRootsAt constructor M
      (rawDirectStructuralTemplateTranslation M hPA inputs)
      targetContext callerPrefix.
Proof.
  intros constructor M hPA inputs sigmaDomain piDomain sigmaEvidence
    piEvidence sourceWitnessList sourceContext endpointWitnessList
    endpointContext callerPrefix sourceRoot restrictedRoot ruleRoot
    hidentification hsourceWitnessed hendpointWitnessed
    hsourceEndpointIncluded hsource hrestricted hrule.
  destruct
    (raw_dynamicTruthBooleanGuardedParentEndpointRoots_of_renamed_restricted_and_rule_roots
      constructor M hPA inputs sigmaDomain piDomain sigmaEvidence piEvidence
      endpointWitnessList endpointContext callerPrefix restrictedRoot ruleRoot
      hidentification hendpointWitnessed hrestricted hrule) as
    (targetWitnessList & targetContext & atomicRoot & domainRoot &
      htargetWitnessed & hendpointTargetIncluded & hatomic & hdomain).
  assert (hsourceTargetIncluded :
      RawContextListIncluded M sourceContext targetContext).
  {
    intros member hmember.
    exact (hendpointTargetIncluded member
      (hsourceEndpointIncluded member hmember)).
  }
  destruct
    (raw_codedPALocalProof_sameTemplatePrefix_witnessedTail_transport
      M hPA (rawDirectStructuralTemplateTranslation M hPA inputs)
      sourceWitnessList sourceContext targetWitnessList targetContext
      (coqDynamicTruthBooleanGuardedDeepPrefix constructor callerPrefix)
      (rawTemplateFormula
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        (tfAll (tfAll (tfAll coqDynamicTruthLocalExclusiveBodyTemplate))))
      sourceRoot hsourceWitnessed htargetWitnessed hsourceTargetIncluded
      hsource) as [transportedSourceRoot htransportedSource].
  exists targetWitnessList, targetContext.
  split; [exact htargetWitnessed |].
  split; [exact hsourceTargetIncluded |].
  constructor.
  - exists transportedSourceRoot. exact htransportedSource.
  - exists atomicRoot. exact hatomic.
  - exists domainRoot. exact hdomain.
Qed.

(** Fixed-root normalized wrapper.  The renamed premise roots may be live
    below any caller prefix; no membership assumption or empty-prefix
    specialization is required. *)
Theorem
    raw_dynamicTruthBooleanGuardedParentBranchRoots_of_zero_normalized_selected_identification_and_renamed_roots :
    forall constructor (M : RawPAModel) (hPA : RawPASatisfies M), forall
      inputs normalizedTranslation witnessList baseContext helperRoots
      callerPrefix restrictedRoot ruleRoot,
  RawCoqDynamicTruthLocalExclusiveTemplateIdentification M inputs
    (rawDynamicTruthZeroSigmaDomainCode M)
    (rawDynamicTruthZeroPiDomainCode M)
    (rawDynamicTruthZeroSigmaEvidenceCode M)
    (rawDynamicTruthZeroPiEvidenceCode M) ->
  RawDynamicTruthNativeLocalZeroGuardedNormalizedResourcesAt M
    normalizedTranslation witnessList baseContext helperRoots ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail
      (rawDirectStructuralTemplateTranslation M hPA inputs)
      baseContext
      (coqDynamicTruthBooleanGuardedDeepPrefix constructor callerPrefix))
    (rawDirectTemplateFormula inputs
      (templateFormulaRename (templateShiftRenamingMany 5)
        coqRestrictedPADerivationSoundnessRestrictedProofTemplate))
    restrictedRoot ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail
      (rawDirectStructuralTemplateTranslation M hPA inputs)
      baseContext
      (coqDynamicTruthBooleanGuardedDeepPrefix constructor callerPrefix))
    (rawDirectTemplateFormula inputs
      (templateFormulaRename (templateShiftRenamingMany 5)
        coqStrongStepProofEndpointAtomicAdequacyRulePremise))
    ruleRoot ->
  exists targetWitnessList targetContext,
    RawCodedPAAxiomWitnessContext M targetWitnessList targetContext /\
    RawContextListIncluded M baseContext targetContext /\
    RawDynamicTruthBooleanGuardedParentBranchRootsAt constructor M
      (rawDirectStructuralTemplateTranslation M hPA inputs)
      targetContext callerPrefix.
Proof.
  intros constructor M hPA inputs normalizedTranslation witnessList
    baseContext helperRoots callerPrefix restrictedRoot ruleRoot
    hidentification hnormalized hrestricted hrule.
  destruct (rawDynamicTruthNativeLocalZeroGuardedNormalized_fields
    M normalizedTranslation witnessList baseContext helperRoots hnormalized)
    as [hbaseWitnessed _].
  destruct
    (raw_dynamicTruthGuardedBranchSource_of_zero_normalized_under_prefix
      M hPA inputs normalizedTranslation witnessList baseContext helperRoots
      (coqDynamicTruthBooleanGuardedDeepPrefix constructor callerPrefix)
      hidentification hnormalized) as [sourceRoot hsource].
  exact
    (raw_dynamicTruthBooleanGuardedParentBranchRoots_of_source_and_renamed_roots_on_witnessed_extension
      constructor M hPA inputs
      (rawDynamicTruthZeroSigmaDomainCode M)
      (rawDynamicTruthZeroPiDomainCode M)
      (rawDynamicTruthZeroSigmaEvidenceCode M)
      (rawDynamicTruthZeroPiEvidenceCode M)
      witnessList baseContext witnessList baseContext callerPrefix
      sourceRoot restrictedRoot ruleRoot hidentification hbaseWitnessed
      hbaseWitnessed (fun member hmember => hmember)
      hsource hrestricted hrule).
Qed.

(** Growing-root normalized wrapper.  Restricted-proof projection and rule
    compilation are independent computations and may append different finite
    PA witness batches.  Their pair is synchronized beneath the unchanged
    five-binder Boolean prefix before endpoint compilation. *)
Theorem
    raw_dynamicTruthBooleanGuardedParentBranchRoots_of_zero_normalized_selected_identification_and_independently_growing_renamed_roots :
    forall constructor (M : RawPAModel) (hPA : RawPASatisfies M), forall
      inputs normalizedTranslation witnessList baseContext helperRoots
      callerPrefix,
  RawCoqDynamicTruthLocalExclusiveTemplateIdentification M inputs
    (rawDynamicTruthZeroSigmaDomainCode M)
    (rawDynamicTruthZeroPiDomainCode M)
    (rawDynamicTruthZeroSigmaEvidenceCode M)
    (rawDynamicTruthZeroPiEvidenceCode M) ->
  RawDynamicTruthNativeLocalZeroGuardedNormalizedResourcesAt M
    normalizedTranslation witnessList baseContext helperRoots ->
  RawCodedPAGrowingTemplateLocalProofAt M
    (rawDirectStructuralTemplateTranslation M hPA inputs)
    witnessList baseContext
    (coqDynamicTruthBooleanGuardedDeepPrefix constructor callerPrefix)
    (rawDirectTemplateFormula inputs
      (templateFormulaRename (templateShiftRenamingMany 5)
        coqRestrictedPADerivationSoundnessRestrictedProofTemplate)) ->
  RawCodedPAGrowingTemplateLocalProofAt M
    (rawDirectStructuralTemplateTranslation M hPA inputs)
    witnessList baseContext
    (coqDynamicTruthBooleanGuardedDeepPrefix constructor callerPrefix)
    (rawDirectTemplateFormula inputs
      (templateFormulaRename (templateShiftRenamingMany 5)
        coqStrongStepProofEndpointAtomicAdequacyRulePremise)) ->
  exists targetWitnessList targetContext,
    RawCodedPAAxiomWitnessContext M targetWitnessList targetContext /\
    RawContextListIncluded M baseContext targetContext /\
    RawDynamicTruthBooleanGuardedParentBranchRootsAt constructor M
      (rawDirectStructuralTemplateTranslation M hPA inputs)
      targetContext callerPrefix.
Proof.
  intros constructor M hPA inputs normalizedTranslation witnessList
    baseContext helperRoots callerPrefix hidentification hnormalized
    hrestrictedGrowing hruleGrowing.
  destruct (rawDynamicTruthNativeLocalZeroGuardedNormalized_fields
    M normalizedTranslation witnessList baseContext helperRoots hnormalized)
    as [hbaseWitnessed _].
  destruct
    (raw_dynamicTruthGuardedBranchSource_of_zero_normalized_under_prefix
      M hPA inputs normalizedTranslation witnessList baseContext helperRoots
      (coqDynamicTruthBooleanGuardedDeepPrefix constructor callerPrefix)
      hidentification hnormalized) as [sourceRoot hsource].
  destruct
    (raw_codedPAGrowingTemplateLocalProofAt_pair_at_prefix
      M hPA (rawDirectStructuralTemplateTranslation M hPA inputs)
      witnessList baseContext
      (coqDynamicTruthBooleanGuardedDeepPrefix constructor callerPrefix)
      (rawDirectTemplateFormula inputs
        (templateFormulaRename (templateShiftRenamingMany 5)
          coqRestrictedPADerivationSoundnessRestrictedProofTemplate))
      (rawDirectTemplateFormula inputs
        (templateFormulaRename (templateShiftRenamingMany 5)
          coqStrongStepProofEndpointAtomicAdequacyRulePremise))
      hrestrictedGrowing hruleGrowing) as
    (endpointWitnessList & endpointContext & restrictedRoot & ruleRoot &
      hendpointWitnessed & hbaseEndpointIncluded & hrestricted & hrule).
  exact
    (raw_dynamicTruthBooleanGuardedParentBranchRoots_of_source_and_renamed_roots_on_witnessed_extension
      constructor M hPA inputs
      (rawDynamicTruthZeroSigmaDomainCode M)
      (rawDynamicTruthZeroPiDomainCode M)
      (rawDynamicTruthZeroSigmaEvidenceCode M)
      (rawDynamicTruthZeroPiEvidenceCode M)
      witnessList baseContext endpointWitnessList endpointContext callerPrefix
      sourceRoot restrictedRoot ruleRoot hidentification hbaseWitnessed
      hendpointWitnessed hbaseEndpointIncluded hsource hrestricted hrule).
Qed.

(** Synchronize the normalized source with the two endpoint roots. *)
Theorem
    raw_dynamicTruthBooleanGuardedParentBranchRoots_of_zero_normalized_selected_identification_and_template_assumptions :
    forall constructor (M : RawPAModel) (hPA : RawPASatisfies M), forall
      inputs normalizedTranslation witnessList baseContext helperRoots
      callerPrefix,
  RawCoqDynamicTruthLocalExclusiveTemplateIdentification M inputs
    (rawDynamicTruthZeroSigmaDomainCode M)
    (rawDynamicTruthZeroPiDomainCode M)
    (rawDynamicTruthZeroSigmaEvidenceCode M)
    (rawDynamicTruthZeroPiEvidenceCode M) ->
  RawDynamicTruthNativeLocalZeroGuardedNormalizedResourcesAt M
    normalizedTranslation witnessList baseContext helperRoots ->
  In coqRestrictedPADerivationSoundnessRestrictedProofTemplate
    callerPrefix ->
  In coqStrongStepProofEndpointAtomicAdequacyRulePremise callerPrefix ->
  exists targetWitnessList targetContext,
    RawCodedPAAxiomWitnessContext M targetWitnessList targetContext /\
    RawContextListIncluded M baseContext targetContext /\
    RawDynamicTruthBooleanGuardedParentBranchRootsAt constructor M
      (rawDirectStructuralTemplateTranslation M hPA inputs)
      targetContext callerPrefix.
Proof.
  intros constructor M hPA inputs normalizedTranslation witnessList
    baseContext helperRoots callerPrefix hidentification hnormalized
    hrestrictedIn hruleIn.
  destruct (rawDynamicTruthNativeLocalZeroGuardedNormalized_fields
    M normalizedTranslation witnessList baseContext helperRoots
    hnormalized) as [hbaseWitnessed _].
  destruct
    (raw_dynamicTruthGuardedBranchSource_of_zero_normalized_under_prefix
      M hPA inputs normalizedTranslation witnessList baseContext helperRoots
      (coqDynamicTruthBooleanGuardedDeepPrefix constructor callerPrefix)
      hidentification hnormalized)
    as [sourceRoot hsource].
  destruct
    (raw_dynamicTruthBooleanGuardedParentEndpointRoots_of_template_assumptions
      constructor M hPA inputs
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
      (coqDynamicTruthBooleanGuardedDeepPrefix constructor callerPrefix)
      (rawTemplateFormula
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        (tfAll (tfAll (tfAll
          coqDynamicTruthLocalExclusiveBodyTemplate))))
      sourceRoot hbaseWitnessed htargetWitnessed hincluded hsource)
    as [transportedSourceRoot htransportedSource].
  exists targetWitnessList, targetContext.
  split; [exact htargetWitnessed |].
  split; [exact hincluded |].
  constructor.
  - exists transportedSourceRoot. exact htransportedSource.
  - exists atomicRoot. exact hatomic.
  - exists domainRoot. exact hdomain.
Qed.

End
  PABoundedRawCodedDynamicTruthNativeZeroBooleanGuardedParentCompilation.
