(**
  Reduce the native rank-zero predecessor callback to three logical roots.

  The old zero callback returned the completed predecessor-exclusivity proof.
  At rank zero, however, every syntactic coordinate of that proof is a fixed
  quoted formula.  The direct-template identification established in
  [RawCodedDynamicTruthZeroLocalExclusiveTemplateIdentification] lets us
  assemble the completed proof here.  A client now supplies only
  admissibility, Sigma evidence, and Pi evidence on one witnessed extension.
*)

From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors
  RawCodedPAAxiomWitness
  RawCodedRestrictedPAProof
  RawCodedPALocalProofExistential
  RawCodedPALocalProofWitnessedContextMerge
  RawCodedTemplateProofCompiler
  RawCodedDynamicTruthLocalDecisionExclusiveBase
  RawCodedDynamicTruthNativeLocalPositiveGraph
  RawCodedDynamicTruthNativeLocalProofCompilation
  RawCodedDynamicTruthLocalFieldProjectionCompilation
  RawCodedDynamicTruthPredecessorStateExclusivityCompilation
  RawCodedDynamicTruthNativeLocalGrowingPredecessorStagedCallbackCompilation
  RawCodedDynamicTruthZeroLocalExclusiveTemplateIdentification.

Module
  PABoundedRawCodedDynamicTruthNativeZeroPredecessorLogicalRootsCompilation.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedPAAxiomWitness.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPALocalProofWitnessedContextMerge.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedDynamicTruthLocalDecisionExclusiveBase.
Import PABoundedRawCodedDynamicTruthNativeLocalPositiveGraph.
Import PABoundedRawCodedDynamicTruthNativeLocalProofCompilation.
Import PABoundedRawCodedDynamicTruthLocalFieldProjectionCompilation.
Import
  PABoundedRawCodedDynamicTruthPredecessorStateExclusivityCompilation.
Import
  PABoundedRawCodedDynamicTruthNativeLocalGrowingPredecessorStagedCallbackCompilation.
Import
  PABoundedRawCodedDynamicTruthZeroLocalExclusiveTemplateIdentification.

(** The four formulas consumed by the zero predecessor closure are fixed.
    Naming their codes keeps the residual compiler interface readable. *)
Definition rawDynamicTruthZeroSigmaDomainCode (M : RawPAModel) : M :=
  rawQuotedFormulaCode M dynamicTruthZeroSigmaDomainFormula.

Definition rawDynamicTruthZeroPiDomainCode (M : RawPAModel) : M :=
  rawQuotedFormulaCode M dynamicTruthZeroPiDomainFormula.

Definition rawDynamicTruthZeroSigmaEvidenceCode (M : RawPAModel) : M :=
  rawQuotedFormulaCode M dynamicTruthZeroSigmaEvidenceFormula.

Definition rawDynamicTruthZeroPiEvidenceCode (M : RawPAModel) : M :=
  rawQuotedFormulaCode M dynamicTruthZeroPiEvidenceFormula.

(** Quoting the four concrete leaves reconstructs exactly the base local
    decision/exclusivity field carried by the native helper package. *)
Lemma raw_dynamicTruthZeroLocalDecisionExclusiveFieldCode : forall
    (M : RawPAModel), RawPASatisfies M ->
  rawDynamicTruthLocalDecisionExclusiveFieldCode M
    (rawDynamicTruthZeroSigmaDomainCode M)
    (rawDynamicTruthZeroPiDomainCode M)
    (rawDynamicTruthZeroSigmaEvidenceCode M)
    (rawDynamicTruthZeroPiEvidenceCode M) =
  rawQuotedFormulaCode M dynamicTruthLocalDecisionExclusiveBaseFormula.
Proof.
  intros M hPA.
  unfold rawDynamicTruthZeroSigmaDomainCode,
    rawDynamicTruthZeroPiDomainCode,
    rawDynamicTruthZeroSigmaEvidenceCode,
    rawDynamicTruthZeroPiEvidenceCode.
  rewrite rawDynamicTruthLocalDecisionExclusiveFieldCode_quoted
    by exact hPA.
  unfold dynamicTruthZeroSigmaDomainFormula,
    dynamicTruthZeroPiDomainFormula,
    dynamicTruthZeroSigmaEvidenceFormula,
    dynamicTruthZeroPiEvidenceFormula.
  rewrite dynamicTruthLocalDecisionExclusiveCarrierFormula_fixedLevel.
  reflexivity.
Qed.

(** Arithmetic/proof-traversal boundary for rank zero.  The source witness
    list is passed explicitly because it is already stored in the current
    helper package; asking a compiler to rediscover it would be stronger.

    The trace coordinates remain available to the eventual concrete global
    row compiler, but the output is only the three logical leaves needed by
    the generic template closure. *)
Definition
    RawDynamicTruthNativeLocalZeroGrowingLogicalRootsCompilerOnWitnessedBase
    (M : RawPAModel) : Prop :=
  forall (tail : nat -> M) level baseContext
      inputGlobalSigma inputGlobalPi
      sigmaDomain piDomain sigmaEvidence piEvidence sourceWitnessList,
    RawCodedPAAxiomWitnessContext M sourceWitnessList baseContext ->
    RawDynamicTruthNativeLocalProofTraceAt M tail level
      inputGlobalSigma inputGlobalPi sigmaDomain piDomain
      sigmaEvidence piEvidence ->
    level = raw_zero M ->
    exists targetWitnessList targetContext,
      RawCodedPAAxiomWitnessContext M targetWitnessList targetContext /\
      RawContextListIncluded M baseContext targetContext /\
      RawDynamicTruthPredecessorStateLogicalRootsAt M targetContext
        (rawDynamicTruthZeroSigmaDomainCode M)
        (rawDynamicTruthZeroPiDomainCode M)
        (rawDynamicTruthZeroSigmaEvidenceCode M)
        (rawDynamicTruthZeroPiEvidenceCode M).

Arguments
  RawDynamicTruthNativeLocalZeroGrowingLogicalRootsCompilerOnWitnessedBase
  M : clear implicits.

(** Assemble the former zero callback from the smaller logical-root
    compiler.  The carried base proof is first identified with the concrete
    four-leaf field, then its exclusivity conjunct is projected.  The generic
    witnessed-context closure transports that conjunct and consumes the
    three newly compiled leaves. *)
Theorem
    raw_dynamicTruthNativeLocalZeroPredecessorRootCompiler_of_growing_logical_roots
    : forall (M : RawPAModel), RawPASatisfies M -> forall
      (translation : RawCodedTemplateTranslation M),
  RawDynamicTruthNativeLocalZeroGrowingLogicalRootsCompilerOnWitnessedBase M ->
  RawDynamicTruthNativeLocalZeroPredecessorRootCompiler M translation.
Proof.
  intros M hPA translation hlogical tail level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal
    witnessList baseContext helperRoots
    inputGlobalSigma inputGlobalPi
    sigmaDomain piDomain sigmaEvidence piEvidence currentLocalRoot
    hcurrent htrace hlevel hfield hcurrentProof.
  pose proof hcurrent as hfields.
  destruct hfields as
    [_ (storedLocalRoot & currentCrossLevelRoot & currentShiftRoot &
      currentSubstitutionRoot & currentAxiomSoundnessRoot &
      currentFinalRoot & hbaseWitnessed & hhelperRoots)].
  destruct (hlogical tail level baseContext
      inputGlobalSigma inputGlobalPi sigmaDomain piDomain
      sigmaEvidence piEvidence witnessList hbaseWitnessed htrace hlevel) as
    (targetWitnessList & targetContext & htargetWitnessed &
      hincluded & hlogicalRoots).
  assert (hbaseFormulaProof :
    RawCodedPALocalProofOf M baseContext
      (rawQuotedFormulaCode M
        dynamicTruthLocalDecisionExclusiveBaseFormula)
      currentLocalRoot).
  {
    rewrite <- hfield.
    exact hcurrentProof.
  }
  assert (hzeroFieldProof :
    RawCodedPALocalProofOf M baseContext
      (rawDynamicTruthLocalDecisionExclusiveFieldCode M
        (rawDynamicTruthZeroSigmaDomainCode M)
        (rawDynamicTruthZeroPiDomainCode M)
        (rawDynamicTruthZeroSigmaEvidenceCode M)
        (rawDynamicTruthZeroPiEvidenceCode M))
      currentLocalRoot).
  {
    rewrite raw_dynamicTruthZeroLocalDecisionExclusiveFieldCode
      by exact hPA.
    exact hbaseFormulaProof.
  }
  pose proof
    (raw_dynamicTruthLocalDecisionExclusiveProjectedRootsAt_of_local
      M hPA baseContext
      (rawDynamicTruthZeroSigmaDomainCode M)
      (rawDynamicTruthZeroPiDomainCode M)
      (rawDynamicTruthZeroSigmaEvidenceCode M)
      (rawDynamicTruthZeroPiEvidenceCode M)
      currentLocalRoot hzeroFieldProof) as hprojected.
  destruct hprojected as [hdecisionProjection hexclusiveProjection].
  destruct
    (raw_dynamicTruthZeroLocalExclusiveTemplateIdentification_exists M hPA)
    as [inputs hidentification].
  exists targetWitnessList, targetContext.
  split; [exact htargetWitnessed |].
  split; [exact hincluded |].
  exact
    (raw_dynamicTruthImpPredecessorStateExclusivityRoot_of_local_exclusive_template_on_witnessed_extension
      M hPA baseContext targetWitnessList targetContext
      (rawDynamicTruthZeroSigmaDomainCode M)
      (rawDynamicTruthZeroPiDomainCode M)
      (rawDynamicTruthZeroSigmaEvidenceCode M)
      (rawDynamicTruthZeroPiEvidenceCode M)
      (rawDynamicTruthLocalExclusiveProjectionRoot M baseContext
        (rawDynamicTruthZeroSigmaDomainCode M)
        (rawDynamicTruthZeroPiDomainCode M)
        (rawDynamicTruthZeroSigmaEvidenceCode M)
        (rawDynamicTruthZeroPiEvidenceCode M)
        currentLocalRoot)
      (raw_codedPAAxiomWitnessContext_context_realizable M
        witnessList baseContext hbaseWitnessed)
      htargetWitnessed hincluded hexclusiveProjection
      (raw_dynamicTruthPredecessorStateTemplateApplicationBridgeAt_of_direct_logical_roots
        M hPA targetContext
        (rawDynamicTruthZeroSigmaDomainCode M)
        (rawDynamicTruthZeroPiDomainCode M)
        (rawDynamicTruthZeroSigmaEvidenceCode M)
        (rawDynamicTruthZeroPiEvidenceCode M)
        inputs hidentification hlogicalRoots)).
Qed.

End
  PABoundedRawCodedDynamicTruthNativeZeroPredecessorLogicalRootsCompilation.
