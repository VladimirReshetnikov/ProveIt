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
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  BoundedConsistency
  CodedSyntax
  CompactRestrictedPAConsistencyFormulaCodeGraph
  RawCodedSyntaxConstructors
  RawCodedNumeralTermCode
  RawCodedAssignment
  RawCodedFormulaOperations
  RawCodedRestrictedPAConsistency
  RawCodedRestrictedPAConsistencyFormulaCode
  RawCodedContextLists
  RawCodedContextStructure
  RawCodedFixedLevelTruthTotality
  RawCodedPAAxiomWitness
  RawCodedPAAxiomWitnessPrefix
  RawCodedProofAtomicAdequacyStandard
  RawCodedRestrictedPAProof
  RawCodedPALocalProofExistential
  RawCodedProofAssumptionLeaf
  RawCodedPALocalProofComposition
  RawCodedPALocalProofConjunction
  RawCodedPALocalProofContextInsertUnconditional
  RawCodedPALocalProofWitnessedContextMerge
  RawCodedTemplateProofCompiler
  RawCodedTemplateDirectStructuralTranslation
  RawCodedTemplateDirectStructuralPAAgreement
  RawCodedTemplatePAEmbedding
  RawCodedTemplatePAEmbeddingSelfShiftTail
  RawCodedTemplateLocalProofStandardWitnessTailTransport
  RawCodedTemplateBottomDirectStructuralInputs
  RawCodedTemplateTernaryApplication
  RawCodedTernaryPredicateRootClosure
  RawCodedTruthCertificateMasterSuccessorBridge
  RawCodedTruthCertificateMasterFixedHelperBatchExtension
  RawCodedDynamicTruthMixedQFOpaqueQuantifierCellCompilation
  RawCodedDynamicLocalFieldGraph
  RawCodedDynamicTruthLocalDecisionExclusiveBase
  RawCodedDynamicTruthTransportFieldBaseGraphs
  RawCodedDynamicTruthAxiomSoundnessBaseGraph
  RawCodedDynamicTruthMasterSplicedBasePackage
  RawCodedDynamicTruthNativeMasterEndpoint
  RawCodedDynamicTruthPairedGlobalSuccessorGraph
  RawCodedDynamicTruthGlobalBaseRootClosure
  RawCodedDynamicTruthPairedGlobalFormulaCodeOrbitGraph
  RawCodedDynamicTruthNativeLocalPositiveGraph
  RawCodedDynamicTruthNativeCrossLevelPositiveGraph
  RawCodedDynamicTruthNativeShiftPositiveGraph
  RawCodedDynamicTruthNativeSubstitutionPositiveGraph
  RawCodedDynamicTruthNativeAxiomSoundnessPositiveGraph
  RawCodedDynamicTruthNativeLocalProofCompilation
  RawCodedDynamicTruthLocalFieldProjectionCompilation
  RawCodedDynamicTruthLocalCollisionMatrixAssembly
  RawCodedDynamicTruthImpBranchExclusivity
  RawCodedDynamicTruthLocalAdmissibilityCompilation
  RawCodedDynamicTruthPredecessorStateExclusivityCompilation
  RawCodedDynamicTruthPredecessorStateProjectionCompilation
  RawCodedDynamicTruthPredecessorDirectEvidenceLogicalRoots
  RawCodedDynamicTruthNativeLocalStagedCallbackCompilation
  RawCodedDynamicTruthNativeLocalGrowingPredecessorStagedCallbackCompilation
  RawCodedDynamicTruthZeroLocalExclusiveTemplateIdentification.

Module
  PABoundedRawCodedDynamicTruthNativeZeroPredecessorLogicalRootsCompilation.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedConsistency.
Import PABoundedCodedSyntax.
Import PABoundedCompactRestrictedPAConsistencyFormulaCodeGraph.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedNumeralTermCode.
Import PABoundedRawCodedAssignment.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedRestrictedPAConsistency.
Import PABoundedRawCodedRestrictedPAConsistencyFormulaCode.
Import PABoundedRawCodedContextLists.
Import PABoundedRawCodedContextStructure.
Import PABoundedRawCodedFixedLevelTruthTotality.
Import PABoundedRawCodedPAAxiomWitness.
Import PABoundedRawCodedPAAxiomWitnessPrefix.
Import PABoundedRawCodedProofAtomicAdequacyStandard.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedProofAssumptionLeaf.
Import PABoundedRawCodedPALocalProofComposition.
Import PABoundedRawCodedPALocalProofConjunction.
Import PABoundedRawCodedPALocalProofContextInsertUnconditional.
Import PABoundedRawCodedPALocalProofWitnessedContextMerge.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedTemplateDirectStructuralTranslation.
Import PABoundedRawCodedTemplateDirectStructuralPAAgreement.
Import PABoundedRawCodedTemplatePAEmbedding.
Import PABoundedRawCodedTemplatePAEmbeddingSelfShiftTail.
Import PABoundedRawCodedTemplateLocalProofStandardWitnessTailTransport.
Import PABoundedRawCodedTemplateBottomDirectStructuralInputs.
Import PABoundedRawCodedTemplateTernaryApplication.
Import PABoundedRawCodedTernaryPredicateRootClosure.
Import PABoundedRawCodedTruthCertificateMasterSuccessorBridge.
Import PABoundedRawCodedTruthCertificateMasterFixedHelperBatchExtension.
Import
  PABoundedRawCodedDynamicTruthMixedQFOpaqueQuantifierCellCompilation.
Import PABoundedRawCodedDynamicLocalFieldGraph.
Import PABoundedRawCodedDynamicTruthLocalDecisionExclusiveBase.
Import PABoundedRawCodedDynamicTruthTransportFieldBaseGraphs.
Import PABoundedRawCodedDynamicTruthAxiomSoundnessBaseGraph.
Import PABoundedRawCodedDynamicTruthMasterSplicedBasePackage.
Import PABoundedRawCodedDynamicTruthNativeMasterEndpoint.
Import PABoundedRawCodedDynamicTruthPairedGlobalSuccessorGraph.
Import PABoundedRawCodedDynamicTruthGlobalBaseRootClosure.
Import PABoundedRawCodedDynamicTruthPairedGlobalFormulaCodeOrbitGraph.
Import PABoundedRawCodedDynamicTruthNativeLocalPositiveGraph.
Import PABoundedRawCodedDynamicTruthNativeCrossLevelPositiveGraph.
Import PABoundedRawCodedDynamicTruthNativeShiftPositiveGraph.
Import PABoundedRawCodedDynamicTruthNativeSubstitutionPositiveGraph.
Import PABoundedRawCodedDynamicTruthNativeAxiomSoundnessPositiveGraph.
Import PABoundedRawCodedDynamicTruthNativeLocalProofCompilation.
Import PABoundedRawCodedDynamicTruthLocalFieldProjectionCompilation.
Import PABoundedRawCodedDynamicTruthLocalCollisionMatrixAssembly.
Import PABoundedRawCodedDynamicTruthImpBranchExclusivity.
Import PABoundedRawCodedDynamicTruthLocalAdmissibilityCompilation.
Import
  PABoundedRawCodedDynamicTruthPredecessorStateExclusivityCompilation.
Import
  PABoundedRawCodedDynamicTruthPredecessorStateProjectionCompilation.
Import
  PABoundedRawCodedDynamicTruthPredecessorDirectEvidenceLogicalRoots.
Import PABoundedRawCodedDynamicTruthNativeLocalStagedCallbackCompilation.
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

(** Strong fixed rank-zero proof boundary.  Once the four formulas have been
    identified with literal quotations, their logical-root package depends
    only on the witnessed PA tail under the two fixed predecessor-state
    assumptions.  In particular, neither a native trace nor any global code
    selected by that trace occurs in the result type.

    This interface is useful as a sufficient condition, but it is stronger
    than the traversal problem: the state assumptions alone do not record
    that their lookup tables came from the canonical global successor.  The
    public residual below therefore retains that successor data rather than
    claiming that this fixed compiler is constructible in isolation. *)
Definition RawDynamicTruthZeroGrowingLogicalRootsCompilerOnWitnessedBase
    (M : RawPAModel) : Prop :=
  forall sourceWitnessList baseContext,
    RawCodedPAAxiomWitnessContext M sourceWitnessList baseContext ->
    exists targetWitnessList targetContext,
      RawCodedPAAxiomWitnessContext M targetWitnessList targetContext /\
      RawContextListIncluded M baseContext targetContext /\
      RawDynamicTruthPredecessorStateLogicalRootsAt M targetContext
        (rawDynamicTruthZeroSigmaDomainCode M)
        (rawDynamicTruthZeroPiDomainCode M)
        (rawDynamicTruthZeroSigmaEvidenceCode M)
        (rawDynamicTruthZeroPiEvidenceCode M).

Arguments RawDynamicTruthZeroGrowingLogicalRootsCompilerOnWitnessedBase
  M : clear implicits.

(** Curry the two fixed state assumptions around one conjunction containing
    all three desired leaves.  Proving this single ordinary PA formula is a
    sufficient condition for the strong fixed compiler above.  No theorem
    below claims that PA proves this open formula: its free table variables
    deliberately make the missing global-source hypotheses visible. *)
Definition dynamicTruthZeroLogicalRootsLawFormula : formula :=
  pImp dynamicTruthPredecessorSigmaStateMemberBodyFormula
    (pImp dynamicTruthPredecessorPiStateMemberBodyFormula
      (pAnd
        (dynamicTruthLocalAdmissibleFormula
          dynamicTruthZeroSigmaDomainFormula
          dynamicTruthZeroPiDomainFormula)
        (pAnd dynamicTruthZeroSigmaEvidenceFormula
          dynamicTruthZeroPiEvidenceFormula))).

(** Quoting the fixed admissibility formula agrees with the carrier-level
    constructor used by the logical-root record. *)
Lemma raw_dynamicTruthZeroLocalAdmissibleCode : forall
    (M : RawPAModel), RawPASatisfies M ->
  rawDynamicTruthLocalAdmissibleCode M
      (rawDynamicTruthZeroSigmaDomainCode M)
      (rawDynamicTruthZeroPiDomainCode M) =
  rawQuotedFormulaCode M
    (dynamicTruthLocalAdmissibleFormula
      dynamicTruthZeroSigmaDomainFormula
      dynamicTruthZeroPiDomainFormula).
Proof.
  intros M hPA.
  unfold rawDynamicTruthLocalAdmissibleCode,
    dynamicTruthLocalAdmissibleFormula,
    rawDynamicTruthZeroSigmaDomainCode,
    rawDynamicTruthZeroPiDomainCode.
  rewrite <- (rawQuotedFormulaCode_standard M hPA
    (codedFormulaAtomicallyAdequateTermAt (tVar 2))).
  rewrite <- (rawQuotedFormulaCode_standard M hPA
    (codedAssignmentDefinedThroughTermAt
      (tVar 1) (tVar 0) (tVar 2))).
  reflexivity.
Qed.

(** Reduce the model-indexed fixed compiler to one ordinary PA derivation.
    The derivation is materialized over the caller's witnessed tail once,
    transplanted beneath the two state assumptions, and applied twice.  The
    three conjunction projections therefore share one exact witnessed
    extension. *)
Theorem
    raw_dynamicTruthZeroGrowingLogicalRootsCompilerOnWitnessedBase_of_PA_law
    : Formula.BProv Formula.Ax_s nil
        dynamicTruthZeroLogicalRootsLawFormula ->
  forall (M : RawPAModel), RawPASatisfies M ->
    RawDynamicTruthZeroGrowingLogicalRootsCompilerOnWitnessedBase M.
Proof.
  intros hlaw M hPA sourceWitnessList baseContext hsource.
  set (inputs := rawBottomTemplateDirectStructuralInputs M hPA).
  set (translation := rawDirectStructuralTemplateTranslation M hPA inputs).
  destruct
    (raw_codedTemplatePALocalProofOf_of_BProv_on_witnessed_tail
      M hPA translation
      (rawDirectStructuralTemplatePAAgreement M hPA inputs)
      sourceWitnessList baseContext
      dynamicTruthZeroLogicalRootsLawFormula hsource hlaw) as
    (witnesses & lawRoot & htargetWitnessed & hlawRoot).
  set (targetWitnessList :=
    rawStandardPAAxiomWitnessPrefixWitnessListCode M
      witnesses sourceWitnessList).
  set (targetContext :=
    rawStandardPAAxiomWitnessPrefixContextCode M witnesses baseContext).
  fold targetWitnessList targetContext in htargetWitnessed.
  unfold translation in hlawRoot.
  rewrite (rawTemplateFormula_embedPA
    (rawDirectStructuralTemplatePAAgreement M hPA inputs)
    dynamicTruthZeroLogicalRootsLawFormula) in hlawRoot.
  fold targetContext in hlawRoot.
  assert (htargetRealizable : RawContextListRealizable M targetContext).
  {
    exact (raw_codedPAAxiomWitnessContext_context_realizable
      M targetWitnessList targetContext htargetWitnessed).
  }
  set (sigmaCode :=
    rawDynamicTruthPredecessorSigmaStateMemberBodyCode M).
  set (piCode :=
    rawDynamicTruthPredecessorPiStateMemberBodyCode M).
  set (sigmaContext := rawListNode M sigmaCode targetContext).
  set (jointContext := rawListNode M piCode sigmaContext).
  assert (hsigmaContextRealizable : RawContextListRealizable M sigmaContext).
  {
    unfold sigmaContext, sigmaCode.
    exact (raw_contextList_cons_realizable M hPA targetContext
      (rawDynamicTruthPredecessorSigmaStateMemberBodyCode M)
      htargetRealizable).
  }
  destruct (raw_codedPALocalProof_adequateConsTransplant M hPA
    targetContext sigmaCode
    (rawQuotedFormulaCode M dynamicTruthZeroLogicalRootsLawFormula)
    lawRoot
    (raw_quotedFormula_atomically_adequate M hPA
      dynamicTruthPredecessorSigmaStateMemberBodyFormula)
    htargetRealizable hlawRoot) as [sigmaLawRoot hsigmaLaw].
  destruct (raw_codedPALocalProof_adequateConsTransplant M hPA
    sigmaContext piCode
    (rawQuotedFormulaCode M dynamicTruthZeroLogicalRootsLawFormula)
    sigmaLawRoot
    (raw_quotedFormula_atomically_adequate M hPA
      dynamicTruthPredecessorPiStateMemberBodyFormula)
    hsigmaContextRealizable hsigmaLaw) as [jointLawRoot hjointLaw].
  pose proof (raw_codedPALocalProofOf_assumption M hPA targetContext
    sigmaCode htargetRealizable) as hsigmaAtSigma.
  destruct (raw_codedPALocalProof_adequateConsTransplant M hPA
    sigmaContext piCode sigmaCode
    (rawProofAssumptionRoot M sigmaContext sigmaCode)
    (raw_quotedFormula_atomically_adequate M hPA
      dynamicTruthPredecessorPiStateMemberBodyFormula)
    hsigmaContextRealizable hsigmaAtSigma) as
    [sigmaJointRoot hsigmaJoint].
  pose proof (raw_codedPALocalProofOf_assumption M hPA sigmaContext
    piCode hsigmaContextRealizable) as hpiJoint.
  unfold dynamicTruthZeroLogicalRootsLawFormula in hjointLaw.
  unfold sigmaCode, piCode in hjointLaw, hsigmaJoint, hpiJoint.
  change (RawCodedPALocalProofOf M jointContext
    (rawFormulaImpCode M
      (rawDynamicTruthPredecessorSigmaStateMemberBodyCode M)
      (rawFormulaImpCode M
        (rawDynamicTruthPredecessorPiStateMemberBodyCode M)
        (rawFormulaAndCode M
          (rawQuotedFormulaCode M
            (dynamicTruthLocalAdmissibleFormula
              dynamicTruthZeroSigmaDomainFormula
              dynamicTruthZeroPiDomainFormula))
          (rawFormulaAndCode M
            (rawDynamicTruthZeroSigmaEvidenceCode M)
            (rawDynamicTruthZeroPiEvidenceCode M))))) jointLawRoot)
    in hjointLaw.
  rewrite <- (raw_dynamicTruthZeroLocalAdmissibleCode M hPA) in hjointLaw.
  pose proof (raw_codedPALocalProofOf_impE M hPA jointContext
    (rawDynamicTruthPredecessorSigmaStateMemberBodyCode M)
    (rawFormulaImpCode M
      (rawDynamicTruthPredecessorPiStateMemberBodyCode M)
      (rawFormulaAndCode M
        (rawDynamicTruthLocalAdmissibleCode M
          (rawDynamicTruthZeroSigmaDomainCode M)
          (rawDynamicTruthZeroPiDomainCode M))
        (rawFormulaAndCode M
          (rawDynamicTruthZeroSigmaEvidenceCode M)
          (rawDynamicTruthZeroPiEvidenceCode M))))
    jointLawRoot sigmaJointRoot hjointLaw hsigmaJoint) as hafterSigma.
  lazymatch type of hafterSigma with
  | RawCodedPALocalProofOf _ _ _ ?afterSigmaRoot =>
      pose proof (raw_codedPALocalProofOf_impE M hPA jointContext
        (rawDynamicTruthPredecessorPiStateMemberBodyCode M)
        (rawFormulaAndCode M
          (rawDynamicTruthLocalAdmissibleCode M
            (rawDynamicTruthZeroSigmaDomainCode M)
            (rawDynamicTruthZeroPiDomainCode M))
          (rawFormulaAndCode M
            (rawDynamicTruthZeroSigmaEvidenceCode M)
            (rawDynamicTruthZeroPiEvidenceCode M)))
        afterSigmaRoot (rawProofAssumptionRoot M jointContext
          (rawDynamicTruthPredecessorPiStateMemberBodyCode M))
        hafterSigma hpiJoint) as hallRoots
  end.
  lazymatch type of hallRoots with
  | RawCodedPALocalProofOf _ _ _ ?allRoot =>
      pose proof (raw_codedPALocalProofOf_andE1 M hPA jointContext
        (rawDynamicTruthLocalAdmissibleCode M
          (rawDynamicTruthZeroSigmaDomainCode M)
          (rawDynamicTruthZeroPiDomainCode M))
        (rawFormulaAndCode M
          (rawDynamicTruthZeroSigmaEvidenceCode M)
          (rawDynamicTruthZeroPiEvidenceCode M)) allRoot hallRoots)
        as hadmissible;
      pose proof (raw_codedPALocalProofOf_andE2 M hPA jointContext
        (rawDynamicTruthLocalAdmissibleCode M
          (rawDynamicTruthZeroSigmaDomainCode M)
          (rawDynamicTruthZeroPiDomainCode M))
        (rawFormulaAndCode M
          (rawDynamicTruthZeroSigmaEvidenceCode M)
          (rawDynamicTruthZeroPiEvidenceCode M)) allRoot hallRoots)
        as hevidencePair
  end.
  lazymatch type of hevidencePair with
  | RawCodedPALocalProofOf _ _ _ ?evidencePairRoot =>
      pose proof (raw_codedPALocalProofOf_andE1 M hPA jointContext
        (rawDynamicTruthZeroSigmaEvidenceCode M)
        (rawDynamicTruthZeroPiEvidenceCode M)
        evidencePairRoot hevidencePair) as hsigmaEvidence;
      pose proof (raw_codedPALocalProofOf_andE2 M hPA jointContext
        (rawDynamicTruthZeroSigmaEvidenceCode M)
        (rawDynamicTruthZeroPiEvidenceCode M)
        evidencePairRoot hevidencePair) as hpiEvidence
  end.
  exists targetWitnessList, targetContext.
  split; [exact htargetWitnessed |].
  split.
  - unfold targetContext.
    exact (raw_standardPAAxiomWitnessPrefixContextCode_target_included
      M hPA witnesses baseContext).
  - change (RawDynamicTruthPredecessorStateLogicalRootsAt M targetContext
      (rawDynamicTruthZeroSigmaDomainCode M)
      (rawDynamicTruthZeroPiDomainCode M)
      (rawDynamicTruthZeroSigmaEvidenceCode M)
      (rawDynamicTruthZeroPiEvidenceCode M)).
    unfold jointContext, sigmaContext, sigmaCode, piCode in
      hadmissible, hsigmaEvidence, hpiEvidence.
    constructor.
    + eexists. exact hadmissible.
    + eexists. exact hsigmaEvidence.
    + eexists. exact hpiEvidence.
Qed.

(** Full literal-zero form of the native trace.  Unlike the earlier
    first-step projection below, this package retains the second global
    successor and both applications which actually determine the level-one
    evidence formulas.  The arbitrary carrier-valued level and a separate
    equality to zero have disappeared. *)
Definition RawDynamicTruthNativeLocalZeroFullTraceAt
    (M : RawPAModel) (tail : nat -> M)
    (inputGlobalSigma inputGlobalPi
      sigmaDomain piDomain sigmaEvidence piEvidence : M) : Prop :=
  RawDynamicTruthPairedGlobalFormulaCodeAdequateOrbitAt M
      tail (raw_succ M (raw_zero M))
      inputGlobalSigma inputGlobalPi /\
  exists evidenceGlobalSigma evidenceGlobalPi inputLevelNumeral : M,
    RawDynamicTruthPairedGlobalSuccessorAt M
      inputGlobalSigma inputGlobalPi (raw_succ M (raw_zero M))
      evidenceGlobalSigma evidenceGlobalPi /\
    RawNumeralTermCodeAt M (raw_succ M (raw_zero M))
      inputLevelNumeral /\
    RawCodedFormulaSingleSubstitution M inputLevelNumeral
      (rawNumeralValue M
        (formulaCode dynamicTruthLocalSigmaInputDomainTemplate))
      sigmaDomain /\
    RawCodedFormulaSingleSubstitution M inputLevelNumeral
      (rawNumeralValue M
        (formulaCode dynamicTruthLocalPiInputDomainTemplate))
      piDomain /\
    RawDynamicTruthLocalTernaryApplication M
      evidenceGlobalSigma sigmaEvidence /\
    RawDynamicTruthLocalTernaryApplication M
      evidenceGlobalPi piEvidence.

Arguments RawDynamicTruthNativeLocalZeroFullTraceAt
  M tail inputGlobalSigma inputGlobalPi
  sigmaDomain piDomain sigmaEvidence piEvidence : clear implicits.

(** Specializing a native trace to zero is exactly the full package above;
    this is a definitional rebracketing, not a semantic weakening. *)
Lemma raw_dynamicTruthNativeLocalProofTraceAt_zero_iff : forall
    (M : RawPAModel) (tail : nat -> M)
      inputGlobalSigma inputGlobalPi
      sigmaDomain piDomain sigmaEvidence piEvidence,
  RawDynamicTruthNativeLocalProofTraceAt M tail (raw_zero M)
    inputGlobalSigma inputGlobalPi sigmaDomain piDomain
    sigmaEvidence piEvidence <->
  RawDynamicTruthNativeLocalZeroFullTraceAt M tail
    inputGlobalSigma inputGlobalPi sigmaDomain piDomain
    sigmaEvidence piEvidence.
Proof.
  intros M tail inputGlobalSigma inputGlobalPi
    sigmaDomain piDomain sigmaEvidence piEvidence.
  unfold RawDynamicTruthNativeLocalProofTraceAt,
    RawDynamicTruthNativeLocalZeroFullTraceAt.
  split.
  - intros (horbit & inputLevel & evidenceGlobalSigma &
      evidenceGlobalPi & inputLevelNumeral & hlevel & hsuccessor &
      hnumeral & hsigmaDomain & hpiDomain & hsigmaEvidence & hpiEvidence).
    subst inputLevel.
    split; [exact horbit |].
    exists evidenceGlobalSigma, evidenceGlobalPi, inputLevelNumeral.
    repeat split; assumption.
  - intros (horbit & evidenceGlobalSigma & evidenceGlobalPi &
      inputLevelNumeral & hsuccessor & hnumeral & hsigmaDomain &
      hpiDomain & hsigmaEvidence & hpiEvidence).
    split; [exact horbit |].
    exists (raw_succ M (raw_zero M)), evidenceGlobalSigma,
      evidenceGlobalPi, inputLevelNumeral.
    repeat split; try reflexivity; assumption.
Qed.

(** A trace indexed by zero is not itself the missing rank-zero local row:
    its public input predicates sit at global level one.  Nevertheless its
    orbit component remembers the unique preceding global pair.  Opening
    that single orbit edge identifies the predecessor with the two literal
    rank-zero base quotations.

    Retaining root closure of the base pair and atomic adequacy of the level
    one outputs avoids repeating this orbit inversion in the eventual
    proof-producing traversal compiler. *)
Theorem raw_dynamicTruthNativeLocalProofTraceAt_zero_global_predecessor :
    forall (M : RawPAModel), RawPASatisfies M -> forall
      (tail : nat -> M) level inputGlobalSigma inputGlobalPi
      sigmaDomain piDomain sigmaEvidence piEvidence,
  RawDynamicTruthNativeLocalProofTraceAt M tail level
    inputGlobalSigma inputGlobalPi sigmaDomain piDomain
    sigmaEvidence piEvidence ->
  level = raw_zero M ->
  RawDynamicTruthPairedGlobalSuccessorAt M
      (rawDynamicTruthGlobalSigmaBaseCode M)
      (rawDynamicTruthGlobalPiBaseCode M)
      (raw_zero M) inputGlobalSigma inputGlobalPi /\
  RawCodedTernaryPredicateRootClosed M
      (rawDynamicTruthGlobalSigmaBaseCode M) /\
  RawCodedTernaryPredicateRootClosed M
      (rawDynamicTruthGlobalPiBaseCode M) /\
  RawCodedFormulaAtomicallyAdequate M inputGlobalSigma /\
  RawCodedFormulaAtomicallyAdequate M inputGlobalPi.
Proof.
  intros M hPA tail level inputGlobalSigma inputGlobalPi
    sigmaDomain piDomain sigmaEvidence piEvidence htrace hlevel.
  subst level.
  destruct htrace as [horbit _].
  destruct horbit as [horbit [hinputSigmaAdequate hinputPiAdequate]].
  destruct
    (proj1
      (raw_dynamicTruthPairedGlobalFormulaCodeOrbitAt_succ_iff M hPA
        tail (raw_zero M) inputGlobalSigma inputGlobalPi)
      horbit) as
    (previousGlobalSigma & previousGlobalPi & hpreviousOrbit & hsuccessor).
  pose proof
    (proj1
      (raw_dynamicTruthPairedGlobalFormulaCodeOrbitAt_zero_iff M hPA
        tail previousGlobalSigma previousGlobalPi)
      hpreviousOrbit) as hpreviousBaseGraph.
  pose proof
    (proj1
      (raw_sat_dynamicTruthPairedGlobalBaseGraph_iff M tail
        previousGlobalSigma previousGlobalPi)
      hpreviousBaseGraph) as hpreviousBase.
  unfold RawDynamicTruthPairedGlobalBaseAt,
    RawDynamicTruthPairedGlobalWrapperAt in hpreviousBase.
  destruct hpreviousBase as [hpreviousSigma hpreviousPi].
  subst previousGlobalSigma. subst previousGlobalPi.
  refine (conj hsuccessor (conj
    (rawDynamicTruthGlobalSigmaBaseCode_root_closed M hPA) (conj
      (rawDynamicTruthGlobalPiBaseCode_root_closed M hPA) (conj
        hinputSigmaAdequate hinputPiAdequate)))).
Qed.

(** Literal-zero projection of the preceding theorem.  Clients of the full
    trace no longer need to reintroduce an arbitrary level merely to recover
    the fixed global predecessor. *)
Corollary raw_dynamicTruthNativeLocalZeroFullTraceAt_global_predecessor :
    forall (M : RawPAModel), RawPASatisfies M -> forall
      (tail : nat -> M) inputGlobalSigma inputGlobalPi
      sigmaDomain piDomain sigmaEvidence piEvidence,
  RawDynamicTruthNativeLocalZeroFullTraceAt M tail
    inputGlobalSigma inputGlobalPi sigmaDomain piDomain
    sigmaEvidence piEvidence ->
  RawDynamicTruthPairedGlobalSuccessorAt M
      (rawDynamicTruthGlobalSigmaBaseCode M)
      (rawDynamicTruthGlobalPiBaseCode M)
      (raw_zero M) inputGlobalSigma inputGlobalPi /\
  RawCodedTernaryPredicateRootClosed M
      (rawDynamicTruthGlobalSigmaBaseCode M) /\
  RawCodedTernaryPredicateRootClosed M
      (rawDynamicTruthGlobalPiBaseCode M) /\
  RawCodedFormulaAtomicallyAdequate M inputGlobalSigma /\
  RawCodedFormulaAtomicallyAdequate M inputGlobalPi.
Proof.
  intros M hPA tail inputGlobalSigma inputGlobalPi
    sigmaDomain piDomain sigmaEvidence piEvidence hfull.
  exact (raw_dynamicTruthNativeLocalProofTraceAt_zero_global_predecessor
    M hPA tail (raw_zero M) inputGlobalSigma inputGlobalPi
    sigmaDomain piDomain sigmaEvidence piEvidence
    (proj2 (raw_dynamicTruthNativeLocalProofTraceAt_zero_iff M tail
      inputGlobalSigma inputGlobalPi sigmaDomain piDomain
      sigmaEvidence piEvidence) hfull) eq_refl).
Qed.

(** Proof-producing boundary after canonical orbit inversion.  In contrast
    with the trace-facing compiler below, this interface contains no unused
    local-row coordinates and no equality asserting that an arbitrary level
    is zero.  Its two global inputs are exactly the outputs of the one
    successor edge from the fixed rank-zero base pair.

    Root closure of the fixed inputs is retained explicitly because the next
    traversal compiler uses it to justify arbitrary represented ternary
    substitutions.  Atomic adequacy of the outputs is the corresponding
    syntactic invariant needed to compile their applications. *)
Definition
    RawDynamicTruthNativeLocalZeroGrowingLogicalRootsCompilerOnCanonicalGlobalStep
    (M : RawPAModel) : Prop :=
  forall sourceWitnessList baseContext inputGlobalSigma inputGlobalPi,
    RawCodedPAAxiomWitnessContext M sourceWitnessList baseContext ->
    RawDynamicTruthPairedGlobalSuccessorAt M
      (rawDynamicTruthGlobalSigmaBaseCode M)
      (rawDynamicTruthGlobalPiBaseCode M)
      (raw_zero M) inputGlobalSigma inputGlobalPi ->
    RawCodedTernaryPredicateRootClosed M
      (rawDynamicTruthGlobalSigmaBaseCode M) ->
    RawCodedTernaryPredicateRootClosed M
      (rawDynamicTruthGlobalPiBaseCode M) ->
    RawCodedFormulaAtomicallyAdequate M inputGlobalSigma ->
    RawCodedFormulaAtomicallyAdequate M inputGlobalPi ->
    exists targetWitnessList targetContext,
      RawCodedPAAxiomWitnessContext M targetWitnessList targetContext /\
      RawContextListIncluded M baseContext targetContext /\
      RawDynamicTruthPredecessorStateLogicalRootsAt M targetContext
        (rawDynamicTruthZeroSigmaDomainCode M)
        (rawDynamicTruthZeroPiDomainCode M)
        (rawDynamicTruthZeroSigmaEvidenceCode M)
        (rawDynamicTruthZeroPiEvidenceCode M).

Arguments
  RawDynamicTruthNativeLocalZeroGrowingLogicalRootsCompilerOnCanonicalGlobalStep
  M : clear implicits.

(** The proof-producing residue of the canonical rank-zero traversal.
    Atomic adequacy and the rank-domain disjunction are kept separate from
    the two polarity roots: the generic direct-evidence handoff can then
    construct admissibility once, on the exact witnessed context chosen by
    the traversal.  Unlike [dynamicTruthZeroLogicalRootsLawFormula], this
    package is guarded by the canonical global successor data at its call
    site and therefore does not forget why the two state lookups denote
    genuine truth-certificate rows. *)
Record RawDynamicTruthZeroDirectEvidenceRootsAt
    (M : RawPAModel) (baseContext : M) : Prop := {
  rawDynamicTruthZeroDirectEvidence_atomic : exists root,
    RawCodedPALocalProofOf M
      (rawDynamicTruthPredecessorJointStateContext M baseContext)
      (rawDynamicTruthLocalAtomicAdequacyCode M) root;
  rawDynamicTruthZeroDirectEvidence_domain : exists root,
    RawCodedPALocalProofOf M
      (rawDynamicTruthPredecessorJointStateContext M baseContext)
      (rawFormulaOrCode M
        (rawDynamicTruthZeroSigmaDomainCode M)
        (rawDynamicTruthZeroPiDomainCode M)) root;
  rawDynamicTruthZeroDirectEvidence_sigma : exists root,
    RawCodedPALocalProofOf M
      (rawDynamicTruthPredecessorJointStateContext M baseContext)
      (rawDynamicTruthZeroSigmaEvidenceCode M) root;
  rawDynamicTruthZeroDirectEvidence_pi : exists root,
    RawCodedPALocalProofOf M
      (rawDynamicTruthPredecessorJointStateContext M baseContext)
      (rawDynamicTruthZeroPiEvidenceCode M) root
}.

Arguments RawDynamicTruthZeroDirectEvidenceRootsAt M baseContext
  : clear implicits.

(** Shared direct-evidence handoff.  Both trace-facing and normalized
    traversal clients may first choose a context carrying the four direct
    roots.  This lemma is the unique place where that context is extended
    once more for admissibility and where the two inclusions are composed. *)
Theorem raw_dynamicTruthZeroGrowingLogicalRoots_of_direct_evidence :
    forall (M : RawPAModel), RawPASatisfies M -> forall
      sourceContext evidenceWitnessList evidenceContext,
  RawCodedPAAxiomWitnessContext M evidenceWitnessList evidenceContext ->
  RawContextListIncluded M sourceContext evidenceContext ->
  RawDynamicTruthZeroDirectEvidenceRootsAt M evidenceContext ->
  exists targetWitnessList targetContext,
    RawCodedPAAxiomWitnessContext M targetWitnessList targetContext /\
    RawContextListIncluded M sourceContext targetContext /\
    RawDynamicTruthPredecessorStateLogicalRootsAt M targetContext
      (rawDynamicTruthZeroSigmaDomainCode M)
      (rawDynamicTruthZeroPiDomainCode M)
      (rawDynamicTruthZeroSigmaEvidenceCode M)
      (rawDynamicTruthZeroPiEvidenceCode M).
Proof.
  intros M hPA sourceContext evidenceWitnessList evidenceContext
    hevidenceWitnessed hsourceEvidenceIncluded hroots.
  destruct hroots as
    [(atomicRoot & hatomic) (domainRoot & hdomain)
      (sigmaRoot & hsigma) (piRoot & hpi)].
  set (inputs := rawBottomTemplateDirectStructuralInputs M hPA).
  set (translation := rawDirectStructuralTemplateTranslation M hPA inputs).
  destruct
    (raw_dynamicTruthPredecessorStateLogicalRootsAt_of_direct_evidence_atomic_and_domain
      M hPA translation
      (rawDirectStructuralTemplatePAAgreement M hPA inputs)
      evidenceWitnessList evidenceContext
      (rawDynamicTruthZeroSigmaDomainCode M)
      (rawDynamicTruthZeroPiDomainCode M)
      (rawDynamicTruthZeroSigmaEvidenceCode M)
      (rawDynamicTruthZeroPiEvidenceCode M)
      atomicRoot domainRoot sigmaRoot piRoot
      hevidenceWitnessed hatomic hdomain hsigma hpi) as
    (targetWitnessList & targetContext & htargetWitnessed &
      hevidenceTargetIncluded & hlogicalRoots).
  exists targetWitnessList, targetContext.
  split; [exact htargetWitnessed |].
  split.
  - intros member hmember.
    exact (hevidenceTargetIncluded member
      (hsourceEvidenceIncluded member hmember)).
  - exact hlogicalRoots.
Qed.

(** Honest canonical rank-zero resource boundary.  A compiler may use the
    exact successor edge from the two fixed global base predicates, their
    root-closure proofs, and adequacy of the two successor outputs.  It may
    also grow the caller's witnessed PA context before returning the four
    direct roots. *)
Definition
    RawDynamicTruthNativeLocalZeroGrowingDirectEvidenceCompilerOnCanonicalGlobalStep
    (M : RawPAModel) : Prop :=
  forall sourceWitnessList baseContext inputGlobalSigma inputGlobalPi,
    RawCodedPAAxiomWitnessContext M sourceWitnessList baseContext ->
    RawDynamicTruthPairedGlobalSuccessorAt M
      (rawDynamicTruthGlobalSigmaBaseCode M)
      (rawDynamicTruthGlobalPiBaseCode M)
      (raw_zero M) inputGlobalSigma inputGlobalPi ->
    RawCodedTernaryPredicateRootClosed M
      (rawDynamicTruthGlobalSigmaBaseCode M) ->
    RawCodedTernaryPredicateRootClosed M
      (rawDynamicTruthGlobalPiBaseCode M) ->
    RawCodedFormulaAtomicallyAdequate M inputGlobalSigma ->
    RawCodedFormulaAtomicallyAdequate M inputGlobalPi ->
    exists evidenceWitnessList evidenceContext,
      RawCodedPAAxiomWitnessContext M
        evidenceWitnessList evidenceContext /\
      RawContextListIncluded M baseContext evidenceContext /\
      RawDynamicTruthZeroDirectEvidenceRootsAt M evidenceContext.

Arguments
  RawDynamicTruthNativeLocalZeroGrowingDirectEvidenceCompilerOnCanonicalGlobalStep
  M : clear implicits.

(** Compile the four canonical traversal roots into the three logical roots.
    The only nontrivial extra work is admissibility: its generic compiler may
    add PA-axiom witnesses, so inclusions are composed across the traversal
    context and the admissibility context. *)
Theorem
    raw_dynamicTruthNativeLocalZeroGrowingLogicalRootsCompilerOnCanonicalGlobalStep_of_direct_evidence
    : forall (M : RawPAModel), RawPASatisfies M ->
  RawDynamicTruthNativeLocalZeroGrowingDirectEvidenceCompilerOnCanonicalGlobalStep
    M ->
  RawDynamicTruthNativeLocalZeroGrowingLogicalRootsCompilerOnCanonicalGlobalStep
    M.
Proof.
  intros M hPA hdirect sourceWitnessList baseContext
    inputGlobalSigma inputGlobalPi hsource hsuccessor
    hbaseSigmaClosed hbasePiClosed hinputSigmaAdequate hinputPiAdequate.
  destruct (hdirect sourceWitnessList baseContext
    inputGlobalSigma inputGlobalPi hsource hsuccessor
    hbaseSigmaClosed hbasePiClosed
    hinputSigmaAdequate hinputPiAdequate) as
    (evidenceWitnessList & evidenceContext & hevidenceWitnessed &
      hbaseEvidenceIncluded & hroots).
  exact (raw_dynamicTruthZeroGrowingLogicalRoots_of_direct_evidence
    M hPA baseContext evidenceWitnessList evidenceContext
    hevidenceWitnessed hbaseEvidenceIncluded hroots).
Qed.

(** Trace-facing direct-evidence boundary used by the actual zero callback.
    A local trace at rank zero contains not only the base-to-input global
    edge but also the input-to-evidence successor, the represented numeral
    substitution, and both final ternary applications.  Keeping that full
    trace available avoids requiring a client to reconstruct data which the
    callback has already established. *)
Definition
    RawDynamicTruthNativeLocalZeroGrowingDirectEvidenceCompilerOnWitnessedBase
    (M : RawPAModel) : Prop :=
  forall (tail : nat -> M) baseContext
      inputGlobalSigma inputGlobalPi
      sigmaDomain piDomain sigmaEvidence piEvidence sourceWitnessList,
    RawCodedPAAxiomWitnessContext M sourceWitnessList baseContext ->
    RawDynamicTruthNativeLocalZeroFullTraceAt M tail
      inputGlobalSigma inputGlobalPi sigmaDomain piDomain
      sigmaEvidence piEvidence ->
    exists evidenceWitnessList evidenceContext,
      RawCodedPAAxiomWitnessContext M
        evidenceWitnessList evidenceContext /\
      RawContextListIncluded M baseContext evidenceContext /\
      RawDynamicTruthZeroDirectEvidenceRootsAt M evidenceContext.

Arguments
  RawDynamicTruthNativeLocalZeroGrowingDirectEvidenceCompilerOnWitnessedBase
  M : clear implicits.

(** A compiler which deliberately uses only the first canonical global step
    is a special case of the full-trace boundary.  This implication records
    formally that retaining the complete trace relaxes the residual premise;
    no existing one-step construction is lost. *)
Theorem
    raw_dynamicTruthNativeLocalZeroGrowingDirectEvidenceCompilerOnWitnessedBase_of_canonical_global_step
    : forall (M : RawPAModel), RawPASatisfies M ->
  RawDynamicTruthNativeLocalZeroGrowingDirectEvidenceCompilerOnCanonicalGlobalStep
    M ->
  RawDynamicTruthNativeLocalZeroGrowingDirectEvidenceCompilerOnWitnessedBase
    M.
Proof.
  intros M hPA hcanonical tail baseContext
    inputGlobalSigma inputGlobalPi sigmaDomain piDomain
    sigmaEvidence piEvidence sourceWitnessList hsource hfull.
  destruct
    (raw_dynamicTruthNativeLocalZeroFullTraceAt_global_predecessor
      M hPA tail inputGlobalSigma inputGlobalPi
      sigmaDomain piDomain sigmaEvidence piEvidence hfull) as
    (hsuccessor & hbaseSigmaClosed & hbasePiClosed &
      hinputSigmaAdequate & hinputPiAdequate).
  exact (hcanonical sourceWitnessList baseContext
    inputGlobalSigma inputGlobalPi hsource hsuccessor
    hbaseSigmaClosed hbasePiClosed
    hinputSigmaAdequate hinputPiAdequate).
Qed.

(** The represented proof resources actually carried at a zero current
    level, after eliminating the five spliced graph wrappers.  The first five
    targets are now literal quotations of their fixed base theorems.  The
    sixth target remains the compact restricted-consistency code selected by
    its own graph; it is retained because the callback already carries its
    represented proof even though the four zero roots need not consume it. *)
Record RawDynamicTruthNativeLocalZeroCurrentFieldRootsAt
    (M : RawPAModel) (witnessList baseContext : M) : Prop := {
  rawDynamicTruthNativeLocalZeroCurrentFields_witnessed :
    RawCodedPAAxiomWitnessContext M witnessList baseContext;
  rawDynamicTruthNativeLocalZeroCurrentFields_local : exists root,
    RawCodedPALocalProofOf M baseContext
      (rawQuotedFormulaCode M
        dynamicTruthLocalDecisionExclusiveBaseFormula) root;
  rawDynamicTruthNativeLocalZeroCurrentFields_crossLevel : exists root,
    RawCodedPALocalProofOf M baseContext
      (rawQuotedFormulaCode M
        dynamicTruthCrossLevelBaseFieldFormula) root;
  rawDynamicTruthNativeLocalZeroCurrentFields_shift : exists root,
    RawCodedPALocalProofOf M baseContext
      (rawQuotedFormulaCode M dynamicTruthShiftBaseFieldFormula) root;
  rawDynamicTruthNativeLocalZeroCurrentFields_substitution : exists root,
    RawCodedPALocalProofOf M baseContext
      (rawQuotedFormulaCode M
        dynamicTruthSubstitutionBaseFieldFormula) root;
  rawDynamicTruthNativeLocalZeroCurrentFields_axiomSoundness : exists root,
    RawCodedPALocalProofOf M baseContext
      (rawQuotedFormulaCode M
        dynamicTruthAxiomSoundnessBaseFieldFormula) root;
  rawDynamicTruthNativeLocalZeroCurrentFields_final : exists root,
    RawCodedPALocalProofOf M baseContext
      (rawNumeralValue M
        (formulaCode (restrictedPAConsistencyFormula 0))) root
}.

Arguments RawDynamicTruthNativeLocalZeroCurrentFieldRootsAt
  M witnessList baseContext : clear implicits.

(** Normalize all five spliced current-field graphs in one pass and rewrite
    their already-carried local proofs to the exact fixed targets.  This is
    the proof-resource analogue of the earlier local-coordinate zero case,
    but it retains every current theorem potentially useful to the rank-zero
    traversal compiler. *)
Theorem raw_dynamicTruthNativeLocalCurrentHelperContextAt_zero_field_roots :
    forall (M : RawPAModel), RawPASatisfies M -> forall
      (translation : RawCodedTemplateTranslation M)
      (tail : nat -> M) level
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      witnessList baseContext helperRoots,
  RawDynamicTruthNativeLocalCurrentHelperContextAt M translation
    tail level currentLocal currentCrossLevel currentShift
    currentSubstitution currentAxiomSoundness currentFinal
    witnessList baseContext helperRoots ->
  level = raw_zero M ->
  RawDynamicTruthNativeLocalZeroCurrentFieldRootsAt M
    witnessList baseContext.
Proof.
  intros M hPA translation tail level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal witnessList baseContext helperRoots
    hcurrent hlevel.
  destruct hcurrent as [[hgraphs _hcommon] hproofs].
  unfold RawSixFieldMasterGraphWitnessesAt in hgraphs.
  destruct hgraphs as
    (hlocalGraph & hcrossGraph & hshiftGraph & hsubstitutionGraph &
      haxiomGraph & hfinalGraph).
  destruct hproofs as
    (localRoot & crossLevelRoot & shiftRoot & substitutionRoot &
      axiomSoundnessRoot & finalRoot & hwitnessed & hlocal & hcrossLevel &
      hshift & hsubstitution & haxiomSoundness & hfinal & hhelpers).
  subst level.
  unfold dynamicTruthNativeSplicedLocalFieldGraph,
    dynamicTruthSplicedLocalFieldGraph in hlocalGraph.
  apply (proj1
    (raw_dynamicLocalFieldGraph_zero_iff M hPA
      dynamicTruthLocalDecisionExclusiveBaseFormulaCodeGraph
      dynamicTruthNativeLocalPositiveGraph tail currentLocal))
    in hlocalGraph.
  pose proof (proj1
    (dynamicTruthLocalDecisionExclusiveBaseFormulaCodeGraph_representation
      M hPA tail (raw_zero M) currentLocal) hlocalGraph) as hlocalCode.
  unfold dynamicTruthNativeSplicedCrossLevelFieldGraph,
    dynamicTruthSplicedCrossLevelFieldGraph in hcrossGraph.
  apply (proj1
    (raw_dynamicLocalFieldGraph_zero_iff M hPA
      dynamicTruthCrossLevelBaseFieldGraph
      dynamicTruthNativeCrossLevelPositiveGraph tail currentCrossLevel))
    in hcrossGraph.
  pose proof (proj1
    (dynamicTruthCrossLevelBaseFieldGraph_zero_iff
      M hPA tail currentCrossLevel) hcrossGraph) as hcrossCode.
  unfold dynamicTruthNativeSplicedShiftFieldGraph,
    dynamicTruthSplicedShiftFieldGraph in hshiftGraph.
  apply (proj1
    (raw_dynamicLocalFieldGraph_zero_iff M hPA
      dynamicTruthShiftBaseFieldGraph
      dynamicTruthNativeShiftPositiveGraph tail currentShift))
    in hshiftGraph.
  pose proof (proj1
    (dynamicTruthShiftBaseFieldGraph_zero_iff
      M hPA tail currentShift) hshiftGraph) as hshiftCode.
  unfold dynamicTruthNativeSplicedSubstitutionFieldGraph,
    dynamicTruthSplicedSubstitutionFieldGraph in hsubstitutionGraph.
  apply (proj1
    (raw_dynamicLocalFieldGraph_zero_iff M hPA
      dynamicTruthSubstitutionBaseFieldGraph
      dynamicTruthNativeSubstitutionPositiveGraph
      tail currentSubstitution)) in hsubstitutionGraph.
  pose proof (proj1
    (dynamicTruthSubstitutionBaseFieldGraph_zero_iff
      M hPA tail currentSubstitution) hsubstitutionGraph)
    as hsubstitutionCode.
  unfold dynamicTruthNativeSplicedAxiomSoundnessFieldGraph,
    dynamicTruthSplicedAxiomSoundnessFieldGraph in haxiomGraph.
  apply (proj1
    (raw_dynamicLocalFieldGraph_zero_iff M hPA
      dynamicTruthAxiomSoundnessBaseFieldGraph
      dynamicTruthNativeAxiomSoundnessPositiveGraph
      tail currentAxiomSoundness)) in haxiomGraph.
  pose proof (proj1
    (dynamicTruthAxiomSoundnessBaseFieldGraph_zero_iff
      M hPA tail currentAxiomSoundness) haxiomGraph) as haxiomCode.
  pose proof (proj1
    (compactRestrictedPAConsistencyFormulaCodeGraph_representation
      M tail (raw_zero M) currentFinal) hfinalGraph) as hfinalTarget.
  pose proof
    (raw_restrictedPAConsistencyFormulaCodeAt_standard M hPA 0)
    as hfinalStandard.
  change (rawNumeralValue M 0) with (raw_zero M) in hfinalStandard.
  pose proof
    (raw_restrictedPAConsistencyFormulaCodeAt_functional M hPA
      (raw_zero M) currentFinal
      (rawNumeralValue M
        (formulaCode (restrictedPAConsistencyFormula 0)))
      hfinalTarget hfinalStandard) as hfinalCode.
  constructor.
  - exact hwitnessed.
  - exists localRoot. rewrite <- hlocalCode. exact hlocal.
  - exists crossLevelRoot. rewrite <- hcrossCode. exact hcrossLevel.
  - exists shiftRoot. rewrite <- hshiftCode. exact hshift.
  - exists substitutionRoot.
    rewrite <- hsubstitutionCode. exact hsubstitution.
  - exists axiomSoundnessRoot.
    rewrite <- haxiomCode. exact haxiomSoundness.
  - exists finalRoot. rewrite <- hfinalCode. exact hfinal.
Qed.

(** Exact proof-producing state visible after the zero callback has been
    normalized.  Unlike [RawDynamicTruthNativeLocalCurrentHelperContextAt],
    this record contains no arbitrary current field codes and no spliced
    graph witnesses.  It retains all information which can matter to a proof
    compiler: the six literal field roots, the ordered forty-helper batch,
    and the four roots projected from the two predecessor assumptions. *)
Record RawDynamicTruthNativeLocalZeroNormalizedResourcesAt
    (M : RawPAModel)
    (translation : RawCodedTemplateTranslation M)
    (witnessList baseContext : M) (helperRoots : list M) : Prop := {
  rawDynamicTruthNativeLocalZeroNormalized_fields :
    RawDynamicTruthNativeLocalZeroCurrentFieldRootsAt M
      witnessList baseContext;
  rawDynamicTruthNativeLocalZeroNormalized_helpers :
    RawFixedPAHelperBatchLocalProofs M translation baseContext
      rawDynamicTruthReadyAndAllMixedQFPAHelpers helperRoots;
  rawDynamicTruthNativeLocalZeroNormalized_state :
    RawDynamicTruthPredecessorStateProjectionRootsAt M baseContext
}.

Arguments RawDynamicTruthNativeLocalZeroNormalizedResourcesAt
  M translation witnessList baseContext helperRoots : clear implicits.

(** Eliminate the current graphs exactly once.  The helper proof list is
    taken verbatim from the callback package, while the six field proofs are
    rewritten by the normalization theorem above. *)
Theorem raw_dynamicTruthNativeLocalCurrentHelperContextAt_zero_normalized :
    forall (M : RawPAModel), RawPASatisfies M -> forall
      (translation : RawCodedTemplateTranslation M)
      (tail : nat -> M) level
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      witnessList baseContext helperRoots,
  RawDynamicTruthNativeLocalCurrentHelperContextAt M translation
    tail level currentLocal currentCrossLevel currentShift
    currentSubstitution currentAxiomSoundness currentFinal
    witnessList baseContext helperRoots ->
  level = raw_zero M ->
  RawDynamicTruthPredecessorStateProjectionRootsAt M baseContext ->
  RawDynamicTruthNativeLocalZeroNormalizedResourcesAt M translation
    witnessList baseContext helperRoots.
Proof.
  intros M hPA translation tail level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal witnessList baseContext helperRoots
    hcurrent hlevel hstate.
  pose proof hcurrent as hfieldSource.
  pose proof
    (raw_dynamicTruthNativeLocalCurrentHelperContextAt_zero_field_roots
      M hPA translation tail level
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal witnessList baseContext helperRoots
      hfieldSource hlevel) as hfields.
  destruct hcurrent as
    [_ (localRoot & crossLevelRoot & shiftRoot & substitutionRoot &
      axiomSoundnessRoot & finalRoot & hwitnessed & hlocal & hcrossLevel &
      hshift & hsubstitution & haxiomSoundness & hfinal & hhelpers)].
  constructor.
  - exact hfields.
  - exact hhelpers.
  - exact hstate.
Qed.

(** Call-site-aligned rank-zero boundary.  The native zero callback does not
    receive an isolated trace: it receives that trace together with the
    complete current helper context, namely represented proofs of all six
    current master fields and the synchronized forty-helper batch.  A
    compiler quantified over arbitrary witnessed tails and traces is
    therefore stronger than the theorem actually needs.

    Keeping the current package available is mathematically important.  The
    trace fixes codes and relational successor witnesses, but it does not by
    itself manufacture represented PA proofs of the selected formulas.  The
    current package is the proof-producing resource already present at the
    callback.  The separately supplied local-field equality and proof root
    are deliberately absent: both are already derivable from this package at
    level zero, as witnessed by the normalization theorem above. *)
Definition
    RawDynamicTruthNativeLocalZeroGrowingDirectEvidenceCompilerOnCurrentHelperContext
    (M : RawPAModel)
    (translation : RawCodedTemplateTranslation M) : Prop :=
  forall (tail : nat -> M) level
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      witnessList baseContext (helperRoots : list M)
      inputGlobalSigma inputGlobalPi
      sigmaDomain piDomain sigmaEvidence piEvidence,
    RawDynamicTruthNativeLocalCurrentHelperContextAt M translation
      tail level currentLocal currentCrossLevel currentShift
      currentSubstitution currentAxiomSoundness currentFinal
      witnessList baseContext helperRoots ->
    RawDynamicTruthNativeLocalProofTraceAt M tail level
      inputGlobalSigma inputGlobalPi sigmaDomain piDomain
      sigmaEvidence piEvidence ->
    level = raw_zero M ->
    exists evidenceWitnessList evidenceContext,
      RawCodedPAAxiomWitnessContext M
        evidenceWitnessList evidenceContext /\
      RawContextListIncluded M baseContext evidenceContext /\
      RawDynamicTruthZeroDirectEvidenceRootsAt M evidenceContext.

Arguments
  RawDynamicTruthNativeLocalZeroGrowingDirectEvidenceCompilerOnCurrentHelperContext
  M translation : clear implicits.

(** Sharp traversal-completion boundary.  The two predecessor assumptions
    are conjunctions of a row bound and a synchronized table lookup.  Their
    four represented projections are entirely structural and can always be
    built from the witnessed callback tail.  Supplying them explicitly to
    the remaining compiler prevents the traversal-specific proof from
    repeating assumption introduction and four [And-E] steps. *)
Definition
    RawDynamicTruthNativeLocalZeroGrowingDirectEvidenceCompilerOnCurrentHelperAndStateProjection
    (M : RawPAModel)
    (translation : RawCodedTemplateTranslation M) : Prop :=
  forall (tail : nat -> M) level
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      witnessList baseContext (helperRoots : list M)
      inputGlobalSigma inputGlobalPi
      sigmaDomain piDomain sigmaEvidence piEvidence,
    RawDynamicTruthNativeLocalCurrentHelperContextAt M translation
      tail level currentLocal currentCrossLevel currentShift
      currentSubstitution currentAxiomSoundness currentFinal
      witnessList baseContext helperRoots ->
    RawDynamicTruthNativeLocalProofTraceAt M tail level
      inputGlobalSigma inputGlobalPi sigmaDomain piDomain
      sigmaEvidence piEvidence ->
    level = raw_zero M ->
    RawDynamicTruthPredecessorStateProjectionRootsAt M baseContext ->
    exists evidenceWitnessList evidenceContext,
      RawCodedPAAxiomWitnessContext M
        evidenceWitnessList evidenceContext /\
      RawContextListIncluded M baseContext evidenceContext /\
      RawDynamicTruthZeroDirectEvidenceRootsAt M evidenceContext.

Arguments
  RawDynamicTruthNativeLocalZeroGrowingDirectEvidenceCompilerOnCurrentHelperAndStateProjection
  M translation : clear implicits.

(** Fully normalized residual boundary.  The level equation, six current
    field graphs, and raw trace wrapper have disappeared.  The compiler sees
    precisely the represented resources available at rank zero and the
    complete two-successor trace which relates them to the requested four
    direct evidence roots. *)
Definition
    RawDynamicTruthNativeLocalZeroGrowingDirectEvidenceCompilerOnNormalizedResources
    (M : RawPAModel)
    (translation : RawCodedTemplateTranslation M) : Prop :=
  forall (tail : nat -> M) witnessList baseContext (helperRoots : list M)
      inputGlobalSigma inputGlobalPi
      sigmaDomain piDomain sigmaEvidence piEvidence,
    RawDynamicTruthNativeLocalZeroNormalizedResourcesAt M translation
      witnessList baseContext helperRoots ->
    RawDynamicTruthNativeLocalZeroFullTraceAt M tail
      inputGlobalSigma inputGlobalPi sigmaDomain piDomain
      sigmaEvidence piEvidence ->
    exists evidenceWitnessList evidenceContext,
      RawCodedPAAxiomWitnessContext M
        evidenceWitnessList evidenceContext /\
      RawContextListIncluded M baseContext evidenceContext /\
      RawDynamicTruthZeroDirectEvidenceRootsAt M evidenceContext.

Arguments
  RawDynamicTruthNativeLocalZeroGrowingDirectEvidenceCompilerOnNormalizedResources
  M translation : clear implicits.

(** Reconstruct the call-site-shaped boundary from the normalized one.  This
    adapter is the only place where current graph inversion, the level-zero
    trace equivalence, and state projection are synchronized. *)
Theorem
    raw_dynamicTruthNativeLocalZeroGrowingDirectEvidenceCompilerOnCurrentHelperAndStateProjection_of_normalized_resources
    : forall (M : RawPAModel), RawPASatisfies M -> forall
      (translation : RawCodedTemplateTranslation M),
  RawDynamicTruthNativeLocalZeroGrowingDirectEvidenceCompilerOnNormalizedResources
    M translation ->
  RawDynamicTruthNativeLocalZeroGrowingDirectEvidenceCompilerOnCurrentHelperAndStateProjection
    M translation.
Proof.
  intros M hPA translation hcompiler tail level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal witnessList baseContext helperRoots
    inputGlobalSigma inputGlobalPi sigmaDomain piDomain
    sigmaEvidence piEvidence hcurrent htrace hlevel hstate.
  pose proof
    (raw_dynamicTruthNativeLocalCurrentHelperContextAt_zero_normalized
      M hPA translation tail level
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal witnessList baseContext helperRoots
      hcurrent hlevel hstate) as hnormalized.
  subst level.
  exact (hcompiler tail witnessList baseContext helperRoots
    inputGlobalSigma inputGlobalPi sigmaDomain piDomain
    sigmaEvidence piEvidence hnormalized
    (proj1 (raw_dynamicTruthNativeLocalProofTraceAt_zero_iff M tail
      inputGlobalSigma inputGlobalPi sigmaDomain piDomain
      sigmaEvidence piEvidence) htrace)).
Qed.

(** Install the four structural state roots before invoking the sharp
    traversal compiler.  The current helper package supplies a witnessed PA
    tail, hence a realizable context, which is the sole premise of the
    projection theorem. *)
Theorem
    raw_dynamicTruthNativeLocalZeroGrowingDirectEvidenceCompilerOnCurrentHelperContext_of_state_projection
    : forall (M : RawPAModel), RawPASatisfies M -> forall
      (translation : RawCodedTemplateTranslation M),
  RawDynamicTruthNativeLocalZeroGrowingDirectEvidenceCompilerOnCurrentHelperAndStateProjection
    M translation ->
  RawDynamicTruthNativeLocalZeroGrowingDirectEvidenceCompilerOnCurrentHelperContext
    M translation.
Proof.
  intros M hPA translation hcompiler tail level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal witnessList baseContext helperRoots
    inputGlobalSigma inputGlobalPi sigmaDomain piDomain
    sigmaEvidence piEvidence hcurrent htrace hlevel.
  pose proof hcurrent as hfields.
  destruct hfields as
    [_ (storedLocalRoot & currentCrossLevelRoot & currentShiftRoot &
      currentSubstitutionRoot & currentAxiomSoundnessRoot &
      currentFinalRoot & hbaseWitnessed & hhelperRoots)].
  pose proof
    (raw_dynamicTruthPredecessorStateProjectionRootsAt_of_realizable
      M hPA baseContext
      (raw_codedPAAxiomWitnessContext_context_realizable
        M witnessList baseContext hbaseWitnessed)) as hstateRoots.
  exact (hcompiler tail level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal witnessList baseContext helperRoots
    inputGlobalSigma inputGlobalPi sigmaDomain piDomain
    sigmaEvidence piEvidence hcurrent htrace hlevel hstateRoots).
Qed.

(** Every former tail-only compiler satisfies the weaker callback-aligned
    interface.  This implication is intentionally one-way: a future concrete
    construction may use any of the represented current-field or helper
    proofs which the old interface discarded. *)
Theorem
    raw_dynamicTruthNativeLocalZeroGrowingDirectEvidenceCompilerOnCurrentHelperContext_of_witnessed_base
    : forall (M : RawPAModel), RawPASatisfies M -> forall
      (translation : RawCodedTemplateTranslation M),
  RawDynamicTruthNativeLocalZeroGrowingDirectEvidenceCompilerOnWitnessedBase
    M ->
  RawDynamicTruthNativeLocalZeroGrowingDirectEvidenceCompilerOnCurrentHelperContext
    M translation.
Proof.
  intros M hPA translation hbaseCompiler tail level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal witnessList baseContext helperRoots
    inputGlobalSigma inputGlobalPi sigmaDomain piDomain
    sigmaEvidence piEvidence hcurrent htrace hlevel.
  pose proof hcurrent as hfields.
  destruct hfields as
    [_ (storedLocalRoot & currentCrossLevelRoot & currentShiftRoot &
      currentSubstitutionRoot & currentAxiomSoundnessRoot &
      currentFinalRoot & hbaseWitnessed & hhelperRoots)].
  subst level.
  exact (hbaseCompiler tail baseContext
    inputGlobalSigma inputGlobalPi sigmaDomain piDomain
    sigmaEvidence piEvidence witnessList hbaseWitnessed
    (proj1 (raw_dynamicTruthNativeLocalProofTraceAt_zero_iff M tail
      inputGlobalSigma inputGlobalPi sigmaDomain piDomain
      sigmaEvidence piEvidence) htrace)).
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

(** The trace-facing four-root compiler is sufficient for the historical
    three-root callback boundary. *)
Theorem
    raw_dynamicTruthNativeLocalZeroGrowingLogicalRootsCompilerOnWitnessedBase_of_direct_evidence
    : forall (M : RawPAModel), RawPASatisfies M ->
  RawDynamicTruthNativeLocalZeroGrowingDirectEvidenceCompilerOnWitnessedBase
    M ->
  RawDynamicTruthNativeLocalZeroGrowingLogicalRootsCompilerOnWitnessedBase M.
Proof.
  intros M hPA hdirect tail level baseContext
    inputGlobalSigma inputGlobalPi sigmaDomain piDomain
    sigmaEvidence piEvidence sourceWitnessList hsource htrace hlevel.
  subst level.
  destruct (hdirect tail baseContext
    inputGlobalSigma inputGlobalPi sigmaDomain piDomain
    sigmaEvidence piEvidence sourceWitnessList hsource
    (proj1 (raw_dynamicTruthNativeLocalProofTraceAt_zero_iff M tail
      inputGlobalSigma inputGlobalPi sigmaDomain piDomain
      sigmaEvidence piEvidence) htrace)) as
    (evidenceWitnessList & evidenceContext & hevidenceWitnessed &
      hbaseEvidenceIncluded & hroots).
  exact (raw_dynamicTruthZeroGrowingLogicalRoots_of_direct_evidence
    M hPA baseContext evidenceWitnessList evidenceContext
    hevidenceWitnessed hbaseEvidenceIncluded hroots).
Qed.

(** The sharp fixed compiler handles the trace-shaped callback immediately:
    the trace and its zero-index equality are not discarded assumptions but
    parameters absent from the fixed conclusion. *)
Theorem
    raw_dynamicTruthNativeLocalZeroGrowingLogicalRootsCompilerOnWitnessedBase_of_fixed_logical_roots
    : forall (M : RawPAModel),
  RawDynamicTruthZeroGrowingLogicalRootsCompilerOnWitnessedBase M ->
  RawDynamicTruthNativeLocalZeroGrowingLogicalRootsCompilerOnWitnessedBase M.
Proof.
  intros M hfixed tail level baseContext
    inputGlobalSigma inputGlobalPi sigmaDomain piDomain
    sigmaEvidence piEvidence sourceWitnessList hsource _htrace _hlevel.
  exact (hfixed sourceWitnessList baseContext hsource).
Qed.

(** Any compiler for the canonical one-step package automatically handles
    the older trace-shaped call site.  All discarded trace coordinates are
    genuinely irrelevant: the adequate orbit alone supplies every premise
    consumed below. *)
Theorem
    raw_dynamicTruthNativeLocalZeroGrowingLogicalRootsCompilerOnWitnessedBase_of_canonical_global_step
    : forall (M : RawPAModel), RawPASatisfies M ->
  RawDynamicTruthNativeLocalZeroGrowingLogicalRootsCompilerOnCanonicalGlobalStep
    M ->
  RawDynamicTruthNativeLocalZeroGrowingLogicalRootsCompilerOnWitnessedBase M.
Proof.
  intros M hPA hcanonical tail level baseContext
    inputGlobalSigma inputGlobalPi sigmaDomain piDomain
    sigmaEvidence piEvidence sourceWitnessList hsource htrace hlevel.
  destruct
    (raw_dynamicTruthNativeLocalProofTraceAt_zero_global_predecessor
      M hPA tail level inputGlobalSigma inputGlobalPi
      sigmaDomain piDomain sigmaEvidence piEvidence htrace hlevel) as
    (hsuccessor & hbaseSigmaClosed & hbasePiClosed &
      hinputSigmaAdequate & hinputPiAdequate).
  exact (hcanonical sourceWitnessList baseContext
    inputGlobalSigma inputGlobalPi hsource hsuccessor
    hbaseSigmaClosed hbasePiClosed
    hinputSigmaAdequate hinputPiAdequate).
Qed.

(** Close the concrete rank-zero local field once the three predecessor
    logical roots have been compiled on a witnessed extension.  This is the
    proof-theoretic tail shared by every rank-zero resource interface: it
    identifies the stored base field, projects its exclusivity conjunct, and
    transports that conjunct to the chosen target before applying the direct
    template bridge. *)
Theorem raw_dynamicTruthNativeLocalZeroPredecessorRootAt_of_logical_roots :
    forall (M : RawPAModel), RawPASatisfies M -> forall
      baseWitnessList baseContext currentLocal currentLocalRoot
      targetWitnessList targetContext,
  RawCodedPAAxiomWitnessContext M baseWitnessList baseContext ->
  currentLocal = rawQuotedFormulaCode M
    dynamicTruthLocalDecisionExclusiveBaseFormula ->
  RawCodedPALocalProofOf M baseContext currentLocal currentLocalRoot ->
  RawCodedPAAxiomWitnessContext M targetWitnessList targetContext ->
  RawContextListIncluded M baseContext targetContext ->
  RawDynamicTruthPredecessorStateLogicalRootsAt M targetContext
    (rawDynamicTruthZeroSigmaDomainCode M)
    (rawDynamicTruthZeroPiDomainCode M)
    (rawDynamicTruthZeroSigmaEvidenceCode M)
    (rawDynamicTruthZeroPiEvidenceCode M) ->
  RawDynamicTruthLocalRootAt M targetContext
    (rawDynamicTruthImpPredecessorStateExclusivityCode M).
Proof.
  intros M hPA baseWitnessList baseContext currentLocal currentLocalRoot
    targetWitnessList targetContext hbaseWitnessed hfield hcurrentProof
    htargetWitnessed hincluded hlogicalRoots.
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
        baseWitnessList baseContext hbaseWitnessed)
      htargetWitnessed hincluded hexclusiveProjection
      (raw_dynamicTruthPredecessorStateTemplateApplicationBridgeAt_of_direct_logical_roots
        M hPA targetContext
        (rawDynamicTruthZeroSigmaDomainCode M)
        (rawDynamicTruthZeroPiDomainCode M)
        (rawDynamicTruthZeroSigmaEvidenceCode M)
        (rawDynamicTruthZeroPiEvidenceCode M)
        inputs hidentification hlogicalRoots)).
Qed.

(** Discharge the native zero callback from the weakest call-site-aligned
    four-root producer.  The current helper package is copied only to recover
    its witnessed base; all final field projection and template closure is
    delegated to the shared lemma above. *)
Theorem
    raw_dynamicTruthNativeLocalZeroPredecessorRootCompiler_of_current_helper_direct_evidence
    : forall (M : RawPAModel), RawPASatisfies M -> forall
      (translation : RawCodedTemplateTranslation M),
  RawDynamicTruthNativeLocalZeroGrowingDirectEvidenceCompilerOnCurrentHelperContext
    M translation ->
  RawDynamicTruthNativeLocalZeroPredecessorRootCompiler M translation.
Proof.
  intros M hPA translation hdirect tail level
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
  destruct (hdirect tail level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal
    witnessList baseContext helperRoots
    inputGlobalSigma inputGlobalPi sigmaDomain piDomain
    sigmaEvidence piEvidence hcurrent htrace hlevel) as
    (evidenceWitnessList & evidenceContext & hevidenceWitnessed &
      hbaseEvidenceIncluded & hroots).
  destruct (raw_dynamicTruthZeroGrowingLogicalRoots_of_direct_evidence
    M hPA baseContext evidenceWitnessList evidenceContext
    hevidenceWitnessed hbaseEvidenceIncluded hroots) as
    (targetWitnessList & targetContext & htargetWitnessed &
      hbaseTargetIncluded & hlogicalRoots).
  exists targetWitnessList, targetContext.
  split; [exact htargetWitnessed |].
  split; [exact hbaseTargetIncluded |].
  exact (raw_dynamicTruthNativeLocalZeroPredecessorRootAt_of_logical_roots
    M hPA witnessList baseContext currentLocal currentLocalRoot
    targetWitnessList targetContext hbaseWitnessed hfield hcurrentProof
    htargetWitnessed hbaseTargetIncluded hlogicalRoots).
Qed.

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
  exists targetWitnessList, targetContext.
  split; [exact htargetWitnessed |].
  split; [exact hincluded |].
  exact (raw_dynamicTruthNativeLocalZeroPredecessorRootAt_of_logical_roots
    M hPA witnessList baseContext currentLocal currentLocalRoot
    targetWitnessList targetContext hbaseWitnessed hfield hcurrentProof
    htargetWitnessed hincluded hlogicalRoots).
Qed.

End
  PABoundedRawCodedDynamicTruthNativeZeroPredecessorLogicalRootsCompilation.
