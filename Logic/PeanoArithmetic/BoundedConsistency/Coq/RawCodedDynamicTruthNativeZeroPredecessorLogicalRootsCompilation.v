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
  RawCodedFixedLevelTruthTotality
  RawCodedPAAxiomWitness
  RawCodedRestrictedPAProof
  RawCodedPALocalProofExistential
  RawCodedPALocalProofWitnessedContextMerge
  RawCodedTemplateProofCompiler
  RawCodedTemplateTernaryApplication
  RawCodedTernaryPredicateRootClosure
  RawCodedDynamicTruthLocalDecisionExclusiveBase
  RawCodedDynamicTruthPairedGlobalSuccessorGraph
  RawCodedDynamicTruthGlobalBaseRootClosure
  RawCodedDynamicTruthPairedGlobalFormulaCodeOrbitGraph
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
Import PABoundedRawCodedFixedLevelTruthTotality.
Import PABoundedRawCodedPAAxiomWitness.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPALocalProofWitnessedContextMerge.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedTemplateTernaryApplication.
Import PABoundedRawCodedTernaryPredicateRootClosure.
Import PABoundedRawCodedDynamicTruthLocalDecisionExclusiveBase.
Import PABoundedRawCodedDynamicTruthPairedGlobalSuccessorGraph.
Import PABoundedRawCodedDynamicTruthGlobalBaseRootClosure.
Import PABoundedRawCodedDynamicTruthPairedGlobalFormulaCodeOrbitGraph.
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

(** Sharp fixed rank-zero proof boundary.  Once the four formulas have been
    identified with literal quotations, their logical-root package depends
    only on the witnessed PA tail under the two fixed predecessor-state
    assumptions.  In particular, neither a native trace nor any global code
    selected by that trace occurs in the result type.

    This is the finite proof compiler that remains to be constructed.  The
    more elaborate interfaces below are retained as adapters for existing
    callback call sites and as an audit of where the fixed formulas came
    from. *)
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
