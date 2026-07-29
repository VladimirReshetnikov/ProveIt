(**
  Context-safe compilation of the two native successor-row projections.

  The historical staged-root boundary requested direct-template projection
  packages on the final context containing admissibility and both evidence
  assumptions.  A direct template proof can contain universal-introduction
  nodes, however, so compiling it on that open context would require the
  entire context to be invariant under unit shift.  The evidence assumptions
  are open in the three local-field variables; that is not the right
  eigenvariable condition.

  This file uses the standard safe order instead:

  1. recover deep closure of the exact global-orbit pair already present in
     the native trace;
  2. construct the Sigma/Pi direct structural translators for the exact row
     witnesses exposed by that trace;
  3. compile each closed row-to-branch-disjunction implication on the
     witnessed PA base, whose self-shift is available; and
  4. weaken the completed implication through the three atomically adequate
     assumptions before applying it to the corresponding row root.

  Thus no self-shift of an open evidence context is assumed or manufactured.
*)

From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors
  RawCodedRestrictedPAProof
  RawCodedContextLists
  RawCodedContextStructure
  RawCodedContextShift
  RawCodedProofBinaryConstructors
  RawCodedPALocalProofComposition
  RawCodedPAAxiomContextSelfShift
  RawCodedPALocalProofWitnessedContextMerge
  RawCodedPALocalProofContextInsertUnconditional
  RawCodedPALocalProofExistential
  RawCodedPALocalProofPropositionalRules
  RawCodedPALocalProofFiniteDisjunctionMatrix
  RawCodedTemplatePAEmbedding
  RawCodedTruthCertificateMasterFixedHelperBatchExtension
  RawCodedDynamicTruthMixedQFOpaqueQuantifierCellCompilation
  RawCodedDynamicTruthRestrictedUniversalLocalProofFieldGraph
  RawCodedDynamicTruthRestrictedExistentialLocalProofFieldGraph
  RawCodedTernaryPredicateDeepClosureShiftInterchange
  RawCodedTernaryPredicateDeepClosureOpeningCommuting
  RawCodedDynamicTruthPairedGlobalAdequateOrbitDeepClosure
  RawCodedDynamicTruthSigmaSuccessorRowGraph
  RawCodedDynamicTruthPiSuccessorRowGraph
  RawCodedDynamicTruthNativeLocalPositiveGraph
  RawCodedDynamicTruthLocalCollisionMatrixAssembly
  RawCodedDynamicTruthSuccessorRowBranchDisjunctionCompilation
  RawCodedDynamicTruthNativeLocalProofCompilation
  RawCodedDynamicTruthNativeLocalLeafRootCompiler
  RawCodedDynamicTruthNativeLocalDecisionRootCompilation
  RawCodedDynamicTruthNativeLocalStagedRootCompilation.

Module PABoundedRawCodedDynamicTruthNativeLocalRowProjectionCompilation.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedContextLists.
Import PABoundedRawCodedContextStructure.
Import PABoundedRawCodedContextShift.
Import PABoundedRawCodedProofBinaryConstructors.
Import PABoundedRawCodedPALocalProofComposition.
Import PABoundedRawCodedPAAxiomContextSelfShift.
Import PABoundedRawCodedPALocalProofWitnessedContextMerge.
Import PABoundedRawCodedPALocalProofContextInsertUnconditional.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPALocalProofPropositionalRules.
Import PABoundedRawCodedPALocalProofFiniteDisjunctionMatrix.
Import PABoundedRawCodedTemplatePAEmbedding.
Import PABoundedRawCodedTruthCertificateMasterFixedHelperBatchExtension.
Import PABoundedRawCodedDynamicTruthMixedQFOpaqueQuantifierCellCompilation.
Import
  PABoundedRawCodedDynamicTruthRestrictedUniversalLocalProofFieldGraph.
Import
  PABoundedRawCodedDynamicTruthRestrictedExistentialLocalProofFieldGraph.
Import PABoundedRawCodedTernaryPredicateDeepClosureShiftInterchange.
Import PABoundedRawCodedTernaryPredicateDeepClosureOpeningCommuting.
Import
  PABoundedRawCodedDynamicTruthPairedGlobalAdequateOrbitDeepClosure.
Import PABoundedRawCodedDynamicTruthSigmaSuccessorRowGraph.
Import PABoundedRawCodedDynamicTruthPiSuccessorRowGraph.
Import PABoundedRawCodedDynamicTruthNativeLocalPositiveGraph.
Import PABoundedRawCodedDynamicTruthLocalCollisionMatrixAssembly.
Import
  PABoundedRawCodedDynamicTruthSuccessorRowBranchDisjunctionCompilation.
Import PABoundedRawCodedDynamicTruthNativeLocalProofCompilation.
Import PABoundedRawCodedDynamicTruthNativeLocalLeafRootCompiler.
Import PABoundedRawCodedDynamicTruthNativeLocalDecisionRootCompilation.
Import PABoundedRawCodedDynamicTruthNativeLocalStagedRootCompilation.

(** Deep closure turns the public adequate-orbit trace into exactly the two
    relation-level interchange laws expected by the existing direct
    translators. *)
Lemma raw_dynamicTruthNativeLocalSigma_orbit_interchange :
    forall (M : RawPAModel), RawPASatisfies M ->
  RawDynamicTruthSigmaRestrictedUniversalOrbitTernaryInterchangeTotal M.
Proof.
  intros M hPA tail level globalSigma globalPi horbit.
  destruct
    (raw_dynamicTruthPairedGlobalFormulaCodeAdequateOrbitAt_deep_closed
      M hPA tail level globalSigma globalPi horbit) as [_ hpi].
  split.
  - exact (raw_codedTernaryApplicationShiftInterchange_of_deepClosed
      M hPA globalPi hpi).
  - exact (raw_codedTernaryApplicationOpeningInterchange_of_deepClosed_concrete
      M hPA globalPi hpi).
Qed.

Lemma raw_dynamicTruthNativeLocalPi_orbit_interchange :
    forall (M : RawPAModel), RawPASatisfies M ->
  RawDynamicTruthPiRestrictedExistentialOrbitTernaryInterchangeTotal M.
Proof.
  intros M hPA tail level globalSigma globalPi horbit.
  destruct
    (raw_dynamicTruthPairedGlobalFormulaCodeAdequateOrbitAt_deep_closed
      M hPA tail level globalSigma globalPi horbit) as [hsigma _].
  split.
  - exact (raw_codedTernaryApplicationShiftInterchange_of_deepClosed
      M hPA globalSigma hsigma).
  - exact (raw_codedTernaryApplicationOpeningInterchange_of_deepClosed_concrete
      M hPA globalSigma hsigma).
Qed.

(** Build both direct projection packages on the witnessed PA base.  The
    exact-row relation supplies the very numeral, domain, and lower-
    application traces used by the paired global successor; no fresh row
    parameters are selected. *)
Theorem
    raw_dynamicTruthNativeLocalExactRows_branch_projection_inputs_on_witnessed_base :
    forall (M : RawPAModel), RawPASatisfies M -> forall
      (tail : nat -> M) predecessorLevel inputGlobalSigma inputGlobalPi
      sigmaDomain piDomain sigmaEvidence piEvidence
      sigmaRowDomain piRowDomain lowerPiApplication lowerSigmaApplication
      witnessList baseContext,
  RawDynamicTruthNativeLocalProofTraceAt M tail predecessorLevel
    inputGlobalSigma inputGlobalPi sigmaDomain piDomain
    sigmaEvidence piEvidence ->
  RawDynamicTruthNativeLocalExactRowParametersAt M predecessorLevel
    inputGlobalSigma inputGlobalPi sigmaEvidence piEvidence
    sigmaRowDomain piRowDomain lowerPiApplication lowerSigmaApplication ->
  RawCodedPAAxiomWitnessContext M witnessList baseContext ->
  exists
      sigmaInputs :
        RawDynamicTruthSigmaSuccessorRowBranchDisjunctionCompilationInputs
          M baseContext sigmaRowDomain lowerPiApplication,
    exists
      piInputs :
        RawDynamicTruthPiSuccessorRowBranchDisjunctionCompilationInputs
          M baseContext piRowDomain lowerSigmaApplication,
      True.
Proof.
  intros M hPA tail predecessorLevel inputGlobalSigma inputGlobalPi
    sigmaDomain piDomain sigmaEvidence piEvidence
    sigmaRowDomain piRowDomain lowerPi lowerSigma
    witnessList baseContext htrace hlinked hwitness.
  destruct htrace as [horbit htraceBody].
  destruct hlinked as
    (inputLevel & evidenceGlobalSigma & evidenceGlobalPi &
      localSigmaRow & localPiRow & sigmaUpperNumeral & piUpperNumeral &
      hlevel & hsigmaNumeral & hsigmaDomain & hlowerPi & hsigmaRow &
      hpiNumeral & hpiDomain & hlowerSigma & hpiRow & hwrapper &
      hsigmaEvidence & hpiEvidence).
  subst inputLevel.
  pose proof
    (rawDynamicTruthSigmaRestrictedUniversalOrbitDirectCompilerTotal_of_interchange
      M hPA (raw_dynamicTruthNativeLocalSigma_orbit_interchange M hPA))
    as hsigmaCompiler.
  pose proof
    (rawDynamicTruthPiRestrictedExistentialOrbitDirectCompilerTotal_of_interchange
      M hPA (raw_dynamicTruthNativeLocalPi_orbit_interchange M hPA))
    as hpiCompiler.
  destruct (hsigmaCompiler tail (raw_succ M predecessorLevel)
    inputGlobalSigma inputGlobalPi horbit
    sigmaUpperNumeral sigmaRowDomain lowerPi
    hsigmaNumeral hsigmaDomain hlowerPi) as
    [sigmaDirectInputs hsigmaIdentification].
  destruct (hpiCompiler tail (raw_succ M predecessorLevel)
    inputGlobalSigma inputGlobalPi horbit
    piUpperNumeral piRowDomain lowerSigma
    hpiNumeral hpiDomain hlowerSigma) as
    [piDirectInputs hpiIdentification].
  assert (hbaseRealizable : RawContextListRealizable M baseContext).
  { exact (raw_codedPAAxiomWitnessContext_context_realizable
      M witnessList baseContext hwitness). }
  assert (hbaseShift : RawContextShift M baseContext baseContext).
  { exact (raw_codedPAAxiomWitnessContext_selfShift
      M hPA witnessList baseContext hwitness). }
  exists
    {| rawDynamicTruthSigmaBranchDisjunction_contextRealizable :=
         hbaseRealizable;
       rawDynamicTruthSigmaBranchDisjunction_contextSelfShift :=
         hbaseShift;
       rawDynamicTruthSigmaBranchDisjunction_directInputs :=
         sigmaDirectInputs;
       rawDynamicTruthSigmaBranchDisjunction_identification :=
         hsigmaIdentification |}.
  exists
    {| rawDynamicTruthPiBranchDisjunction_contextRealizable :=
         hbaseRealizable;
       rawDynamicTruthPiBranchDisjunction_contextSelfShift :=
         hbaseShift;
       rawDynamicTruthPiBranchDisjunction_directInputs :=
         piDirectInputs;
       rawDynamicTruthPiBranchDisjunction_identification :=
         hpiIdentification |}.
  exact I.
Qed.

(** The useful endpoint contains the projected [Or7]/[Or6] roots, not the
    direct-translation records used internally to obtain their implication
    theorems. *)
Definition RawDynamicTruthNativeLocalProjectedRowRootsAt
    (M : RawPAModel)
    (baseContext sigmaDomain piDomain sigmaEvidence piEvidence
      lowerPiApplication lowerSigmaApplication : M) : Prop :=
  exists sigmaOrRoot piOrRoot : M,
    RawCodedPALocalProofOf M
      (rawDynamicTruthNativeLocalExclusivePiContextOn M baseContext
        sigmaDomain piDomain sigmaEvidence piEvidence)
      (rawDynamicTruthLocalSigmaOr7Code M lowerPiApplication)
      sigmaOrRoot /\
    RawCodedPALocalProofOf M
      (rawDynamicTruthNativeLocalExclusivePiContextOn M baseContext
        sigmaDomain piDomain sigmaEvidence piEvidence)
      (rawDynamicTruthLocalPiOr6Code M lowerSigmaApplication)
      piOrRoot.

Arguments RawDynamicTruthNativeLocalProjectedRowRootsAt
  M baseContext sigmaDomain piDomain sigmaEvidence piEvidence
  lowerPiApplication lowerSigmaApplication : clear implicits.

(** Compile on the witnessed base, then weaken the finished implication
    through admissibility and both evidence assumptions.  Each weakening is
    justified by the atomic adequacy already derived from the exact native
    trace; no shift of the enlarged context occurs. *)
Theorem
    raw_dynamicTruthNativeLocalProjectedRowRootsAt_of_exact_rows :
    forall (M : RawPAModel), RawPASatisfies M -> forall
      (tail : nat -> M) predecessorLevel inputGlobalSigma inputGlobalPi
      sigmaDomain piDomain sigmaEvidence piEvidence
      sigmaRowDomain piRowDomain lowerPiApplication lowerSigmaApplication
      witnessList baseContext,
  RawDynamicTruthNativeLocalProofTraceAt M tail predecessorLevel
    inputGlobalSigma inputGlobalPi sigmaDomain piDomain
    sigmaEvidence piEvidence ->
  RawDynamicTruthNativeLocalExactRowParametersAt M predecessorLevel
    inputGlobalSigma inputGlobalPi sigmaEvidence piEvidence
    sigmaRowDomain piRowDomain lowerPiApplication lowerSigmaApplication ->
  RawCodedPAAxiomWitnessContext M witnessList baseContext ->
  RawDynamicTruthLocalRootAt M
    (rawDynamicTruthNativeLocalExclusivePiContextOn M baseContext
      sigmaDomain piDomain sigmaEvidence piEvidence)
    (rawDynamicTruthSigmaSuccessorRowCode M
      sigmaRowDomain lowerPiApplication) ->
  RawDynamicTruthLocalRootAt M
    (rawDynamicTruthNativeLocalExclusivePiContextOn M baseContext
      sigmaDomain piDomain sigmaEvidence piEvidence)
    (rawDynamicTruthPiSuccessorRowCode M
      piRowDomain lowerSigmaApplication) ->
  RawDynamicTruthNativeLocalProjectedRowRootsAt M baseContext
    sigmaDomain piDomain sigmaEvidence piEvidence
    lowerPiApplication lowerSigmaApplication.
Proof.
  intros M hPA tail predecessorLevel inputGlobalSigma inputGlobalPi
    sigmaDomain piDomain sigmaEvidence piEvidence
    sigmaRowDomain piRowDomain lowerPi lowerSigma
    witnessList baseContext htrace hlinked hwitness
    [sigmaRowRoot hsigmaRow] [piRowRoot hpiRow].
  destruct
    (raw_dynamicTruthNativeLocalExactRows_branch_projection_inputs_on_witnessed_base
      M hPA tail predecessorLevel inputGlobalSigma inputGlobalPi
      sigmaDomain piDomain sigmaEvidence piEvidence
      sigmaRowDomain piRowDomain lowerPi lowerSigma
      witnessList baseContext htrace hlinked hwitness) as
    (sigmaInputs & piInputs & _).
  pose proof
    (raw_codedPALocalProofOf_dynamicTruthSigmaSuccessorRowBranchDisjunctionImp
      M hPA baseContext sigmaRowDomain lowerPi sigmaInputs)
    as hsigmaImpBase.
  pose proof
    (raw_codedPALocalProofOf_dynamicTruthPiSuccessorRowBranchDisjunctionImp
      M hPA baseContext piRowDomain lowerSigma piInputs)
    as hpiImpBase.
  pose proof
    (raw_dynamicTruthNativeLocalProofTraceAt_linked_adequacy
      M hPA tail predecessorLevel inputGlobalSigma inputGlobalPi
      sigmaDomain piDomain sigmaEvidence piEvidence
      sigmaRowDomain piRowDomain lowerPi lowerSigma htrace hlinked)
    as hadequacy.
  destruct hadequacy as
    [hsigmaDomain hpiDomain hsigmaEvidence hpiEvidence hadmissible
      hsigmaRowDomain hpiRowDomain hlowerPi hlowerSigma].
  assert (hbaseRealizable : RawContextListRealizable M baseContext).
  { exact (raw_codedPAAxiomWitnessContext_context_realizable
      M witnessList baseContext hwitness). }
  set (admissibleCode :=
    rawDynamicTruthLocalAdmissibleCode M sigmaDomain piDomain).
  set (admissibleContext :=
    rawListNode M admissibleCode baseContext).
  set (sigmaContext := rawListNode M sigmaEvidence admissibleContext).
  set (exclusiveContext := rawListNode M piEvidence sigmaContext).
  assert (hadmissibleRealizable :
      RawContextListRealizable M admissibleContext).
  { unfold admissibleContext.
    exact (raw_contextList_cons_realizable M hPA baseContext
      admissibleCode hbaseRealizable). }
  assert (hsigmaRealizable : RawContextListRealizable M sigmaContext).
  { unfold sigmaContext.
    exact (raw_contextList_cons_realizable M hPA admissibleContext
      sigmaEvidence hadmissibleRealizable). }

  destruct (raw_codedPALocalProof_adequateConsTransplant M hPA
    baseContext admissibleCode
    (rawFormulaImpCode M
      (rawDynamicTruthSigmaSuccessorRowCode M sigmaRowDomain lowerPi)
      (rawDynamicTruthLocalSigmaOr7Code M lowerPi))
    (rawDynamicTruthSigmaSuccessorRowBranchDisjunctionImpRoot
      M hPA baseContext sigmaRowDomain lowerPi sigmaInputs)
    hadmissible hbaseRealizable hsigmaImpBase) as
    [sigmaImpAdmissible hsigmaImpAdmissible].
  destruct (raw_codedPALocalProof_adequateConsTransplant M hPA
    admissibleContext sigmaEvidence
    (rawFormulaImpCode M
      (rawDynamicTruthSigmaSuccessorRowCode M sigmaRowDomain lowerPi)
      (rawDynamicTruthLocalSigmaOr7Code M lowerPi))
    sigmaImpAdmissible hsigmaEvidence hadmissibleRealizable
    hsigmaImpAdmissible) as [sigmaImpAtSigma hsigmaImpAtSigma].
  destruct (raw_codedPALocalProof_adequateConsTransplant M hPA
    sigmaContext piEvidence
    (rawFormulaImpCode M
      (rawDynamicTruthSigmaSuccessorRowCode M sigmaRowDomain lowerPi)
      (rawDynamicTruthLocalSigmaOr7Code M lowerPi))
    sigmaImpAtSigma hpiEvidence hsigmaRealizable hsigmaImpAtSigma) as
    [sigmaImpFinal hsigmaImpFinal].

  destruct (raw_codedPALocalProof_adequateConsTransplant M hPA
    baseContext admissibleCode
    (rawFormulaImpCode M
      (rawDynamicTruthPiSuccessorRowCode M piRowDomain lowerSigma)
      (rawDynamicTruthLocalPiOr6Code M lowerSigma))
    (rawDynamicTruthPiSuccessorRowBranchDisjunctionImpRoot
      M hPA baseContext piRowDomain lowerSigma piInputs)
    hadmissible hbaseRealizable hpiImpBase) as
    [piImpAdmissible hpiImpAdmissible].
  destruct (raw_codedPALocalProof_adequateConsTransplant M hPA
    admissibleContext sigmaEvidence
    (rawFormulaImpCode M
      (rawDynamicTruthPiSuccessorRowCode M piRowDomain lowerSigma)
      (rawDynamicTruthLocalPiOr6Code M lowerSigma))
    piImpAdmissible hsigmaEvidence hadmissibleRealizable
    hpiImpAdmissible) as [piImpAtSigma hpiImpAtSigma].
  destruct (raw_codedPALocalProof_adequateConsTransplant M hPA
    sigmaContext piEvidence
    (rawFormulaImpCode M
      (rawDynamicTruthPiSuccessorRowCode M piRowDomain lowerSigma)
      (rawDynamicTruthLocalPiOr6Code M lowerSigma))
    piImpAtSigma hpiEvidence hsigmaRealizable hpiImpAtSigma) as
    [piImpFinal hpiImpFinal].

  assert (hcontextEq : exclusiveContext =
      rawDynamicTruthNativeLocalExclusivePiContextOn M baseContext
        sigmaDomain piDomain sigmaEvidence piEvidence).
  { reflexivity. }
  rewrite <- hcontextEq in hsigmaRow, hpiRow.
  fold exclusiveContext in hsigmaImpFinal, hpiImpFinal.
  exists
    (rawProofImpERoot M exclusiveContext
      (rawDynamicTruthSigmaSuccessorRowCode M sigmaRowDomain lowerPi)
      (rawDynamicTruthLocalSigmaOr7Code M lowerPi)
      sigmaImpFinal sigmaRowRoot),
    (rawProofImpERoot M exclusiveContext
      (rawDynamicTruthPiSuccessorRowCode M piRowDomain lowerSigma)
      (rawDynamicTruthLocalPiOr6Code M lowerSigma)
      piImpFinal piRowRoot).
  split.
  - exact (raw_codedPALocalProofOf_impE M hPA exclusiveContext
      (rawDynamicTruthSigmaSuccessorRowCode M sigmaRowDomain lowerPi)
      (rawDynamicTruthLocalSigmaOr7Code M lowerPi)
      sigmaImpFinal sigmaRowRoot hsigmaImpFinal hsigmaRow).
  - exact (raw_codedPALocalProofOf_impE M hPA exclusiveContext
      (rawDynamicTruthPiSuccessorRowCode M piRowDomain lowerSigma)
      (rawDynamicTruthLocalPiOr6Code M lowerSigma)
      piImpFinal piRowRoot hpiImpFinal hpiRow).
Qed.

(** A strictly smaller staged package than the historical one.  It retains
    the genuinely proof-producing case roots, row roots, collision kernel,
    and context transports, but drops both direct projection packages.  The
    preceding theorem reconstructs those projections after compiling their
    closed implications on the witnessed base. *)
Definition RawDynamicTruthNativeLocalReducedStagedRootsAt
    (M : RawPAModel)
    (baseContext sigmaDomain piDomain sigmaEvidence piEvidence
      sigmaRowDomain piRowDomain
      lowerPiApplication lowerSigmaApplication : M) : Prop :=
    RawDynamicTruthNativeLocalDomainCaseDecisionRootsAt M
      baseContext sigmaDomain piDomain sigmaEvidence piEvidence /\
    RawDynamicTruthLocalRootAt M
      (rawDynamicTruthNativeLocalExclusivePiContextOn M baseContext
        sigmaDomain piDomain sigmaEvidence piEvidence)
      (rawDynamicTruthSigmaSuccessorRowCode M
        sigmaRowDomain lowerPiApplication) /\
    RawDynamicTruthLocalRootAt M
      (rawDynamicTruthNativeLocalExclusivePiContextOn M baseContext
        sigmaDomain piDomain sigmaEvidence piEvidence)
      (rawDynamicTruthPiSuccessorRowCode M
        piRowDomain lowerSigmaApplication) /\
    exists currentKernel :
        RawDynamicTruthNativeLocalCurrentKernelInputsAt M baseContext
          lowerPiApplication lowerSigmaApplication,
      RawContextShift M
        (rawDynamicTruthNativeLocalAdmissibleContextOn M baseContext
          sigmaDomain piDomain)
        (rawDynamicTruthNativeLocalAdmissibleContextOn M baseContext
          sigmaDomain piDomain) /\
      RawContextShift M
        (rawDynamicTruthNativeLocalExclusiveSigmaContextOn M baseContext
          sigmaDomain piDomain sigmaEvidence)
        (rawDynamicTruthNativeLocalExclusiveSigmaContextOn M baseContext
          sigmaDomain piDomain sigmaEvidence) /\
      RawContextShift M
        (rawDynamicTruthNativeLocalExclusivePiContextOn M baseContext
          sigmaDomain piDomain sigmaEvidence piEvidence)
        (rawDynamicTruthNativeLocalExclusivePiContextOn M baseContext
          sigmaDomain piDomain sigmaEvidence piEvidence).

Arguments RawDynamicTruthNativeLocalReducedStagedRootsAt
  M baseContext sigmaDomain piDomain sigmaEvidence piEvidence
  sigmaRowDomain piRowDomain lowerPiApplication lowerSigmaApplication
  : clear implicits.

(** End-to-end local-field construction from the reduced package.  The proof
    deliberately follows the established forty-helper assembly, changing
    only the projection phase: row-to-[Or] implications are compiled on the
    witnessed base and weakened into the exclusive context before the finite
    collision matrix is run. *)
Theorem
    raw_dynamicTruthNativeLocalFieldRootOn_of_reduced_staged_roots_and_40_helpers :
    forall (M : RawPAModel), RawPASatisfies M -> forall
      translation witnessList baseContext helperRoots
      (tail : nat -> M) predecessorLevel inputGlobalSigma inputGlobalPi
      sigmaDomain piDomain sigmaEvidence piEvidence
      sigmaRowDomain piRowDomain lowerPiApplication lowerSigmaApplication,
  RawCodedTemplatePAAgreement M translation ->
  RawCodedPAAxiomWitnessContext M witnessList baseContext ->
  RawFixedPAHelperBatchLocalProofs M translation baseContext
    rawDynamicTruthReadyAndAllMixedQFPAHelpers helperRoots ->
  RawDynamicTruthNativeLocalProofTraceAt M tail predecessorLevel
    inputGlobalSigma inputGlobalPi sigmaDomain piDomain
    sigmaEvidence piEvidence ->
  RawDynamicTruthNativeLocalExactRowParametersAt M predecessorLevel
    inputGlobalSigma inputGlobalPi sigmaEvidence piEvidence
    sigmaRowDomain piRowDomain lowerPiApplication lowerSigmaApplication ->
  RawDynamicTruthNativeLocalReducedStagedRootsAt M baseContext
    sigmaDomain piDomain sigmaEvidence piEvidence
    sigmaRowDomain piRowDomain lowerPiApplication lowerSigmaApplication ->
  RawDynamicTruthNativeLocalFieldRootOn M baseContext
    sigmaDomain piDomain sigmaEvidence piEvidence.
Proof.
  intros M hPA translation witnessList baseContext helperRoots
    tail predecessorLevel inputGlobalSigma inputGlobalPi
    sigmaDomain piDomain sigmaEvidence piEvidence
    sigmaRowDomain piRowDomain lowerPi lowerSigma
    hagreement hwitness hhelpers htrace hlinked hstaged.
  destruct hstaged as
    (hcases & hsigmaRow & hpiRow & currentKernel &
      hadmissibleShift & hsigmaShift & hpiShift).
  pose proof
    (raw_dynamicTruthNativeLocalProofTraceAt_linked_adequacy
      M hPA tail predecessorLevel inputGlobalSigma inputGlobalPi
      sigmaDomain piDomain sigmaEvidence piEvidence
      sigmaRowDomain piRowDomain lowerPi lowerSigma htrace hlinked)
    as hadequacy.
  destruct hadequacy as
    [hsigmaDomain hpiDomain hsigmaEvidence hpiEvidence hadmissible
      hsigmaRowDomain hpiRowDomain hlowerPi hlowerSigma].
  pose proof
    (raw_dynamicTruthNativeLocalProjectedRowRootsAt_of_exact_rows
      M hPA tail predecessorLevel inputGlobalSigma inputGlobalPi
      sigmaDomain piDomain sigmaEvidence piEvidence
      sigmaRowDomain piRowDomain lowerPi lowerSigma
      witnessList baseContext htrace hlinked hwitness
      hsigmaRow hpiRow) as hprojected.
  destruct hprojected as
    (sigmaOrRoot & piOrRoot & hsigmaOr & hpiOr).
  pose proof
    (raw_dynamicTruthNativeLocalCollisionResidualInputsAt_of_current_kernel
      M hPA translation witnessList baseContext helperRoots
      lowerPi lowerSigma hagreement hwitness hhelpers
      hlowerPi hlowerSigma currentKernel) as hresidual.
  pose proof
    (raw_dynamicTruthNativeLocalCollisionMatrixInputs_of_40_helpers
      M hPA translation witnessList baseContext helperRoots
      lowerPi lowerSigma hagreement hwitness hhelpers hresidual)
    as hbaseInputs.
  pose proof
    (raw_dynamicTruthLocalCollisionMatrixInputs_on_exclusive_context
      M hPA baseContext sigmaDomain piDomain sigmaEvidence piEvidence
      lowerPi lowerSigma hbaseInputs hadmissible
      hsigmaEvidence hpiEvidence
      hadmissibleShift hsigmaShift hpiShift)
    as hexclusiveInputs.
  set (exclusiveContext :=
    rawDynamicTruthNativeLocalExclusivePiContextOn M baseContext
      sigmaDomain piDomain sigmaEvidence piEvidence).
  assert (matrixResources :
      RawFiniteDisjunctionMatrixResources M
        (rawDynamicTruthLocalSigmaBranches M lowerPi)
        (rawDynamicTruthLocalPiBranches M lowerSigma)
        exclusiveContext).
  { apply (raw_dynamicTruthLocalCollisionMatrixResources_of_adequacy
      M hPA exclusiveContext lowerPi lowerSigma).
    - exact (rawDynamicTruthLocalCollision_context_realizable
        M exclusiveContext lowerPi lowerSigma hexclusiveInputs).
    - exact hlowerPi.
    - exact hlowerSigma. }
  destruct
    (raw_codedPALocalProofOf_dynamicTruthLocalCollisionMatrix_bottom
      M hPA exclusiveContext lowerPi lowerSigma
      sigmaOrRoot piOrRoot hexclusiveInputs matrixResources
      hsigmaOr hpiOr) as [bottomRoot hbottom].
  assert (hdecision : RawDynamicTruthNativeLocalDecisionRootOn M
      baseContext sigmaDomain piDomain sigmaEvidence piEvidence).
  { apply (raw_dynamicTruthNativeLocalDecisionRootOn_of_structural_roots
      M hPA baseContext sigmaDomain piDomain sigmaEvidence piEvidence).
    - apply (raw_dynamicTruthNativeLocalAdmissibleDomainRootAt_realizable
        M hPA baseContext sigmaDomain piDomain).
      exact (raw_codedPAAxiomWitnessContext_context_realizable
        M witnessList baseContext hwitness).
    - exact hcases. }
  apply (raw_dynamicTruthNativeLocalFieldRootOn_of_leaf_roots
    M hPA baseContext sigmaDomain piDomain sigmaEvidence piEvidence).
  - exact (raw_codedPAAxiomWitnessContext_selfShift
      M hPA witnessList baseContext hwitness).
  - split.
    + exact hdecision.
    + exists bottomRoot. exact hbottom.
Qed.

End PABoundedRawCodedDynamicTruthNativeLocalRowProjectionCompilation.
