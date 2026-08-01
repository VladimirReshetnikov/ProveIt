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
  RawCodedFixedLevelTruthTotality
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
  RawCodedPALocalProofFiniteDisjunction
  RawCodedPALocalProofFiniteDisjunctionMatrix
  RawCodedTemplateProofCompiler
  RawCodedTemplateProofCompilerSelfShiftTail
  RawCodedTemplateDirectStructuralTranslation
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
  RawCodedDynamicTruthUniversalLeafSourceTemplate
  RawCodedDynamicTruthPiUniversalLeafSourceTemplate
  RawCodedDynamicTruthUniversalLeafProofCompilation
  RawCodedDynamicTruthPiTemplateDirectInputs
  RawCodedDynamicTruthQuantifierConditionalCellCompilation
  RawCodedDynamicTruthImpBranchExclusivity
  RawCodedDynamicTruthQuantifierBranchExclusivity
  RawCodedDynamicTruthMixedQFBranchExclusivity
  RawCodedDynamicTruthBinderOffDiagonalExclusivity
  RawCodedDynamicTruthBinderPrincipalProjectionCompilation
  RawCodedDynamicTruthNativeLocalPositiveGraph
  RawCodedDynamicTruthLocalCollisionMatrixAssembly
  RawCodedDynamicTruthSuccessorRowBranchDisjunctionCompilation
  RawCodedDynamicTruthSigmaDomainProjectionProofCompilation
  RawCodedDynamicTruthPiDomainProjectionProofCompilation
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
Import PABoundedRawCodedFixedLevelTruthTotality.
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
Import PABoundedRawCodedPALocalProofFiniteDisjunction.
Import PABoundedRawCodedPALocalProofFiniteDisjunctionMatrix.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedTemplateProofCompilerSelfShiftTail.
Import PABoundedRawCodedTemplateDirectStructuralTranslation.
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
Import PABoundedRawCodedDynamicTruthUniversalLeafSourceTemplate.
Import PABoundedRawCodedDynamicTruthPiUniversalLeafSourceTemplate.
Import PABoundedRawCodedDynamicTruthUniversalLeafProofCompilation.
Import PABoundedRawCodedDynamicTruthPiTemplateDirectInputs.
Import PABoundedRawCodedDynamicTruthQuantifierConditionalCellCompilation.
Import PABoundedRawCodedDynamicTruthImpBranchExclusivity.
Import PABoundedRawCodedDynamicTruthQuantifierBranchExclusivity.
Import PABoundedRawCodedDynamicTruthMixedQFBranchExclusivity.
Import PABoundedRawCodedDynamicTruthBinderOffDiagonalExclusivity.
Import PABoundedRawCodedDynamicTruthBinderPrincipalProjectionCompilation.
Import PABoundedRawCodedDynamicTruthNativeLocalPositiveGraph.
Import PABoundedRawCodedDynamicTruthLocalCollisionMatrixAssembly.
Import
  PABoundedRawCodedDynamicTruthSuccessorRowBranchDisjunctionCompilation.
Import PABoundedRawCodedDynamicTruthSigmaDomainProjectionProofCompilation.
Import PABoundedRawCodedDynamicTruthPiDomainProjectionProofCompilation.
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

(** ------------------------------------------------------------------
    Open domain-projection implications on the witnessed base.

    The older domain-projection graph exported a closed [All13] theorem.
    Native predecessor compilation already owns the exact direct translator
    and a witnessed base that shifts to itself, so closing and reopening all
    thirteen columns would add proof nodes without adding information.  The
    two roots below compile the open row-to-domain implications directly. *)

Definition rawDynamicTruthSigmaSuccessorRowDomainProjectionImpRoot
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (context concreteDomain concreteLowerApplication : M)
    (compilation :
      RawDynamicTruthSigmaSuccessorRowBranchDisjunctionCompilationInputs
        M context concreteDomain concreteLowerApplication) : M :=
  rawTemplateProofCodeOnTail
    (rawDirectStructuralTemplateTranslation M hPA
      (rawDynamicTruthSigmaBranchDisjunction_directInputs compilation))
    context coqDynamicTruthSigmaDomainProjectionProof.

Definition rawDynamicTruthPiSuccessorRowDomainProjectionImpRoot
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (context concreteDomain concreteLowerApplication : M)
    (compilation :
      RawDynamicTruthPiSuccessorRowBranchDisjunctionCompilationInputs
        M context concreteDomain concreteLowerApplication) : M :=
  rawTemplateProofCodeOnTail
    (rawDirectStructuralTemplateTranslation M hPA
      (rawDynamicTruthPiBranchDisjunction_directInputs compilation))
    context coqDynamicTruthPiDomainProjectionProof.

Arguments rawDynamicTruthSigmaSuccessorRowDomainProjectionImpRoot
  M hPA context concreteDomain concreteLowerApplication compilation
  : clear implicits.
Arguments rawDynamicTruthPiSuccessorRowDomainProjectionImpRoot
  M hPA context concreteDomain concreteLowerApplication compilation
  : clear implicits.

Theorem
    raw_codedPALocalProofOf_dynamicTruthSigmaSuccessorRowDomainProjectionImp :
  forall (M : RawPAModel) (hPA : RawPASatisfies M)
    context concreteDomain concreteLowerApplication
    (compilation :
      RawDynamicTruthSigmaSuccessorRowBranchDisjunctionCompilationInputs
        M context concreteDomain concreteLowerApplication),
  RawCodedPALocalProofOf M context
    (rawDynamicTruthSigmaDomainProjectionCode M
      concreteDomain concreteLowerApplication)
    (rawDynamicTruthSigmaSuccessorRowDomainProjectionImpRoot
      M hPA context concreteDomain concreteLowerApplication compilation).
Proof.
  intros M hPA context concreteDomain concreteLowerApplication compilation.
  unfold rawDynamicTruthSigmaSuccessorRowDomainProjectionImpRoot.
  rewrite <- (rawCoqDynamicTruthSigmaDomainProjectionCode_eq_native
    M hPA concreteDomain concreteLowerApplication).
  rewrite <-
    (rawDirect_coqDynamicTruthSigmaDomainProjection_identified
      M (rawDynamicTruthSigmaBranchDisjunction_directInputs compilation)
      concreteDomain concreteLowerApplication
      (rawDynamicTruthSigmaBranchDisjunction_identification compilation)).
  change (RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail
      (rawDirectStructuralTemplateTranslation M hPA
        (rawDynamicTruthSigmaBranchDisjunction_directInputs compilation))
      context nil)
    (rawTemplateFormula
      (rawDirectStructuralTemplateTranslation M hPA
        (rawDynamicTruthSigmaBranchDisjunction_directInputs compilation))
      coqDynamicTruthSigmaDomainProjectionFormula)
    (rawTemplateProofCodeOnTail
      (rawDirectStructuralTemplateTranslation M hPA
        (rawDynamicTruthSigmaBranchDisjunction_directInputs compilation))
      context coqDynamicTruthSigmaDomainProjectionProof)).
  apply (raw_templateProofOnTail_localProof M hPA).
  - exact (rawDynamicTruthSigmaBranchDisjunction_contextRealizable
      compilation).
  - exact (rawDynamicTruthSigmaBranchDisjunction_contextSelfShift
      compilation).
  - exact (proj1 coqDynamicTruthSigmaDomainProjectionProof_derives).
Qed.

Theorem
    raw_codedPALocalProofOf_dynamicTruthPiSuccessorRowDomainProjectionImp :
  forall (M : RawPAModel) (hPA : RawPASatisfies M)
    context concreteDomain concreteLowerApplication
    (compilation :
      RawDynamicTruthPiSuccessorRowBranchDisjunctionCompilationInputs
        M context concreteDomain concreteLowerApplication),
  RawCodedPALocalProofOf M context
    (rawDynamicTruthPiDomainProjectionCode M
      concreteDomain concreteLowerApplication)
    (rawDynamicTruthPiSuccessorRowDomainProjectionImpRoot
      M hPA context concreteDomain concreteLowerApplication compilation).
Proof.
  intros M hPA context concreteDomain concreteLowerApplication compilation.
  unfold rawDynamicTruthPiSuccessorRowDomainProjectionImpRoot.
  rewrite <- (rawCoqDynamicTruthPiDomainProjectionCode_eq_native
    M hPA concreteDomain concreteLowerApplication).
  rewrite <-
    (rawDirect_coqDynamicTruthPiDomainProjection_identified
      M (rawDynamicTruthPiBranchDisjunction_directInputs compilation)
      concreteDomain concreteLowerApplication
      (rawDynamicTruthPiBranchDisjunction_identification compilation)).
  change (RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail
      (rawDirectStructuralTemplateTranslation M hPA
        (rawDynamicTruthPiBranchDisjunction_directInputs compilation))
      context nil)
    (rawTemplateFormula
      (rawDirectStructuralTemplateTranslation M hPA
        (rawDynamicTruthPiBranchDisjunction_directInputs compilation))
      coqDynamicTruthPiDomainProjectionFormula)
    (rawTemplateProofCodeOnTail
      (rawDirectStructuralTemplateTranslation M hPA
        (rawDynamicTruthPiBranchDisjunction_directInputs compilation))
      context coqDynamicTruthPiDomainProjectionProof)).
  apply (raw_templateProofOnTail_localProof M hPA).
  - exact (rawDynamicTruthPiBranchDisjunction_contextRealizable
      compilation).
  - exact (rawDynamicTruthPiBranchDisjunction_contextSelfShift
      compilation).
  - exact (proj1 coqDynamicTruthPiDomainProjectionProof_derives).
Qed.

(** The same direct inputs also carry the two lower-application traces used
    by the opaque quantifier cells.  These traces were historically repeated
    in the current collision kernel; their designated-formula equations are
    already fields of the exact Sigma/Pi row identifications above. *)
Theorem
    raw_dynamicTruthNativeLocalExactRows_lower_direct_traces_on_witnessed_base :
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
  exists piTrace :
      RawDynamicTruthQuantifierLowerApplicationDirectTrace
        M lowerPiApplication,
    exists sigmaTrace :
      RawDynamicTruthQuantifierLowerApplicationDirectTrace
        M lowerSigmaApplication,
      True.
Proof.
  intros M hPA tail predecessorLevel inputGlobalSigma inputGlobalPi
    sigmaDomain piDomain sigmaEvidence piEvidence
    sigmaRowDomain piRowDomain lowerPi lowerSigma
    witnessList baseContext htrace hlinked hwitness.
  destruct
    (raw_dynamicTruthNativeLocalExactRows_branch_projection_inputs_on_witnessed_base
      M hPA tail predecessorLevel inputGlobalSigma inputGlobalPi
      sigmaDomain piDomain sigmaEvidence piEvidence
      sigmaRowDomain piRowDomain lowerPi lowerSigma
      witnessList baseContext htrace hlinked hwitness)
    as [sigmaInputs [piInputs _]].
  exists
    {| rawDynamicTruthQuantifierLowerApplication_inputs :=
         rawDynamicTruthSigmaBranchDisjunction_directInputs sigmaInputs;
       rawDynamicTruthQuantifierLowerApplication_designated :=
         eq_trans
           (rawDirect_coqDynamicTruthLowerPiAtomTemplate
             M (rawDynamicTruthSigmaBranchDisjunction_directInputs
               sigmaInputs))
           (rawCoqDynamicTruthSigmaDirect_lowerApplication_identified
             (rawDynamicTruthSigmaBranchDisjunction_identification
               sigmaInputs)) |}.
  assert (hpiDesignated :
      rawDirectTemplateFormula
        (rawDynamicTruthPiBranchDisjunction_directInputs piInputs)
        coqDynamicTruthLowerPiAtomTemplate = lowerSigma).
  {
    change
      (rawDirectTemplateFormula
        (rawDynamicTruthPiBranchDisjunction_directInputs piInputs)
        coqDynamicTruthLowerSigmaAtomTemplate = lowerSigma).
    exact (eq_trans
      (rawDirect_coqDynamicTruthLowerSigmaAtomTemplate M
        (rawDynamicTruthPiBranchDisjunction_directInputs piInputs))
      (rawCoqDynamicTruthPiDirect_lowerApplication_identified
        (rawDynamicTruthPiBranchDisjunction_identification piInputs))).
  }
  exists
    {| rawDynamicTruthQuantifierLowerApplication_inputs :=
         rawDynamicTruthPiBranchDisjunction_directInputs piInputs;
       rawDynamicTruthQuantifierLowerApplication_designated :=
         hpiDesignated |}.
  exact I.
Qed.

(** All eight binder-principal projections are compiled by the same direct
    Sigma/Pi translations.  The projection theorem depends only on the two
    lower-application identifications, so the row domains are retained solely
    to obtain the exact direct packages selected by this trace. *)
Theorem
    raw_dynamicTruthNativeLocalExactRows_binder_projections_on_witnessed_base :
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
  forall cell : DynamicTruthBinderOffDiagonalCell,
    RawDynamicTruthBinderPrincipalProjectionInterfaceAt M baseContext cell
      lowerPiApplication lowerSigmaApplication.
Proof.
  intros M hPA tail predecessorLevel inputGlobalSigma inputGlobalPi
    sigmaDomain piDomain sigmaEvidence piEvidence
    sigmaRowDomain piRowDomain lowerPi lowerSigma
    witnessList baseContext htrace hlinked hwitness cell.
  destruct
    (raw_dynamicTruthNativeLocalExactRows_branch_projection_inputs_on_witnessed_base
      M hPA tail predecessorLevel inputGlobalSigma inputGlobalPi
      sigmaDomain piDomain sigmaEvidence piEvidence
      sigmaRowDomain piRowDomain lowerPi lowerSigma
      witnessList baseContext htrace hlinked hwitness)
    as [sigmaInputs [piInputs _]].
  exact
    (raw_dynamicTruthBinderPrincipalProjectionInterface_of_direct
      M hPA witnessList baseContext lowerPi lowerSigma
      sigmaRowDomain piRowDomain
      (rawDynamicTruthSigmaBranchDisjunction_directInputs sigmaInputs)
      (rawDynamicTruthPiBranchDisjunction_directInputs piInputs)
      hwitness
      (rawDynamicTruthSigmaBranchDisjunction_identification sigmaInputs)
      (rawDynamicTruthPiBranchDisjunction_identification piInputs)
      cell).
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

(** A finite pair family consists entirely of completed implication proofs,
    so it can be weakened through an adequate context head without requiring
    the enlarged context to shift to itself.  This is the key distinction
    from transporting the uncompiled collision-input record, whose direct
    quantifier traces still need a context shift while they are compiled. *)
Lemma raw_dynamicTruthLocalPairFamily_adequateCons : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      context head leftBranches rightBranches conclusion,
  RawCodedFormulaAtomicallyAdequate M head ->
  RawContextListRealizable M context ->
  RawCodedPALocalFiniteDisjunctionPairFamily M context
    leftBranches rightBranches conclusion ->
  RawCodedPALocalFiniteDisjunctionPairFamily M
    (rawListNode M head context) leftBranches rightBranches conclusion.
Proof.
  intros M hPA context head leftBranches rightBranches conclusion
    hhead hcontext hpairs left hleft right hright.
  destruct (hpairs left hleft right hright) as [root hroot].
  destruct (raw_codedPALocalProof_adequateConsTransplant
    M hPA context head
    (rawFormulaImpCode M left
      (rawFormulaImpCode M right conclusion))
    root hhead hcontext hroot) as [liftedRoot hlifted].
  now exists liftedRoot.
Qed.

(** Four genuinely current-field resources remain after extracting the two
    lower direct traces from the exact row construction.  This record is the
    public kernel of the reduced callback; the older seven-field kernel is
    rebuilt internally immediately before the established helper assembly. *)
Record RawDynamicTruthNativeLocalReducedCurrentKernelInputsAt
    (M : RawPAModel) (context lowerPiApplication lowerSigmaApplication : M)
    : Type := {
  rawDynamicTruthNativeLocalReducedKernel_predecessorRoot :
    RawDynamicTruthLocalRootAt M context
      (rawDynamicTruthImpPredecessorStateExclusivityCode M);
  rawDynamicTruthNativeLocalReducedKernel_sigmaExCrossRoot :
    RawDynamicTruthLocalRootAt M context
      (rawDynamicTruthSigmaExPiExCrossLevelPremiseCode M
        lowerSigmaApplication);
  rawDynamicTruthNativeLocalReducedKernel_sigmaAllCrossRoot :
    RawDynamicTruthLocalRootAt M context
      (rawDynamicTruthSigmaAllPiAllCrossLevelPremiseCode M
        lowerPiApplication);
  rawDynamicTruthNativeLocalReducedKernel_mixedReplayRoot :
    RawDynamicTruthLocalRootAt M context
      (rawDynamicTruthMixedQFReplayExclusivityCode M)
}.

Arguments RawDynamicTruthNativeLocalReducedCurrentKernelInputsAt
  M context lowerPiApplication lowerSigmaApplication : clear implicits.

(** A strictly smaller staged package than the historical one.  It retains
    only the genuinely proof-producing case roots, row roots, and collision
    kernel.  Both direct projection packages and all three temporary-context
    self-shifts are reconstructed or avoided by compiling completed proofs on
    the witnessed PA base before weakening them. *)
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
        RawDynamicTruthNativeLocalReducedCurrentKernelInputsAt M baseContext
          lowerPiApplication lowerSigmaApplication,
      True.

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
    (hcases & hsigmaRow & hpiRow & reducedKernel & _).
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
  destruct
    (raw_dynamicTruthNativeLocalExactRows_lower_direct_traces_on_witnessed_base
      M hPA tail predecessorLevel inputGlobalSigma inputGlobalPi
      sigmaDomain piDomain sigmaEvidence piEvidence
      sigmaRowDomain piRowDomain lowerPi lowerSigma
      witnessList baseContext htrace hlinked hwitness)
    as [piTrace [sigmaTrace _]].
  assert (hbinder : forall cell : DynamicTruthBinderOffDiagonalCell,
      RawDynamicTruthBinderPrincipalProjectionInterfaceAt M baseContext cell
        lowerPi lowerSigma).
  {
    intro cell.
    exact
      (raw_dynamicTruthNativeLocalExactRows_binder_projections_on_witnessed_base
        M hPA tail predecessorLevel inputGlobalSigma inputGlobalPi
        sigmaDomain piDomain sigmaEvidence piEvidence
        sigmaRowDomain piRowDomain lowerPi lowerSigma
        witnessList baseContext htrace hlinked hwitness cell).
  }
  destruct reducedKernel as
    [hpredecessor hsigmaExCross hsigmaAllCross hmixedReplay].
  assert (currentKernel :
      RawDynamicTruthNativeLocalCurrentKernelInputsAt M baseContext
        lowerPi lowerSigma).
  {
    exact
    {| rawDynamicTruthNativeLocalCurrentKernel_predecessorRoot :=
         hpredecessor;
       rawDynamicTruthNativeLocalCurrentKernel_binderProjections :=
         hbinder;
       rawDynamicTruthNativeLocalCurrentKernel_sigmaExTrace := sigmaTrace;
       rawDynamicTruthNativeLocalCurrentKernel_sigmaAllTrace := piTrace;
       rawDynamicTruthNativeLocalCurrentKernel_sigmaExCrossRoot :=
         hsigmaExCross;
       rawDynamicTruthNativeLocalCurrentKernel_sigmaAllCrossRoot :=
         hsigmaAllCross;
       rawDynamicTruthNativeLocalCurrentKernel_mixedReplayRoot :=
         hmixedReplay |}.
  }
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
  set (exclusiveContext :=
    rawDynamicTruthNativeLocalExclusivePiContextOn M baseContext
      sigmaDomain piDomain sigmaEvidence piEvidence).
  pose proof
    (raw_dynamicTruthLocalCollisionMatrix_pair_family
      M hPA baseContext lowerPi lowerSigma hbaseInputs)
    as hbasePairs.
  pose proof
    (rawDynamicTruthLocalCollision_context_realizable
      M baseContext lowerPi lowerSigma hbaseInputs)
    as hbaseRealizable.
  assert (hadmissibleRealizable : RawContextListRealizable M
      (rawDynamicTruthNativeLocalAdmissibleContextOn M baseContext
        sigmaDomain piDomain)).
  { exact (raw_contextList_cons_realizable M hPA baseContext
      (rawDynamicTruthLocalAdmissibleCode M sigmaDomain piDomain)
      hbaseRealizable). }
  assert (hsigmaRealizable : RawContextListRealizable M
      (rawDynamicTruthNativeLocalExclusiveSigmaContextOn M baseContext
        sigmaDomain piDomain sigmaEvidence)).
  { exact (raw_contextList_cons_realizable M hPA
      (rawDynamicTruthNativeLocalAdmissibleContextOn M baseContext
        sigmaDomain piDomain) sigmaEvidence hadmissibleRealizable). }
  assert (hexclusiveRealizable : RawContextListRealizable M
      exclusiveContext).
  { exact (raw_contextList_cons_realizable M hPA
      (rawDynamicTruthNativeLocalExclusiveSigmaContextOn M baseContext
        sigmaDomain piDomain sigmaEvidence)
      piEvidence hsigmaRealizable). }
  pose proof
    (raw_dynamicTruthLocalPairFamily_adequateCons M hPA
      baseContext
      (rawDynamicTruthLocalAdmissibleCode M sigmaDomain piDomain)
      (rawDynamicTruthLocalSigmaBranches M lowerPi)
      (rawDynamicTruthLocalPiBranches M lowerSigma)
      (rawFormulaBotCode M) hadmissible hbaseRealizable hbasePairs)
    as hadmissiblePairs.
  pose proof
    (raw_dynamicTruthLocalPairFamily_adequateCons M hPA
      (rawDynamicTruthNativeLocalAdmissibleContextOn M baseContext
        sigmaDomain piDomain) sigmaEvidence
      (rawDynamicTruthLocalSigmaBranches M lowerPi)
      (rawDynamicTruthLocalPiBranches M lowerSigma)
      (rawFormulaBotCode M) hsigmaEvidence hadmissibleRealizable
      hadmissiblePairs) as hsigmaPairs.
  pose proof
    (raw_dynamicTruthLocalPairFamily_adequateCons M hPA
      (rawDynamicTruthNativeLocalExclusiveSigmaContextOn M baseContext
        sigmaDomain piDomain sigmaEvidence) piEvidence
      (rawDynamicTruthLocalSigmaBranches M lowerPi)
      (rawDynamicTruthLocalPiBranches M lowerSigma)
      (rawFormulaBotCode M) hpiEvidence hsigmaRealizable hsigmaPairs)
    as hexclusivePairs.
  assert (matrixResources :
      RawFiniteDisjunctionMatrixResources M
        (rawDynamicTruthLocalSigmaBranches M lowerPi)
        (rawDynamicTruthLocalPiBranches M lowerSigma)
        exclusiveContext).
  { apply (raw_dynamicTruthLocalCollisionMatrixResources_of_adequacy
      M hPA exclusiveContext lowerPi lowerSigma).
    - exact hexclusiveRealizable.
    - exact hlowerPi.
    - exact hlowerSigma. }
  change (RawCodedPALocalProofOf M exclusiveContext
    (rawFiniteRightDisjunctionCode M
      (rawDynamicTruthLocalSigmaBranches M lowerPi)) sigmaOrRoot)
    in hsigmaOr.
  change (RawCodedPALocalProofOf M exclusiveContext
    (rawFiniteRightDisjunctionCode M
      (rawDynamicTruthLocalPiBranches M lowerSigma)) piOrRoot)
    in hpiOr.
  destruct
    (raw_codedPALocalProofOf_finiteDisjunctionMatrix
      M hPA
      (rawDynamicTruthLocalSigmaBranches M lowerPi)
      (rawDynamicTruthLocalPiBranches M lowerSigma)
      (rawFormulaBotCode M) exclusiveContext sigmaOrRoot piOrRoot
      matrixResources hsigmaOr hpiOr hexclusivePairs)
    as [bottomRoot hbottom].
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
