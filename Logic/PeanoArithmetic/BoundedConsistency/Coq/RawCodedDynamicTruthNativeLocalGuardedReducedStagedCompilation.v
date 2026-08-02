(**
  Predecessor-free collision assembly for the guarded native callback.

  The first guarded matrix adapter still accepted the historical collision
  record.  That record contains the unguarded predecessor-exclusivity root,
  even though the two implication cells are discharged with the corrected
  guarded predecessor.  Consequently the adapter did not actually remove
  the old predecessor obligation.

  This module cuts the dependency at the level at which it is genuinely
  needed.  A collision producer supplies completed pairs for every cell
  except the two implication diagonals.  Those two pairs are constructed
  solely by applying the guarded fixed cells to the guarded predecessor
  root.  The completed family is then transported through the three local
  assumptions and fed directly to the finite matrix compiler.  No legacy
  predecessor code occurs in the new staged package or its field adapter.

  The non-implication family deliberately includes the Boolean diagonal
  pairs.  They cannot be obtained from the implication-specific guarded
  predecessor: its constructor guard says that the parent is an implication.
  Making those two remaining pairs explicit prevents that logical mismatch
  from being hidden inside a large residual record.
*)

From Stdlib Require Import List.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors
  RawCodedContextLists
  RawCodedContextStructure
  RawCodedRestrictedPAProof
  RawCodedPALocalProofExistential
  RawCodedPALocalProofWitnessedContextMerge
  RawCodedPALocalProofWitnessedContextMergeTransportComplete
  RawCodedPAAxiomContextSelfShift
  RawCodedTemplatePAEmbedding
  RawCodedTruthCertificateMasterFixedHelperBatchExtension
  RawCodedPALocalProofFiniteDisjunction
  RawCodedPALocalProofFiniteDisjunctionMatrix
  RawCodedDynamicTruthConstructorBranchDisjointness
  RawCodedDynamicTruthImpBranchExclusivity
  RawCodedDynamicTruthImpGuardedBranchExclusivity
  RawCodedDynamicTruthImpGuardedCollisionHelperBatch
  RawCodedDynamicTruthSigmaSuccessorRowGraph
  RawCodedDynamicTruthPiSuccessorRowGraph
  RawCodedDynamicTruthLocalCollisionMatrixAssembly
  RawCodedDynamicTruthNativeLocalPositiveGraph
  RawCodedDynamicTruthNativeLocalProofCompilation
  RawCodedDynamicTruthNativeLocalDecisionRootCompilation
  RawCodedDynamicTruthNativeLocalLeafRootCompiler
  RawCodedDynamicTruthNativeLocalStagedRootCompilation
  RawCodedDynamicTruthNativeLocalRowProjectionCompilation
  RawCodedDynamicTruthNativeLocalGuardedMatrixCompilation.

Import ListNotations.

Module
  PABoundedRawCodedDynamicTruthNativeLocalGuardedReducedStagedCompilation.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedContextLists.
Import PABoundedRawCodedContextStructure.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPALocalProofWitnessedContextMerge.
Import
  PABoundedRawCodedPALocalProofWitnessedContextMergeTransportComplete.
Import PABoundedRawCodedPAAxiomContextSelfShift.
Import PABoundedRawCodedTemplatePAEmbedding.
Import PABoundedRawCodedTruthCertificateMasterFixedHelperBatchExtension.
Import PABoundedRawCodedPALocalProofFiniteDisjunction.
Import PABoundedRawCodedPALocalProofFiniteDisjunctionMatrix.
Import PABoundedRawCodedDynamicTruthConstructorBranchDisjointness.
Import PABoundedRawCodedDynamicTruthImpBranchExclusivity.
Import PABoundedRawCodedDynamicTruthImpGuardedBranchExclusivity.
Import PABoundedRawCodedDynamicTruthImpGuardedCollisionHelperBatch.
Import PABoundedRawCodedDynamicTruthSigmaSuccessorRowGraph.
Import PABoundedRawCodedDynamicTruthPiSuccessorRowGraph.
Import PABoundedRawCodedDynamicTruthLocalCollisionMatrixAssembly.
Import PABoundedRawCodedDynamicTruthNativeLocalPositiveGraph.
Import PABoundedRawCodedDynamicTruthNativeLocalProofCompilation.
Import PABoundedRawCodedDynamicTruthNativeLocalDecisionRootCompilation.
Import PABoundedRawCodedDynamicTruthNativeLocalLeafRootCompiler.
Import PABoundedRawCodedDynamicTruthNativeLocalStagedRootCompilation.
Import PABoundedRawCodedDynamicTruthNativeLocalRowProjectionCompilation.
Import PABoundedRawCodedDynamicTruthNativeLocalGuardedMatrixCompilation.

(** The only cells omitted from the predecessor-free family are the two
    implication diagonals.  Stating the exclusion proposition separately
    keeps the family reusable by both fixed-context and growing callbacks. *)
Definition DynamicTruthImpDiagonalCell
    (sigmaBranch : DynamicTruthLocalSigmaBranch)
    (piBranch : DynamicTruthLocalPiBranch) : Prop :=
  (sigmaBranch = DTLocalSigmaImpFalseLeft /\
    piBranch = DTLocalPiImp) \/
  (sigmaBranch = DTLocalSigmaImpTrueRight /\
    piBranch = DTLocalPiImp).

Lemma dynamicTruthLocalSigmaBranchOrder_complete : forall branch,
  In branch dynamicTruthLocalSigmaBranchOrder.
Proof.
  intro branch. destruct branch; cbn; tauto.
Qed.

Lemma dynamicTruthLocalPiBranchOrder_complete : forall branch,
  In branch dynamicTruthLocalPiBranchOrder.
Proof.
  intro branch. destruct branch; cbn; tauto.
Qed.

Definition RawDynamicTruthLocalCollisionPairFamilyWithoutImpAt
    (M : RawPAModel) (context lowerPiApplication lowerSigmaApplication : M)
    : Prop :=
  forall sigmaBranch piBranch,
    ~ DynamicTruthImpDiagonalCell sigmaBranch piBranch ->
    RawDynamicTruthLocalRootAt M context
      (rawFormulaImpCode M
        (rawDynamicTruthLocalSigmaBranchCode M
          lowerPiApplication sigmaBranch)
        (rawFormulaImpCode M
          (rawDynamicTruthLocalPiBranchCode M
            lowerSigmaApplication piBranch)
          (rawFormulaBotCode M))).

Arguments RawDynamicTruthLocalCollisionPairFamilyWithoutImpAt
  M context lowerPiApplication lowerSigmaApplication : clear implicits.

(** Completed non-implication pairs are ordinary local proofs, hence they
    transport through any inclusion between witnessed PA contexts without
    reconstructing the low-level collision traces.  This is the structural
    operation needed when the guarded predecessor chooses a larger target
    context than the remainder producer used. *)
Theorem
    raw_dynamicTruthLocalCollisionPairFamilyWithoutImpAt_witnessed_inclusion :
    forall (M : RawPAModel), RawPASatisfies M -> forall
      sourceWitnessList sourceContext targetWitnessList targetContext
      lowerPiApplication lowerSigmaApplication,
  RawCodedPAAxiomWitnessContext M sourceWitnessList sourceContext ->
  RawCodedPAAxiomWitnessContext M targetWitnessList targetContext ->
  RawContextListIncluded M sourceContext targetContext ->
  RawDynamicTruthLocalCollisionPairFamilyWithoutImpAt M sourceContext
    lowerPiApplication lowerSigmaApplication ->
  RawDynamicTruthLocalCollisionPairFamilyWithoutImpAt M targetContext
    lowerPiApplication lowerSigmaApplication.
Proof.
  intros M hPA sourceWitnessList sourceContext
    targetWitnessList targetContext lowerPi lowerSigma
    hsource htarget hincluded hfamily sigmaBranch piBranch hnot.
  destruct (hfamily sigmaBranch piBranch hnot) as [root hroot].
  destruct
    (raw_codedPALocalProofWitnessedContextInclusionWeakening_complete
      M hPA sourceWitnessList sourceContext targetWitnessList targetContext
      (rawFormulaImpCode M
        (rawDynamicTruthLocalSigmaBranchCode M lowerPi sigmaBranch)
        (rawFormulaImpCode M
          (rawDynamicTruthLocalPiBranchCode M lowerSigma piBranch)
          (rawFormulaBotCode M)))
      root hsource htarget hincluded hroot)
    as [targetRoot htargetRoot].
  now exists targetRoot.
Qed.

(** Forgetting two members of a complete pair family is immediate.  This
    compatibility projection is useful while clients migrate away from the
    historical collision-input record. *)
Theorem raw_dynamicTruthLocalCollisionPairFamilyWithoutImpAt_of_family :
    forall (M : RawPAModel) context lowerPiApplication lowerSigmaApplication,
  RawCodedPALocalFiniteDisjunctionPairFamily M context
    (rawDynamicTruthLocalSigmaBranches M lowerPiApplication)
    (rawDynamicTruthLocalPiBranches M lowerSigmaApplication)
    (rawFormulaBotCode M) ->
  RawDynamicTruthLocalCollisionPairFamilyWithoutImpAt M context
    lowerPiApplication lowerSigmaApplication.
Proof.
  intros M context lowerPi lowerSigma hfamily sigmaBranch piBranch _.
  assert (hleft : In
      (rawDynamicTruthLocalSigmaBranchCode M lowerPi sigmaBranch)
      (rawDynamicTruthLocalSigmaBranches M lowerPi)).
  {
    unfold rawDynamicTruthLocalSigmaBranches.
    apply in_map.
    exact (dynamicTruthLocalSigmaBranchOrder_complete sigmaBranch).
  }
  assert (hright : In
      (rawDynamicTruthLocalPiBranchCode M lowerSigma piBranch)
      (rawDynamicTruthLocalPiBranches M lowerSigma)).
  {
    unfold rawDynamicTruthLocalPiBranches.
    apply in_map.
    exact (dynamicTruthLocalPiBranchOrder_complete piBranch).
  }
  exact (hfamily
    (rawDynamicTruthLocalSigmaBranchCode M lowerPi sigmaBranch) hleft
    (rawDynamicTruthLocalPiBranchCode M lowerSigma piBranch) hright).
Qed.

(** Reinsert exactly the two omitted pairs.  No formula root other than the
    pair selected by the branch indices is inspected in this proof. *)
Theorem raw_dynamicTruthLocalCollisionPairFamily_of_without_imp_and_pairs :
    forall (M : RawPAModel) context lowerPiApplication lowerSigmaApplication,
  RawDynamicTruthLocalCollisionPairFamilyWithoutImpAt M context
    lowerPiApplication lowerSigmaApplication ->
  RawDynamicTruthLocalRootAt M context
    (rawFormulaImpCode M
      (rawDynamicTruthLocalSigmaBranchCode M lowerPiApplication
        DTLocalSigmaImpFalseLeft)
      (rawFormulaImpCode M
        (rawDynamicTruthLocalPiBranchCode M lowerSigmaApplication
          DTLocalPiImp)
        (rawFormulaBotCode M))) ->
  RawDynamicTruthLocalRootAt M context
    (rawFormulaImpCode M
      (rawDynamicTruthLocalSigmaBranchCode M lowerPiApplication
        DTLocalSigmaImpTrueRight)
      (rawFormulaImpCode M
        (rawDynamicTruthLocalPiBranchCode M lowerSigmaApplication
          DTLocalPiImp)
        (rawFormulaBotCode M))) ->
  RawCodedPALocalFiniteDisjunctionPairFamily M context
    (rawDynamicTruthLocalSigmaBranches M lowerPiApplication)
    (rawDynamicTruthLocalPiBranches M lowerSigmaApplication)
    (rawFormulaBotCode M).
Proof.
  intros M context lowerPi lowerSigma hwithout
    himpFalse himpTrue left hleft right hright.
  unfold rawDynamicTruthLocalSigmaBranches in hleft.
  apply in_map_iff in hleft.
  destruct hleft as [sigmaBranch [<- _]].
  unfold rawDynamicTruthLocalPiBranches in hright.
  apply in_map_iff in hright.
  destruct hright as [piBranch [<- _]].
  Ltac close_nonimp family :=
    apply family;
    unfold DynamicTruthImpDiagonalCell;
    intros [[hsigma hpi] | [hsigma hpi]];
    discriminate.
  destruct sigmaBranch.
  - destruct piBranch; close_nonimp hwithout.
  - destruct piBranch.
    + close_nonimp hwithout.
    + exact himpFalse.
    + close_nonimp hwithout.
    + close_nonimp hwithout.
    + close_nonimp hwithout.
    + close_nonimp hwithout.
  - destruct piBranch.
    + close_nonimp hwithout.
    + exact himpTrue.
    + close_nonimp hwithout.
    + close_nonimp hwithout.
    + close_nonimp hwithout.
    + close_nonimp hwithout.
  - destruct piBranch; close_nonimp hwithout.
  - destruct piBranch; close_nonimp hwithout.
  - destruct piBranch; close_nonimp hwithout.
  - destruct piBranch; close_nonimp hwithout.
Qed.

(** The two implication pairs are obtained only by modus ponens between the
    guarded predecessor and the corresponding guarded fixed cell. *)
Theorem raw_dynamicTruthLocalCollisionPairFamily_of_without_imp_and_guarded :
    forall (M : RawPAModel), RawPASatisfies M -> forall
      context lowerPiApplication lowerSigmaApplication,
  RawDynamicTruthLocalCollisionPairFamilyWithoutImpAt M context
    lowerPiApplication lowerSigmaApplication ->
  RawDynamicTruthLocalRootAt M context
    (rawDynamicTruthImpGuardedPredecessorStateExclusivityCode M) ->
  RawDynamicTruthLocalRootAt M context
    (rawDynamicTruthImpFalseLeftGuardedConditionalCellCode M) ->
  RawDynamicTruthLocalRootAt M context
    (rawDynamicTruthImpTrueRightGuardedConditionalCellCode M) ->
  RawCodedPALocalFiniteDisjunctionPairFamily M context
    (rawDynamicTruthLocalSigmaBranches M lowerPiApplication)
    (rawDynamicTruthLocalPiBranches M lowerSigmaApplication)
    (rawFormulaBotCode M).
Proof.
  intros M hPA context lowerPi lowerSigma hwithout
    [predecessorRoot hpredecessor]
    [falseCellRoot hfalseCell] [trueCellRoot htrueCell].
  apply (raw_dynamicTruthLocalCollisionPairFamily_of_without_imp_and_pairs
    M context lowerPi lowerSigma hwithout).
  - change (RawDynamicTruthLocalRootAt M context
      (rawFormulaImpCode M
        (rawDynamicTruthSigmaImpFalseLeftEx8BranchCode M)
        (rawFormulaImpCode M
          (rawDynamicTruthPiImpEx8BranchCode M)
          (rawFormulaBotCode M)))).
    exact (raw_dynamicTruthImpFalseLeftGuarded_pair M hPA context
      falseCellRoot predecessorRoot hfalseCell hpredecessor).
  - change (RawDynamicTruthLocalRootAt M context
      (rawFormulaImpCode M
        (rawDynamicTruthSigmaImpTrueRightEx8BranchCode M)
        (rawFormulaImpCode M
          (rawDynamicTruthPiImpEx8BranchCode M)
          (rawFormulaBotCode M)))).
    exact (raw_dynamicTruthImpTrueRightGuarded_pair M hPA context
      trueCellRoot predecessorRoot htrueCell hpredecessor).
Qed.

(** The guarded suffix of the forty-two-helper batch is projected without
    retaining the legacy forty-helper roots. *)
Theorem raw_dynamicTruthNativeLocal_guarded_cell_roots_of_42_helpers :
    forall (M : RawPAModel), RawPASatisfies M -> forall
      translation context roots,
  RawCodedTemplatePAAgreement M translation ->
  RawFixedPAHelperBatchLocalProofs M translation context
    rawDynamicTruthReadyAndGuardedMixedQFPAHelpers roots ->
  RawDynamicTruthLocalRootAt M context
    (rawDynamicTruthImpFalseLeftGuardedConditionalCellCode M) /\
  RawDynamicTruthLocalRootAt M context
    (rawDynamicTruthImpTrueRightGuardedConditionalCellCode M).
Proof.
  intros M hPA translation context roots hagreement hroots.
  destruct (raw_dynamicTruthNativeLocal_helper_roots_of_42_helpers
    M hPA translation context roots hagreement hroots) as
    (legacyRoots & _ & hfalse & htrue).
  now split.
Qed.

(** Common local-field closure once a complete pair family has been compiled
    on the witnessed base.  Extracting this lemma keeps the guarded adapter
    independent of every low-level collision residual. *)
Theorem raw_dynamicTruthNativeLocalFieldRootOn_of_base_pair_family :
    forall (M : RawPAModel), RawPASatisfies M -> forall
      witnessList baseContext
      (tail : nat -> M) predecessorLevel inputGlobalSigma inputGlobalPi
      sigmaDomain piDomain sigmaEvidence piEvidence
      sigmaRowDomain piRowDomain lowerPiApplication lowerSigmaApplication,
  RawCodedPAAxiomWitnessContext M witnessList baseContext ->
  RawDynamicTruthNativeLocalProofTraceAt M tail predecessorLevel
    inputGlobalSigma inputGlobalPi sigmaDomain piDomain
    sigmaEvidence piEvidence ->
  RawDynamicTruthNativeLocalExactRowParametersAt M predecessorLevel
    inputGlobalSigma inputGlobalPi sigmaEvidence piEvidence
    sigmaRowDomain piRowDomain lowerPiApplication lowerSigmaApplication ->
  RawDynamicTruthNativeLocalDomainCaseDecisionRootsAt M
    baseContext sigmaDomain piDomain sigmaEvidence piEvidence ->
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
  RawCodedPALocalFiniteDisjunctionPairFamily M baseContext
    (rawDynamicTruthLocalSigmaBranches M lowerPiApplication)
    (rawDynamicTruthLocalPiBranches M lowerSigmaApplication)
    (rawFormulaBotCode M) ->
  RawDynamicTruthNativeLocalFieldRootOn M baseContext
    sigmaDomain piDomain sigmaEvidence piEvidence.
Proof.
  intros M hPA witnessList baseContext tail predecessorLevel
    inputGlobalSigma inputGlobalPi sigmaDomain piDomain sigmaEvidence
    piEvidence sigmaRowDomain piRowDomain lowerPi lowerSigma
    hwitness htrace hlinked hcases hsigmaRow hpiRow hbasePairs.
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
  pose proof (raw_codedPAAxiomWitnessContext_context_realizable
    M witnessList baseContext hwitness) as hbaseRealizable.
  assert (hadmissibleRealizable : RawContextListRealizable M
      (rawDynamicTruthNativeLocalAdmissibleContextOn M baseContext
        sigmaDomain piDomain)).
  {
    exact (raw_contextList_cons_realizable M hPA baseContext
      (rawDynamicTruthLocalAdmissibleCode M sigmaDomain piDomain)
      hbaseRealizable).
  }
  assert (hsigmaRealizable : RawContextListRealizable M
      (rawDynamicTruthNativeLocalExclusiveSigmaContextOn M baseContext
        sigmaDomain piDomain sigmaEvidence)).
  {
    exact (raw_contextList_cons_realizable M hPA
      (rawDynamicTruthNativeLocalAdmissibleContextOn M baseContext
        sigmaDomain piDomain) sigmaEvidence hadmissibleRealizable).
  }
  set (exclusiveContext :=
    rawDynamicTruthNativeLocalExclusivePiContextOn M baseContext
      sigmaDomain piDomain sigmaEvidence piEvidence).
  assert (hexclusiveRealizable : RawContextListRealizable M
      exclusiveContext).
  {
    exact (raw_contextList_cons_realizable M hPA
      (rawDynamicTruthNativeLocalExclusiveSigmaContextOn M baseContext
        sigmaDomain piDomain sigmaEvidence)
      piEvidence hsigmaRealizable).
  }
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
  {
    apply (raw_dynamicTruthLocalCollisionMatrixResources_of_adequacy
      M hPA exclusiveContext lowerPi lowerSigma).
    - exact hexclusiveRealizable.
    - exact hlowerPi.
    - exact hlowerSigma.
  }
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
  {
    apply (raw_dynamicTruthNativeLocalDecisionRootOn_of_structural_roots
      M hPA baseContext sigmaDomain piDomain sigmaEvidence piEvidence).
    - apply (raw_dynamicTruthNativeLocalAdmissibleDomainRootAt_realizable
        M hPA baseContext sigmaDomain piDomain).
      exact hbaseRealizable.
    - exact hcases.
  }
  apply (raw_dynamicTruthNativeLocalFieldRootOn_of_leaf_roots
    M hPA baseContext sigmaDomain piDomain sigmaEvidence piEvidence).
  - exact (raw_codedPAAxiomWitnessContext_selfShift
      M hPA witnessList baseContext hwitness).
  - split.
    + exact hdecision.
    + exists bottomRoot. exact hbottom.
Qed.

(** The guarded reduced staged package has no field mentioning the legacy
    predecessor formula.  Its sole unresolved collision resource is the
    already-completed family away from the implication diagonal. *)
Definition RawDynamicTruthNativeLocalGuardedReducedStagedRootsAt
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
  RawDynamicTruthLocalCollisionPairFamilyWithoutImpAt M baseContext
    lowerPiApplication lowerSigmaApplication /\
  RawDynamicTruthLocalRootAt M baseContext
    (rawDynamicTruthImpGuardedPredecessorStateExclusivityCode M).

Arguments RawDynamicTruthNativeLocalGuardedReducedStagedRootsAt
  M baseContext sigmaDomain piDomain sigmaEvidence piEvidence
  sigmaRowDomain piRowDomain lowerPiApplication lowerSigmaApplication
  : clear implicits.

(** Small guarded field adapter.  The forty-two fixed helpers contribute
    only their two guarded cells; all legacy helper roots are discarded. *)
Theorem
    raw_dynamicTruthNativeLocalFieldRootOn_of_guarded_reduced_staged_roots_and_42_helpers :
    forall (M : RawPAModel), RawPASatisfies M -> forall
      translation witnessList baseContext helperRoots
      (tail : nat -> M) predecessorLevel inputGlobalSigma inputGlobalPi
      sigmaDomain piDomain sigmaEvidence piEvidence
      sigmaRowDomain piRowDomain lowerPiApplication lowerSigmaApplication,
  RawCodedTemplatePAAgreement M translation ->
  RawCodedPAAxiomWitnessContext M witnessList baseContext ->
  RawFixedPAHelperBatchLocalProofs M translation baseContext
    rawDynamicTruthReadyAndGuardedMixedQFPAHelpers helperRoots ->
  RawDynamicTruthNativeLocalProofTraceAt M tail predecessorLevel
    inputGlobalSigma inputGlobalPi sigmaDomain piDomain
    sigmaEvidence piEvidence ->
  RawDynamicTruthNativeLocalExactRowParametersAt M predecessorLevel
    inputGlobalSigma inputGlobalPi sigmaEvidence piEvidence
    sigmaRowDomain piRowDomain lowerPiApplication lowerSigmaApplication ->
  RawDynamicTruthNativeLocalGuardedReducedStagedRootsAt M baseContext
    sigmaDomain piDomain sigmaEvidence piEvidence
    sigmaRowDomain piRowDomain lowerPiApplication lowerSigmaApplication ->
  RawDynamicTruthNativeLocalFieldRootOn M baseContext
    sigmaDomain piDomain sigmaEvidence piEvidence.
Proof.
  intros M hPA translation witnessList baseContext helperRoots
    tail predecessorLevel inputGlobalSigma inputGlobalPi
    sigmaDomain piDomain sigmaEvidence piEvidence
    sigmaRowDomain piRowDomain lowerPi lowerSigma
    hagreement hwitness hhelpers htrace hlinked
    (hcases & hsigmaRow & hpiRow & hwithout & hpredecessor).
  destruct (raw_dynamicTruthNativeLocal_guarded_cell_roots_of_42_helpers
    M hPA translation baseContext helperRoots hagreement hhelpers) as
    [hfalseCell htrueCell].
  pose proof
    (raw_dynamicTruthLocalCollisionPairFamily_of_without_imp_and_guarded
      M hPA baseContext lowerPi lowerSigma hwithout hpredecessor
      hfalseCell htrueCell) as hbasePairs.
  exact (raw_dynamicTruthNativeLocalFieldRootOn_of_base_pair_family
    M hPA witnessList baseContext tail predecessorLevel
    inputGlobalSigma inputGlobalPi sigmaDomain piDomain
    sigmaEvidence piEvidence sigmaRowDomain piRowDomain
    lowerPi lowerSigma hwitness htrace hlinked
    hcases hsigmaRow hpiRow hbasePairs).
Qed.

End
  PABoundedRawCodedDynamicTruthNativeLocalGuardedReducedStagedCompilation.
