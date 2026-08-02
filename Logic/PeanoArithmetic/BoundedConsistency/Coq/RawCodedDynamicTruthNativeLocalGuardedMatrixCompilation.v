(**
  Guarded implication resources for the native local collision matrix.

  The established native leaf compiler synchronizes forty fixed PA helpers.
  Most of that batch remains correct, including the historical implication
  helpers needed by Boolean cells.  The two implication cells additionally
  need their guarded replacements.  This module appends precisely those two
  helpers, splits the resulting structurally indexed proof family, and keeps
  every root on the same witnessed context.

  The guarded predecessor theorem is carrier-dependent and therefore is not
  a fixed helper.  It is supplied on the base context and transported through
  the admissibility and evidence assumptions together with the two guarded
  cell roots.  The resulting record can invoke the corrected matrix assembler
  without changing the legacy matrix resource type or any Boolean endpoint.
*)

From Stdlib Require Import List.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors
  RawCodedFixedLevelTruthTotality
  RawCodedContextLists
  RawCodedContextStructure
  RawCodedContextShift
  RawCodedRestrictedPAProof
  RawCodedPALocalProofFiniteDisjunctionMatrix
  RawCodedPALocalProofExistential
  RawCodedPALocalProofWitnessedContextMerge
  RawCodedTemplateProofCompiler
  RawCodedTemplatePAEmbedding
  RawCodedTruthCertificateMasterFixedHelperBatchExtension
  RawCodedTruthCertificateMasterHelperLookup
  RawCodedDynamicTruthMixedQFOpaqueQuantifierCellCompilation
  RawCodedDynamicTruthImpGuardedBranchExclusivity
  RawCodedDynamicTruthImpGuardedCollisionHelperBatch
  RawCodedDynamicTruthNativeLocalPositiveGraph
  RawCodedDynamicTruthSigmaSuccessorRowGraph
  RawCodedDynamicTruthPiSuccessorRowGraph
  RawCodedDynamicTruthLocalCollisionMatrixAssembly
  RawCodedDynamicTruthSuccessorRowBranchDisjunctionCompilation
  RawCodedDynamicTruthNativeLocalLeafRootCompiler.

Import ListNotations.

Module
  PABoundedRawCodedDynamicTruthNativeLocalGuardedMatrixCompilation.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedFixedLevelTruthTotality.
Import PABoundedRawCodedContextLists.
Import PABoundedRawCodedContextStructure.
Import PABoundedRawCodedContextShift.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedPALocalProofFiniteDisjunctionMatrix.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPALocalProofWitnessedContextMerge.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedTemplatePAEmbedding.
Import PABoundedRawCodedTruthCertificateMasterFixedHelperBatchExtension.
Import PABoundedRawCodedTruthCertificateMasterHelperLookup.
Import PABoundedRawCodedDynamicTruthMixedQFOpaqueQuantifierCellCompilation.
Import PABoundedRawCodedDynamicTruthImpGuardedBranchExclusivity.
Import PABoundedRawCodedDynamicTruthImpGuardedCollisionHelperBatch.
Import PABoundedRawCodedDynamicTruthNativeLocalPositiveGraph.
Import PABoundedRawCodedDynamicTruthSigmaSuccessorRowGraph.
Import PABoundedRawCodedDynamicTruthPiSuccessorRowGraph.
Import PABoundedRawCodedDynamicTruthLocalCollisionMatrixAssembly.
Import
  PABoundedRawCodedDynamicTruthSuccessorRowBranchDisjunctionCompilation.
Import PABoundedRawCodedDynamicTruthNativeLocalLeafRootCompiler.

(** Only the corrected implication helpers are appended.  The QF helper is
    already the first member of the forty-helper prefix and is not duplicated. *)
Definition rawDynamicTruthGuardedImpCollisionFixedPAHelpers
    : list RawFixedPAHelper :=
  [ rawDynamicTruthImpFalseLeftGuardedCollisionFixedPAHelper;
    rawDynamicTruthImpTrueRightGuardedCollisionFixedPAHelper ].

Definition rawDynamicTruthReadyAndGuardedMixedQFPAHelpers
    : list RawFixedPAHelper :=
  rawDynamicTruthReadyAndAllMixedQFPAHelpers ++
  rawDynamicTruthGuardedImpCollisionFixedPAHelpers.

Lemma rawDynamicTruthReadyAndGuardedMixedQFPAHelpers_length :
  length rawDynamicTruthReadyAndGuardedMixedQFPAHelpers = 42.
Proof.
  unfold rawDynamicTruthReadyAndGuardedMixedQFPAHelpers,
    rawDynamicTruthGuardedImpCollisionFixedPAHelpers.
  rewrite length_app, rawDynamicTruthReadyAndAllMixedQFPAHelpers_length.
  reflexivity.
Qed.

(** A computational prefix projection for structurally indexed proof lists.
    Unlike an existential split in [Prop], this lemma fixes the output list
    with [firstn], so downstream [Type]-valued packages may use it without
    eliminating a propositional witness into data. *)
Lemma raw_fixedPAHelperBatchLocalProofs_app_prefix_firstn : forall
    (M : RawPAModel) translation context prefix suffix roots,
  RawFixedPAHelperBatchLocalProofs M translation context
    (prefix ++ suffix) roots ->
  RawFixedPAHelperBatchLocalProofs M translation context prefix
    (firstn (length prefix) roots).
Proof.
  intros M translation context prefix.
  induction prefix as [| helper prefixTail ih];
    intros suffix roots hroots.
  - exact I.
  - destruct roots as [| root rootsTail].
    + contradiction.
    + cbn [RawFixedPAHelperBatchLocalProofs] in hroots.
      destruct hroots as [hroot htail].
      cbn [length firstn RawFixedPAHelperBatchLocalProofs].
      split; [exact hroot | exact (ih suffix rootsTail htail)].
Qed.

(** Recover both the legacy prefix and the two corrected native roots.  The
    prefix root list is data and is therefore returned by a dependent sum;
    the local proof judgments remain propositions.  Membership lookup avoids
    equality on proof-indexed helper records. *)
Theorem raw_dynamicTruthNativeLocal_helper_roots_of_42_helpers : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      translation context roots,
  RawCodedTemplatePAAgreement M translation ->
  RawFixedPAHelperBatchLocalProofs M translation context
    rawDynamicTruthReadyAndGuardedMixedQFPAHelpers roots ->
  { legacyRoots : list M &
    RawFixedPAHelperBatchLocalProofs M translation context
      rawDynamicTruthReadyAndAllMixedQFPAHelpers legacyRoots /\
    RawDynamicTruthLocalRootAt M context
      (rawDynamicTruthImpFalseLeftGuardedConditionalCellCode M) /\
    RawDynamicTruthLocalRootAt M context
      (rawDynamicTruthImpTrueRightGuardedConditionalCellCode M) }.
Proof.
  intros M hPA translation context roots hagreement hroots.
  assert (hlegacy : RawFixedPAHelperBatchLocalProofs M translation context
      rawDynamicTruthReadyAndAllMixedQFPAHelpers
      (firstn (length rawDynamicTruthReadyAndAllMixedQFPAHelpers) roots)).
  {
    apply (raw_fixedPAHelperBatchLocalProofs_app_prefix_firstn
      M translation context rawDynamicTruthReadyAndAllMixedQFPAHelpers
      rawDynamicTruthGuardedImpCollisionFixedPAHelpers roots).
    exact hroots.
  }
  assert (hfalseIn : In
      rawDynamicTruthImpFalseLeftGuardedCollisionFixedPAHelper
      rawDynamicTruthGuardedImpCollisionFixedPAHelpers).
  {
    unfold rawDynamicTruthGuardedImpCollisionFixedPAHelpers.
    cbn. auto.
  }
  assert (htrueIn : In
      rawDynamicTruthImpTrueRightGuardedCollisionFixedPAHelper
      rawDynamicTruthGuardedImpCollisionFixedPAHelpers).
  {
    unfold rawDynamicTruthGuardedImpCollisionFixedPAHelpers.
    cbn. auto.
  }
  assert (hfalseFull : In
      rawDynamicTruthImpFalseLeftGuardedCollisionFixedPAHelper
      rawDynamicTruthReadyAndGuardedMixedQFPAHelpers).
  {
    unfold rawDynamicTruthReadyAndGuardedMixedQFPAHelpers.
    apply in_or_app. right. exact hfalseIn.
  }
  assert (htrueFull : In
      rawDynamicTruthImpTrueRightGuardedCollisionFixedPAHelper
      rawDynamicTruthReadyAndGuardedMixedQFPAHelpers).
  {
    unfold rawDynamicTruthReadyAndGuardedMixedQFPAHelpers.
    apply in_or_app. right. exact htrueIn.
  }
  pose proof (raw_fixedPAHelperBatchLocalProofs_member
    M translation context rawDynamicTruthReadyAndGuardedMixedQFPAHelpers
    roots rawDynamicTruthImpFalseLeftGuardedCollisionFixedPAHelper
    hroots hfalseFull) as hfalse.
  pose proof (raw_fixedPAHelperBatchLocalProofs_member
    M translation context rawDynamicTruthReadyAndGuardedMixedQFPAHelpers
    roots rawDynamicTruthImpTrueRightGuardedCollisionFixedPAHelper
    hroots htrueFull) as htrue.
  rewrite (rawDynamicTruthImpFalseGuardedHelperTarget_eq_native
    M hPA translation hagreement) in hfalse.
  rewrite (rawDynamicTruthImpTrueGuardedHelperTarget_eq_native
    M hPA translation hagreement) in htrue.
  exists (firstn
    (length rawDynamicTruthReadyAndAllMixedQFPAHelpers) roots).
  split; [exact hlegacy |].
  split; [exact hfalse | exact htrue].
Qed.

(** Transport one root through the exact three temporary assumptions used by
    the exclusivity branch.  Keeping this operation generic avoids repeating
    the same three adequate-cons transplants for predecessor and cell roots. *)
Lemma raw_dynamicTruthLocalRootAt_on_exclusive_context : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      baseContext sigmaDomain piDomain sigmaEvidence piEvidence target,
  RawContextListRealizable M baseContext ->
  RawCodedFormulaAtomicallyAdequate M
    (rawDynamicTruthLocalAdmissibleCode M sigmaDomain piDomain) ->
  RawCodedFormulaAtomicallyAdequate M sigmaEvidence ->
  RawCodedFormulaAtomicallyAdequate M piEvidence ->
  RawDynamicTruthLocalRootAt M baseContext target ->
  RawDynamicTruthLocalRootAt M
    (rawDynamicTruthNativeLocalExclusivePiContextOn M baseContext
      sigmaDomain piDomain sigmaEvidence piEvidence) target.
Proof.
  intros M hPA baseContext sigmaDomain piDomain sigmaEvidence piEvidence
    target hbase hadmissible hsigma hpi hroot.
  pose proof (raw_dynamicTruthLocalRootAt_adequateCons M hPA
    baseContext
    (rawDynamicTruthLocalAdmissibleCode M sigmaDomain piDomain)
    target hadmissible hbase hroot) as hfirst.
  assert (hfirstContext : RawContextListRealizable M
      (rawDynamicTruthNativeLocalAdmissibleContextOn M baseContext
        sigmaDomain piDomain)).
  {
    exact (raw_contextList_cons_realizable M hPA baseContext
      (rawDynamicTruthLocalAdmissibleCode M sigmaDomain piDomain)
      hbase).
  }
  pose proof (raw_dynamicTruthLocalRootAt_adequateCons M hPA
    (rawDynamicTruthNativeLocalAdmissibleContextOn M baseContext
      sigmaDomain piDomain) sigmaEvidence target hsigma hfirstContext
    hfirst) as hsecond.
  assert (hsecondContext : RawContextListRealizable M
      (rawDynamicTruthNativeLocalExclusiveSigmaContextOn M baseContext
        sigmaDomain piDomain sigmaEvidence)).
  {
    exact (raw_contextList_cons_realizable M hPA
      (rawDynamicTruthNativeLocalAdmissibleContextOn M baseContext
        sigmaDomain piDomain) sigmaEvidence hfirstContext).
  }
  exact (raw_dynamicTruthLocalRootAt_adequateCons M hPA
    (rawDynamicTruthNativeLocalExclusiveSigmaContextOn M baseContext
      sigmaDomain piDomain sigmaEvidence) piEvidence target hpi
    hsecondContext hsecond).
Qed.

(** Legacy matrix data and the corrected implication resources are bundled
    at one literal exclusive context. *)
Record RawDynamicTruthNativeLocalGuardedExclusiveMatrixResourcesAt
    (M : RawPAModel)
    (context sigmaRowDomain piRowDomain
      lowerPiApplication lowerSigmaApplication : M) : Type := {
  rawDynamicTruthNativeLocalGuardedExclusive_legacy :
    RawDynamicTruthNativeLocalExclusiveMatrixResourcesAt M context
      sigmaRowDomain piRowDomain lowerPiApplication lowerSigmaApplication;
  rawDynamicTruthNativeLocalGuardedExclusive_predecessor :
    RawDynamicTruthLocalRootAt M context
      (rawDynamicTruthImpGuardedPredecessorStateExclusivityCode M);
  rawDynamicTruthNativeLocalGuardedExclusive_falseCell :
    RawDynamicTruthLocalRootAt M context
      (rawDynamicTruthImpFalseLeftGuardedConditionalCellCode M);
  rawDynamicTruthNativeLocalGuardedExclusive_trueCell :
    RawDynamicTruthLocalRootAt M context
      (rawDynamicTruthImpTrueRightGuardedConditionalCellCode M)
}.

Arguments RawDynamicTruthNativeLocalGuardedExclusiveMatrixResourcesAt
  M context sigmaRowDomain piRowDomain
  lowerPiApplication lowerSigmaApplication : clear implicits.

(** Build the guarded package from one synchronized forty-two-helper family.
    The predecessor root and both fixed cell roots are moved by the same
    generic exclusive-context transport. *)
Theorem
    raw_dynamicTruthNativeLocalGuardedExclusiveMatrixResourcesAt_of_42_helpers :
    forall (M : RawPAModel) (hPA : RawPASatisfies M)
      translation witnessList baseContext helperRoots
      sigmaDomain piDomain sigmaEvidence piEvidence
      sigmaRowDomain piRowDomain lowerPiApplication lowerSigmaApplication,
  RawCodedTemplatePAAgreement M translation ->
  RawCodedPAAxiomWitnessContext M witnessList baseContext ->
  RawFixedPAHelperBatchLocalProofs M translation baseContext
    rawDynamicTruthReadyAndGuardedMixedQFPAHelpers helperRoots ->
  RawDynamicTruthNativeLocalCollisionResidualInputsAt M baseContext
    lowerPiApplication lowerSigmaApplication ->
  RawDynamicTruthLocalRootAt M baseContext
    (rawDynamicTruthImpGuardedPredecessorStateExclusivityCode M) ->
  RawCodedFormulaAtomicallyAdequate M
    (rawDynamicTruthLocalAdmissibleCode M sigmaDomain piDomain) ->
  RawCodedFormulaAtomicallyAdequate M sigmaEvidence ->
  RawCodedFormulaAtomicallyAdequate M piEvidence ->
  RawContextShift M
    (rawDynamicTruthNativeLocalAdmissibleContextOn M baseContext
      sigmaDomain piDomain)
    (rawDynamicTruthNativeLocalAdmissibleContextOn M baseContext
      sigmaDomain piDomain) ->
  RawContextShift M
    (rawDynamicTruthNativeLocalExclusiveSigmaContextOn M baseContext
      sigmaDomain piDomain sigmaEvidence)
    (rawDynamicTruthNativeLocalExclusiveSigmaContextOn M baseContext
      sigmaDomain piDomain sigmaEvidence) ->
  RawContextShift M
    (rawDynamicTruthNativeLocalExclusivePiContextOn M baseContext
      sigmaDomain piDomain sigmaEvidence piEvidence)
    (rawDynamicTruthNativeLocalExclusivePiContextOn M baseContext
      sigmaDomain piDomain sigmaEvidence piEvidence) ->
  RawDynamicTruthSigmaSuccessorRowBranchDisjunctionCompilationInputs M
    (rawDynamicTruthNativeLocalExclusivePiContextOn M baseContext
      sigmaDomain piDomain sigmaEvidence piEvidence)
    sigmaRowDomain lowerPiApplication ->
  RawDynamicTruthPiSuccessorRowBranchDisjunctionCompilationInputs M
    (rawDynamicTruthNativeLocalExclusivePiContextOn M baseContext
      sigmaDomain piDomain sigmaEvidence piEvidence)
    piRowDomain lowerSigmaApplication ->
  RawFiniteDisjunctionMatrixResources M
    (rawDynamicTruthLocalSigmaBranches M lowerPiApplication)
    (rawDynamicTruthLocalPiBranches M lowerSigmaApplication)
    (rawDynamicTruthNativeLocalExclusivePiContextOn M baseContext
      sigmaDomain piDomain sigmaEvidence piEvidence) ->
  RawDynamicTruthNativeLocalGuardedExclusiveMatrixResourcesAt M
    (rawDynamicTruthNativeLocalExclusivePiContextOn M baseContext
      sigmaDomain piDomain sigmaEvidence piEvidence)
    sigmaRowDomain piRowDomain lowerPiApplication lowerSigmaApplication.
Proof.
  intros M hPA translation witnessList baseContext helperRoots
    sigmaDomain piDomain sigmaEvidence piEvidence
    sigmaRowDomain piRowDomain lowerPi lowerSigma
    hagreement hwitness hhelpers residual hpredecessor
    hadmissible hsigma hpi hadmissibleShift hsigmaShift hpiShift
    sigmaProjection piProjection matrixResources.
  destruct (raw_dynamicTruthNativeLocal_helper_roots_of_42_helpers
    M hPA translation baseContext helperRoots hagreement hhelpers) as
    (legacyRoots & hlegacyHelpers & hfalseCell & htrueCell).
  pose proof
    (raw_dynamicTruthNativeLocalExclusiveMatrixResourcesAt_of_40_helpers
      M hPA translation witnessList baseContext legacyRoots
      sigmaDomain piDomain sigmaEvidence piEvidence
      sigmaRowDomain piRowDomain lowerPi lowerSigma
      hagreement hwitness hlegacyHelpers residual
      hadmissible hsigma hpi hadmissibleShift hsigmaShift hpiShift
      sigmaProjection piProjection matrixResources) as legacy.
  pose proof (raw_codedPAAxiomWitnessContext_context_realizable
    M witnessList baseContext hwitness) as hbase.
  refine
    {| rawDynamicTruthNativeLocalGuardedExclusive_legacy := legacy;
       rawDynamicTruthNativeLocalGuardedExclusive_predecessor := _;
       rawDynamicTruthNativeLocalGuardedExclusive_falseCell := _;
       rawDynamicTruthNativeLocalGuardedExclusive_trueCell := _ |}.
  - exact (raw_dynamicTruthLocalRootAt_on_exclusive_context M hPA
      baseContext sigmaDomain piDomain sigmaEvidence piEvidence
      (rawDynamicTruthImpGuardedPredecessorStateExclusivityCode M)
      hbase hadmissible hsigma hpi hpredecessor).
  - exact (raw_dynamicTruthLocalRootAt_on_exclusive_context M hPA
      baseContext sigmaDomain piDomain sigmaEvidence piEvidence
      (rawDynamicTruthImpFalseLeftGuardedConditionalCellCode M)
      hbase hadmissible hsigma hpi hfalseCell).
  - exact (raw_dynamicTruthLocalRootAt_on_exclusive_context M hPA
      baseContext sigmaDomain piDomain sigmaEvidence piEvidence
      (rawDynamicTruthImpTrueRightGuardedConditionalCellCode M)
      hbase hadmissible hsigma hpi htrueCell).
Qed.

(** Corrected native exclusivity endpoint.  Row projection remains shared
    with the legacy resource; only the final pair-family selection changes. *)
Theorem raw_dynamicTruthNativeLocalExclusiveRootOn_of_rows_and_guarded_matrix :
    forall (M : RawPAModel) (hPA : RawPASatisfies M)
      baseContext sigmaDomain piDomain sigmaEvidence piEvidence
      sigmaRowDomain piRowDomain lowerPiApplication lowerSigmaApplication,
  RawDynamicTruthNativeLocalGuardedExclusiveMatrixResourcesAt M
    (rawDynamicTruthNativeLocalExclusivePiContextOn M baseContext
      sigmaDomain piDomain sigmaEvidence piEvidence)
    sigmaRowDomain piRowDomain lowerPiApplication lowerSigmaApplication ->
  (exists sigmaRowRoot piRowRoot : M,
    RawCodedPALocalProofOf M
      (rawDynamicTruthNativeLocalExclusivePiContextOn M baseContext
        sigmaDomain piDomain sigmaEvidence piEvidence)
      (rawDynamicTruthSigmaSuccessorRowCode M
        sigmaRowDomain lowerPiApplication) sigmaRowRoot /\
    RawCodedPALocalProofOf M
      (rawDynamicTruthNativeLocalExclusivePiContextOn M baseContext
        sigmaDomain piDomain sigmaEvidence piEvidence)
      (rawDynamicTruthPiSuccessorRowCode M
        piRowDomain lowerSigmaApplication) piRowRoot) ->
  RawDynamicTruthNativeLocalExclusiveRootOn M baseContext
    sigmaDomain piDomain sigmaEvidence piEvidence.
Proof.
  intros M hPA baseContext sigmaDomain piDomain sigmaEvidence piEvidence
    sigmaRowDomain piRowDomain lowerPi lowerSigma guarded
    (sigmaRowRoot & piRowRoot & hsigmaRow & hpiRow).
  set (context :=
    rawDynamicTruthNativeLocalExclusivePiContextOn M baseContext
      sigmaDomain piDomain sigmaEvidence piEvidence).
  pose (legacy := rawDynamicTruthNativeLocalGuardedExclusive_legacy
    M context sigmaRowDomain piRowDomain lowerPi lowerSigma guarded).
  pose proof
    (raw_codedPALocalProofOf_dynamicTruthSigmaSuccessorRowBranchDisjunction
      M hPA context sigmaRowDomain lowerPi
      (rawDynamicTruthNativeLocalExclusive_sigmaProjection
        M context sigmaRowDomain piRowDomain lowerPi lowerSigma legacy)
      sigmaRowRoot hsigmaRow) as hsigmaOr7.
  pose proof
    (raw_codedPALocalProofOf_dynamicTruthPiSuccessorRowBranchDisjunction
      M hPA context piRowDomain lowerSigma
      (rawDynamicTruthNativeLocalExclusive_piProjection
        M context sigmaRowDomain piRowDomain lowerPi lowerSigma legacy)
      piRowRoot hpiRow) as hpiOr6.
  destruct
    (raw_codedPALocalProofOf_dynamicTruthLocalCollisionMatrix_bottom_guarded_imp
      M hPA context lowerPi lowerSigma
      (rawDynamicTruthSigmaSuccessorRowBranchDisjunctionRoot
        M hPA context sigmaRowDomain lowerPi
        (rawDynamicTruthNativeLocalExclusive_sigmaProjection
          M context sigmaRowDomain piRowDomain lowerPi lowerSigma legacy)
        sigmaRowRoot)
      (rawDynamicTruthPiSuccessorRowBranchDisjunctionRoot
        M hPA context piRowDomain lowerSigma
        (rawDynamicTruthNativeLocalExclusive_piProjection
          M context sigmaRowDomain piRowDomain lowerPi lowerSigma legacy)
        piRowRoot)
      (rawDynamicTruthNativeLocalExclusive_collisionInputs
        M context sigmaRowDomain piRowDomain lowerPi lowerSigma legacy)
      (rawDynamicTruthNativeLocalGuardedExclusive_predecessor
        M context sigmaRowDomain piRowDomain lowerPi lowerSigma guarded)
      (rawDynamicTruthNativeLocalGuardedExclusive_falseCell
        M context sigmaRowDomain piRowDomain lowerPi lowerSigma guarded)
      (rawDynamicTruthNativeLocalGuardedExclusive_trueCell
        M context sigmaRowDomain piRowDomain lowerPi lowerSigma guarded)
      (rawDynamicTruthNativeLocalExclusive_matrixResources
        M context sigmaRowDomain piRowDomain lowerPi lowerSigma legacy)
      hsigmaOr7 hpiOr6) as [bottomRoot hbottom].
  exists bottomRoot. exact hbottom.
Qed.

End PABoundedRawCodedDynamicTruthNativeLocalGuardedMatrixCompilation.
