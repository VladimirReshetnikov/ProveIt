(**
  Witnessed-tail compilation of the two native local-field leaves.

  The connective shell in [RawCodedDynamicTruthNativeLocalProofCompilation]
  deliberately asks for roots over literal assumption contexts.  Arithmetic
  collision theorems, however, are represented by local roots over a
  witnessed PA-axiom context.  Erasing that tail would be an invalid
  strengthening.  This file therefore keeps the witnessed tail visible and
  compiles the strongest honest intermediate result.

  For exclusivity, all finite work is concrete: the native Sigma and Pi rows
  are projected to Or7 and Or6, and the audited forty-two-cell matrix derives
  bottom.  Two proof-producing interfaces remain visible:

  - a broad row-root callback supplies the two native row roots in the
    context containing admissibility and both evidence assumptions;
  - local decision supplies the evidence disjunction in the context
    containing admissibility.

  These are not semantic assumptions.  They ask for represented local proof
  roots with exact endpoints.  The row callback below is intentionally
  parametric in all four row arguments, so it is stronger than the eventual
  trace-linked evidence compiler; the exact non-parametric endpoint is
  [raw_dynamicTruthNativeLocalExclusiveRootOn_of_rows_and_matrix].  In
  particular, no validity/completeness principle and no equality between
  independently selected contexts appears.
*)

From Stdlib Require Import List.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors
  RawCodedFixedLevelTruthTotality
  RawCodedTemplateProofCompiler
  RawCodedTemplatePAEmbedding
  RawCodedContextLists
  RawCodedContextStructure
  RawCodedContextShift
  RawCodedPALocalProofExistential
  RawCodedPALocalProofContextInsertUnconditional
  RawCodedPALocalProofFiniteDisjunctionMatrix
  RawCodedRestrictedPAProof
  RawCodedTruthCertificateMasterFixedHelperBatchExtension
  RawCodedTruthCertificateMasterHelperLookup
  RawCodedTruthCertificateMasterCollisionHelperBatch
  RawCodedTruthCertificateMasterBinderPrincipalHelperBatch
  RawCodedTruthCertificateMasterMixedQFHelperBatch
  RawCodedDynamicTruthQFBranchExclusivity
  RawCodedDynamicTruthImpBranchExclusivity
  RawCodedDynamicTruthBooleanBranchExclusivity
  RawCodedDynamicTruthConstructorBranchDisjointness
  RawCodedDynamicTruthBinderOffDiagonalExclusivity
  RawCodedDynamicTruthMixedQFBranchExclusivity
  RawCodedDynamicTruthQuantifierBranchExclusivity
  RawCodedDynamicTruthQuantifierConditionalCellCompilation
  RawCodedDynamicTruthMixedQFHelperRootExtraction
  RawCodedDynamicTruthMixedQFOpaqueQuantifierCellCompilation
  RawCodedDynamicTruthNativeLocalPositiveGraph
  RawCodedDynamicTruthSigmaSuccessorRowGraph
  RawCodedDynamicTruthPiSuccessorRowGraph
  RawCodedDynamicTruthNativeLocalProofCompilation
  RawCodedDynamicTruthLocalCollisionMatrixAssembly
  RawCodedDynamicTruthSuccessorRowBranchDisjunctionCompilation.

Import ListNotations.

Module PABoundedRawCodedDynamicTruthNativeLocalLeafRootCompiler.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedFixedLevelTruthTotality.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedTemplatePAEmbedding.
Import PABoundedRawCodedContextLists.
Import PABoundedRawCodedContextStructure.
Import PABoundedRawCodedContextShift.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPALocalProofContextInsertUnconditional.
Import PABoundedRawCodedPALocalProofFiniteDisjunctionMatrix.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedTruthCertificateMasterFixedHelperBatchExtension.
Import PABoundedRawCodedTruthCertificateMasterHelperLookup.
Import PABoundedRawCodedTruthCertificateMasterCollisionHelperBatch.
Import PABoundedRawCodedTruthCertificateMasterBinderPrincipalHelperBatch.
Import PABoundedRawCodedTruthCertificateMasterMixedQFHelperBatch.
Import PABoundedRawCodedDynamicTruthQFBranchExclusivity.
Import PABoundedRawCodedDynamicTruthImpBranchExclusivity.
Import PABoundedRawCodedDynamicTruthBooleanBranchExclusivity.
Import PABoundedRawCodedDynamicTruthConstructorBranchDisjointness.
Import PABoundedRawCodedDynamicTruthBinderOffDiagonalExclusivity.
Import PABoundedRawCodedDynamicTruthMixedQFBranchExclusivity.
Import PABoundedRawCodedDynamicTruthQuantifierBranchExclusivity.
Import PABoundedRawCodedDynamicTruthQuantifierConditionalCellCompilation.
Import PABoundedRawCodedDynamicTruthMixedQFHelperRootExtraction.
Import
  PABoundedRawCodedDynamicTruthMixedQFOpaqueQuantifierCellCompilation.
Import PABoundedRawCodedDynamicTruthNativeLocalPositiveGraph.
Import PABoundedRawCodedDynamicTruthSigmaSuccessorRowGraph.
Import PABoundedRawCodedDynamicTruthPiSuccessorRowGraph.
Import PABoundedRawCodedDynamicTruthNativeLocalProofCompilation.
Import PABoundedRawCodedDynamicTruthLocalCollisionMatrixAssembly.
Import
  PABoundedRawCodedDynamicTruthSuccessorRowBranchDisjunctionCompilation.

(** ------------------------------------------------------------------
    Exact assumption contexts over an arbitrary PA tail. *)

Definition rawDynamicTruthNativeLocalAdmissibleContextOn
    (M : RawPAModel) (baseContext sigmaDomain piDomain : M) : M :=
  rawListNode M
    (rawDynamicTruthLocalAdmissibleCode M sigmaDomain piDomain)
    baseContext.

Definition rawDynamicTruthNativeLocalExclusiveSigmaContextOn
    (M : RawPAModel)
    (baseContext sigmaDomain piDomain sigmaEvidence : M) : M :=
  rawListNode M sigmaEvidence
    (rawDynamicTruthNativeLocalAdmissibleContextOn M baseContext
      sigmaDomain piDomain).

Definition rawDynamicTruthNativeLocalExclusivePiContextOn
    (M : RawPAModel)
    (baseContext sigmaDomain piDomain sigmaEvidence piEvidence : M) : M :=
  rawListNode M piEvidence
    (rawDynamicTruthNativeLocalExclusiveSigmaContextOn M baseContext
      sigmaDomain piDomain sigmaEvidence).

Arguments rawDynamicTruthNativeLocalAdmissibleContextOn
  M baseContext sigmaDomain piDomain : clear implicits.
Arguments rawDynamicTruthNativeLocalExclusiveSigmaContextOn
  M baseContext sigmaDomain piDomain sigmaEvidence : clear implicits.
Arguments rawDynamicTruthNativeLocalExclusivePiContextOn
  M baseContext sigmaDomain piDomain sigmaEvidence piEvidence
  : clear implicits.

Definition RawDynamicTruthNativeLocalDecisionRootOn
    (M : RawPAModel)
    (baseContext sigmaDomain piDomain sigmaEvidence piEvidence : M)
    : Prop :=
  exists root : M,
    RawCodedPALocalProofOf M
      (rawDynamicTruthNativeLocalAdmissibleContextOn M baseContext
        sigmaDomain piDomain)
      (rawFormulaOrCode M sigmaEvidence piEvidence) root.

Definition RawDynamicTruthNativeLocalExclusiveRootOn
    (M : RawPAModel)
    (baseContext sigmaDomain piDomain sigmaEvidence piEvidence : M)
    : Prop :=
  exists root : M,
    RawCodedPALocalProofOf M
      (rawDynamicTruthNativeLocalExclusivePiContextOn M baseContext
        sigmaDomain piDomain sigmaEvidence piEvidence)
      (rawFormulaBotCode M) root.

Arguments RawDynamicTruthNativeLocalDecisionRootOn
  M baseContext sigmaDomain piDomain sigmaEvidence piEvidence
  : clear implicits.
Arguments RawDynamicTruthNativeLocalExclusiveRootOn
  M baseContext sigmaDomain piDomain sigmaEvidence piEvidence
  : clear implicits.

(** The first residual interface is the proof-producing decision step.  Its
    trace argument prevents a caller from silently reusing a decision root
    belonging to a different orbit edge or different application outputs. *)
Definition RawDynamicTruthNativeLocalDecisionEvidenceRootInterface
    (M : RawPAModel) : Prop :=
  forall (tail : nat -> M) predecessorLevel
      inputGlobalSigma inputGlobalPi
      sigmaDomain piDomain sigmaEvidence piEvidence baseContext,
    RawDynamicTruthNativeLocalProofTraceAt M tail predecessorLevel
      inputGlobalSigma inputGlobalPi sigmaDomain piDomain
      sigmaEvidence piEvidence ->
    RawDynamicTruthNativeLocalDecisionRootOn M baseContext
      sigmaDomain piDomain sigmaEvidence piEvidence.

Arguments RawDynamicTruthNativeLocalDecisionEvidenceRootInterface M
  : clear implicits.

(** This broad modular adapter asks for row roots at every four supplied row
    parameters.  It is useful only when a caller already owns a total row
    compiler.  The local trace above does not itself link arbitrary values of
    [sigmaRowDomain], [piRowDomain], [lowerPiApplication], and
    [lowerSigmaApplication] to its successor edge, so this definition must
    not be mistaken for the eventual trace-linked global-evidence compiler.
    The theorem [raw_dynamicTruthNativeLocalExclusiveRootOn_of_rows_and_matrix]
    below is the exact endpoint: it consumes concrete row roots and matrix
    resources indexed by the very same four parameters. *)
Definition RawDynamicTruthNativeGlobalEvidenceRowRootInterface
    (M : RawPAModel) : Prop :=
  forall (tail : nat -> M) predecessorLevel
      inputGlobalSigma inputGlobalPi
      sigmaDomain piDomain sigmaEvidence piEvidence baseContext
      sigmaRowDomain piRowDomain lowerPiApplication lowerSigmaApplication,
    RawDynamicTruthNativeLocalProofTraceAt M tail predecessorLevel
      inputGlobalSigma inputGlobalPi sigmaDomain piDomain
      sigmaEvidence piEvidence ->
    exists sigmaRowRoot piRowRoot : M,
      RawCodedPALocalProofOf M
        (rawDynamicTruthNativeLocalExclusivePiContextOn M baseContext
          sigmaDomain piDomain sigmaEvidence piEvidence)
        (rawDynamicTruthSigmaSuccessorRowCode M
          sigmaRowDomain lowerPiApplication) sigmaRowRoot /\
      RawCodedPALocalProofOf M
        (rawDynamicTruthNativeLocalExclusivePiContextOn M baseContext
          sigmaDomain piDomain sigmaEvidence piEvidence)
        (rawDynamicTruthPiSuccessorRowCode M
          piRowDomain lowerSigmaApplication) piRowRoot.

Arguments RawDynamicTruthNativeGlobalEvidenceRowRootInterface M
  : clear implicits.

(** ------------------------------------------------------------------
    Projection of the synchronized forty-helper batch.

    The helper family is structurally indexed, so every lookup below
    preserves the exact helper/root correspondence.  The equations rewrite
    translated ordinary quotations to the native carrier polynomials; no
    semantic formula equality is used. *)

Lemma raw_dynamicTruthNativeLocal_helper_root : forall
    (M : RawPAModel) translation context roots helper,
  RawFixedPAHelperBatchLocalProofs M translation context
    rawDynamicTruthReadyAndAllMixedQFPAHelpers roots ->
  In helper rawDynamicTruthReadyAndAllMixedQFPAHelpers ->
  exists root : M,
    RawCodedPALocalProofOf M context
      (rawFixedPAHelperTranslatedTargetCode M translation helper) root.
Proof.
  intros M translation context roots helper hroots hin.
  exact (raw_fixedPAHelperBatchLocalProofs_member M translation context
    rawDynamicTruthReadyAndAllMixedQFPAHelpers roots helper hroots hin).
Qed.

Lemma rawDynamicTruthQFCollisionHelperTarget_eq_native : forall
    (M : RawPAModel), RawPASatisfies M -> forall translation,
  RawCodedTemplatePAAgreement M translation ->
  rawFixedPAHelperTranslatedTargetCode M translation
    rawDynamicTruthQFCollisionFixedPAHelper =
  rawDynamicTruthQFEx8BranchExclusivityCode M.
Proof.
  intros M hPA translation hagreement.
  unfold rawFixedPAHelperTranslatedTargetCode,
    rawDynamicTruthQFCollisionFixedPAHelper.
  cbn [rawFixedPAHelperFormula].
  rewrite (rawTemplateFormula_embedPA hagreement).
  symmetry. exact (rawDynamicTruthQFEx8BranchExclusivityCode_eq_quoted
    M hPA).
Qed.

Lemma rawDynamicTruthImpFalseHelperTarget_eq_native : forall
    (M : RawPAModel), RawPASatisfies M -> forall translation,
  RawCodedTemplatePAAgreement M translation ->
  rawFixedPAHelperTranslatedTargetCode M translation
    rawDynamicTruthImpFalseLeftCollisionFixedPAHelper =
  rawDynamicTruthImpFalseLeftConditionalCellCode M.
Proof.
  intros M hPA translation hagreement.
  unfold rawFixedPAHelperTranslatedTargetCode,
    rawDynamicTruthImpFalseLeftCollisionFixedPAHelper.
  cbn [rawFixedPAHelperFormula].
  rewrite (rawTemplateFormula_embedPA hagreement).
  symmetry. exact (rawDynamicTruthImpFalseLeftConditionalCellCode_eq_quoted
    M hPA).
Qed.

Lemma rawDynamicTruthImpTrueHelperTarget_eq_native : forall
    (M : RawPAModel), RawPASatisfies M -> forall translation,
  RawCodedTemplatePAAgreement M translation ->
  rawFixedPAHelperTranslatedTargetCode M translation
    rawDynamicTruthImpTrueRightCollisionFixedPAHelper =
  rawDynamicTruthImpTrueRightConditionalCellCode M.
Proof.
  intros M hPA translation hagreement.
  unfold rawFixedPAHelperTranslatedTargetCode,
    rawDynamicTruthImpTrueRightCollisionFixedPAHelper.
  cbn [rawFixedPAHelperFormula].
  rewrite (rawTemplateFormula_embedPA hagreement).
  symmetry. exact (rawDynamicTruthImpTrueRightConditionalCellCode_eq_quoted
    M hPA).
Qed.

Lemma rawDynamicTruthAndHelperTarget_eq_native : forall
    (M : RawPAModel), RawPASatisfies M -> forall translation,
  RawCodedTemplatePAAgreement M translation ->
  rawFixedPAHelperTranslatedTargetCode M translation
    rawDynamicTruthAndCollisionFixedPAHelper =
  rawDynamicTruthAndConditionalCellCode M.
Proof.
  intros M hPA translation hagreement.
  unfold rawFixedPAHelperTranslatedTargetCode,
    rawDynamicTruthAndCollisionFixedPAHelper.
  cbn [rawFixedPAHelperFormula].
  rewrite (rawTemplateFormula_embedPA hagreement).
  symmetry. exact (rawDynamicTruthAndConditionalCellCode_eq_quoted
    M hPA).
Qed.

Lemma rawDynamicTruthOrHelperTarget_eq_native : forall
    (M : RawPAModel), RawPASatisfies M -> forall translation,
  RawCodedTemplatePAAgreement M translation ->
  rawFixedPAHelperTranslatedTargetCode M translation
    rawDynamicTruthOrCollisionFixedPAHelper =
  rawDynamicTruthOrConditionalCellCode M.
Proof.
  intros M hPA translation hagreement.
  unfold rawFixedPAHelperTranslatedTargetCode,
    rawDynamicTruthOrCollisionFixedPAHelper.
  cbn [rawFixedPAHelperFormula].
  rewrite (rawTemplateFormula_embedPA hagreement).
  symmetry. exact (rawDynamicTruthOrConditionalCellCode_eq_quoted
    M hPA).
Qed.

Lemma rawDynamicTruthBinderPrincipalHelperTarget_eq_native : forall
    (M : RawPAModel), RawPASatisfies M -> forall translation,
  RawCodedTemplatePAAgreement M translation -> forall cell,
  rawFixedPAHelperTranslatedTargetCode M translation
    (rawDynamicTruthBinderPrincipalCollisionPAHelper cell) =
  rawDynamicTruthBinderPrincipalCollisionCode M cell.
Proof.
  intros M hPA translation hagreement cell.
  unfold rawFixedPAHelperTranslatedTargetCode,
    rawDynamicTruthBinderPrincipalCollisionPAHelper.
  cbn [rawFixedPAHelperFormula].
  rewrite (rawTemplateFormula_embedPA hagreement).
  symmetry. exact (rawDynamicTruthBinderPrincipalCollisionCode_eq_quoted
    M hPA cell).
Qed.

(** Five direct cell roots are the non-parametric diagonal entries of the
    matrix. *)
Theorem raw_dynamicTruthNativeLocal_basicCollisionRoots_of_40_helpers :
    forall (M : RawPAModel), RawPASatisfies M -> forall
      translation context roots,
  RawCodedTemplatePAAgreement M translation ->
  RawFixedPAHelperBatchLocalProofs M translation context
    rawDynamicTruthReadyAndAllMixedQFPAHelpers roots ->
  RawDynamicTruthLocalRootAt M context
      (rawDynamicTruthQFEx8BranchExclusivityCode M) /\
  RawDynamicTruthLocalRootAt M context
      (rawDynamicTruthImpFalseLeftConditionalCellCode M) /\
  RawDynamicTruthLocalRootAt M context
      (rawDynamicTruthImpTrueRightConditionalCellCode M) /\
  RawDynamicTruthLocalRootAt M context
      (rawDynamicTruthAndConditionalCellCode M) /\
  RawDynamicTruthLocalRootAt M context
      (rawDynamicTruthOrConditionalCellCode M).
Proof.
  intros M hPA translation context roots hagreement hroots.
  assert (lookup : forall helper,
      In helper rawDynamicTruthReadyAndAllMixedQFPAHelpers ->
      exists root : M, RawCodedPALocalProofOf M context
        (rawFixedPAHelperTranslatedTargetCode M translation helper) root).
  { intros helper hin. exact (raw_dynamicTruthNativeLocal_helper_root
      M translation context roots helper hroots hin). }
  destruct (lookup rawDynamicTruthQFCollisionFixedPAHelper) as
    [qfRoot hqf].
  { unfold rawDynamicTruthReadyAndAllMixedQFPAHelpers,
      rawDynamicTruthReadyBinderPrincipalAndMixedQFPAHelpers,
      rawDynamicTruthReadyAndBinderPrincipalPAHelpers,
      rawDynamicTruthReadyCollisionFixedPAHelpers,
      rawDynamicTruthFirstThreeCollisionFixedPAHelpers.
    cbn. tauto. }
  destruct (lookup rawDynamicTruthImpFalseLeftCollisionFixedPAHelper) as
    [impFalseRoot himpFalse].
  { unfold rawDynamicTruthReadyAndAllMixedQFPAHelpers,
      rawDynamicTruthReadyBinderPrincipalAndMixedQFPAHelpers,
      rawDynamicTruthReadyAndBinderPrincipalPAHelpers,
      rawDynamicTruthReadyCollisionFixedPAHelpers,
      rawDynamicTruthFirstThreeCollisionFixedPAHelpers.
    cbn. tauto. }
  destruct (lookup rawDynamicTruthImpTrueRightCollisionFixedPAHelper) as
    [impTrueRoot himpTrue].
  { unfold rawDynamicTruthReadyAndAllMixedQFPAHelpers,
      rawDynamicTruthReadyBinderPrincipalAndMixedQFPAHelpers,
      rawDynamicTruthReadyAndBinderPrincipalPAHelpers,
      rawDynamicTruthReadyCollisionFixedPAHelpers,
      rawDynamicTruthFirstThreeCollisionFixedPAHelpers.
    cbn. tauto. }
  destruct (lookup rawDynamicTruthAndCollisionFixedPAHelper) as
    [andRoot hand].
  { unfold rawDynamicTruthReadyAndAllMixedQFPAHelpers,
      rawDynamicTruthReadyBinderPrincipalAndMixedQFPAHelpers,
      rawDynamicTruthReadyAndBinderPrincipalPAHelpers,
      rawDynamicTruthReadyCollisionFixedPAHelpers,
      rawDynamicTruthFirstThreeCollisionFixedPAHelpers.
    cbn. tauto. }
  destruct (lookup rawDynamicTruthOrCollisionFixedPAHelper) as
    [orRoot hor].
  { unfold rawDynamicTruthReadyAndAllMixedQFPAHelpers,
      rawDynamicTruthReadyBinderPrincipalAndMixedQFPAHelpers,
      rawDynamicTruthReadyAndBinderPrincipalPAHelpers,
      rawDynamicTruthReadyCollisionFixedPAHelpers,
      rawDynamicTruthFirstThreeCollisionFixedPAHelpers.
    cbn. tauto. }
  rewrite (rawDynamicTruthQFCollisionHelperTarget_eq_native
    M hPA translation hagreement) in hqf.
  rewrite (rawDynamicTruthImpFalseHelperTarget_eq_native
    M hPA translation hagreement) in himpFalse.
  rewrite (rawDynamicTruthImpTrueHelperTarget_eq_native
    M hPA translation hagreement) in himpTrue.
  rewrite (rawDynamicTruthAndHelperTarget_eq_native
    M hPA translation hagreement) in hand.
  rewrite (rawDynamicTruthOrHelperTarget_eq_native
    M hPA translation hagreement) in hor.
  split.
  - exists qfRoot. exact hqf.
  - split.
    + exists impFalseRoot. exact himpFalse.
    + split.
      * exists impTrueRoot. exact himpTrue.
      * split.
        -- exists andRoot. exact hand.
        -- exists orRoot. exact hor.
Qed.

Lemma rawDynamicTruthFixedConstructorHelperTarget_eq_native : forall
    (M : RawPAModel), RawPASatisfies M -> forall translation,
  RawCodedTemplatePAAgreement M translation -> forall
      sigmaBranch piBranch
      (hcell : In (sigmaBranch, piBranch)
        dynamicTruthFixedConstructorCells),
  rawFixedPAHelperTranslatedTargetCode M translation
    (rawDynamicTruthFixedConstructorCollisionPAHelper
      sigmaBranch piBranch hcell) =
  rawDynamicTruthFixedConstructorBranchDisjointnessCode M
    sigmaBranch piBranch.
Proof.
  intros M hPA translation hagreement sigmaBranch piBranch hcell.
  unfold rawFixedPAHelperTranslatedTargetCode,
    rawDynamicTruthFixedConstructorCollisionPAHelper.
  cbn [rawFixedPAHelperFormula].
  rewrite (rawTemplateFormula_embedPA hagreement).
  unfold rawDynamicTruthFixedConstructorBranchDisjointnessCode.
  symmetry.
  exact (rawDynamicTruthConstructorBranchDisjointnessCode_eq_quoted
    M hPA sigmaBranch pBot piBranch pBot).
Qed.

Lemma rawDynamicTruthLocalSigmaConstructorCode_eq_fixed : forall
    (M : RawPAModel), RawPASatisfies M -> forall sigmaBranch,
  sigmaBranch <> DTSigmaAll -> forall lowerPiApplication,
  rawDynamicTruthLocalSigmaConstructorBranchCode M
    lowerPiApplication sigmaBranch =
  rawDynamicTruthSigmaConstructorEx8BranchCode M sigmaBranch pBot.
Proof.
  intros M hPA sigmaBranch hfixed lowerPi.
  destruct sigmaBranch.
  - change (rawDynamicTruthSigmaImpFalseLeftEx8BranchCode M =
      rawDynamicTruthSigmaConstructorEx8BranchCode M
        DTSigmaImpFalseLeft pBot).
    rewrite rawDynamicTruthSigmaConstructorEx8BranchCode_eq_quoted
      by exact hPA.
    rewrite rawDynamicTruthSigmaImpFalseLeftEx8BranchCode_eq_quoted
      by exact hPA.
    reflexivity.
  - change (rawDynamicTruthSigmaImpTrueRightEx8BranchCode M =
      rawDynamicTruthSigmaConstructorEx8BranchCode M
        DTSigmaImpTrueRight pBot).
    rewrite rawDynamicTruthSigmaConstructorEx8BranchCode_eq_quoted
      by exact hPA.
    rewrite rawDynamicTruthSigmaImpTrueRightEx8BranchCode_eq_quoted
      by exact hPA.
    reflexivity.
  - change (rawDynamicTruthSigmaAndEx8BranchCode M =
      rawDynamicTruthSigmaConstructorEx8BranchCode M DTSigmaAnd pBot).
    rewrite rawDynamicTruthSigmaConstructorEx8BranchCode_eq_quoted
      by exact hPA.
    rewrite rawDynamicTruthSigmaAndEx8BranchCode_eq_quoted by exact hPA.
    reflexivity.
  - change (rawDynamicTruthSigmaOrEx8BranchCode M =
      rawDynamicTruthSigmaConstructorEx8BranchCode M DTSigmaOr pBot).
    rewrite rawDynamicTruthSigmaConstructorEx8BranchCode_eq_quoted
      by exact hPA.
    rewrite rawDynamicTruthSigmaOrEx8BranchCode_eq_quoted by exact hPA.
    reflexivity.
  - change (rawDynamicTruthSigmaEx8BranchCode M =
      rawDynamicTruthSigmaConstructorEx8BranchCode M DTSigmaEx pBot).
    rewrite rawDynamicTruthSigmaConstructorEx8BranchCode_eq_quoted
      by exact hPA.
    rewrite rawDynamicTruthSigmaEx8BranchCode_eq_quoted by exact hPA.
    reflexivity.
  - contradiction.
Qed.

Lemma rawDynamicTruthLocalPiConstructorCode_eq_fixed : forall
    (M : RawPAModel), RawPASatisfies M -> forall piBranch,
  piBranch <> DTPiEx -> forall lowerSigmaApplication,
  rawDynamicTruthLocalPiConstructorBranchCode M
    lowerSigmaApplication piBranch =
  rawDynamicTruthPiConstructorEx8BranchCode M piBranch pBot.
Proof.
  intros M hPA piBranch hfixed lowerSigma.
  destruct piBranch.
  - change (rawDynamicTruthPiImpEx8BranchCode M =
      rawDynamicTruthPiConstructorEx8BranchCode M DTPiImp pBot).
    rewrite rawDynamicTruthPiConstructorEx8BranchCode_eq_quoted
      by exact hPA.
    rewrite rawDynamicTruthPiImpEx8BranchCode_eq_quoted by exact hPA.
    reflexivity.
  - change (rawDynamicTruthPiAndEx8BranchCode M =
      rawDynamicTruthPiConstructorEx8BranchCode M DTPiAnd pBot).
    rewrite rawDynamicTruthPiConstructorEx8BranchCode_eq_quoted
      by exact hPA.
    rewrite rawDynamicTruthPiAndEx8BranchCode_eq_quoted by exact hPA.
    reflexivity.
  - change (rawDynamicTruthPiOrEx8BranchCode M =
      rawDynamicTruthPiConstructorEx8BranchCode M DTPiOr pBot).
    rewrite rawDynamicTruthPiConstructorEx8BranchCode_eq_quoted
      by exact hPA.
    rewrite rawDynamicTruthPiOrEx8BranchCode_eq_quoted by exact hPA.
    reflexivity.
  - change (rawDynamicTruthPiAllEx8BranchCode M =
      rawDynamicTruthPiConstructorEx8BranchCode M DTPiAll pBot).
    rewrite rawDynamicTruthPiConstructorEx8BranchCode_eq_quoted
      by exact hPA.
    rewrite rawDynamicTruthPiAllEx8BranchCode_eq_quoted by exact hPA.
    reflexivity.
  - contradiction.
Qed.

Lemma rawDynamicTruthFixedConstructorCode_eq_local : forall
    (M : RawPAModel), RawPASatisfies M -> forall sigmaBranch piBranch,
  DynamicTruthFixedConstructorCell sigmaBranch piBranch ->
  forall lowerPiApplication lowerSigmaApplication,
  rawDynamicTruthFixedConstructorBranchDisjointnessCode M
    sigmaBranch piBranch =
  rawFormulaImpCode M
    (rawDynamicTruthLocalSigmaConstructorBranchCode M
      lowerPiApplication sigmaBranch)
    (rawFormulaImpCode M
      (rawDynamicTruthLocalPiConstructorBranchCode M
        lowerSigmaApplication piBranch)
      (rawFormulaBotCode M)).
Proof.
  intros M hPA sigmaBranch piBranch (hsigma & hpi & _hdisjoint)
    lowerPi lowerSigma.
  unfold rawDynamicTruthFixedConstructorBranchDisjointnessCode,
    rawDynamicTruthConstructorBranchDisjointnessCode.
  rewrite (rawDynamicTruthLocalSigmaConstructorCode_eq_fixed
    M hPA sigmaBranch hsigma lowerPi).
  rewrite (rawDynamicTruthLocalPiConstructorCode_eq_fixed
    M hPA piBranch hpi lowerSigma).
  reflexivity.
Qed.

(** Split a synchronized batch at an append without comparing helper records.
    This structural inverse is especially important for the fixed-constructor
    helpers: their records contain proof-indexed certificates, so selecting
    them by record equality would require proof irrelevance. *)
Lemma raw_fixedPAHelperBatchLocalProofs_app_inv : forall
    (M : RawPAModel) translation context left right roots,
  RawFixedPAHelperBatchLocalProofs M translation context
    (left ++ right) roots ->
  exists leftRoots rightRoots,
    RawFixedPAHelperBatchLocalProofs M translation context left leftRoots /\
    RawFixedPAHelperBatchLocalProofs M translation context right rightRoots.
Proof.
  intros M translation context left.
  induction left as [| helper helperTail ih]; intros right roots hroots.
  - exists [], roots. split.
    + exact I.
    + exact hroots.
  - destruct roots as [| root rootTail].
    + contradiction.
    + cbn [RawFixedPAHelperBatchLocalProofs] in hroots.
      destruct hroots as [hroot htail].
      destruct (ih right rootTail htail) as
        (leftRoots & rightRoots & hleft & hright).
      exists (root :: leftRoots), rightRoots. split.
      * cbn [RawFixedPAHelperBatchLocalProofs]. now split.
      * exact hright.
Qed.

(** The sixteen proof-indexed fixed-constructor helpers are extracted as a
    synchronized sub-batch.  Converting this sub-batch to the extensional
    fixed-pair family would require comparing the membership certificates
    stored in helper records, so that last conversion remains an explicit
    residual below. *)
Theorem raw_dynamicTruthNativeLocal_fixedPairBatch_of_40_helpers :
    forall (M : RawPAModel) translation context roots,
  RawFixedPAHelperBatchLocalProofs M translation context
    rawDynamicTruthReadyAndAllMixedQFPAHelpers roots ->
  exists fixedRoots,
    RawFixedPAHelperBatchLocalProofs M translation context
      rawDynamicTruthFixedConstructorCollisionPAHelpers fixedRoots.
Proof.
  intros M translation context roots hroots.
  unfold rawDynamicTruthReadyAndAllMixedQFPAHelpers in hroots.
  destruct (raw_fixedPAHelperBatchLocalProofs_app_inv M translation
    context rawDynamicTruthReadyBinderPrincipalAndMixedQFPAHelpers
    rawDynamicTruthMixedQFOpaqueTransportSeedPAHelpers roots hroots) as
    (roots38 & _opaqueRoots & hroots38 & _hopaque).
  unfold rawDynamicTruthReadyBinderPrincipalAndMixedQFPAHelpers in hroots38.
  destruct (raw_fixedPAHelperBatchLocalProofs_app_inv M translation
    context rawDynamicTruthReadyAndBinderPrincipalPAHelpers
    rawDynamicTruthMixedQFFixedPAHelpers roots38 hroots38) as
    (roots29 & _mixedRoots & hroots29 & _hmixed).
  unfold rawDynamicTruthReadyAndBinderPrincipalPAHelpers in hroots29.
  destruct (raw_fixedPAHelperBatchLocalProofs_app_inv M translation
    context rawDynamicTruthReadyCollisionFixedPAHelpers
    rawDynamicTruthBinderPrincipalCollisionPAHelpers roots29 hroots29) as
    (roots21 & _binderRoots & hroots21 & _hbinder).
  unfold rawDynamicTruthReadyCollisionFixedPAHelpers in hroots21.
  destruct (raw_fixedPAHelperBatchLocalProofs_app_inv M translation
    context rawDynamicTruthFirstThreeCollisionFixedPAHelpers
    ([rawDynamicTruthAndCollisionFixedPAHelper;
       rawDynamicTruthOrCollisionFixedPAHelper] ++
      rawDynamicTruthFixedConstructorCollisionPAHelpers)
    roots21 hroots21) as
    (_firstThreeRoots & boolAndFixedRoots & _hfirstThree & hboolAndFixed).
  destruct (raw_fixedPAHelperBatchLocalProofs_app_inv M translation
    context
    [rawDynamicTruthAndCollisionFixedPAHelper;
     rawDynamicTruthOrCollisionFixedPAHelper]
    rawDynamicTruthFixedConstructorCollisionPAHelpers
    boolAndFixedRoots hboolAndFixed) as
    (_booleanRoots & fixedRoots & _hboolean & hfixed).
  now exists fixedRoots.
Qed.

(** Every binder principal helper is available in the common context.  The
    proof uses the public eight-cell completeness theorem rather than a
    positional list index. *)
Theorem raw_dynamicTruthNativeLocal_binderPrincipalRoots_of_40_helpers :
    forall (M : RawPAModel), RawPASatisfies M -> forall
      translation context roots,
  RawCodedTemplatePAAgreement M translation ->
  RawFixedPAHelperBatchLocalProofs M translation context
    rawDynamicTruthReadyAndAllMixedQFPAHelpers roots ->
  forall cell,
    RawDynamicTruthBinderPrincipalCollisionAvailableAt M context cell.
Proof.
  intros M hPA translation context roots hagreement hroots cell.
  destruct (raw_dynamicTruthNativeLocal_helper_root M translation context
    roots (rawDynamicTruthBinderPrincipalCollisionPAHelper cell)
    hroots) as [root hroot].
  - unfold rawDynamicTruthReadyAndAllMixedQFPAHelpers,
      rawDynamicTruthReadyBinderPrincipalAndMixedQFPAHelpers,
      rawDynamicTruthReadyAndBinderPrincipalPAHelpers.
    apply in_or_app. left.
    apply in_or_app. left.
    apply in_or_app. right.
    unfold rawDynamicTruthBinderPrincipalCollisionPAHelpers.
    apply in_map.
    exact (dynamicTruthBinderOffDiagonalCells_complete cell).
  - rewrite (rawDynamicTruthBinderPrincipalHelperTarget_eq_native
      M hPA translation hagreement cell) in hroot.
    now exists root.
Qed.

(** The two opaque cells are transported from the final fixed-bottom seeds;
    the other nine are recovered from the 38-prefix.  Both operations retain
    the one literal witnessed context of the synchronized batch. *)
Theorem raw_dynamicTruthNativeLocal_mixedQFRoots_of_40_helpers : forall
    (M : RawPAModel) (hPA : RawPASatisfies M)
      translation witnessList context roots
      lowerPiApplication lowerSigmaApplication,
  RawCodedTemplatePAAgreement M translation ->
  RawCodedPAAxiomWitnessContext M witnessList context ->
  RawFixedPAHelperBatchLocalProofs M translation context
    rawDynamicTruthReadyAndAllMixedQFPAHelpers roots ->
  RawDynamicTruthQuantifierLowerApplicationDirectTrace
    M lowerPiApplication ->
  RawDynamicTruthQuantifierLowerApplicationDirectTrace
    M lowerSigmaApplication ->
  RawDynamicTruthMixedQFAllCellRootsAt M context
    lowerPiApplication lowerSigmaApplication.
Proof.
  intros M hPA translation witnessList context roots lowerPi lowerSigma
    hagreement hwitness hroots piTrace sigmaTrace.
  destruct (raw_mixedQFOpaqueTransportSeedRoots_of_40helper_roots
    M hPA translation hagreement context roots hroots) as
    (prefixRoots & sigmaQFPiExSeedRoot & sigmaAllPiQFSeedRoot &
      _horder & hprefix & hsigmaQFPiExSeed & hsigmaAllPiQFSeed).
  pose proof
    (raw_codedPALocalProofOf_dynamicTruthSigmaQFPiExOpaqueCell_witnessed
      M hPA witnessList context lowerSigma sigmaQFPiExSeedRoot
      sigmaTrace hwitness hsigmaQFPiExSeed) as hsigmaQFPiEx.
  pose proof
    (raw_codedPALocalProofOf_dynamicTruthSigmaAllPiQFOpaqueCell_witnessed
      M hPA witnessList context lowerPi sigmaAllPiQFSeedRoot
      piTrace hwitness hsigmaAllPiQFSeed) as hsigmaAllPiQF.
  apply (raw_dynamicTruthMixedQFAllCellRootsAt_of_helper_batch
    M hPA translation hagreement context prefixRoots lowerPi lowerSigma
    hprefix).
  split.
  - eexists. exact hsigmaQFPiEx.
  - eexists. exact hsigmaAllPiQF.
Qed.

(** The synchronized batch directly supplies the five non-parametric
    diagonal roots, all binder-principal roots, and all mixed-QF roots.  The
    residual record keeps the genuinely carrier-dependent resources plus the
    extensional sixteen-cell fixed-pair family.  Its canonical helper
    sub-batch is extracted above, but converting proof-indexed helper records
    to that extensional family without proof irrelevance is intentionally not
    hidden here. *)
Record RawDynamicTruthNativeLocalCollisionResidualInputsAt
    (M : RawPAModel) (context lowerPiApplication lowerSigmaApplication : M)
    : Type := {
  rawDynamicTruthNativeLocalCollision_contextRealizable :
    RawContextListRealizable M context;
  rawDynamicTruthNativeLocalCollision_lowerPiAdequate :
    RawCodedFormulaAtomicallyAdequate M lowerPiApplication;
  rawDynamicTruthNativeLocalCollision_lowerSigmaAdequate :
    RawCodedFormulaAtomicallyAdequate M lowerSigmaApplication;
  rawDynamicTruthNativeLocalCollision_contextSelfShift :
    RawContextShift M context context;
  rawDynamicTruthNativeLocalCollision_predecessorRoot :
    RawDynamicTruthLocalRootAt M context
      (rawDynamicTruthImpPredecessorStateExclusivityCode M);
  rawDynamicTruthNativeLocalCollision_fixedPairs :
    RawDynamicTruthLocalFixedPairFamily M context
      lowerPiApplication lowerSigmaApplication;
  rawDynamicTruthNativeLocalCollision_binderProjections :
    forall cell : DynamicTruthBinderOffDiagonalCell,
      RawDynamicTruthBinderPrincipalProjectionInterfaceAt M context cell
        lowerPiApplication lowerSigmaApplication;
  rawDynamicTruthNativeLocalCollision_sigmaExTrace :
    RawDynamicTruthQuantifierLowerApplicationDirectTrace
      M lowerSigmaApplication;
  rawDynamicTruthNativeLocalCollision_sigmaAllTrace :
    RawDynamicTruthQuantifierLowerApplicationDirectTrace
      M lowerPiApplication;
  rawDynamicTruthNativeLocalCollision_sigmaExCrossRoot :
    RawDynamicTruthLocalRootAt M context
      (rawDynamicTruthSigmaExPiExCrossLevelPremiseCode M
        lowerSigmaApplication);
  rawDynamicTruthNativeLocalCollision_sigmaAllCrossRoot :
    RawDynamicTruthLocalRootAt M context
      (rawDynamicTruthSigmaAllPiAllCrossLevelPremiseCode M
        lowerPiApplication);
  rawDynamicTruthNativeLocalCollision_mixedReplayRoot :
    RawDynamicTruthLocalRootAt M context
      (rawDynamicTruthMixedQFReplayExclusivityCode M)
}.

Arguments RawDynamicTruthNativeLocalCollisionResidualInputsAt
  M context lowerPiApplication lowerSigmaApplication : clear implicits.

(** Assemble the exact matrix-input record.  Every root obtained from the
    helper batch remains in [context]; the opaque transports use the same
    witnessed context and therefore introduce no hidden context choice. *)
Theorem raw_dynamicTruthNativeLocalCollisionMatrixInputs_of_40_helpers :
    forall (M : RawPAModel) (hPA : RawPASatisfies M)
      translation witnessList context roots
      lowerPiApplication lowerSigmaApplication,
  RawCodedTemplatePAAgreement M translation ->
  RawCodedPAAxiomWitnessContext M witnessList context ->
  RawFixedPAHelperBatchLocalProofs M translation context
    rawDynamicTruthReadyAndAllMixedQFPAHelpers roots ->
  RawDynamicTruthNativeLocalCollisionResidualInputsAt M context
    lowerPiApplication lowerSigmaApplication ->
  RawDynamicTruthLocalCollisionMatrixInputs M context
    lowerPiApplication lowerSigmaApplication.
Proof.
  intros M hPA translation witnessList context roots lowerPi lowerSigma
    hagreement hwitness hhelpers residual.
  destruct (raw_dynamicTruthNativeLocal_basicCollisionRoots_of_40_helpers
    M hPA translation context roots hagreement hhelpers) as
    (hqf & himpFalse & himpTrue & hand & hor).
  pose proof
    (raw_dynamicTruthNativeLocal_binderPrincipalRoots_of_40_helpers
      M hPA translation context roots hagreement hhelpers)
    as hbinderPrincipals.
  pose proof
    (raw_dynamicTruthNativeLocal_mixedQFRoots_of_40_helpers
      M hPA translation witnessList context roots lowerPi lowerSigma
      hagreement hwitness hhelpers
      (rawDynamicTruthNativeLocalCollision_sigmaAllTrace
        M context lowerPi lowerSigma residual)
      (rawDynamicTruthNativeLocalCollision_sigmaExTrace
        M context lowerPi lowerSigma residual))
    as hmixed.
  refine
    {| rawDynamicTruthLocalCollision_context_realizable :=
         rawDynamicTruthNativeLocalCollision_contextRealizable
           M context lowerPi lowerSigma residual;
       rawDynamicTruthLocalCollision_lowerPi_adequate :=
         rawDynamicTruthNativeLocalCollision_lowerPiAdequate
           M context lowerPi lowerSigma residual;
       rawDynamicTruthLocalCollision_lowerSigma_adequate :=
         rawDynamicTruthNativeLocalCollision_lowerSigmaAdequate
           M context lowerPi lowerSigma residual;
       rawDynamicTruthLocalCollision_context_self_shift :=
         rawDynamicTruthNativeLocalCollision_contextSelfShift
           M context lowerPi lowerSigma residual;
       rawDynamicTruthLocalCollision_qf_root := hqf;
       rawDynamicTruthLocalCollision_predecessor_root :=
         rawDynamicTruthNativeLocalCollision_predecessorRoot
           M context lowerPi lowerSigma residual;
       rawDynamicTruthLocalCollision_impFalse_root := himpFalse;
       rawDynamicTruthLocalCollision_impTrue_root := himpTrue;
       rawDynamicTruthLocalCollision_and_root := hand;
       rawDynamicTruthLocalCollision_or_root := hor;
       rawDynamicTruthLocalCollision_fixed_pairs :=
         rawDynamicTruthNativeLocalCollision_fixedPairs
           M context lowerPi lowerSigma residual;
       rawDynamicTruthLocalCollision_binder_inputs := _;
       rawDynamicTruthLocalCollision_sigmaEx_direct_trace := _;
       rawDynamicTruthLocalCollision_sigmaAll_direct_trace := _;
       rawDynamicTruthLocalCollision_sigmaEx_cross_root :=
         rawDynamicTruthNativeLocalCollision_sigmaExCrossRoot
           M context lowerPi lowerSigma residual;
       rawDynamicTruthLocalCollision_sigmaAll_cross_root :=
         rawDynamicTruthNativeLocalCollision_sigmaAllCrossRoot
           M context lowerPi lowerSigma residual;
       rawDynamicTruthLocalCollision_mixed_replay_root :=
         rawDynamicTruthNativeLocalCollision_mixedReplayRoot
           M context lowerPi lowerSigma residual;
       rawDynamicTruthLocalCollision_mixed_cell_roots := hmixed |}.
  - intro cell. split.
    + exact (rawDynamicTruthNativeLocalCollision_binderProjections
        M context lowerPi lowerSigma residual cell).
    + exact (hbinderPrincipals cell).
  - constructor.
    exact (rawDynamicTruthNativeLocalCollision_sigmaExTrace
      M context lowerPi lowerSigma residual).
  - constructor.
    exact (rawDynamicTruthNativeLocalCollision_sigmaAllTrace
      M context lowerPi lowerSigma residual).
Qed.

(** ------------------------------------------------------------------
    Honest extension from a witnessed PA tail to temporary assumptions. *)

Lemma raw_dynamicTruthLocalRootAt_adequateCons : forall
    (M : RawPAModel), RawPASatisfies M -> forall context head target,
  RawCodedFormulaAtomicallyAdequate M head ->
  RawContextListRealizable M context ->
  RawDynamicTruthLocalRootAt M context target ->
  RawDynamicTruthLocalRootAt M (rawListNode M head context) target.
Proof.
  intros M hPA context head target hhead hcontext [root hroot].
  destruct (raw_codedPALocalProof_adequateConsTransplant
    M hPA context head target root hhead hcontext hroot) as
    [newRoot hnewRoot].
  now exists newRoot.
Qed.

Lemma raw_dynamicTruthBinderOffDiagonalInputs_adequateCons : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      context head cell lowerPiApplication lowerSigmaApplication,
  RawCodedFormulaAtomicallyAdequate M head ->
  RawContextListRealizable M context ->
  RawDynamicTruthBinderOffDiagonalProofInputsAt M context cell
    lowerPiApplication lowerSigmaApplication ->
  RawDynamicTruthBinderOffDiagonalProofInputsAt M
    (rawListNode M head context) cell
    lowerPiApplication lowerSigmaApplication.
Proof.
  intros M hPA context head cell lowerPi lowerSigma hhead hcontext
    ((sigmaProjectionRoot & piProjectionRoot &
        hsigmaProjection & hpiProjection) &
      (principalRoot & hprincipal)).
  destruct (raw_codedPALocalProof_adequateConsTransplant M hPA
    context head
    (rawFormulaImpCode M
      (rawDynamicTruthBinderOffDiagonalSigmaBranchCode M cell lowerPi)
      (rawDynamicTruthBinderSigmaPrincipalCode M cell))
    sigmaProjectionRoot hhead hcontext hsigmaProjection) as
    [newSigmaRoot hnewSigma].
  destruct (raw_codedPALocalProof_adequateConsTransplant M hPA
    context head
    (rawFormulaImpCode M
      (rawDynamicTruthBinderOffDiagonalPiBranchCode M cell lowerSigma)
      (rawDynamicTruthBinderPiPrincipalCode M cell))
    piProjectionRoot hhead hcontext hpiProjection) as
    [newPiRoot hnewPi].
  destruct (raw_codedPALocalProof_adequateConsTransplant M hPA
    context head (rawDynamicTruthBinderPrincipalCollisionCode M cell)
    principalRoot hhead hcontext hprincipal) as
    [newPrincipalRoot hnewPrincipal].
  split.
  - exists newSigmaRoot, newPiRoot. split; assumption.
  - now exists newPrincipalRoot.
Qed.

(** Transplant the complete matrix input record through one adequate context
    head.  The caller supplies the self-shift of the resulting context; all
    proof roots are rebuilt by the represented context-insertion compiler. *)
Theorem raw_dynamicTruthLocalCollisionMatrixInputs_adequateCons : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      context head lowerPiApplication lowerSigmaApplication,
  RawCodedFormulaAtomicallyAdequate M head ->
  RawContextShift M (rawListNode M head context)
    (rawListNode M head context) ->
  RawDynamicTruthLocalCollisionMatrixInputs M context
    lowerPiApplication lowerSigmaApplication ->
  RawDynamicTruthLocalCollisionMatrixInputs M
    (rawListNode M head context)
    lowerPiApplication lowerSigmaApplication.
Proof.
  intros M hPA context head lowerPi lowerSigma hhead hnewShift inputs.
  pose proof (rawDynamicTruthLocalCollision_context_realizable
    M context lowerPi lowerSigma inputs) as hcontext.
  assert (liftRoot : forall target,
      RawDynamicTruthLocalRootAt M context target ->
      RawDynamicTruthLocalRootAt M (rawListNode M head context) target).
  { intros target hroot.
    exact (raw_dynamicTruthLocalRootAt_adequateCons
      M hPA context head target hhead hcontext hroot). }
  assert (fixedPairs : RawDynamicTruthLocalFixedPairFamily M
      (rawListNode M head context) lowerPi lowerSigma).
  { intros sigmaBranch piBranch hcell.
    apply liftRoot.
    exact (rawDynamicTruthLocalCollision_fixed_pairs
      M context lowerPi lowerSigma inputs sigmaBranch piBranch hcell). }
  assert (binderInputs : forall cell,
      RawDynamicTruthBinderOffDiagonalProofInputsAt M
        (rawListNode M head context) cell lowerPi lowerSigma).
  { intro cell.
    exact (raw_dynamicTruthBinderOffDiagonalInputs_adequateCons
      M hPA context head cell lowerPi lowerSigma hhead hcontext
      (rawDynamicTruthLocalCollision_binder_inputs
        M context lowerPi lowerSigma inputs cell)). }
  assert (mixedCells : forall cell,
      RawDynamicTruthLocalRootAt M (rawListNode M head context)
        (rawDynamicTruthMixedQFCellCode M cell lowerPi lowerSigma)).
  { intro cell. apply liftRoot.
    exact (rawDynamicTruthLocalCollision_mixed_cell_roots
      M context lowerPi lowerSigma inputs cell). }
  refine
    {| rawDynamicTruthLocalCollision_context_realizable :=
         raw_contextList_cons_realizable M hPA context head hcontext;
       rawDynamicTruthLocalCollision_lowerPi_adequate :=
         rawDynamicTruthLocalCollision_lowerPi_adequate
           M context lowerPi lowerSigma inputs;
       rawDynamicTruthLocalCollision_lowerSigma_adequate :=
         rawDynamicTruthLocalCollision_lowerSigma_adequate
           M context lowerPi lowerSigma inputs;
       rawDynamicTruthLocalCollision_context_self_shift := hnewShift;
       rawDynamicTruthLocalCollision_qf_root :=
         liftRoot _ (rawDynamicTruthLocalCollision_qf_root
           M context lowerPi lowerSigma inputs);
       rawDynamicTruthLocalCollision_predecessor_root :=
         liftRoot _ (rawDynamicTruthLocalCollision_predecessor_root
           M context lowerPi lowerSigma inputs);
       rawDynamicTruthLocalCollision_impFalse_root :=
         liftRoot _ (rawDynamicTruthLocalCollision_impFalse_root
           M context lowerPi lowerSigma inputs);
       rawDynamicTruthLocalCollision_impTrue_root :=
         liftRoot _ (rawDynamicTruthLocalCollision_impTrue_root
           M context lowerPi lowerSigma inputs);
       rawDynamicTruthLocalCollision_and_root :=
         liftRoot _ (rawDynamicTruthLocalCollision_and_root
           M context lowerPi lowerSigma inputs);
       rawDynamicTruthLocalCollision_or_root :=
         liftRoot _ (rawDynamicTruthLocalCollision_or_root
           M context lowerPi lowerSigma inputs);
       rawDynamicTruthLocalCollision_fixed_pairs := fixedPairs;
       rawDynamicTruthLocalCollision_binder_inputs := binderInputs;
       rawDynamicTruthLocalCollision_sigmaEx_direct_trace :=
         rawDynamicTruthLocalCollision_sigmaEx_direct_trace
           M context lowerPi lowerSigma inputs;
       rawDynamicTruthLocalCollision_sigmaAll_direct_trace :=
         rawDynamicTruthLocalCollision_sigmaAll_direct_trace
           M context lowerPi lowerSigma inputs;
       rawDynamicTruthLocalCollision_sigmaEx_cross_root :=
         liftRoot _ (rawDynamicTruthLocalCollision_sigmaEx_cross_root
           M context lowerPi lowerSigma inputs);
       rawDynamicTruthLocalCollision_sigmaAll_cross_root :=
         liftRoot _ (rawDynamicTruthLocalCollision_sigmaAll_cross_root
           M context lowerPi lowerSigma inputs);
       rawDynamicTruthLocalCollision_mixed_replay_root :=
         liftRoot _ (rawDynamicTruthLocalCollision_mixed_replay_root
           M context lowerPi lowerSigma inputs);
       rawDynamicTruthLocalCollision_mixed_cell_roots := mixedCells |}.
Qed.

(** Three successive applications move a matrix compiled over a witnessed PA
    tail into the exact exclusive context.  The three adequacy and self-shift
    facts are the complete context-extension boundary; there is no equality
    or erasure premise. *)
Theorem raw_dynamicTruthLocalCollisionMatrixInputs_on_exclusive_context :
    forall (M : RawPAModel), RawPASatisfies M -> forall
      baseContext sigmaDomain piDomain sigmaEvidence piEvidence
      lowerPiApplication lowerSigmaApplication,
  RawDynamicTruthLocalCollisionMatrixInputs M baseContext
    lowerPiApplication lowerSigmaApplication ->
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
  RawDynamicTruthLocalCollisionMatrixInputs M
    (rawDynamicTruthNativeLocalExclusivePiContextOn M baseContext
      sigmaDomain piDomain sigmaEvidence piEvidence)
    lowerPiApplication lowerSigmaApplication.
Proof.
  intros M hPA baseContext sigmaDomain piDomain sigmaEvidence piEvidence
    lowerPi lowerSigma hbase hadmissible hsigma hpi
    hadmissibleShift hsigmaShift hpiShift.
  pose proof (raw_dynamicTruthLocalCollisionMatrixInputs_adequateCons
    M hPA baseContext
    (rawDynamicTruthLocalAdmissibleCode M sigmaDomain piDomain)
    lowerPi lowerSigma hadmissible hadmissibleShift hbase) as hfirst.
  pose proof (raw_dynamicTruthLocalCollisionMatrixInputs_adequateCons
    M hPA
    (rawDynamicTruthNativeLocalAdmissibleContextOn M baseContext
      sigmaDomain piDomain)
    sigmaEvidence lowerPi lowerSigma hsigma hsigmaShift hfirst) as hsecond.
  exact (raw_dynamicTruthLocalCollisionMatrixInputs_adequateCons
    M hPA
    (rawDynamicTruthNativeLocalExclusiveSigmaContextOn M baseContext
      sigmaDomain piDomain sigmaEvidence)
    piEvidence lowerPi lowerSigma hpi hpiShift hsecond).
Qed.

(** ------------------------------------------------------------------
    Complete witnessed-tail matrix compilation. *)

Record RawDynamicTruthNativeLocalExclusiveMatrixResourcesAt
    (M : RawPAModel)
    (context sigmaRowDomain piRowDomain
      lowerPiApplication lowerSigmaApplication : M) : Type := {
  rawDynamicTruthNativeLocalExclusive_sigmaProjection :
    RawDynamicTruthSigmaSuccessorRowBranchDisjunctionCompilationInputs
      M context sigmaRowDomain lowerPiApplication;
  rawDynamicTruthNativeLocalExclusive_piProjection :
    RawDynamicTruthPiSuccessorRowBranchDisjunctionCompilationInputs
      M context piRowDomain lowerSigmaApplication;
  rawDynamicTruthNativeLocalExclusive_collisionInputs :
    RawDynamicTruthLocalCollisionMatrixInputs M context
      lowerPiApplication lowerSigmaApplication;
  rawDynamicTruthNativeLocalExclusive_matrixResources :
    RawFiniteDisjunctionMatrixResources M
      (rawDynamicTruthLocalSigmaBranches M lowerPiApplication)
      (rawDynamicTruthLocalPiBranches M lowerSigmaApplication)
      context
}.

Arguments RawDynamicTruthNativeLocalExclusiveMatrixResourcesAt
  M context sigmaRowDomain piRowDomain
  lowerPiApplication lowerSigmaApplication : clear implicits.

(** This is the first-class witnessed-tail endpoint of the synchronized
    helper work.  The helper batch is compiled over [baseContext], then the
    complete collision record is transported through the three temporary
    assumptions.  Row projection traces and finite-case resources already
    designated for the final context complete the returned matrix package. *)
Theorem
    raw_dynamicTruthNativeLocalExclusiveMatrixResourcesAt_of_40_helpers :
    forall (M : RawPAModel) (hPA : RawPASatisfies M)
      translation witnessList baseContext helperRoots
      sigmaDomain piDomain sigmaEvidence piEvidence
      sigmaRowDomain piRowDomain lowerPiApplication lowerSigmaApplication,
  RawCodedTemplatePAAgreement M translation ->
  RawCodedPAAxiomWitnessContext M witnessList baseContext ->
  RawFixedPAHelperBatchLocalProofs M translation baseContext
    rawDynamicTruthReadyAndAllMixedQFPAHelpers helperRoots ->
  RawDynamicTruthNativeLocalCollisionResidualInputsAt M baseContext
    lowerPiApplication lowerSigmaApplication ->
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
  RawDynamicTruthNativeLocalExclusiveMatrixResourcesAt M
    (rawDynamicTruthNativeLocalExclusivePiContextOn M baseContext
      sigmaDomain piDomain sigmaEvidence piEvidence)
    sigmaRowDomain piRowDomain lowerPiApplication lowerSigmaApplication.
Proof.
  intros M hPA translation witnessList baseContext helperRoots
    sigmaDomain piDomain sigmaEvidence piEvidence
    sigmaRowDomain piRowDomain lowerPi lowerSigma
    hagreement hwitness hhelpers residual
    hadmissible hsigma hpi hadmissibleShift hsigmaShift hpiShift
    sigmaProjection piProjection matrixResources.
  pose proof
    (raw_dynamicTruthNativeLocalCollisionMatrixInputs_of_40_helpers
      M hPA translation witnessList baseContext helperRoots
      lowerPi lowerSigma hagreement hwitness hhelpers residual)
    as hbaseInputs.
  pose proof
    (raw_dynamicTruthLocalCollisionMatrixInputs_on_exclusive_context
      M hPA baseContext sigmaDomain piDomain sigmaEvidence piEvidence
      lowerPi lowerSigma hbaseInputs hadmissible hsigma hpi
      hadmissibleShift hsigmaShift hpiShift)
    as hexclusiveInputs.
  refine
    {| rawDynamicTruthNativeLocalExclusive_sigmaProjection :=
         sigmaProjection;
       rawDynamicTruthNativeLocalExclusive_piProjection := piProjection;
       rawDynamicTruthNativeLocalExclusive_collisionInputs :=
         hexclusiveInputs;
       rawDynamicTruthNativeLocalExclusive_matrixResources :=
         matrixResources |}.
Qed.

Theorem raw_dynamicTruthNativeLocalExclusiveRootOn_of_rows_and_matrix :
    forall (M : RawPAModel) (hPA : RawPASatisfies M)
      baseContext sigmaDomain piDomain sigmaEvidence piEvidence
      sigmaRowDomain piRowDomain lowerPiApplication lowerSigmaApplication,
  RawDynamicTruthNativeLocalExclusiveMatrixResourcesAt M
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
    sigmaRowDomain piRowDomain lowerPi lowerSigma resources
    (sigmaRowRoot & piRowRoot & hsigmaRow & hpiRow).
  set (context :=
    rawDynamicTruthNativeLocalExclusivePiContextOn M baseContext
      sigmaDomain piDomain sigmaEvidence piEvidence).
  pose proof
    (raw_codedPALocalProofOf_dynamicTruthSigmaSuccessorRowBranchDisjunction
      M hPA context sigmaRowDomain lowerPi
      (rawDynamicTruthNativeLocalExclusive_sigmaProjection
        M context sigmaRowDomain piRowDomain lowerPi lowerSigma resources)
      sigmaRowRoot hsigmaRow) as hsigmaOr7.
  pose proof
    (raw_codedPALocalProofOf_dynamicTruthPiSuccessorRowBranchDisjunction
      M hPA context piRowDomain lowerSigma
      (rawDynamicTruthNativeLocalExclusive_piProjection
        M context sigmaRowDomain piRowDomain lowerPi lowerSigma resources)
      piRowRoot hpiRow) as hpiOr6.
  destruct
    (raw_codedPALocalProofOf_dynamicTruthLocalCollisionMatrix_bottom
      M hPA context lowerPi lowerSigma
      (rawDynamicTruthSigmaSuccessorRowBranchDisjunctionRoot
        M hPA context sigmaRowDomain lowerPi
        (rawDynamicTruthNativeLocalExclusive_sigmaProjection
          M context sigmaRowDomain piRowDomain lowerPi lowerSigma resources)
        sigmaRowRoot)
      (rawDynamicTruthPiSuccessorRowBranchDisjunctionRoot
        M hPA context piRowDomain lowerSigma
        (rawDynamicTruthNativeLocalExclusive_piProjection
          M context sigmaRowDomain piRowDomain lowerPi lowerSigma resources)
        piRowRoot)
      (rawDynamicTruthNativeLocalExclusive_collisionInputs
        M context sigmaRowDomain piRowDomain lowerPi lowerSigma resources)
      (rawDynamicTruthNativeLocalExclusive_matrixResources
        M context sigmaRowDomain piRowDomain lowerPi lowerSigma resources)
      hsigmaOr7 hpiOr6) as [bottomRoot hbottom].
  exists bottomRoot. exact hbottom.
Qed.

(** A trace-indexed adapter names precisely the point at which the global
    evidence eliminator hands control to the completely compiled matrix. *)
Theorem raw_dynamicTruthNativeLocalExclusiveRootOn_of_interface :
    forall (M : RawPAModel) (hPA : RawPASatisfies M),
  RawDynamicTruthNativeGlobalEvidenceRowRootInterface M ->
  forall (tail : nat -> M) predecessorLevel
      inputGlobalSigma inputGlobalPi
      sigmaDomain piDomain sigmaEvidence piEvidence baseContext
      sigmaRowDomain piRowDomain lowerPiApplication lowerSigmaApplication,
  RawDynamicTruthNativeLocalProofTraceAt M tail predecessorLevel
    inputGlobalSigma inputGlobalPi sigmaDomain piDomain
    sigmaEvidence piEvidence ->
  RawDynamicTruthNativeLocalExclusiveMatrixResourcesAt M
    (rawDynamicTruthNativeLocalExclusivePiContextOn M baseContext
      sigmaDomain piDomain sigmaEvidence piEvidence)
    sigmaRowDomain piRowDomain lowerPiApplication lowerSigmaApplication ->
  RawDynamicTruthNativeLocalExclusiveRootOn M baseContext
    sigmaDomain piDomain sigmaEvidence piEvidence.
Proof.
  intros M hPA hrows tail predecessorLevel inputGlobalSigma inputGlobalPi
    sigmaDomain piDomain sigmaEvidence piEvidence baseContext
    sigmaRowDomain piRowDomain lowerPi lowerSigma htrace hresources.
  apply (raw_dynamicTruthNativeLocalExclusiveRootOn_of_rows_and_matrix
    M hPA baseContext sigmaDomain piDomain sigmaEvidence piEvidence
    sigmaRowDomain piRowDomain lowerPi lowerSigma hresources).
  exact (hrows tail predecessorLevel inputGlobalSigma inputGlobalPi
    sigmaDomain piDomain sigmaEvidence piEvidence baseContext
    sigmaRowDomain piRowDomain lowerPi lowerSigma htrace).
Qed.

(** ------------------------------------------------------------------
    The honest witnessed-tail leaf bundle and literal-tail adapter. *)

Definition RawDynamicTruthNativeLocalLeafRootsOn
    (M : RawPAModel)
    (baseContext sigmaDomain piDomain sigmaEvidence piEvidence : M)
    : Prop :=
  RawDynamicTruthNativeLocalDecisionRootOn M baseContext
    sigmaDomain piDomain sigmaEvidence piEvidence /\
  RawDynamicTruthNativeLocalExclusiveRootOn M baseContext
    sigmaDomain piDomain sigmaEvidence piEvidence.

Arguments RawDynamicTruthNativeLocalLeafRootsOn
  M baseContext sigmaDomain piDomain sigmaEvidence piEvidence
  : clear implicits.

Theorem raw_dynamicTruthNativeLocalLeafRootsOn_of_interfaces :
    forall (M : RawPAModel) (hPA : RawPASatisfies M),
  RawDynamicTruthNativeLocalDecisionEvidenceRootInterface M ->
  RawDynamicTruthNativeGlobalEvidenceRowRootInterface M ->
  forall (tail : nat -> M) predecessorLevel
      inputGlobalSigma inputGlobalPi
      sigmaDomain piDomain sigmaEvidence piEvidence baseContext
      sigmaRowDomain piRowDomain lowerPiApplication lowerSigmaApplication,
  RawDynamicTruthNativeLocalProofTraceAt M tail predecessorLevel
    inputGlobalSigma inputGlobalPi sigmaDomain piDomain
    sigmaEvidence piEvidence ->
  RawDynamicTruthNativeLocalExclusiveMatrixResourcesAt M
    (rawDynamicTruthNativeLocalExclusivePiContextOn M baseContext
      sigmaDomain piDomain sigmaEvidence piEvidence)
    sigmaRowDomain piRowDomain lowerPiApplication lowerSigmaApplication ->
  RawDynamicTruthNativeLocalLeafRootsOn M baseContext
    sigmaDomain piDomain sigmaEvidence piEvidence.
Proof.
  intros M hPA hdecision hrows tail predecessorLevel
    inputGlobalSigma inputGlobalPi sigmaDomain piDomain
    sigmaEvidence piEvidence baseContext sigmaRowDomain piRowDomain
    lowerPi lowerSigma htrace hresources.
  split.
  - exact (hdecision tail predecessorLevel inputGlobalSigma inputGlobalPi
      sigmaDomain piDomain sigmaEvidence piEvidence baseContext htrace).
  - exact (raw_dynamicTruthNativeLocalExclusiveRootOn_of_interface
      M hPA hrows tail predecessorLevel inputGlobalSigma inputGlobalPi
      sigmaDomain piDomain sigmaEvidence piEvidence baseContext
      sigmaRowDomain piRowDomain lowerPi lowerSigma htrace hresources).
Qed.

(** No context erasure occurs here: at the literal empty tail the generalized
    contexts reduce definitionally to the contexts of the earlier shell. *)
Lemma raw_dynamicTruthNativeLocalLeafRootsAt_of_empty_tail : forall
    (M : RawPAModel) sigmaDomain piDomain sigmaEvidence piEvidence,
  RawDynamicTruthNativeLocalLeafRootsOn M (raw_zero M)
    sigmaDomain piDomain sigmaEvidence piEvidence ->
  RawDynamicTruthNativeLocalLeafRootsAt M
    sigmaDomain piDomain sigmaEvidence piEvidence.
Proof.
  intros M sigmaDomain piDomain sigmaEvidence piEvidence hroots.
  exact hroots.
Qed.

(** The original compiler follows only when callers provide the two missing
    interfaces and matrix resources at the *literal* empty tail.  Stating
    this adapter explicitly prevents a witnessed PA tail from being silently
    identified with zero. *)
Definition RawDynamicTruthNativeLocalEmptyTailMatrixResourceCompiler
    (M : RawPAModel) : Type :=
  forall (tail : nat -> M) predecessorLevel
      inputGlobalSigma inputGlobalPi
      sigmaDomain piDomain sigmaEvidence piEvidence,
    RawDynamicTruthNativeLocalProofTraceAt M tail predecessorLevel
      inputGlobalSigma inputGlobalPi sigmaDomain piDomain
      sigmaEvidence piEvidence ->
    { sigmaRowDomain : M &
      { piRowDomain : M &
        { lowerPiApplication : M &
          { lowerSigmaApplication : M &
            RawDynamicTruthNativeLocalExclusiveMatrixResourcesAt M
              (rawDynamicTruthNativeLocalExclusivePiContextOn M
                (raw_zero M) sigmaDomain piDomain
                sigmaEvidence piEvidence)
              sigmaRowDomain piRowDomain
              lowerPiApplication lowerSigmaApplication }}}}.

Arguments RawDynamicTruthNativeLocalEmptyTailMatrixResourceCompiler M
  : clear implicits.

Theorem raw_dynamicTruthNativeLocalLeafRootCompiler_of_interfaces :
    forall (M : RawPAModel), RawPASatisfies M ->
  RawDynamicTruthNativeLocalDecisionEvidenceRootInterface M ->
  RawDynamicTruthNativeGlobalEvidenceRowRootInterface M ->
  RawDynamicTruthNativeLocalEmptyTailMatrixResourceCompiler M ->
  RawDynamicTruthNativeLocalLeafRootCompiler M.
Proof.
  intros M hPA hdecision hrows hmatrix tail predecessorLevel
    inputGlobalSigma inputGlobalPi sigmaDomain piDomain
    sigmaEvidence piEvidence htrace.
  destruct (hmatrix tail predecessorLevel inputGlobalSigma inputGlobalPi
    sigmaDomain piDomain sigmaEvidence piEvidence htrace) as
    (sigmaRowDomain & piRowDomain & lowerPi & lowerSigma & hresources).
  apply raw_dynamicTruthNativeLocalLeafRootsAt_of_empty_tail.
  exact (raw_dynamicTruthNativeLocalLeafRootsOn_of_interfaces
    M hPA hdecision hrows tail predecessorLevel
    inputGlobalSigma inputGlobalPi sigmaDomain piDomain
    sigmaEvidence piEvidence (raw_zero M)
    sigmaRowDomain piRowDomain lowerPi lowerSigma htrace hresources).
Qed.

End PABoundedRawCodedDynamicTruthNativeLocalLeafRootCompiler.
