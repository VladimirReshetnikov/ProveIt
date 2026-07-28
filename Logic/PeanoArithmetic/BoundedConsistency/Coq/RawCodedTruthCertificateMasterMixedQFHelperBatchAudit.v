(** Audit of the nine fixed mixed-QF helpers and the combined 38-root batch. *)

From Stdlib Require Import List.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA.
From BoundedPAConsistency Require Import
  RawCodedTemplateProofCompiler
  RawCodedTemplatePAEmbedding
  RawCodedTruthCertificateMasterFixedHelperBatchExtension
  RawCodedTruthCertificateMasterBinderPrincipalHelperBatch
  RawCodedDynamicTruthMixedQFBranchExclusivity
  RawCodedTruthCertificateMasterMixedQFHelperBatch.

Import ListNotations.

Module PABoundedRawCodedTruthCertificateMasterMixedQFHelperBatchAudit.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedTemplatePAEmbedding.
Import PABoundedRawCodedTruthCertificateMasterFixedHelperBatchExtension.
Import PABoundedRawCodedTruthCertificateMasterBinderPrincipalHelperBatch.
Import PABoundedRawCodedDynamicTruthMixedQFBranchExclusivity.
Import PABoundedRawCodedTruthCertificateMasterMixedQFHelperBatch.

(** Public construction and exact counts. *)
Check rawDynamicTruthMixedQFFixedPAHelper.
Check rawDynamicTruthMixedQFFixedPAHelpers.
Check rawDynamicTruthMixedQFFixedPAHelpers_length.
Check rawDynamicTruthMixedQFFixedPAHelpers_order.
Check rawDynamicTruthReadyBinderPrincipalAndMixedQFPAHelpers.
Check rawDynamicTruthReadyBinderPrincipalAndMixedQFPAHelpers_length.
Check rawDynamicTruthReadyBinderPrincipalAndMixedQFPAHelpers_order.

Goal length rawDynamicTruthMixedQFFixedPAHelpers = 9.
Proof. exact rawDynamicTruthMixedQFFixedPAHelpers_length. Qed.

Goal length rawDynamicTruthReadyBinderPrincipalAndMixedQFPAHelpers = 38.
Proof.
  exact rawDynamicTruthReadyBinderPrincipalAndMixedQFPAHelpers_length.
Qed.

(** The suffix order is literal and contains exactly the nine public fixed
    cells. *)
Goal rawDynamicTruthMixedQFFixedPAHelpers =
  [ rawDynamicTruthMixedQFFixedPAHelper DTMQFSigmaQFPiImp;
    rawDynamicTruthMixedQFFixedPAHelper DTMQFSigmaQFPiAnd;
    rawDynamicTruthMixedQFFixedPAHelper DTMQFSigmaQFPiOr;
    rawDynamicTruthMixedQFFixedPAHelper DTMQFSigmaQFPiAll;
    rawDynamicTruthMixedQFFixedPAHelper DTMQFSigmaImpFalseLeftPiQF;
    rawDynamicTruthMixedQFFixedPAHelper DTMQFSigmaImpTrueRightPiQF;
    rawDynamicTruthMixedQFFixedPAHelper DTMQFSigmaAndPiQF;
    rawDynamicTruthMixedQFFixedPAHelper DTMQFSigmaOrPiQF;
    rawDynamicTruthMixedQFFixedPAHelper DTMQFSigmaExPiQF ].
Proof. exact rawDynamicTruthMixedQFFixedPAHelpers_order. Qed.

Goal map rawFixedPAHelperFormula rawDynamicTruthMixedQFFixedPAHelpers =
  map (fun cell => dynamicTruthMixedQFCellFormula cell pBot pBot)
    dynamicTruthMixedQFFixedCodeCells.
Proof. reflexivity. Qed.

(** The two opaque quantified cells are outside this suffix. *)
Goal ~ In DTMQFSigmaQFPiEx dynamicTruthMixedQFFixedCodeCells.
Proof. cbn; intuition congruence. Qed.

Goal ~ In DTMQFSigmaAllPiQF dynamicTruthMixedQFFixedCodeCells.
Proof. cbn; intuition congruence. Qed.

(** Generic and list-level native target alignment. *)
Check rawDynamicTruthMixedQFFixedPAHelperTarget_eq_native.
Check rawDynamicTruthMixedQFFixedNativeTargetCodes.
Check rawDynamicTruthMixedQFFixedPAHelperTargets_eq_native.
Check
  rawDynamicTruthReadyBinderPrincipalAndMixedQFPAHelperTargets_eq_quoted.
Check
  rawDynamicTruthReadyBinderPrincipalAndMixedQFPAHelperTargets_split_native.

(** Exercise the arbitrary-carrier equation separately at each of the nine
    positions. *)
Goal forall (M : RawPAModel), RawPASatisfies M ->
  forall (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall lowerPi lowerSigma,
  rawFixedPAHelperTranslatedTargetCode M translation
    (rawDynamicTruthMixedQFFixedPAHelper DTMQFSigmaQFPiImp) =
  rawDynamicTruthMixedQFCellCode M DTMQFSigmaQFPiImp
    lowerPi lowerSigma.
Proof.
  intros M hPA translation hagreement lowerPi lowerSigma.
  apply rawDynamicTruthMixedQFFixedPAHelperTarget_eq_native;
    [exact hPA | exact hagreement | cbn; intuition].
Qed.

Goal forall (M : RawPAModel), RawPASatisfies M ->
  forall (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall lowerPi lowerSigma,
  rawFixedPAHelperTranslatedTargetCode M translation
    (rawDynamicTruthMixedQFFixedPAHelper DTMQFSigmaQFPiAnd) =
  rawDynamicTruthMixedQFCellCode M DTMQFSigmaQFPiAnd lowerPi lowerSigma.
Proof.
  intros M hPA translation hagreement lowerPi lowerSigma.
  apply rawDynamicTruthMixedQFFixedPAHelperTarget_eq_native;
    [exact hPA | exact hagreement | cbn; intuition].
Qed.

Goal forall (M : RawPAModel), RawPASatisfies M ->
  forall (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall lowerPi lowerSigma,
  rawFixedPAHelperTranslatedTargetCode M translation
    (rawDynamicTruthMixedQFFixedPAHelper DTMQFSigmaQFPiOr) =
  rawDynamicTruthMixedQFCellCode M DTMQFSigmaQFPiOr lowerPi lowerSigma.
Proof.
  intros M hPA translation hagreement lowerPi lowerSigma.
  apply rawDynamicTruthMixedQFFixedPAHelperTarget_eq_native;
    [exact hPA | exact hagreement | cbn; intuition].
Qed.

Goal forall (M : RawPAModel), RawPASatisfies M ->
  forall (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall lowerPi lowerSigma,
  rawFixedPAHelperTranslatedTargetCode M translation
    (rawDynamicTruthMixedQFFixedPAHelper DTMQFSigmaQFPiAll) =
  rawDynamicTruthMixedQFCellCode M DTMQFSigmaQFPiAll lowerPi lowerSigma.
Proof.
  intros M hPA translation hagreement lowerPi lowerSigma.
  apply rawDynamicTruthMixedQFFixedPAHelperTarget_eq_native;
    [exact hPA | exact hagreement | cbn; intuition].
Qed.

Goal forall (M : RawPAModel), RawPASatisfies M ->
  forall (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall lowerPi lowerSigma,
  rawFixedPAHelperTranslatedTargetCode M translation
    (rawDynamicTruthMixedQFFixedPAHelper
      DTMQFSigmaImpFalseLeftPiQF) =
  rawDynamicTruthMixedQFCellCode M DTMQFSigmaImpFalseLeftPiQF
    lowerPi lowerSigma.
Proof.
  intros M hPA translation hagreement lowerPi lowerSigma.
  apply rawDynamicTruthMixedQFFixedPAHelperTarget_eq_native;
    [exact hPA | exact hagreement | cbn; intuition].
Qed.

Goal forall (M : RawPAModel), RawPASatisfies M ->
  forall (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall lowerPi lowerSigma,
  rawFixedPAHelperTranslatedTargetCode M translation
    (rawDynamicTruthMixedQFFixedPAHelper
      DTMQFSigmaImpTrueRightPiQF) =
  rawDynamicTruthMixedQFCellCode M DTMQFSigmaImpTrueRightPiQF
    lowerPi lowerSigma.
Proof.
  intros M hPA translation hagreement lowerPi lowerSigma.
  apply rawDynamicTruthMixedQFFixedPAHelperTarget_eq_native;
    [exact hPA | exact hagreement | cbn; intuition].
Qed.

Goal forall (M : RawPAModel), RawPASatisfies M ->
  forall (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall lowerPi lowerSigma,
  rawFixedPAHelperTranslatedTargetCode M translation
    (rawDynamicTruthMixedQFFixedPAHelper DTMQFSigmaAndPiQF) =
  rawDynamicTruthMixedQFCellCode M DTMQFSigmaAndPiQF lowerPi lowerSigma.
Proof.
  intros M hPA translation hagreement lowerPi lowerSigma.
  apply rawDynamicTruthMixedQFFixedPAHelperTarget_eq_native;
    [exact hPA | exact hagreement | cbn; intuition].
Qed.

Goal forall (M : RawPAModel), RawPASatisfies M ->
  forall (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall lowerPi lowerSigma,
  rawFixedPAHelperTranslatedTargetCode M translation
    (rawDynamicTruthMixedQFFixedPAHelper DTMQFSigmaOrPiQF) =
  rawDynamicTruthMixedQFCellCode M DTMQFSigmaOrPiQF lowerPi lowerSigma.
Proof.
  intros M hPA translation hagreement lowerPi lowerSigma.
  apply rawDynamicTruthMixedQFFixedPAHelperTarget_eq_native;
    [exact hPA | exact hagreement | cbn; intuition].
Qed.

Goal forall (M : RawPAModel), RawPASatisfies M ->
  forall (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall lowerPi lowerSigma,
  rawFixedPAHelperTranslatedTargetCode M translation
    (rawDynamicTruthMixedQFFixedPAHelper DTMQFSigmaExPiQF) =
  rawDynamicTruthMixedQFCellCode M DTMQFSigmaExPiQF lowerPi lowerSigma.
Proof.
  intros M hPA translation hagreement lowerPi lowerSigma.
  apply rawDynamicTruthMixedQFFixedPAHelperTarget_eq_native;
    [exact hPA | exact hagreement | cbn; intuition].
Qed.

(** One literal common context contains the six master roots and all
    thirty-eight ordered helper roots. *)
Check
  raw_sixFieldMasterCommonContextProofsWithReadyBinderPrincipalAndMixedQFHelpers.

Print Assumptions rawDynamicTruthMixedQFFixedPAHelpers_length.
Print Assumptions rawDynamicTruthMixedQFFixedPAHelpers_order.
Print Assumptions rawDynamicTruthMixedQFFixedPAHelperTarget_eq_native.
Print Assumptions rawDynamicTruthMixedQFFixedPAHelperTargets_eq_native.
Print Assumptions
  rawDynamicTruthReadyBinderPrincipalAndMixedQFPAHelpers_length.
Print Assumptions
  rawDynamicTruthReadyBinderPrincipalAndMixedQFPAHelperTargets_split_native.
Print Assumptions
  raw_sixFieldMasterCommonContextProofsWithReadyBinderPrincipalAndMixedQFHelpers.

End PABoundedRawCodedTruthCertificateMasterMixedQFHelperBatchAudit.
