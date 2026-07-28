(**
  Append the nine carrier-independent mixed-QF collision helpers to the
  synchronized master batch.

  The preceding batch has twenty-nine entries: twenty-one ready collision
  formulas followed by eight fixed binder-principal formulas.  Exactly nine
  mixed QF/non-QF cells have branch codes independent of both lower
  applications.  Their ordinary PA theorems can therefore be compiled as
  fixed helpers and interpreted at arbitrary carrier lower codes.

  The two remaining mixed cells, Sigma-QF/Pi-Ex and Sigma-All/Pi-QF, retain
  a genuine lower-application code.  They are deliberately absent here.
  The resulting batch has exactly thirty-eight entries and makes no claim
  about those two opaque compiler obligations.
*)

From Stdlib Require Import List.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors
  RawCodedTemplateProofCompiler
  RawCodedTemplatePAEmbedding
  RawCodedTruthCertificateMasterBaseBridge
  RawCodedTruthCertificateMasterFixedHelperBatchExtension
  RawCodedTruthCertificateMasterCollisionHelperBatch
  RawCodedTruthCertificateMasterBinderPrincipalHelperBatch
  RawCodedDynamicTruthMixedQFBranchExclusivity.

Import ListNotations.

Module PABoundedRawCodedTruthCertificateMasterMixedQFHelperBatch.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedTemplatePAEmbedding.
Import PABoundedRawCodedTruthCertificateMasterBaseBridge.
Import PABoundedRawCodedTruthCertificateMasterFixedHelperBatchExtension.
Import PABoundedRawCodedTruthCertificateMasterCollisionHelperBatch.
Import PABoundedRawCodedTruthCertificateMasterBinderPrincipalHelperBatch.
Import PABoundedRawCodedDynamicTruthMixedQFBranchExclusivity.

(** Each fixed helper uses bottom for its two metatheoretic lower formulae.
    Carrier-level irrelevance below transports this one ordinary theorem to
    every pair of carrier lower-application codes. *)
Definition rawDynamicTruthMixedQFFixedPAHelper
    (cell : DynamicTruthMixedQFCell) : RawFixedPAHelper :=
  {| rawFixedPAHelperFormula :=
       dynamicTruthMixedQFCellFormula cell pBot pBot;
     rawFixedPAHelperBProv :=
       PA_proves_dynamicTruthMixedQFCellFormula cell pBot pBot |}.

Definition rawDynamicTruthMixedQFFixedPAHelpers : list RawFixedPAHelper :=
  map rawDynamicTruthMixedQFFixedPAHelper
    dynamicTruthMixedQFFixedCodeCells.

Lemma rawDynamicTruthMixedQFFixedPAHelpers_length :
  length rawDynamicTruthMixedQFFixedPAHelpers = 9.
Proof. reflexivity. Qed.

(** This literal equality audits both order and exclusion.  In particular,
    neither lower-dependent quantified cell occurs in the helper suffix. *)
Lemma rawDynamicTruthMixedQFFixedPAHelpers_order :
  rawDynamicTruthMixedQFFixedPAHelpers =
  [ rawDynamicTruthMixedQFFixedPAHelper DTMQFSigmaQFPiImp;
    rawDynamicTruthMixedQFFixedPAHelper DTMQFSigmaQFPiAnd;
    rawDynamicTruthMixedQFFixedPAHelper DTMQFSigmaQFPiOr;
    rawDynamicTruthMixedQFFixedPAHelper DTMQFSigmaQFPiAll;
    rawDynamicTruthMixedQFFixedPAHelper DTMQFSigmaImpFalseLeftPiQF;
    rawDynamicTruthMixedQFFixedPAHelper DTMQFSigmaImpTrueRightPiQF;
    rawDynamicTruthMixedQFFixedPAHelper DTMQFSigmaAndPiQF;
    rawDynamicTruthMixedQFFixedPAHelper DTMQFSigmaOrPiQF;
    rawDynamicTruthMixedQFFixedPAHelper DTMQFSigmaExPiQF ].
Proof. reflexivity. Qed.

(** One translated helper target is literally the corresponding native cell
    code for arbitrary carrier lower inputs.  The proof first exposes the
    ordinary quotation through PA agreement, then uses the standard quoted
    specialization and finally the exact fixed-lower irrelevance theorem. *)
Lemma rawDynamicTruthMixedQFFixedPAHelperTarget_eq_native : forall
    (M : RawPAModel), RawPASatisfies M ->
  forall (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall cell,
  In cell dynamicTruthMixedQFFixedCodeCells ->
  forall lowerPiApplication lowerSigmaApplication,
  rawFixedPAHelperTranslatedTargetCode M translation
    (rawDynamicTruthMixedQFFixedPAHelper cell) =
  rawDynamicTruthMixedQFCellCode M cell
    lowerPiApplication lowerSigmaApplication.
Proof.
  intros M hPA translation hagreement cell hfixed
    lowerPiApplication lowerSigmaApplication.
  unfold rawFixedPAHelperTranslatedTargetCode,
    rawDynamicTruthMixedQFFixedPAHelper.
  cbn [rawFixedPAHelperFormula].
  rewrite (rawTemplateFormula_embedPA hagreement).
  rewrite <- (rawDynamicTruthMixedQFCellCode_eq_quoted
    M hPA cell pBot pBot).
  exact (rawDynamicTruthMixedQFCellCode_fixed_lower_irrelevant
    M cell hfixed
    (rawQuotedFormulaCode M pBot) (rawQuotedFormulaCode M pBot)
    lowerPiApplication lowerSigmaApplication).
Qed.

Definition rawDynamicTruthMixedQFFixedNativeTargetCodes
    (M : RawPAModel)
    (lowerPiApplication lowerSigmaApplication : M) : list M :=
  map (fun cell =>
    rawDynamicTruthMixedQFCellCode M cell
      lowerPiApplication lowerSigmaApplication)
    dynamicTruthMixedQFFixedCodeCells.

(** Position-for-position target alignment for all nine helpers. *)
Lemma rawDynamicTruthMixedQFFixedPAHelperTargets_eq_native : forall
    (M : RawPAModel), RawPASatisfies M ->
  forall (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall lowerPiApplication lowerSigmaApplication,
  rawFixedPAHelperBatchTranslatedTargetCodes M translation
    rawDynamicTruthMixedQFFixedPAHelpers =
  rawDynamicTruthMixedQFFixedNativeTargetCodes M
    lowerPiApplication lowerSigmaApplication.
Proof.
  intros M hPA translation hagreement
    lowerPiApplication lowerSigmaApplication.
  unfold rawFixedPAHelperBatchTranslatedTargetCodes,
    rawDynamicTruthMixedQFFixedPAHelpers,
    rawDynamicTruthMixedQFFixedNativeTargetCodes.
  rewrite map_map.
  apply map_ext_in. intros cell hcell.
  exact (rawDynamicTruthMixedQFFixedPAHelperTarget_eq_native
    M hPA translation hagreement cell hcell
    lowerPiApplication lowerSigmaApplication).
Qed.

(** Append the nine native mixed-QF helpers after the established
    twenty-nine-entry prefix. *)
Definition rawDynamicTruthReadyBinderPrincipalAndMixedQFPAHelpers
    : list RawFixedPAHelper :=
  rawDynamicTruthReadyAndBinderPrincipalPAHelpers ++
  rawDynamicTruthMixedQFFixedPAHelpers.

Lemma rawDynamicTruthReadyBinderPrincipalAndMixedQFPAHelpers_length :
  length rawDynamicTruthReadyBinderPrincipalAndMixedQFPAHelpers = 38.
Proof.
  unfold rawDynamicTruthReadyBinderPrincipalAndMixedQFPAHelpers.
  rewrite length_app,
    rawDynamicTruthReadyAndBinderPrincipalPAHelpers_length,
    rawDynamicTruthMixedQFFixedPAHelpers_length.
  reflexivity.
Qed.

Lemma rawDynamicTruthReadyBinderPrincipalAndMixedQFPAHelpers_order :
  rawDynamicTruthReadyBinderPrincipalAndMixedQFPAHelpers =
  rawDynamicTruthReadyAndBinderPrincipalPAHelpers ++
  [ rawDynamicTruthMixedQFFixedPAHelper DTMQFSigmaQFPiImp;
    rawDynamicTruthMixedQFFixedPAHelper DTMQFSigmaQFPiAnd;
    rawDynamicTruthMixedQFFixedPAHelper DTMQFSigmaQFPiOr;
    rawDynamicTruthMixedQFFixedPAHelper DTMQFSigmaQFPiAll;
    rawDynamicTruthMixedQFFixedPAHelper DTMQFSigmaImpFalseLeftPiQF;
    rawDynamicTruthMixedQFFixedPAHelper DTMQFSigmaImpTrueRightPiQF;
    rawDynamicTruthMixedQFFixedPAHelper DTMQFSigmaAndPiQF;
    rawDynamicTruthMixedQFFixedPAHelper DTMQFSigmaOrPiQF;
    rawDynamicTruthMixedQFFixedPAHelper DTMQFSigmaExPiQF ].
Proof.
  unfold rawDynamicTruthReadyBinderPrincipalAndMixedQFPAHelpers.
  rewrite rawDynamicTruthMixedQFFixedPAHelpers_order.
  reflexivity.
Qed.

(** Generic translated-target agreement for the complete 38-entry batch. *)
Corollary
    rawDynamicTruthReadyBinderPrincipalAndMixedQFPAHelperTargets_eq_quoted :
    forall (M : RawPAModel)
      (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  rawFixedPAHelperBatchTranslatedTargetCodes M translation
    rawDynamicTruthReadyBinderPrincipalAndMixedQFPAHelpers =
  map (fun helper =>
    rawQuotedFormulaCode M (rawFixedPAHelperFormula helper))
    rawDynamicTruthReadyBinderPrincipalAndMixedQFPAHelpers.
Proof.
  intros M translation hagreement.
  exact (rawFixedPAHelperBatchTranslatedTargetCodes_eq_quoted
    M translation hagreement
    rawDynamicTruthReadyBinderPrincipalAndMixedQFPAHelpers).
Qed.

(** The target list splits into the unchanged twenty-nine-entry prefix and
    the nine native mixed-QF cell codes, at arbitrary carrier lower inputs. *)
Lemma
    rawDynamicTruthReadyBinderPrincipalAndMixedQFPAHelperTargets_split_native :
    forall (M : RawPAModel), RawPASatisfies M ->
  forall (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall lowerPiApplication lowerSigmaApplication,
  rawFixedPAHelperBatchTranslatedTargetCodes M translation
    rawDynamicTruthReadyBinderPrincipalAndMixedQFPAHelpers =
  rawFixedPAHelperBatchTranslatedTargetCodes M translation
    rawDynamicTruthReadyAndBinderPrincipalPAHelpers ++
  rawDynamicTruthMixedQFFixedNativeTargetCodes M
    lowerPiApplication lowerSigmaApplication.
Proof.
  intros M hPA translation hagreement
    lowerPiApplication lowerSigmaApplication.
  unfold rawDynamicTruthReadyBinderPrincipalAndMixedQFPAHelpers,
    rawFixedPAHelperBatchTranslatedTargetCodes.
  rewrite map_app.
  fold (rawFixedPAHelperBatchTranslatedTargetCodes M translation
    rawDynamicTruthMixedQFFixedPAHelpers).
  rewrite (rawDynamicTruthMixedQFFixedPAHelperTargets_eq_native
    M hPA translation hagreement
    lowerPiApplication lowerSigmaApplication).
  reflexivity.
Qed.

(** All six master roots and all thirty-eight helper roots inhabit one
    literally shared witnessed context. *)
Corollary
    raw_sixFieldMasterCommonContextProofsWithReadyBinderPrincipalAndMixedQFHelpers :
    forall (M : RawPAModel), RawPASatisfies M ->
  forall (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall field1 field2 field3 field4 field5 finalField,
  RawSixFieldMasterCommonContextProofsOf M
    field1 field2 field3 field4 field5 finalField ->
  RawSixFieldMasterCommonContextProofsWithFixedPAHelperBatchOf
    M translation field1 field2 field3 field4 field5 finalField
    rawDynamicTruthReadyBinderPrincipalAndMixedQFPAHelpers.
Proof.
  intros M hPA translation hagreement
    field1 field2 field3 field4 field5 finalField hmaster.
  exact (raw_sixFieldMasterCommonContextProofsWithFixedPAHelperBatch
    M hPA translation hagreement
    field1 field2 field3 field4 field5 finalField
    rawDynamicTruthReadyBinderPrincipalAndMixedQFPAHelpers hmaster).
Qed.

End PABoundedRawCodedTruthCertificateMasterMixedQFHelperBatch.
