(**
  Synchronize the eight fixed binder-principal collision proofs with the
  native collision helper family.

  The carrier-sensitive binder cells are not themselves fixed PA formulas:
  their Sigma-All or Pi-Ex branches contain opaque lower-application codes.
  Their *principal constructor collisions*, however, are fixed ordinary PA
  theorems.  The carrier projection compiler needs those theorem roots in
  exactly the same witnessed context as the current six-field master and the
  previously compiled collision helpers.

  This module packages one principal helper for every member of the explicit
  eight-cell classification and appends them to the twenty-one ready
  collision helpers.  The resulting twenty-nine-root batch does not claim
  twenty-nine completed matrix cells: its final eight entries are precisely
  the fixed principal collisions consumed after branch-to-principal
  projection.
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
  RawCodedDynamicTruthBinderOffDiagonalExclusivity.

Import ListNotations.

Module PABoundedRawCodedTruthCertificateMasterBinderPrincipalHelperBatch.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedTemplatePAEmbedding.
Import PABoundedRawCodedTruthCertificateMasterBaseBridge.
Import PABoundedRawCodedTruthCertificateMasterFixedHelperBatchExtension.
Import PABoundedRawCodedTruthCertificateMasterCollisionHelperBatch.
Import PABoundedRawCodedDynamicTruthBinderOffDiagonalExclusivity.

Definition rawDynamicTruthBinderPrincipalCollisionPAHelper
    (cell : DynamicTruthBinderOffDiagonalCell) : RawFixedPAHelper :=
  {| rawFixedPAHelperFormula :=
       dynamicTruthBinderPrincipalCollisionFormula cell;
     rawFixedPAHelperBProv :=
       PA_proves_dynamicTruthBinderPrincipalCollisionFormula cell |}.

Definition rawDynamicTruthBinderPrincipalCollisionPAHelpers
    : list RawFixedPAHelper :=
  map rawDynamicTruthBinderPrincipalCollisionPAHelper
    dynamicTruthBinderOffDiagonalCells.

Lemma rawDynamicTruthBinderPrincipalCollisionPAHelpers_length :
  length rawDynamicTruthBinderPrincipalCollisionPAHelpers = 8.
Proof. reflexivity. Qed.

(** The dependency order puts direct cell theorems first and the principal
    constructor facts needed by carrier binder projections afterward. *)
Definition rawDynamicTruthReadyAndBinderPrincipalPAHelpers
    : list RawFixedPAHelper :=
  rawDynamicTruthReadyCollisionFixedPAHelpers ++
  rawDynamicTruthBinderPrincipalCollisionPAHelpers.

Lemma rawDynamicTruthReadyAndBinderPrincipalPAHelpers_length :
  length rawDynamicTruthReadyAndBinderPrincipalPAHelpers = 29.
Proof. reflexivity. Qed.

Corollary
    rawDynamicTruthReadyAndBinderPrincipalPAHelperTargets_eq_quoted :
    forall (M : RawPAModel)
      (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  rawFixedPAHelperBatchTranslatedTargetCodes M translation
    rawDynamicTruthReadyAndBinderPrincipalPAHelpers =
  map (fun helper =>
    rawQuotedFormulaCode M (rawFixedPAHelperFormula helper))
    rawDynamicTruthReadyAndBinderPrincipalPAHelpers.
Proof.
  intros M translation hagreement.
  exact (rawFixedPAHelperBatchTranslatedTargetCodes_eq_quoted
    M translation hagreement
    rawDynamicTruthReadyAndBinderPrincipalPAHelpers).
Qed.

(** All six master roots and all twenty-nine helpers now mention one literal
    context code.  In particular, no later binder projection may accidentally
    use a principal collision certificate compiled over a different prefix. *)
Corollary
    raw_sixFieldMasterCommonContextProofsWithReadyAndBinderPrincipalHelpers :
    forall (M : RawPAModel), RawPASatisfies M ->
  forall (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall field1 field2 field3 field4 field5 finalField,
  RawSixFieldMasterCommonContextProofsOf M
    field1 field2 field3 field4 field5 finalField ->
  RawSixFieldMasterCommonContextProofsWithFixedPAHelperBatchOf
    M translation field1 field2 field3 field4 field5 finalField
    rawDynamicTruthReadyAndBinderPrincipalPAHelpers.
Proof.
  intros M hPA translation hagreement
    field1 field2 field3 field4 field5 finalField hmaster.
  exact (raw_sixFieldMasterCommonContextProofsWithFixedPAHelperBatch
    M hPA translation hagreement
    field1 field2 field3 field4 field5 finalField
    rawDynamicTruthReadyAndBinderPrincipalPAHelpers hmaster).
Qed.

End PABoundedRawCodedTruthCertificateMasterBinderPrincipalHelperBatch.
