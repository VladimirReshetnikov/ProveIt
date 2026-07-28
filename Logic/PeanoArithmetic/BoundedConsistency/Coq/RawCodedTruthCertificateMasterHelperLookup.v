(**
  Order-preserving lookup in a synchronized fixed-helper batch.

  [RawFixedPAHelperBatchLocalProofs] relates two ordinary Rocq lists: each
  helper is paired position-for-position with a local proof root in one
  represented context.  Consumers of a large batch should not have to
  destruct all roots merely to recover one named helper.  The structural
  lemma below turns ordinary list membership into the corresponding local
  proof while retaining the literal shared context and translated target.

  This is only an elimination principle for an already constructed batch;
  it adds no helper, proof, weakening, or semantic assumption.
*)

From Stdlib Require Import List.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import HierarchyReduction.
From BoundedPAConsistency Require Import
  RawCodedTemplateProofCompiler
  RawCodedPALocalProofExistential
  RawCodedTruthCertificateMasterFixedHelperBatchExtension.

Import ListNotations.

Module PABoundedRawCodedTruthCertificateMasterHelperLookup.

Import PA.
Import PAHierarchyReduction.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedTruthCertificateMasterFixedHelperBatchExtension.

(** Recover the root paired with any named member of the helper list.  The
    proof follows the two lists together, so multiplicity and ordering remain
    exactly those of the original structural batch relation. *)
Theorem raw_fixedPAHelperBatchLocalProofs_member : forall
    (M : RawPAModel) translation context helpers roots helper,
  RawFixedPAHelperBatchLocalProofs
    M translation context helpers roots ->
  In helper helpers ->
  exists root : M,
    RawCodedPALocalProofOf M context
      (rawFixedPAHelperTranslatedTargetCode M translation helper) root.
Proof.
  intros M translation context helpers.
  induction helpers as [| head tail ih]; intros roots helper hproofs hin.
  - contradiction.
  - destruct roots as [| root rootTail].
    + contradiction.
    + cbn [RawFixedPAHelperBatchLocalProofs] in hproofs.
      destruct hproofs as [hroot htail].
      destruct hin as [<- | hin].
      * now exists root.
      * exact (ih rootTail helper htail hin).
Qed.

(** Left and right append adapters avoid repeatedly unfolding a combined
    helper batch at call sites. *)
Corollary raw_fixedPAHelperBatchLocalProofs_member_app_left : forall
    (M : RawPAModel) translation context left right roots helper,
  RawFixedPAHelperBatchLocalProofs
    M translation context (left ++ right) roots ->
  In helper left ->
  exists root : M,
    RawCodedPALocalProofOf M context
      (rawFixedPAHelperTranslatedTargetCode M translation helper) root.
Proof.
  intros M translation context left right roots helper hproofs hin.
  apply (raw_fixedPAHelperBatchLocalProofs_member
    M translation context (left ++ right) roots helper hproofs).
  apply in_or_app. now left.
Qed.

Corollary raw_fixedPAHelperBatchLocalProofs_member_app_right : forall
    (M : RawPAModel) translation context left right roots helper,
  RawFixedPAHelperBatchLocalProofs
    M translation context (left ++ right) roots ->
  In helper right ->
  exists root : M,
    RawCodedPALocalProofOf M context
      (rawFixedPAHelperTranslatedTargetCode M translation helper) root.
Proof.
  intros M translation context left right roots helper hproofs hin.
  apply (raw_fixedPAHelperBatchLocalProofs_member
    M translation context (left ++ right) roots helper hproofs).
  apply in_or_app. now right.
Qed.

End PABoundedRawCodedTruthCertificateMasterHelperLookup.
