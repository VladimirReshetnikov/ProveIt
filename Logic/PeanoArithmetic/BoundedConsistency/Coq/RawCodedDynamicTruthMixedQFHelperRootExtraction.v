(**
  Recover the nine fixed mixed-QF roots from the synchronized helper batch.

  The 38-entry master batch stores helper roots position-for-position.  The
  generic lookup theorem recovers a named fixed helper, while the native
  target-alignment theorem identifies that helper with the corresponding
  carrier cell for arbitrary lower applications.  Combining those results
  gives the exact nine-root family expected by the local collision matrix.

  Two cells retain an opaque lower application and are not fixed helpers.
  The final adapter therefore accepts precisely those two same-context roots
  and returns the full eleven-cell family.  It does not manufacture either
  opaque root or change the represented context.
*)

From Stdlib Require Import List.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA.
From BoundedPAConsistency Require Import
  RawCodedTemplateProofCompiler
  RawCodedTemplatePAEmbedding
  RawCodedPALocalProofExistential
  RawCodedTruthCertificateMasterFixedHelperBatchExtension
  RawCodedTruthCertificateMasterMixedQFHelperBatch
  RawCodedTruthCertificateMasterHelperLookup
  RawCodedDynamicTruthMixedQFBranchExclusivity
  RawCodedDynamicTruthLocalCollisionMatrixAssembly.

Import ListNotations.

Module PABoundedRawCodedDynamicTruthMixedQFHelperRootExtraction.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedTemplatePAEmbedding.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedTruthCertificateMasterFixedHelperBatchExtension.
Import PABoundedRawCodedTruthCertificateMasterMixedQFHelperBatch.
Import PABoundedRawCodedTruthCertificateMasterHelperLookup.
Import PABoundedRawCodedDynamicTruthMixedQFBranchExclusivity.
Import PABoundedRawCodedDynamicTruthLocalCollisionMatrixAssembly.

Definition RawDynamicTruthMixedQFFixedCellRootsAt
    (M : RawPAModel) (context lowerPiApplication lowerSigmaApplication : M)
    : Prop :=
  forall cell : DynamicTruthMixedQFCell,
    In cell dynamicTruthMixedQFFixedCodeCells ->
    RawDynamicTruthLocalRootAt M context
      (rawDynamicTruthMixedQFCellCode M cell
        lowerPiApplication lowerSigmaApplication).

Arguments RawDynamicTruthMixedQFFixedCellRootsAt
  M context lowerPiApplication lowerSigmaApplication : clear implicits.

(** Every one of the nine fixed helpers can be selected by ordinary list
    membership.  Rewriting its translated target is safe for arbitrary
    carrier lower inputs because fixed-lower irrelevance has already been
    proved for exactly this classified cell family. *)
Theorem raw_dynamicTruthMixedQFFixedCellRootsAt_of_helper_batch : forall
    (M : RawPAModel), RawPASatisfies M ->
  forall (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall context helperRoots lowerPiApplication lowerSigmaApplication,
  RawFixedPAHelperBatchLocalProofs M translation context
    rawDynamicTruthReadyBinderPrincipalAndMixedQFPAHelpers helperRoots ->
  RawDynamicTruthMixedQFFixedCellRootsAt M context
    lowerPiApplication lowerSigmaApplication.
Proof.
  intros M hPA translation hagreement context helperRoots
    lowerPiApplication lowerSigmaApplication hhelpers cell hfixed.
  assert (hin : In (rawDynamicTruthMixedQFFixedPAHelper cell)
      rawDynamicTruthReadyBinderPrincipalAndMixedQFPAHelpers).
  {
    unfold rawDynamicTruthReadyBinderPrincipalAndMixedQFPAHelpers.
    apply in_or_app. right.
    unfold rawDynamicTruthMixedQFFixedPAHelpers.
    apply in_map. exact hfixed.
  }
  destruct (raw_fixedPAHelperBatchLocalProofs_member
    M translation context
    rawDynamicTruthReadyBinderPrincipalAndMixedQFPAHelpers
    helperRoots (rawDynamicTruthMixedQFFixedPAHelper cell)
    hhelpers hin) as [root hroot].
  exists root.
  rewrite (rawDynamicTruthMixedQFFixedPAHelperTarget_eq_native
    M hPA translation hagreement cell hfixed
    lowerPiApplication lowerSigmaApplication) in hroot.
  exact hroot.
Qed.

(** The only two roots not supplied by the fixed helper suffix. *)
Definition RawDynamicTruthMixedQFOpaqueCellRootsAt
    (M : RawPAModel) (context lowerPiApplication lowerSigmaApplication : M)
    : Prop :=
  RawDynamicTruthLocalRootAt M context
    (rawDynamicTruthMixedQFCellCode M DTMQFSigmaQFPiEx
      lowerPiApplication lowerSigmaApplication) /\
  RawDynamicTruthLocalRootAt M context
    (rawDynamicTruthMixedQFCellCode M DTMQFSigmaAllPiQF
      lowerPiApplication lowerSigmaApplication).

Arguments RawDynamicTruthMixedQFOpaqueCellRootsAt
  M context lowerPiApplication lowerSigmaApplication : clear implicits.

Definition RawDynamicTruthMixedQFAllCellRootsAt
    (M : RawPAModel) (context lowerPiApplication lowerSigmaApplication : M)
    : Prop :=
  forall cell : DynamicTruthMixedQFCell,
    RawDynamicTruthLocalRootAt M context
      (rawDynamicTruthMixedQFCellCode M cell
        lowerPiApplication lowerSigmaApplication).

Arguments RawDynamicTruthMixedQFAllCellRootsAt
  M context lowerPiApplication lowerSigmaApplication : clear implicits.

(** Finite adapter from the nine fixed roots and the exact two opaque roots
    to the matrix's all-eleven family. *)
Theorem raw_dynamicTruthMixedQFAllCellRootsAt_of_fixed_and_opaque : forall
    (M : RawPAModel) context lowerPiApplication lowerSigmaApplication,
  RawDynamicTruthMixedQFFixedCellRootsAt M context
    lowerPiApplication lowerSigmaApplication ->
  RawDynamicTruthMixedQFOpaqueCellRootsAt M context
    lowerPiApplication lowerSigmaApplication ->
  RawDynamicTruthMixedQFAllCellRootsAt M context
    lowerPiApplication lowerSigmaApplication.
Proof.
  intros M context lowerPi lowerSigma hfixed [hpiEx hsigmaAll] cell.
  destruct cell.
  - apply hfixed; cbn; intuition.
  - apply hfixed; cbn; intuition.
  - apply hfixed; cbn; intuition.
  - apply hfixed; cbn; intuition.
  - exact hpiEx.
  - apply hfixed; cbn; intuition.
  - apply hfixed; cbn; intuition.
  - apply hfixed; cbn; intuition.
  - apply hfixed; cbn; intuition.
  - apply hfixed; cbn; intuition.
  - exact hsigmaAll.
Qed.

Corollary raw_dynamicTruthMixedQFAllCellRootsAt_of_helper_batch : forall
    (M : RawPAModel), RawPASatisfies M ->
  forall (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall context helperRoots lowerPiApplication lowerSigmaApplication,
  RawFixedPAHelperBatchLocalProofs M translation context
    rawDynamicTruthReadyBinderPrincipalAndMixedQFPAHelpers helperRoots ->
  RawDynamicTruthMixedQFOpaqueCellRootsAt M context
    lowerPiApplication lowerSigmaApplication ->
  RawDynamicTruthMixedQFAllCellRootsAt M context
    lowerPiApplication lowerSigmaApplication.
Proof.
  intros M hPA translation hagreement context helperRoots
    lowerPi lowerSigma hhelpers hopaque.
  apply (raw_dynamicTruthMixedQFAllCellRootsAt_of_fixed_and_opaque
    M context lowerPi lowerSigma).
  - exact (raw_dynamicTruthMixedQFFixedCellRootsAt_of_helper_batch
      M hPA translation hagreement context helperRoots lowerPi lowerSigma
      hhelpers).
  - exact hopaque.
Qed.

End PABoundedRawCodedDynamicTruthMixedQFHelperRootExtraction.
