(**
  Fixed PA helpers and local application for guarded implication collisions.

  Boolean collision cells still consume the historical predecessor premise,
  whereas the two implication cells now have a strictly weaker guarded
  premise.  Keeping this helper batch separate prevents a matrix rewrite
  from accidentally changing the Boolean endpoints.  Both guarded cells are
  ordinary PA theorems and can therefore be compiled beside the QF helper on
  one witnessed finite-axiom extension.
*)

From Stdlib Require Import List.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors
  RawCodedPALocalProofExistential
  RawCodedPALocalProofComposition
  RawCodedTemplateProofCompiler
  RawCodedTemplatePAEmbedding
  RawCodedTruthCertificateMasterFixedHelperBatchExtension
  RawCodedTruthCertificateMasterHelperLookup
  RawCodedDynamicTruthQFBranchExclusivity
  RawCodedDynamicTruthImpBranchExclusivity
  RawCodedDynamicTruthImpGuardedBranchExclusivity.

Module PABoundedRawCodedDynamicTruthImpGuardedCollisionHelperBatch.

Import ListNotations.
Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPALocalProofComposition.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedTemplatePAEmbedding.
Import PABoundedRawCodedTruthCertificateMasterFixedHelperBatchExtension.
Import PABoundedRawCodedTruthCertificateMasterHelperLookup.
Import PABoundedRawCodedDynamicTruthQFBranchExclusivity.
Import PABoundedRawCodedDynamicTruthImpBranchExclusivity.
Import PABoundedRawCodedDynamicTruthImpGuardedBranchExclusivity.

Definition rawDynamicTruthImpFalseLeftGuardedCollisionFixedPAHelper
    : RawFixedPAHelper :=
  {| rawFixedPAHelperFormula :=
       dynamicTruthImpFalseLeftGuardedConditionalCellFormula;
     rawFixedPAHelperBProv :=
       PA_proves_dynamicTruthImpFalseLeftGuardedConditionalCellFormula |}.

Definition rawDynamicTruthImpTrueRightGuardedCollisionFixedPAHelper
    : RawFixedPAHelper :=
  {| rawFixedPAHelperFormula :=
       dynamicTruthImpTrueRightGuardedConditionalCellFormula;
     rawFixedPAHelperBProv :=
       PA_proves_dynamicTruthImpTrueRightGuardedConditionalCellFormula |}.

Definition rawDynamicTruthFirstThreeGuardedCollisionFixedPAHelpers
    : list RawFixedPAHelper :=
  [ rawDynamicTruthQFCollisionFixedPAHelper;
    rawDynamicTruthImpFalseLeftGuardedCollisionFixedPAHelper;
    rawDynamicTruthImpTrueRightGuardedCollisionFixedPAHelper ].

Lemma rawDynamicTruthFirstThreeGuardedCollisionFixedPAHelperTargets_eq_quoted :
    forall (M : RawPAModel)
      (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  rawFixedPAHelperBatchTranslatedTargetCodes M translation
    rawDynamicTruthFirstThreeGuardedCollisionFixedPAHelpers =
  [ rawQuotedFormulaCode M
      dynamicTruthQFEx8BranchExclusivityFormula;
    rawQuotedFormulaCode M
      dynamicTruthImpFalseLeftGuardedConditionalCellFormula;
    rawQuotedFormulaCode M
      dynamicTruthImpTrueRightGuardedConditionalCellFormula ].
Proof.
  intros M translation hagreement.
  unfold rawFixedPAHelperBatchTranslatedTargetCodes,
    rawDynamicTruthFirstThreeGuardedCollisionFixedPAHelpers,
    rawDynamicTruthQFCollisionFixedPAHelper,
    rawDynamicTruthImpFalseLeftGuardedCollisionFixedPAHelper,
    rawDynamicTruthImpTrueRightGuardedCollisionFixedPAHelper,
    rawFixedPAHelperTranslatedTargetCode.
  cbn [map rawFixedPAHelperFormula].
  repeat rewrite (rawTemplateFormula_embedPA hagreement).
  reflexivity.
Qed.

Lemma rawDynamicTruthImpFalseGuardedHelperTarget_eq_native : forall
    (M : RawPAModel), RawPASatisfies M -> forall translation,
  RawCodedTemplatePAAgreement M translation ->
  rawFixedPAHelperTranslatedTargetCode M translation
    rawDynamicTruthImpFalseLeftGuardedCollisionFixedPAHelper =
  rawDynamicTruthImpFalseLeftGuardedConditionalCellCode M.
Proof.
  intros M hPA translation hagreement.
  unfold rawFixedPAHelperTranslatedTargetCode,
    rawDynamicTruthImpFalseLeftGuardedCollisionFixedPAHelper.
  cbn [rawFixedPAHelperFormula].
  rewrite (rawTemplateFormula_embedPA hagreement).
  symmetry.
  exact (rawDynamicTruthImpFalseLeftGuardedConditionalCellCode_eq_quoted
    M hPA).
Qed.

Lemma rawDynamicTruthQFGuardedBatchHelperTarget_eq_native : forall
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
  symmetry.
  exact (rawDynamicTruthQFEx8BranchExclusivityCode_eq_quoted M hPA).
Qed.

Lemma rawDynamicTruthImpTrueGuardedHelperTarget_eq_native : forall
    (M : RawPAModel), RawPASatisfies M -> forall translation,
  RawCodedTemplatePAAgreement M translation ->
  rawFixedPAHelperTranslatedTargetCode M translation
    rawDynamicTruthImpTrueRightGuardedCollisionFixedPAHelper =
  rawDynamicTruthImpTrueRightGuardedConditionalCellCode M.
Proof.
  intros M hPA translation hagreement.
  unfold rawFixedPAHelperTranslatedTargetCode,
    rawDynamicTruthImpTrueRightGuardedCollisionFixedPAHelper.
  cbn [rawFixedPAHelperFormula].
  rewrite (rawTemplateFormula_embedPA hagreement).
  symmetry.
  exact (rawDynamicTruthImpTrueRightGuardedConditionalCellCode_eq_quoted
    M hPA).
Qed.

(** Extract the two guarded cells and the unchanged QF cell from any common
    local proof batch using only list membership. *)
Theorem raw_dynamicTruthGuardedBasicCollisionRoots_of_helper_batch : forall
    (M : RawPAModel), RawPASatisfies M -> forall translation context roots,
  RawCodedTemplatePAAgreement M translation ->
  RawFixedPAHelperBatchLocalProofs M translation context
    rawDynamicTruthFirstThreeGuardedCollisionFixedPAHelpers roots ->
  (exists root, RawCodedPALocalProofOf M context
      (rawDynamicTruthQFEx8BranchExclusivityCode M) root) /\
  (exists root, RawCodedPALocalProofOf M context
      (rawDynamicTruthImpFalseLeftGuardedConditionalCellCode M) root) /\
  (exists root, RawCodedPALocalProofOf M context
      (rawDynamicTruthImpTrueRightGuardedConditionalCellCode M) root).
Proof.
  intros M hPA translation context roots hagreement hroots.
  assert (lookup : forall helper,
      In helper rawDynamicTruthFirstThreeGuardedCollisionFixedPAHelpers ->
      exists root : M, RawCodedPALocalProofOf M context
        (rawFixedPAHelperTranslatedTargetCode M translation helper) root).
  {
    intros helper hin.
    exact (raw_fixedPAHelperBatchLocalProofs_member
      M translation context
      rawDynamicTruthFirstThreeGuardedCollisionFixedPAHelpers roots
      helper hroots hin).
  }
  destruct (lookup rawDynamicTruthQFCollisionFixedPAHelper)
    as [qfRoot hqf].
  {
    unfold rawDynamicTruthFirstThreeGuardedCollisionFixedPAHelpers.
    cbn. auto.
  }
  destruct (lookup
    rawDynamicTruthImpFalseLeftGuardedCollisionFixedPAHelper)
    as [falseRoot hfalse].
  {
    unfold rawDynamicTruthFirstThreeGuardedCollisionFixedPAHelpers.
    cbn. auto.
  }
  destruct (lookup
    rawDynamicTruthImpTrueRightGuardedCollisionFixedPAHelper)
    as [trueRoot htrue].
  {
    unfold rawDynamicTruthFirstThreeGuardedCollisionFixedPAHelpers.
    cbn. auto.
  }
  rewrite (rawDynamicTruthQFGuardedBatchHelperTarget_eq_native
    M hPA translation hagreement) in hqf.
  rewrite (rawDynamicTruthImpFalseGuardedHelperTarget_eq_native
    M hPA translation hagreement) in hfalse.
  rewrite (rawDynamicTruthImpTrueGuardedHelperTarget_eq_native
    M hPA translation hagreement) in htrue.
  split; [exists qfRoot; exact hqf |].
  split; [exists falseRoot; exact hfalse |].
  exists trueRoot. exact htrue.
Qed.

(** Apply each guarded conditional cell to its guarded predecessor proof.
    The result is the literal two-branch collision formula consumed by a
    finite disjunction matrix; the branch assumptions remain unintroduced. *)
Theorem raw_dynamicTruthImpFalseLeftGuarded_pair : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      context cellRoot predecessorRoot,
  RawCodedPALocalProofOf M context
    (rawDynamicTruthImpFalseLeftGuardedConditionalCellCode M) cellRoot ->
  RawCodedPALocalProofOf M context
    (rawDynamicTruthImpGuardedPredecessorStateExclusivityCode M)
    predecessorRoot ->
  exists pairRoot,
    RawCodedPALocalProofOf M context
      (rawFormulaImpCode M
        (rawDynamicTruthSigmaImpFalseLeftEx8BranchCode M)
        (rawFormulaImpCode M
          (rawDynamicTruthPiImpEx8BranchCode M)
          (rawFormulaBotCode M))) pairRoot.
Proof.
  intros M hPA context cellRoot predecessorRoot hcell hpredecessor.
  unfold rawDynamicTruthImpFalseLeftGuardedConditionalCellCode in hcell.
  pose proof (raw_codedPALocalProofOf_impE M hPA context
    (rawDynamicTruthImpGuardedPredecessorStateExclusivityCode M)
    (rawFormulaImpCode M
      (rawDynamicTruthSigmaImpFalseLeftEx8BranchCode M)
      (rawFormulaImpCode M
        (rawDynamicTruthPiImpEx8BranchCode M)
        (rawFormulaBotCode M)))
    cellRoot predecessorRoot hcell hpredecessor) as hpair.
  eexists. exact hpair.
Qed.

Theorem raw_dynamicTruthImpTrueRightGuarded_pair : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      context cellRoot predecessorRoot,
  RawCodedPALocalProofOf M context
    (rawDynamicTruthImpTrueRightGuardedConditionalCellCode M) cellRoot ->
  RawCodedPALocalProofOf M context
    (rawDynamicTruthImpGuardedPredecessorStateExclusivityCode M)
    predecessorRoot ->
  exists pairRoot,
    RawCodedPALocalProofOf M context
      (rawFormulaImpCode M
        (rawDynamicTruthSigmaImpTrueRightEx8BranchCode M)
        (rawFormulaImpCode M
          (rawDynamicTruthPiImpEx8BranchCode M)
          (rawFormulaBotCode M))) pairRoot.
Proof.
  intros M hPA context cellRoot predecessorRoot hcell hpredecessor.
  unfold rawDynamicTruthImpTrueRightGuardedConditionalCellCode in hcell.
  pose proof (raw_codedPALocalProofOf_impE M hPA context
    (rawDynamicTruthImpGuardedPredecessorStateExclusivityCode M)
    (rawFormulaImpCode M
      (rawDynamicTruthSigmaImpTrueRightEx8BranchCode M)
      (rawFormulaImpCode M
        (rawDynamicTruthPiImpEx8BranchCode M)
        (rawFormulaBotCode M)))
    cellRoot predecessorRoot hcell hpredecessor) as hpair.
  eexists. exact hpair.
Qed.

End PABoundedRawCodedDynamicTruthImpGuardedCollisionHelperBatch.
