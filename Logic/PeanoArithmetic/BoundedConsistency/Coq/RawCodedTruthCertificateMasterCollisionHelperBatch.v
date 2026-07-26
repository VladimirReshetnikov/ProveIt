(**
  One common-context batch for every native collision theorem currently
  available without a carrier-parametric binder compiler.

  The finite helper infrastructure already knows how to compile an ordered
  family of ordinary PA theorems above one witnessed PA context.  This file
  supplies the concrete family needed by the native Sigma/Pi collision
  matrix:

  - the unconditional QF/QF collision;
  - the two conditional implication collisions;
  - the conditional conjunction and disjunction collisions; and
  - the sixteen lower-independent off-diagonal constructor collisions.

  The four conditional same-constructor entries still contain the explicit
  predecessor-state exclusivity antecedent.  Adding their PA proofs to the
  common context does not claim that this antecedent has been discharged.
  Likewise, this batch deliberately excludes all carrier-sensitive binder
  cells and all mixed QF/non-QF cells.  Its advertised size is therefore
  exactly twenty-one, not the full forty-two-cell matrix.
*)

From Stdlib Require Import List.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors
  RawCodedTemplateSyntax
  RawCodedTemplateProofCompiler
  RawCodedTemplatePAEmbedding
  RawCodedTruthCertificateMasterBaseBridge
  RawCodedTruthCertificateMasterFixedHelperBatchExtension
  RawCodedDynamicTruthBooleanBranchExclusivity
  RawCodedDynamicTruthConstructorBranchDisjointness.

Import ListNotations.

Module PABoundedRawCodedTruthCertificateMasterCollisionHelperBatch.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedTemplatePAEmbedding.
Import PABoundedRawCodedTruthCertificateMasterBaseBridge.
Import PABoundedRawCodedTruthCertificateMasterFixedHelperBatchExtension.
Import PABoundedRawCodedDynamicTruthBooleanBranchExclusivity.
Import PABoundedRawCodedDynamicTruthConstructorBranchDisjointness.

(** The two Boolean diagonal cells use exactly the conditional PA theorems
    proved by the native branch module. *)
Definition rawDynamicTruthAndCollisionFixedPAHelper : RawFixedPAHelper :=
  {| rawFixedPAHelperFormula := dynamicTruthAndConditionalCellFormula;
     rawFixedPAHelperBProv :=
       PA_proves_dynamicTruthAndConditionalCellFormula |}.

Definition rawDynamicTruthOrCollisionFixedPAHelper : RawFixedPAHelper :=
  {| rawFixedPAHelperFormula := dynamicTruthOrConditionalCellFormula;
     rawFixedPAHelperBProv :=
       PA_proves_dynamicTruthOrConditionalCellFormula |}.

(** Turn one certified member of the sixteen-cell classification into a
    helper.  Keeping the membership proof as an argument prevents a caller
    from silently inserting one of the eight lower-dependent cells. *)
Definition rawDynamicTruthFixedConstructorCollisionPAHelper
    (sigmaBranch : DynamicTruthSigmaConstructorBranch)
    (piBranch : DynamicTruthPiConstructorBranch)
    (hcell : In (sigmaBranch, piBranch)
      dynamicTruthFixedConstructorCells) : RawFixedPAHelper :=
  {| rawFixedPAHelperFormula :=
       dynamicTruthFixedConstructorBranchDisjointnessFormula
         sigmaBranch piBranch;
     rawFixedPAHelperBProv :=
       PA_proves_dynamicTruthFixedConstructorBranchDisjointnessFormula
         sigmaBranch piBranch hcell |}.

(** The list follows [dynamicTruthFixedConstructorCells] literally.  The
    small local tactic terms prove only membership in that transparent finite
    list; no mathematical proof is hidden in them. *)
Definition rawDynamicTruthFixedConstructorCollisionPAHelpers
    : list RawFixedPAHelper :=
  [ rawDynamicTruthFixedConstructorCollisionPAHelper
      DTSigmaImpFalseLeft DTPiAnd (ltac:(cbn; tauto));
    rawDynamicTruthFixedConstructorCollisionPAHelper
      DTSigmaImpFalseLeft DTPiOr (ltac:(cbn; tauto));
    rawDynamicTruthFixedConstructorCollisionPAHelper
      DTSigmaImpFalseLeft DTPiAll (ltac:(cbn; tauto));
    rawDynamicTruthFixedConstructorCollisionPAHelper
      DTSigmaImpTrueRight DTPiAnd (ltac:(cbn; tauto));
    rawDynamicTruthFixedConstructorCollisionPAHelper
      DTSigmaImpTrueRight DTPiOr (ltac:(cbn; tauto));
    rawDynamicTruthFixedConstructorCollisionPAHelper
      DTSigmaImpTrueRight DTPiAll (ltac:(cbn; tauto));
    rawDynamicTruthFixedConstructorCollisionPAHelper
      DTSigmaAnd DTPiImp (ltac:(cbn; tauto));
    rawDynamicTruthFixedConstructorCollisionPAHelper
      DTSigmaAnd DTPiOr (ltac:(cbn; tauto));
    rawDynamicTruthFixedConstructorCollisionPAHelper
      DTSigmaAnd DTPiAll (ltac:(cbn; tauto));
    rawDynamicTruthFixedConstructorCollisionPAHelper
      DTSigmaOr DTPiImp (ltac:(cbn; tauto));
    rawDynamicTruthFixedConstructorCollisionPAHelper
      DTSigmaOr DTPiAnd (ltac:(cbn; tauto));
    rawDynamicTruthFixedConstructorCollisionPAHelper
      DTSigmaOr DTPiAll (ltac:(cbn; tauto));
    rawDynamicTruthFixedConstructorCollisionPAHelper
      DTSigmaEx DTPiImp (ltac:(cbn; tauto));
    rawDynamicTruthFixedConstructorCollisionPAHelper
      DTSigmaEx DTPiAnd (ltac:(cbn; tauto));
    rawDynamicTruthFixedConstructorCollisionPAHelper
      DTSigmaEx DTPiOr (ltac:(cbn; tauto));
    rawDynamicTruthFixedConstructorCollisionPAHelper
      DTSigmaEx DTPiAll (ltac:(cbn; tauto)) ].

Lemma rawDynamicTruthFixedConstructorCollisionPAHelpers_length :
  length rawDynamicTruthFixedConstructorCollisionPAHelpers = 16.
Proof. reflexivity. Qed.

(** The complete ready batch extends the existing QF/implication prefix in
    dependency order, then appends the two Boolean cells and the sixteen
    fixed-constructor cells. *)
Definition rawDynamicTruthReadyCollisionFixedPAHelpers
    : list RawFixedPAHelper :=
  rawDynamicTruthFirstThreeCollisionFixedPAHelpers ++
  [ rawDynamicTruthAndCollisionFixedPAHelper;
    rawDynamicTruthOrCollisionFixedPAHelper ] ++
  rawDynamicTruthFixedConstructorCollisionPAHelpers.

Lemma rawDynamicTruthReadyCollisionFixedPAHelpers_length :
  length rawDynamicTruthReadyCollisionFixedPAHelpers = 21.
Proof. reflexivity. Qed.

(** Agreement of one template translation exposes the target of every
    helper in an arbitrary batch as the corresponding ordinary PA quotation.
    This generic map lemma is useful here because it avoids a fragile
    twenty-one-element target equation. *)
Lemma rawFixedPAHelperBatchTranslatedTargetCodes_eq_quoted : forall
    (M : RawPAModel) (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation -> forall helpers,
  rawFixedPAHelperBatchTranslatedTargetCodes M translation helpers =
  map (fun helper =>
    rawQuotedFormulaCode M (rawFixedPAHelperFormula helper)) helpers.
Proof.
  intros M translation hagreement helpers.
  unfold rawFixedPAHelperBatchTranslatedTargetCodes.
  apply map_ext. intro helper.
  unfold rawFixedPAHelperTranslatedTargetCode.
  exact (rawTemplateFormula_embedPA hagreement
    (rawFixedPAHelperFormula helper)).
Qed.

Corollary rawDynamicTruthReadyCollisionFixedPAHelperTargets_eq_quoted :
    forall (M : RawPAModel)
      (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  rawFixedPAHelperBatchTranslatedTargetCodes M translation
    rawDynamicTruthReadyCollisionFixedPAHelpers =
  map (fun helper =>
    rawQuotedFormulaCode M (rawFixedPAHelperFormula helper))
    rawDynamicTruthReadyCollisionFixedPAHelpers.
Proof.
  intros M translation hagreement.
  exact (rawFixedPAHelperBatchTranslatedTargetCodes_eq_quoted
    M translation hagreement rawDynamicTruthReadyCollisionFixedPAHelpers).
Qed.

(** All six current master roots and all twenty-one helper roots inhabit one
    syntactically identical witnessed PA context. *)
Corollary
    raw_sixFieldMasterCommonContextProofsWithReadyCollisionHelpers : forall
    (M : RawPAModel), RawPASatisfies M ->
  forall (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall field1 field2 field3 field4 field5 finalField,
  RawSixFieldMasterCommonContextProofsOf M
    field1 field2 field3 field4 field5 finalField ->
  RawSixFieldMasterCommonContextProofsWithFixedPAHelperBatchOf
    M translation field1 field2 field3 field4 field5 finalField
    rawDynamicTruthReadyCollisionFixedPAHelpers.
Proof.
  intros M hPA translation hagreement
    field1 field2 field3 field4 field5 finalField hmaster.
  exact (raw_sixFieldMasterCommonContextProofsWithFixedPAHelperBatch
    M hPA translation hagreement
    field1 field2 field3 field4 field5 finalField
    rawDynamicTruthReadyCollisionFixedPAHelpers hmaster).
Qed.

End PABoundedRawCodedTruthCertificateMasterCollisionHelperBatch.
