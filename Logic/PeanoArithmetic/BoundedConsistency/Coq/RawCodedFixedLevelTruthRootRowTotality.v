(**
  Closed root-row totality for positive fixed-level truth.

  Fixed-level totality returns a globally closed Sigma-truth certificate or
  Pi-falsity certificate.  Append-based consumers operate one layer lower:
  they need the selected closed row and the traversal tables interpreting
  its earlier-state references.  This module composes totality with the
  generic root-row projections and preserves all ten traversal witnesses.
*)

From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA.
From BoundedPAConsistency Require Import
  RawCodedFixedLevelTruth
  RawCodedFixedLevelTruthTraversal
  RawCodedFixedLevelTruthTotality
  RawCodedFixedLevelTruthScheduleInvariant
  RawCodedFixedLevelTruthSchedule
  RawCodedFixedLevelTruthRootRowProjection.

Module PABoundedRawCodedFixedLevelTruthRootRowTotality.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PABoundedRawCodedFixedLevelTruth.
Import PABoundedRawCodedFixedLevelTruthTraversal.
Import PABoundedRawCodedFixedLevelTruthTotality.
Import PABoundedRawCodedFixedLevelTruthScheduleInvariant.
Import PABoundedRawCodedFixedLevelTruthSchedule.
Import PABoundedRawCodedFixedLevelTruthRootRowProjection.

(** One selected positive root row, retaining its complete traversal. *)
Definition RawFixedLevelPositiveCertificateRootRowAt
    (M : RawPAModel) (lower : nat) (expectedMode root
      assignmentCode assignmentStep : M) : Prop :=
  exists modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep bound rootIndex,
    RawFixedLevelSuccessorTruthTraversal M lower
      (RawFixedLevelSigmaTruthCertificate M lower)
      (RawFixedLevelPiFalsityCertificate M lower)
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      bound rootIndex expectedMode root assignmentCode assignmentStep /\
    RawFixedLevelClosedSuccessorRow M lower
      (RawFixedLevelSigmaTruthCertificate M lower)
      (RawFixedLevelPiFalsityCertificate M lower)
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      rootIndex expectedMode root assignmentCode assignmentStep.

Arguments RawFixedLevelPositiveCertificateRootRowAt
  M lower expectedMode root assignmentCode assignmentStep : clear implicits.

(** Totality's two alternatives, now viewed at their root rows. *)
Definition RawFixedLevelPositiveCertificateRootRowDecisionAt
    (M : RawPAModel) (lower : nat)
    (root assignmentCode assignmentStep : M) : Prop :=
  RawFixedLevelPositiveCertificateRootRowAt M lower
    (rawFixedLevelSigmaMode M) root assignmentCode assignmentStep \/
  RawFixedLevelPositiveCertificateRootRowAt M lower
    (rawFixedLevelPiMode M) root assignmentCode assignmentStep.

Arguments RawFixedLevelPositiveCertificateRootRowDecisionAt
  M lower root assignmentCode assignmentStep : clear implicits.

(** Repackage the existing Sigma certificate projection. *)
Corollary raw_fixedLevelSigmaTruthCertificate_succ_root_row_at : forall
    (M : RawPAModel) lower root assignmentCode assignmentStep,
  RawFixedLevelSigmaTruthCertificate M (S lower)
    root assignmentCode assignmentStep ->
  RawFixedLevelPositiveCertificateRootRowAt M lower
    (rawFixedLevelSigmaMode M) root assignmentCode assignmentStep.
Proof.
  intros M lower root assignmentCode assignmentStep hcertificate.
  exact
    (raw_fixedLevelSigmaTruthCertificate_succ_root_closed_row
      M lower root assignmentCode assignmentStep hcertificate).
Qed.

(** Repackage the dual Pi certificate projection. *)
Corollary raw_fixedLevelPiFalsityCertificate_succ_root_row_at : forall
    (M : RawPAModel) lower root assignmentCode assignmentStep,
  RawFixedLevelPiFalsityCertificate M (S lower)
    root assignmentCode assignmentStep ->
  RawFixedLevelPositiveCertificateRootRowAt M lower
    (rawFixedLevelPiMode M) root assignmentCode assignmentStep.
Proof.
  intros M lower root assignmentCode assignmentStep hcertificate.
  exact
    (raw_fixedLevelPiFalsityCertificate_succ_root_closed_row
      M lower root assignmentCode assignmentStep hcertificate).
Qed.

(** Any semantic totality source yields the corresponding closed-row
    decision without discarding its traversal witnesses. *)
Theorem raw_fixedLevelInputTruthCertificateTotalityAt_root_row_decision :
  forall (M : RawPAModel) lower,
  RawFixedLevelInputTruthCertificateTotalityAt M lower ->
  forall root assignmentCode assignmentStep,
  RawFixedLevelTruthAdmissible M lower
    root assignmentCode assignmentStep ->
  RawFixedLevelPositiveCertificateRootRowDecisionAt M lower
    root assignmentCode assignmentStep.
Proof.
  intros M lower htotality root assignmentCode assignmentStep hadmissible.
  destruct (htotality root assignmentCode assignmentStep hadmissible)
    as [hsigma | hpi].
  - left. exact
      (raw_fixedLevelSigmaTruthCertificate_succ_root_row_at
        M lower root assignmentCode assignmentStep hsigma).
  - right. exact
      (raw_fixedLevelPiFalsityCertificate_succ_root_row_at
        M lower root assignmentCode assignmentStep hpi).
Qed.

(** Unconditional PA-model endpoint supplied by the constructed positive
    fixed-level schedule. *)
Theorem raw_fixedLevelInputTruthCertificate_root_row_decision : forall
    lower (M : RawPAModel), RawPASatisfies M ->
  forall root assignmentCode assignmentStep,
  RawFixedLevelTruthAdmissible M lower
    root assignmentCode assignmentStep ->
  RawFixedLevelPositiveCertificateRootRowDecisionAt M lower
    root assignmentCode assignmentStep.
Proof.
  intros lower M hPA root assignmentCode assignmentStep hadmissible.
  exact
    (raw_fixedLevelInputTruthCertificateTotalityAt_root_row_decision
      M lower
      (raw_fixedLevelInputTruthCertificateTotalityAt_all lower M hPA)
      root assignmentCode assignmentStep hadmissible).
Qed.

End PABoundedRawCodedFixedLevelTruthRootRowTotality.
