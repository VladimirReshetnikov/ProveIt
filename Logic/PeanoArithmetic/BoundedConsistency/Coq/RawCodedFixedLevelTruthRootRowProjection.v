(**
  Root-row projections for positive fixed-level truth certificates.

  The foundational traversal module deliberately keeps the seven traversal
  fields and the recursive certificate definitions close to their semantic
  proofs.  Consumers of totality need only one small consequence: the stored
  root lookup is covered by the traversal's universally closed row family.
  This extension module exposes that projection without increasing the
  rebuild fan-out of the foundational file.
*)

From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import HierarchyReduction.
From BoundedPAConsistency Require Import
  RawCodedFixedLevelTruth RawCodedFixedLevelTruthTraversal.

Module PABoundedRawCodedFixedLevelTruthRootRowProjection.

Import PA.
Import PAHierarchyReduction.
Import PABoundedRawCodedFixedLevelTruth.
Import PABoundedRawCodedFixedLevelTruthTraversal.

(** Project the row at the recorded root lookup. *)
Lemma raw_fixedLevelSuccessorTruthTraversal_root_closed_row : forall
    (M : RawPAModel) lower lowerSigmaEvidence lowerPiEvidence
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    bound rootIndex rootMode root assignmentCode assignmentStep,
  RawFixedLevelSuccessorTruthTraversal M lower
    lowerSigmaEvidence lowerPiEvidence
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    bound rootIndex rootMode root assignmentCode assignmentStep ->
  RawFixedLevelClosedSuccessorRow M lower
    lowerSigmaEvidence lowerPiEvidence
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    rootIndex rootMode root assignmentCode assignmentStep.
Proof.
  intros M lower lowerSigmaEvidence lowerPiEvidence
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    bound rootIndex rootMode root assignmentCode assignmentStep
    (_ & _ & _ & _ & hrootBound & hrootLookup & hrows).
  exact (hrows rootIndex rootMode root assignmentCode assignmentStep
    hrootBound hrootLookup).
Qed.

(** A positive Sigma certificate exposes its native closed Sigma root row
    together with the traversal tables which interpret it. *)
Corollary raw_fixedLevelSigmaTruthCertificate_succ_root_closed_row : forall
    (M : RawPAModel) lower root assignmentCode assignmentStep,
  RawFixedLevelSigmaTruthCertificate M (S lower)
    root assignmentCode assignmentStep ->
  exists modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep bound rootIndex,
    RawFixedLevelSuccessorTruthTraversal M lower
      (fun child childAssignmentCode childAssignmentStep =>
        RawFixedLevelSigmaTruthCertificate M lower
          child childAssignmentCode childAssignmentStep)
      (fun child childAssignmentCode childAssignmentStep =>
        RawFixedLevelPiFalsityCertificate M lower
          child childAssignmentCode childAssignmentStep)
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      bound rootIndex (rawFixedLevelSigmaMode M)
      root assignmentCode assignmentStep /\
    RawFixedLevelClosedSuccessorRow M lower
      (RawFixedLevelSigmaTruthCertificate M lower)
      (RawFixedLevelPiFalsityCertificate M lower)
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      rootIndex (rawFixedLevelSigmaMode M)
      root assignmentCode assignmentStep.
Proof.
  intros M lower root assignmentCode assignmentStep hcertificate.
  cbn [RawFixedLevelSigmaTruthCertificate] in hcertificate.
  destruct hcertificate as
    (modeCode & modeStep & formulaCode & formulaStep &
      assignmentCodeCode & assignmentCodeStep &
      assignmentStepCode & assignmentStepStep & bound & rootIndex &
      htraversal).
  exists modeCode, modeStep, formulaCode, formulaStep,
    assignmentCodeCode, assignmentCodeStep,
    assignmentStepCode, assignmentStepStep, bound, rootIndex.
  split; [exact htraversal |].
  exact
    (raw_fixedLevelSuccessorTruthTraversal_root_closed_row M lower
      (RawFixedLevelSigmaTruthCertificate M lower)
      (RawFixedLevelPiFalsityCertificate M lower)
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      bound rootIndex (rawFixedLevelSigmaMode M)
      root assignmentCode assignmentStep htraversal).
Qed.

(** Dual root-row projection for positive Pi-falsity certificates. *)
Corollary raw_fixedLevelPiFalsityCertificate_succ_root_closed_row : forall
    (M : RawPAModel) lower root assignmentCode assignmentStep,
  RawFixedLevelPiFalsityCertificate M (S lower)
    root assignmentCode assignmentStep ->
  exists modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep bound rootIndex,
    RawFixedLevelSuccessorTruthTraversal M lower
      (fun child childAssignmentCode childAssignmentStep =>
        RawFixedLevelSigmaTruthCertificate M lower
          child childAssignmentCode childAssignmentStep)
      (fun child childAssignmentCode childAssignmentStep =>
        RawFixedLevelPiFalsityCertificate M lower
          child childAssignmentCode childAssignmentStep)
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      bound rootIndex (rawFixedLevelPiMode M)
      root assignmentCode assignmentStep /\
    RawFixedLevelClosedSuccessorRow M lower
      (RawFixedLevelSigmaTruthCertificate M lower)
      (RawFixedLevelPiFalsityCertificate M lower)
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      rootIndex (rawFixedLevelPiMode M)
      root assignmentCode assignmentStep.
Proof.
  intros M lower root assignmentCode assignmentStep hcertificate.
  cbn [RawFixedLevelPiFalsityCertificate] in hcertificate.
  destruct hcertificate as
    (modeCode & modeStep & formulaCode & formulaStep &
      assignmentCodeCode & assignmentCodeStep &
      assignmentStepCode & assignmentStepStep & bound & rootIndex &
      htraversal).
  exists modeCode, modeStep, formulaCode, formulaStep,
    assignmentCodeCode, assignmentCodeStep,
    assignmentStepCode, assignmentStepStep, bound, rootIndex.
  split; [exact htraversal |].
  exact
    (raw_fixedLevelSuccessorTruthTraversal_root_closed_row M lower
      (RawFixedLevelSigmaTruthCertificate M lower)
      (RawFixedLevelPiFalsityCertificate M lower)
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      bound rootIndex (rawFixedLevelPiMode M)
      root assignmentCode assignmentStep htraversal).
Qed.

End PABoundedRawCodedFixedLevelTruthRootRowProjection.
