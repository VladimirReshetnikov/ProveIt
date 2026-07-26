(**
  Discharge the term-opening premise used by formula substitution totality.

  This adapter is kept separate so the lower-level opening construction does
  not depend on its formula-substitution client.  It also records the useful
  unconditional formula-level consequence explicitly.
*)

From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA.
From BoundedPAConsistency Require Import
  RawCodedFormulaOperations RawCodedTermEvaluationRealization
  RawCodedFixedLevelTruthTotality
  RawCodedTermOpeningTotality
  RawCodedFormulaSingleSubstitutionTotality.

Module PABoundedRawCodedTermOpeningTotalityDischarge.

Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedTermEvaluationRealization.
Import PABoundedRawCodedFixedLevelTruthTotality.
Import PABoundedRawCodedTermOpeningTotality.
Import PABoundedRawCodedFormulaSingleSubstitutionTotality.

Theorem raw_codedTermOpening_total : forall
    (M : RawPAModel), RawPASatisfies M ->
  RawCodedTermOpeningTotal M.
Proof.
  intros M hPA input assignmentCode assignmentStep hsyntax
    cutoff liftedReplacement.
  exact (raw_codedTermOpening_exists_of_syntax_realizable M hPA
    input assignmentCode assignmentStep hsyntax
    cutoff liftedReplacement).
Qed.

Corollary
    raw_codedFormulaSingleSubstitution_exists_of_atomically_adequate_total :
  forall (M : RawPAModel), RawPASatisfies M -> forall source,
  RawCodedFormulaAtomicallyAdequate M source ->
  forall replacement assignmentCode assignmentStep,
  RawTermSyntaxRealizable M replacement assignmentCode assignmentStep ->
  exists target,
    RawCodedFormulaSingleSubstitution M replacement source target.
Proof.
  intros M hPA source hadequate replacement
    assignmentCode assignmentStep hreplacement.
  exact
    (raw_codedFormulaSingleSubstitution_exists_of_atomically_adequate
      M hPA (raw_codedTermOpening_total M hPA)
      source hadequate replacement assignmentCode assignmentStep
      hreplacement).
Qed.

End PABoundedRawCodedTermOpeningTotalityDischarge.
