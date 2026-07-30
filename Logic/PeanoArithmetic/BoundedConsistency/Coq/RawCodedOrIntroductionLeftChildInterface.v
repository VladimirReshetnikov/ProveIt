(**
  Arithmetic child-interface descent for left disjunction introduction.

  The direct soundness compiler needs the same bundle of consequences in
  several guises.  This module proves it at the semantic relation level once,
  without mentioning template syntax or truth predicates.  The hierarchy
  bound is a carrier element, so the result applies equally at standard and
  nonstandard levels.
*)

From Stdlib Require Import List.
From PAHF Require Import PAHF.
From PAListCoding Require Import ListCode Representability.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelector CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedAssignment
  RawCodedSyntaxConstructors
  RawCodedProofConstructors
  RawCodedProofDescent
  RawCodedProofEndpoints
  RawCodedProofRules
  RawCodedProofOrIConstructors
  RawCodedFixedLevelTruthTotality
  RawCodedFixedLevelTruthAdmissibleLowering
  RawCodedProofAtomicAdequacy
  RawCodedProofFormulaCoverage
  RawCodedProofRuleCoverage
  RawCodedRestrictedProofAdmissibility
  RawCodedCarrierRestrictedProofReroot.

Import ListNotations.

Module PABoundedRawCodedOrIntroductionLeftChildInterface.

Import PA.
Import PAListCode.
Import PAListRepresentability.
Import PAHierarchyReduction.
Import PACanonicalSelector.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedAssignment.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedProofConstructors.
Import PABoundedRawCodedProofDescent.
Import PABoundedRawCodedProofEndpoints.
Import PABoundedRawCodedProofRules.
Import PABoundedRawCodedProofOrIConstructors.
Import PABoundedRawCodedFixedLevelTruthTotality.
Import PABoundedRawCodedFixedLevelTruthAdmissibleLowering.
Import PABoundedRawCodedProofAtomicAdequacy.
Import PABoundedRawCodedProofFormulaCoverage.
Import PABoundedRawCodedProofRuleCoverage.
Import PABoundedRawCodedRestrictedProofAdmissibility.
Import PABoundedRawCodedCarrierRestrictedProofReroot.

(** The literal constructor data expected by each generic recursive-child
    preservation theorem.  Isolating it here avoids repeating the tag row,
    zero payloads, and recursive-case membership proof. *)
Lemma raw_orIntroductionLeft_recursive_child_data : forall
    (M : RawPAModel) root context leftFormula rightFormula child,
  root = rawProofOrIRoot M RawOrLeft
    context leftFormula rightFormula child ->
  RawProofConstructorCode M
    root context leftFormula rightFormula
    (raw_zero M) (raw_zero M) child (raw_zero M) (raw_zero M) /\
  In
    ([rawNumeralValue M 8; context; leftFormula; rightFormula; child],
     [child])
    (rawProofRecursiveCases M
      context leftFormula rightFormula
      (raw_zero M) (raw_zero M) child (raw_zero M) (raw_zero M)) /\
  root = rawListCode M
    [rawNumeralValue M 8; context; leftFormula; rightFormula; child] /\
  In child [child].
Proof.
  intros M root context leftFormula rightFormula child hcode.
  repeat split.
  - rewrite hcode. apply raw_proofOrIRoot_constructor.
  - unfold rawProofRecursiveCases. cbn. tauto.
  - exact hcode.
  - left. reflexivity.
Qed.

(** Carrier restriction already records hierarchy boundedness for every
    endpoint occurrence at its root. *)
Lemma raw_carrierRestrictedProofAt_endpoint_bounded : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    tail level root context conclusion,
  RawCarrierRestrictedProofAt M tail level root ->
  RawProofEndpoint M root context conclusion ->
  RawCarrierFormulaQuantifierBounded M level conclusion.
Proof.
  intros M hPA tail level root context conclusion
    (supportCode & supportStep & htraversal & hroot) hendpoint.
  pose proof (proj2 htraversal root
    (raw_assignment_lt_self_succ M hPA root) hroot) as hnodeAt.
  apply (proj1 (raw_carrierRestrictedProofNodeAt_iff M tail level
    root supportCode supportStep)) in hnodeAt.
  destruct hnodeAt as [_ [_ [_ hendpoints]]].
  exact (proj2 (hendpoints context conclusion hendpoint)).
Qed.

(** All proof-wide certificates and endpoint-local admissibility descend in
    one pass.  The returned conjunction is ordered to match the four-field
    child interface used by the represented strong-prefix predicate. *)
Theorem raw_orIntroductionLeft_child_interface : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    tail level root coverageBound context leftFormula rightFormula child
    assignmentCode assignmentStep,
  RawCarrierRestrictedProofAt M tail level root ->
  RawProofAtomicallyAdequate M root ->
  RawProofFormulaCoverage M root coverageBound ->
  RawProofRuleCoverage M root ->
  root = rawProofOrIRoot M RawOrLeft
    context leftFormula rightFormula child ->
  RawProofEndpoint M child context leftFormula ->
  RawCodedAssignmentDefinedThrough M
    assignmentCode assignmentStep coverageBound ->
  rawLt M child root /\
  RawCarrierRestrictedProofAt M tail level child /\
  RawProofAtomicallyAdequate M child /\
  RawProofFormulaCoverage M child coverageBound /\
  RawProofRuleCoverage M child /\
  RawProofRuleValid M child context leftFormula /\
  RawCodedFormulaAtomicallyAdequate M leftFormula /\
  RawCodedAssignmentDefinedThrough M
    assignmentCode assignmentStep leftFormula /\
  RawCarrierFormulaQuantifierBounded M level leftFormula.
Proof.
  intros M hPA tail level root coverageBound context leftFormula
    rightFormula child assignmentCode assignmentStep
    hrestricted hatomic hformulaCoverage hruleCoverage hcode
    hendpoint hassignmentCoverage.
  destruct (raw_orIntroductionLeft_recursive_child_data M root context
    leftFormula rightFormula child hcode) as
    [hconstructor [hentry [hfields hchild]]].

  destruct (raw_proofAtomicallyAdequate_recursive_child M hPA
    root hatomic context leftFormula rightFormula
    (raw_zero M) (raw_zero M) child (raw_zero M) (raw_zero M)
    hconstructor _ _ hentry hfields child hchild) as
    [hchildAtomic hbelow].
  destruct (raw_proofFormulaCoverage_public_recursive_child M hPA
    root coverageBound hformulaCoverage context leftFormula rightFormula
    (raw_zero M) (raw_zero M) child (raw_zero M) (raw_zero M)
    hconstructor _ _ hentry hfields child hchild) as
    [hchildFormulaCoverage _].
  destruct (raw_proofRuleCoverage_public_recursive_child M hPA
    root hruleCoverage context leftFormula rightFormula
    (raw_zero M) (raw_zero M) child (raw_zero M) (raw_zero M)
    hconstructor _ _ hentry hfields child hchild) as
    [hchildRuleCoverage _].
  pose proof (raw_carrierRestrictedProofAt_orI_left_child M hPA
    tail level root context leftFormula rightFormula child
    hrestricted hcode) as hchildRestricted.
  pose proof (raw_proofRuleCoverage_public_root_complete M hPA
    child hchildRuleCoverage context leftFormula hendpoint)
    as hchildRuleValid.
  pose proof (raw_proofAtomicallyAdequate_root_endpoint M hPA
    child hchildAtomic context leftFormula hendpoint) as
    [_ hleftAtomic].
  pose proof (raw_proofFormulaCoverage_public_root_endpoint M hPA
    child coverageBound hchildFormulaCoverage
    context leftFormula hendpoint) as [_ hleftBelowCoverage].
  pose proof (raw_codedAssignmentDefinedThrough_of_lt M hPA
    assignmentCode assignmentStep leftFormula coverageBound
    hleftBelowCoverage hassignmentCoverage) as hleftDefined.
  pose proof (raw_carrierRestrictedProofAt_endpoint_bounded M hPA
    tail level child context leftFormula hchildRestricted hendpoint)
    as hleftBounded.

  repeat split; assumption.
Qed.

End PABoundedRawCodedOrIntroductionLeftChildInterface.
