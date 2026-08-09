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
  RawCodedCarrierRestrictedProofReroot
  RawCodedRestrictedPADerivationSoundnessRecursiveChildInterface.

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
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessRecursiveChildInterface.

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
  exact
    (raw_recursive_constructor_child_interface
      M hPA tail level root coverageBound context
      leftFormula rightFormula (raw_zero M) (raw_zero M)
      child (raw_zero M) (raw_zero M)
      [rawNumeralValue M 8; context; leftFormula; rightFormula; child]
      [child] child leftFormula assignmentCode assignmentStep
      hrestricted hatomic hformulaCoverage hruleCoverage
      hconstructor hentry hfields hchild hendpoint hassignmentCoverage).
Qed.

End PABoundedRawCodedOrIntroductionLeftChildInterface.
