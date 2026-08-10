(**
  Constructor-generic child descent with an independent endpoint context.

  Most natural-deduction rules check a recursive child in the constructor's
  parent context.  Binder rules are the important exception: for example,
  the body child of existential elimination is checked in the binder-extended
  context.  This small companion to the ordinary recursive-child interface
  keeps the parent context used to decode the constructor separate from the
  context displayed by the selected child's endpoint.
*)

From Stdlib Require Import List Lia.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAListCoding Require Import Representability.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelector CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawModelCompleteness
  PolynomialPairInjectivity
  RawCodedAssignment
  RawCodedSyntaxConstructors
  RawCodedProofConstructors
  RawCodedProofDescent
  RawCodedProofTraversal
  RawCodedProofEndpoints
  RawCodedProofRules
  RawCodedProofAtomicAdequacy
  RawCodedProofFormulaCoverage
  RawCodedProofRuleCoverage
  RawCodedFixedLevelTruthTotality
  RawCodedFixedLevelTruthAdmissibleLowering
  RawCodedRestrictedPAProof
  RawCodedRestrictedProofAdmissibility
  RawCodedCarrierRestrictedProofReroot
  RawCodedRestrictedPADerivationSoundnessRecursiveChildInterface.

Import ListNotations.

Module
  PABoundedRawCodedRestrictedPADerivationSoundnessRecursiveChildEndpointContextInterface.

Import PA.
Import PAListRepresentability.
Import PAHierarchyReduction.
Import PACanonicalSelector.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawModelCompleteness.
Import PABoundedPolynomialPairInjectivity.
Import PABoundedRawCodedAssignment.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedProofConstructors.
Import PABoundedRawCodedProofDescent.
Import PABoundedRawCodedProofTraversal.
Import PABoundedRawCodedProofEndpoints.
Import PABoundedRawCodedProofRules.
Import PABoundedRawCodedProofAtomicAdequacy.
Import PABoundedRawCodedProofFormulaCoverage.
Import PABoundedRawCodedProofRuleCoverage.
Import PABoundedRawCodedFixedLevelTruthTotality.
Import PABoundedRawCodedFixedLevelTruthAdmissibleLowering.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedRestrictedProofAdmissibility.
Import PABoundedRawCodedCarrierRestrictedProofReroot.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessRecursiveChildInterface.

(** The constructor is decoded at [parentContext], but the selected endpoint
    is allowed to display a distinct [childContext].  All inherited proof
    certificates depend only on the selected child.  The endpoint-specific
    rule-validity and formula-bound facts are therefore derived at
    [childContext], with no equality premise between the two contexts. *)
Theorem raw_recursive_constructor_child_interface_at_endpoint_context :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    tail level root coverageBound parentContext a b c t
      child1 child2 child3 fields children child childContext
      childConclusion assignmentCode assignmentStep,
  RawCarrierRestrictedProofAt M tail level root ->
  RawProofAtomicallyAdequate M root ->
  RawProofFormulaCoverage M root coverageBound ->
  RawProofRuleCoverage M root ->
  RawProofConstructorCode M root parentContext a b c t
    child1 child2 child3 ->
  In (fields, children)
    (rawProofRecursiveCases M parentContext a b c t
      child1 child2 child3) ->
  root = rawListCode M fields ->
  In child children ->
  RawProofEndpoint M child childContext childConclusion ->
  RawCodedAssignmentDefinedThrough M
    assignmentCode assignmentStep coverageBound ->
  rawLt M child root /\
  RawCarrierRestrictedProofAt M tail level child /\
  RawProofAtomicallyAdequate M child /\
  RawProofFormulaCoverage M child coverageBound /\
  RawProofRuleCoverage M child /\
  RawProofRuleValid M child childContext childConclusion /\
  RawCodedFormulaAtomicallyAdequate M childConclusion /\
  RawCodedAssignmentDefinedThrough M
    assignmentCode assignmentStep childConclusion /\
  RawCarrierFormulaQuantifierBounded M level childConclusion.
Proof.
  intros M hPA tail level root coverageBound parentContext a b c t
    child1 child2 child3 fields children child childContext
    childConclusion assignmentCode assignmentStep
    hrestricted hatomic hformulaCoverage hruleCoverage
    hconstructor hentry hfields hchild hendpoint hassignmentCoverage.
  destruct (raw_proofAtomicallyAdequate_recursive_child M hPA
    root hatomic parentContext a b c t child1 child2 child3
    hconstructor _ _ hentry hfields child hchild) as
    [hchildAtomic hbelow].
  destruct (raw_proofFormulaCoverage_public_recursive_child M hPA
    root coverageBound hformulaCoverage parentContext a b c t
    child1 child2 child3 hconstructor _ _ hentry hfields child hchild)
    as [hchildFormulaCoverage _].
  destruct (raw_proofRuleCoverage_public_recursive_child M hPA
    root hruleCoverage parentContext a b c t child1 child2 child3
    hconstructor _ _ hentry hfields child hchild) as
    [hchildRuleCoverage _].
  pose proof
    (raw_carrierRestrictedProofAt_recursive_constructor_child
      M hPA tail level root parentContext a b c t child1 child2 child3
      fields children child hrestricted hconstructor hentry hfields hchild)
    as hchildRestricted.
  pose proof (raw_proofRuleCoverage_public_root_complete M hPA
    child hchildRuleCoverage childContext childConclusion hendpoint)
    as hchildRuleValid.
  pose proof (raw_proofAtomicallyAdequate_root_endpoint M hPA
    child hchildAtomic childContext childConclusion hendpoint) as
    [_ hchildConclusionAtomic].
  pose proof (raw_proofFormulaCoverage_public_root_endpoint M hPA
    child coverageBound hchildFormulaCoverage
    childContext childConclusion hendpoint) as [_ hbelowCoverage].
  pose proof (raw_codedAssignmentDefinedThrough_of_lt M hPA
    assignmentCode assignmentStep childConclusion coverageBound
    hbelowCoverage hassignmentCoverage) as hchildDefined.
  pose proof (raw_carrierRestrictedProof_endpoint_formula_bounded M hPA
    tail level child hchildRestricted childContext childConclusion hendpoint)
    as hchildBounded.
  repeat split; assumption.
Qed.

End
  PABoundedRawCodedRestrictedPADerivationSoundnessRecursiveChildEndpointContextInterface.
