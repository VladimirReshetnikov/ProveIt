(**
  Constructor-generic recursive-child descent for restricted PA proofs.

  Every recursive natural-deduction rule needs the same represented facts
  about each child: the child is smaller, is still a carrier-restricted
  proof, inherits the three proof-wide certificates, has a valid endpoint,
  and its endpoint formula remains inside both the assignment and
  quantifier bounds.  Earlier rule-case developments established these
  facts separately.  This module packages the common argument at the exact
  constructor-table boundary, before specializing to any rule tag.

  The hypotheses deliberately expose the selected entry of
  [rawProofRecursiveCases].  A rule-specific client only has to compute its
  constructor code, its field list, and membership of the chosen child.
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
  RawCodedCarrierRestrictedProofReroot.

Import ListNotations.

Module
  PABoundedRawCodedRestrictedPADerivationSoundnessRecursiveChildInterface.

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

(** Reroot a carrier-restricted traversal at any child selected by the
    recursive-constructor table.  The same support code and support step are
    retained; only the traversal bound is weakened from [root + 1] to
    [child + 1]. *)
Theorem raw_carrierRestrictedProofAt_recursive_constructor_child : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    tail level root context a b c t child1 child2 child3 fields children child,
  RawCarrierRestrictedProofAt M tail level root ->
  RawProofConstructorCode M root context a b c t child1 child2 child3 ->
  In (fields, children)
    (rawProofRecursiveCases M context a b c t child1 child2 child3) ->
  root = rawListCode M fields ->
  In child children ->
  RawCarrierRestrictedProofAt M tail level child.
Proof.
  intros M hPA tail level root context a b c t child1 child2 child3
    fields children child
    (supportCode & supportStep & htraversal & hroot)
    hconstructor hentry hfields hchild.
  assert (hrootBelow : rawLt M root (raw_succ M root)).
  { apply raw_assignment_lt_self_succ. exact hPA. }
  pose proof (proj2 htraversal root hrootBelow hroot) as hrootNode.
  pose proof (raw_carrierRestrictedProofNodeAt_syntax M tail level
    root supportCode supportStep hrootNode) as hsyntax.
  pose proof (raw_proofSyntaxStep_closes_constructor M
    root supportCode supportStep hsyntax
    context a b c t child1 child2 child3 hconstructor) as hclosed.
  destruct (raw_proofConstructorClosed_recursive_child M
    root supportCode supportStep
    context a b c t child1 child2 child3 hclosed
    fields children hentry hfields child hchild)
    as [hchildSupported hchildBelow].
  exists supportCode, supportStep. split.
  - apply (raw_carrierRestrictedProofTraversalAt_weaken M hPA tail level
      (raw_succ M root) (raw_succ M child)
      supportCode supportStep htraversal).
    eapply raw_le_trans; [exact hPA | |].
    + exact (raw_succ_le_of_lt_pair M hPA child root hchildBelow).
    + exact (raw_lt_to_le M root (raw_succ M root) hrootBelow).
  - exact hchildSupported.
Qed.

(** Complete inherited interface for one recursive child.  In addition to
    the carrier reroot above, atomic adequacy, formula coverage, and rule
    coverage descend through the very same constructor-table entry.  The
    endpoint then turns those proof-wide certificates into the local facts
    used by every direct soundness rule case. *)
Theorem raw_recursive_constructor_child_interface : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    tail level root coverageBound context a b c t
      child1 child2 child3 fields children child childConclusion
      assignmentCode assignmentStep,
  RawCarrierRestrictedProofAt M tail level root ->
  RawProofAtomicallyAdequate M root ->
  RawProofFormulaCoverage M root coverageBound ->
  RawProofRuleCoverage M root ->
  RawProofConstructorCode M root context a b c t child1 child2 child3 ->
  In (fields, children)
    (rawProofRecursiveCases M context a b c t child1 child2 child3) ->
  root = rawListCode M fields ->
  In child children ->
  RawProofEndpoint M child context childConclusion ->
  RawCodedAssignmentDefinedThrough M
    assignmentCode assignmentStep coverageBound ->
  rawLt M child root /\
  RawCarrierRestrictedProofAt M tail level child /\
  RawProofAtomicallyAdequate M child /\
  RawProofFormulaCoverage M child coverageBound /\
  RawProofRuleCoverage M child /\
  RawProofRuleValid M child context childConclusion /\
  RawCodedFormulaAtomicallyAdequate M childConclusion /\
  RawCodedAssignmentDefinedThrough M
    assignmentCode assignmentStep childConclusion /\
  RawCarrierFormulaQuantifierBounded M level childConclusion.
Proof.
  intros M hPA tail level root coverageBound context a b c t
    child1 child2 child3 fields children child childConclusion
    assignmentCode assignmentStep
    hrestricted hatomic hformulaCoverage hruleCoverage
    hconstructor hentry hfields hchild hendpoint hassignmentCoverage.
  destruct (raw_proofAtomicallyAdequate_recursive_child M hPA
    root hatomic context a b c t child1 child2 child3
    hconstructor _ _ hentry hfields child hchild) as
    [hchildAtomic hbelow].
  destruct (raw_proofFormulaCoverage_public_recursive_child M hPA
    root coverageBound hformulaCoverage context a b c t
    child1 child2 child3 hconstructor _ _ hentry hfields child hchild) as
    [hchildFormulaCoverage _].
  destruct (raw_proofRuleCoverage_public_recursive_child M hPA
    root hruleCoverage context a b c t child1 child2 child3
    hconstructor _ _ hentry hfields child hchild) as
    [hchildRuleCoverage _].
  pose proof
    (raw_carrierRestrictedProofAt_recursive_constructor_child
      M hPA tail level root context a b c t child1 child2 child3
      fields children child hrestricted hconstructor hentry hfields hchild)
    as hchildRestricted.
  pose proof (raw_proofRuleCoverage_public_root_complete M hPA
    child hchildRuleCoverage context childConclusion hendpoint)
    as hchildRuleValid.
  pose proof (raw_proofAtomicallyAdequate_root_endpoint M hPA
    child hchildAtomic context childConclusion hendpoint) as
    [_ hchildConclusionAtomic].
  pose proof (raw_proofFormulaCoverage_public_root_endpoint M hPA
    child coverageBound hchildFormulaCoverage
    context childConclusion hendpoint) as [_ hbelowCoverage].
  pose proof (raw_codedAssignmentDefinedThrough_of_lt M hPA
    assignmentCode assignmentStep childConclusion coverageBound
    hbelowCoverage hassignmentCoverage) as hchildDefined.
  pose proof (raw_carrierRestrictedProof_endpoint_formula_bounded M hPA
    tail level child hchildRestricted context childConclusion hendpoint)
    as hchildBounded.
  repeat split; assumption.
Qed.

End
  PABoundedRawCodedRestrictedPADerivationSoundnessRecursiveChildInterface.
