(**
  Structural compilation of dynamic-local admissibility.

  The native local field guards both decision and exclusivity by the
  right-associated conjunction

      atomic(formula) /\
        (assignment-defined(formula) /\ (Sigma-domain \/ Pi-domain)).

  Traversal clients obtain these three facts from different represented
  sources.  This module keeps that semantic separation visible and performs
  only the two conjunction-introduction steps needed to package them.  The
  context is completely arbitrary: no witnessed-tail, realizability, or
  standardness hypothesis is needed once the three local proofs exist.
*)

From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  CodedSyntax
  RawCodedAssignment
  RawCodedFixedLevelTruthTotality
  RawCodedSyntaxConstructors
  RawCodedProofAndIConstructor
  RawCodedPALocalProofExistential
  RawCodedPALocalProofAndIntroduction
  RawCodedDynamicTruthNativeLocalPositiveGraph.

Module PABoundedRawCodedDynamicTruthLocalAdmissibilityCompilation.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedCodedSyntax.
Import PABoundedRawCodedAssignment.
Import PABoundedRawCodedFixedLevelTruthTotality.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedProofAndIConstructor.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPALocalProofAndIntroduction.
Import PABoundedRawCodedDynamicTruthNativeLocalPositiveGraph.

(** Stable names for the two fixed formula codes in the admissibility
    guard.  These are transparent definitions, not additional witnesses. *)
Definition rawDynamicTruthLocalAtomicAdequacyCode
    (M : RawPAModel) : M :=
  rawNumeralValue M
    (formulaCode (codedFormulaAtomicallyAdequateTermAt (tVar 2))).

Definition rawDynamicTruthLocalAssignmentDefinedCode
    (M : RawPAModel) : M :=
  rawNumeralValue M
    (formulaCode
      (codedAssignmentDefinedThroughTermAt (tVar 1) (tVar 0) (tVar 2))).

Arguments rawDynamicTruthLocalAtomicAdequacyCode M : clear implicits.
Arguments rawDynamicTruthLocalAssignmentDefinedCode M : clear implicits.

(** Logical assembly does not depend on which free PA terms occupy the
    formula and assignment coordinates.  Exposing the two quoted leaf codes
    makes the conjunction compiler reusable after capture-avoiding
    instantiation beneath unrelated binders. *)
Definition rawDynamicTruthAdmissibleCodeOf
    (M : RawPAModel) (atomicCode assignmentCode sigmaDomain piDomain : M)
    : M :=
  rawFormulaAndCode M atomicCode
    (rawFormulaAndCode M assignmentCode
      (rawFormulaOrCode M sigmaDomain piDomain)).

Arguments rawDynamicTruthAdmissibleCodeOf
  M atomicCode assignmentCode sigmaDomain piDomain : clear implicits.

Record RawDynamicTruthAdmissibilityCodeComponentsAt
    (M : RawPAModel)
    (context atomicCode assignmentCode sigmaDomain piDomain : M) : Prop := {
  rawDynamicTruthAdmissibilityCodeComponents_atomic : exists root,
    RawCodedPALocalProofOf M context atomicCode root;
  rawDynamicTruthAdmissibilityCodeComponents_assignment : exists root,
    RawCodedPALocalProofOf M context assignmentCode root;
  rawDynamicTruthAdmissibilityCodeComponents_domain : exists root,
    RawCodedPALocalProofOf M context
      (rawFormulaOrCode M sigmaDomain piDomain) root
}.

Arguments RawDynamicTruthAdmissibilityCodeComponentsAt
  M context atomicCode assignmentCode sigmaDomain piDomain
  : clear implicits.

(** General conjunction assembly for already identified leaf codes. *)
Theorem raw_codedPALocalProofOf_dynamicTruthAdmissibleCodeOf_components :
  forall (M : RawPAModel), RawPASatisfies M -> forall
      context atomicCode assignmentCode sigmaDomain piDomain,
  RawDynamicTruthAdmissibilityCodeComponentsAt M context
    atomicCode assignmentCode sigmaDomain piDomain ->
  exists root,
    RawCodedPALocalProofOf M context
      (rawDynamicTruthAdmissibleCodeOf M
        atomicCode assignmentCode sigmaDomain piDomain) root.
Proof.
  intros M hPA context atomicCode assignmentCode sigmaDomain piDomain
    [[atomicRoot hatomic] [assignmentRoot hassignment]
      [domainRoot hdomain]].
  pose proof (raw_codedPALocalProofOf_andI M hPA context
    assignmentCode (rawFormulaOrCode M sigmaDomain piDomain)
    assignmentRoot domainRoot hassignment hdomain) as hassignmentAndDomain.
  lazymatch type of hassignmentAndDomain with
  | RawCodedPALocalProofOf _ _ _ ?assignmentAndDomainRoot =>
      pose proof (raw_codedPALocalProofOf_andI M hPA context
        atomicCode
        (rawFormulaAndCode M assignmentCode
          (rawFormulaOrCode M sigmaDomain piDomain))
        atomicRoot assignmentAndDomainRoot
        hatomic hassignmentAndDomain) as hadmissible;
      exists (rawProofAndIRoot M context atomicCode
        (rawFormulaAndCode M assignmentCode
          (rawFormulaOrCode M sigmaDomain piDomain))
        atomicRoot assignmentAndDomainRoot);
      exact hadmissible
  end.
Qed.

(** The independently produced represented roots.  Keeping this record in
    [Prop] permits callers to eliminate existential proof-code choices while
    constructing the final [Prop]-valued logical-roots package. *)
Record RawDynamicTruthLocalAdmissibilityComponentsAt
    (M : RawPAModel) (context sigmaDomain piDomain : M) : Prop := {
  rawDynamicTruthLocalAdmissibilityComponents_atomic : exists root,
    RawCodedPALocalProofOf M context
      (rawDynamicTruthLocalAtomicAdequacyCode M) root;
  rawDynamicTruthLocalAdmissibilityComponents_assignment : exists root,
    RawCodedPALocalProofOf M context
      (rawDynamicTruthLocalAssignmentDefinedCode M) root;
  rawDynamicTruthLocalAdmissibilityComponents_domain : exists root,
    RawCodedPALocalProofOf M context
      (rawFormulaOrCode M sigmaDomain piDomain) root
}.

Arguments RawDynamicTruthLocalAdmissibilityComponentsAt
  M context sigmaDomain piDomain : clear implicits.

(** Assemble the exact native admissibility code.  The only PA hypothesis is
    the one required by the generic represented [And-I] constructor. *)
Theorem raw_codedPALocalProofOf_dynamicTruthLocalAdmissible_of_components :
  forall (M : RawPAModel), RawPASatisfies M -> forall
      context sigmaDomain piDomain,
  RawDynamicTruthLocalAdmissibilityComponentsAt M context
    sigmaDomain piDomain ->
  exists root,
    RawCodedPALocalProofOf M context
      (rawDynamicTruthLocalAdmissibleCode M sigmaDomain piDomain) root.
Proof.
  intros M hPA context sigmaDomain piDomain
    [hatomic hassignment hdomain].
  change (exists root, RawCodedPALocalProofOf M context
    (rawDynamicTruthAdmissibleCodeOf M
      (rawDynamicTruthLocalAtomicAdequacyCode M)
      (rawDynamicTruthLocalAssignmentDefinedCode M)
      sigmaDomain piDomain) root).
  apply
    (raw_codedPALocalProofOf_dynamicTruthAdmissibleCodeOf_components
      M hPA context
      (rawDynamicTruthLocalAtomicAdequacyCode M)
      (rawDynamicTruthLocalAssignmentDefinedCode M)
      sigmaDomain piDomain).
  constructor; assumption.
Qed.

End PABoundedRawCodedDynamicTruthLocalAdmissibilityCompilation.
