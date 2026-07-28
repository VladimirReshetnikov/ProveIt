(**
  Implication introduction and disjunction rules in arbitrary coded contexts.

  The lower-level constructor modules prove coverage and endpoint correctness
  for each raw proof node.  Dynamic truth compilers normally manipulate the
  smaller [RawCodedPALocalProofOf] package, however, because their contexts
  contain temporary nonstandard assumptions rather than only witnessed PA
  axioms.  This module exposes the missing propositional constructors at that
  interface.

  No formula code is decoded and no context is changed implicitly.  In
  particular, the two case children of disjunction elimination must already
  live in the literal cons contexts required by the raw natural-deduction
  rule.  Context insertion, when needed, remains a separate explicit step.
*)

From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors RawCodedProofEndpoints
  RawCodedProofRuleCoverage RawCodedProofImpIConstructor
  RawCodedProofOrIConstructors RawCodedProofOrEConstructor
  RawCodedPALocalProofExistential.

Module PABoundedRawCodedPALocalProofPropositionalRules.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedProofEndpoints.
Import PABoundedRawCodedProofRuleCoverage.
Import PABoundedRawCodedProofImpIConstructor.
Import PABoundedRawCodedProofOrIConstructors.
Import PABoundedRawCodedProofOrEConstructor.
Import PABoundedRawCodedPALocalProofExistential.

(** Discharge the literal head assumption of a local child context. *)
Theorem raw_codedPALocalProofOf_impI : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      context antecedent consequent child,
  RawCodedPALocalProofOf M
    (rawListNode M antecedent context) consequent child ->
  RawCodedPALocalProofOf M context
    (rawFormulaImpCode M antecedent consequent)
    (rawProofImpIRoot M context antecedent consequent child).
Proof.
  intros M hPA context antecedent consequent child
    [hcoverage hendpoint].
  split.
  - exact (raw_proofImpI_ruleCoverage M hPA
      context antecedent consequent child hcoverage hendpoint).
  - exact (raw_proofImpI_endpoint M
      context antecedent consequent child).
Qed.

(** Inject either already-proved disjunct without inspecting its code. *)
Theorem raw_codedPALocalProofOf_orI : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      injection context left right child,
  RawCodedPALocalProofOf M context
    (rawOrInjectionPremise M injection left right) child ->
  RawCodedPALocalProofOf M context
    (rawFormulaOrCode M left right)
    (rawProofOrIRoot M injection context left right child).
Proof.
  intros M hPA injection context left right child
    [hcoverage hendpoint].
  split.
  - exact (raw_proofOrI_ruleCoverage M hPA
      injection context left right child hcoverage hendpoint).
  - exact (raw_proofOrI_endpoint M
      injection context left right child).
Qed.

Corollary raw_codedPALocalProofOf_orI1 : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      context left right child,
  RawCodedPALocalProofOf M context left child ->
  RawCodedPALocalProofOf M context
    (rawFormulaOrCode M left right)
    (rawProofOrIRoot M RawOrLeft context left right child).
Proof.
  intros M hPA context left right child hchild.
  exact (raw_codedPALocalProofOf_orI M hPA RawOrLeft
    context left right child hchild).
Qed.

Corollary raw_codedPALocalProofOf_orI2 : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      context left right child,
  RawCodedPALocalProofOf M context right child ->
  RawCodedPALocalProofOf M context
    (rawFormulaOrCode M left right)
    (rawProofOrIRoot M RawOrRight context left right child).
Proof.
  intros M hPA context left right child hchild.
  exact (raw_codedPALocalProofOf_orI M hPA RawOrRight
    context left right child hchild).
Qed.

(** Eliminate a disjunction when both case proofs share the same parent
    context after their respective branch has been consed at its head. *)
Theorem raw_codedPALocalProofOf_orE : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      context left right conclusion
      disjunctionChild leftChild rightChild,
  RawCodedPALocalProofOf M context
    (rawFormulaOrCode M left right) disjunctionChild ->
  RawCodedPALocalProofOf M
    (rawListNode M left context) conclusion leftChild ->
  RawCodedPALocalProofOf M
    (rawListNode M right context) conclusion rightChild ->
  RawCodedPALocalProofOf M context conclusion
    (rawProofOrERoot M context left right conclusion
      disjunctionChild leftChild rightChild).
Proof.
  intros M hPA context left right conclusion
    disjunctionChild leftChild rightChild
    [hdisjunctionCoverage hdisjunctionEndpoint]
    [hleftCoverage hleftEndpoint]
    [hrightCoverage hrightEndpoint].
  split.
  - exact (raw_proofOrE_ruleCoverage M hPA
      context left right conclusion
      disjunctionChild leftChild rightChild
      hdisjunctionCoverage hdisjunctionEndpoint
      hleftCoverage hleftEndpoint hrightCoverage hrightEndpoint).
  - exact (raw_proofOrE_endpoint M
      context left right conclusion
      disjunctionChild leftChild rightChild).
Qed.

End PABoundedRawCodedPALocalProofPropositionalRules.
