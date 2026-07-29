(** Conjunction projections in an arbitrary temporary proof context. *)

From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors RawCodedProofEndpoints
  RawCodedProofRuleCoverage RawCodedProofAndEConstructors
  RawCodedPALocalProofExistential.

Module PABoundedRawCodedPALocalProofConjunction.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedProofEndpoints.
Import PABoundedRawCodedProofRuleCoverage.
Import PABoundedRawCodedProofAndEConstructors.
Import PABoundedRawCodedPALocalProofExistential.

Theorem raw_codedPALocalProofOf_andE : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      projection context left right child,
  RawCodedPALocalProofOf M context
    (rawFormulaAndCode M left right) child ->
  RawCodedPALocalProofOf M context
    (rawAndProjectionConclusion M projection left right)
    (rawProofAndERoot M projection context left right child).
Proof.
  intros M hPA projection context left right child
    [hcoverage hendpoint].
  split.
  - exact (raw_proofAndE_ruleCoverage M hPA projection
      context left right child hcoverage hendpoint).
  - exact (raw_proofAndE_endpoint M
      projection context left right child).
Qed.

Corollary raw_codedPALocalProofOf_andE1 : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      context left right child,
  RawCodedPALocalProofOf M context
    (rawFormulaAndCode M left right) child ->
  RawCodedPALocalProofOf M context left
    (rawProofAndERoot M RawAndLeft context left right child).
Proof.
  intros M hPA context left right child hchild.
  exact (raw_codedPALocalProofOf_andE M hPA RawAndLeft
    context left right child hchild).
Qed.

Corollary raw_codedPALocalProofOf_andE2 : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      context left right child,
  RawCodedPALocalProofOf M context
    (rawFormulaAndCode M left right) child ->
  RawCodedPALocalProofOf M context right
    (rawProofAndERoot M RawAndRight context left right child).
Proof.
  intros M hPA context left right child hchild.
  exact (raw_codedPALocalProofOf_andE M hPA RawAndRight
    context left right child hchild).
Qed.

(** Two-step projections are deliberately existential in their proof root.
    Most clients care about the selected formula and should not have to repeat
    the implementation-specific nesting of the two [AndE] root constructors. *)
Corollary raw_codedPALocalProofOf_andE11 : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      context first second rest child,
  RawCodedPALocalProofOf M context
    (rawFormulaAndCode M (rawFormulaAndCode M first second) rest) child ->
  exists root, RawCodedPALocalProofOf M context first root.
Proof.
  intros M hPA context first second rest child hchild.
  pose proof (raw_codedPALocalProofOf_andE1 M hPA context
    (rawFormulaAndCode M first second) rest child hchild) as hpair.
  lazymatch type of hpair with
  | RawCodedPALocalProofOf _ _ _ ?pairRoot =>
      exists (rawProofAndERoot M RawAndLeft context first second pairRoot);
      exact (raw_codedPALocalProofOf_andE1 M hPA context
        first second pairRoot hpair)
  end.
Qed.

Corollary raw_codedPALocalProofOf_andE12 : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      context first second rest child,
  RawCodedPALocalProofOf M context
    (rawFormulaAndCode M (rawFormulaAndCode M first second) rest) child ->
  exists root, RawCodedPALocalProofOf M context second root.
Proof.
  intros M hPA context first second rest child hchild.
  pose proof (raw_codedPALocalProofOf_andE1 M hPA context
    (rawFormulaAndCode M first second) rest child hchild) as hpair.
  lazymatch type of hpair with
  | RawCodedPALocalProofOf _ _ _ ?pairRoot =>
      exists (rawProofAndERoot M RawAndRight context first second pairRoot);
      exact (raw_codedPALocalProofOf_andE2 M hPA context
        first second pairRoot hpair)
  end.
Qed.

Corollary raw_codedPALocalProofOf_andE21 : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      context first second third child,
  RawCodedPALocalProofOf M context
    (rawFormulaAndCode M first (rawFormulaAndCode M second third)) child ->
  exists root, RawCodedPALocalProofOf M context second root.
Proof.
  intros M hPA context first second third child hchild.
  pose proof (raw_codedPALocalProofOf_andE2 M hPA context
    first (rawFormulaAndCode M second third) child hchild) as hpair.
  lazymatch type of hpair with
  | RawCodedPALocalProofOf _ _ _ ?pairRoot =>
      exists (rawProofAndERoot M RawAndLeft context second third pairRoot);
      exact (raw_codedPALocalProofOf_andE1 M hPA context
        second third pairRoot hpair)
  end.
Qed.

Corollary raw_codedPALocalProofOf_andE22 : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      context first second third child,
  RawCodedPALocalProofOf M context
    (rawFormulaAndCode M first (rawFormulaAndCode M second third)) child ->
  exists root, RawCodedPALocalProofOf M context third root.
Proof.
  intros M hPA context first second third child hchild.
  pose proof (raw_codedPALocalProofOf_andE2 M hPA context
    first (rawFormulaAndCode M second third) child hchild) as hpair.
  lazymatch type of hpair with
  | RawCodedPALocalProofOf _ _ _ ?pairRoot =>
      exists (rawProofAndERoot M RawAndRight context second third pairRoot);
      exact (raw_codedPALocalProofOf_andE2 M hPA context
        second third pairRoot hpair)
  end.
Qed.

(** The path [left; right; left] occurs in constructor certificates whose
    first component has a head field followed by two auxiliary fields. *)
Corollary raw_codedPALocalProofOf_andE121 : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      context first second third rest child,
  RawCodedPALocalProofOf M context
    (rawFormulaAndCode M
      (rawFormulaAndCode M first
        (rawFormulaAndCode M second third)) rest) child ->
  exists root, RawCodedPALocalProofOf M context second root.
Proof.
  intros M hPA context first second third rest child hchild.
  pose proof (raw_codedPALocalProofOf_andE1 M hPA context
    (rawFormulaAndCode M first (rawFormulaAndCode M second third))
    rest child hchild) as hleft.
  lazymatch type of hleft with
  | RawCodedPALocalProofOf _ _ _ ?leftRoot =>
      exact (raw_codedPALocalProofOf_andE21 M hPA context
        first second third leftRoot hleft)
  end.
Qed.

End PABoundedRawCodedPALocalProofConjunction.
