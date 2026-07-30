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

(** A complete projection view of the right-associated seven-field records
    used by restricted-proof certificates and global truth traversals.  Each
    field stores an honest represented proof root; no semantic reading of the
    conjunction code is involved. *)
Record RawCodedPALocalProofAnd7FieldsAt
    (M : RawPAModel) (context a b c d f g h : M) : Prop := {
  rawCodedPALocalProofAnd7Fields_first : exists root,
    RawCodedPALocalProofOf M context a root;
  rawCodedPALocalProofAnd7Fields_second : exists root,
    RawCodedPALocalProofOf M context b root;
  rawCodedPALocalProofAnd7Fields_third : exists root,
    RawCodedPALocalProofOf M context c root;
  rawCodedPALocalProofAnd7Fields_fourth : exists root,
    RawCodedPALocalProofOf M context d root;
  rawCodedPALocalProofAnd7Fields_fifth : exists root,
    RawCodedPALocalProofOf M context f root;
  rawCodedPALocalProofAnd7Fields_sixth : exists root,
    RawCodedPALocalProofOf M context g root;
  rawCodedPALocalProofAnd7Fields_seventh : exists root,
    RawCodedPALocalProofOf M context h root
}.

Arguments RawCodedPALocalProofAnd7FieldsAt M context a b c d f g h
  : clear implicits.

(** Project all seven fields in one pass down the right-associated spine.
    Naming every intermediate tail root makes the exact proof-code ancestry
    visible while keeping clients independent of those implementation
    details. *)
Theorem raw_codedPALocalProofOf_and7E : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      context a b c d f g h sourceRoot,
  RawCodedPALocalProofOf M context
    (rawFormulaAndCode M a
      (rawFormulaAndCode M b
        (rawFormulaAndCode M c
          (rawFormulaAndCode M d
            (rawFormulaAndCode M f
              (rawFormulaAndCode M g h)))))) sourceRoot ->
  RawCodedPALocalProofAnd7FieldsAt M context a b c d f g h.
Proof.
  intros M hPA context a b c d f g h sourceRoot hsource.
  pose proof (raw_codedPALocalProofOf_andE1 M hPA context a
    (rawFormulaAndCode M b
      (rawFormulaAndCode M c
        (rawFormulaAndCode M d
          (rawFormulaAndCode M f (rawFormulaAndCode M g h)))))
    sourceRoot hsource) as ha.
  pose proof (raw_codedPALocalProofOf_andE2 M hPA context a
    (rawFormulaAndCode M b
      (rawFormulaAndCode M c
        (rawFormulaAndCode M d
          (rawFormulaAndCode M f (rawFormulaAndCode M g h)))))
    sourceRoot hsource) as htail1.
  lazymatch type of htail1 with
  | RawCodedPALocalProofOf _ _ _ ?tail1Root =>
      pose proof (raw_codedPALocalProofOf_andE1 M hPA context b
        (rawFormulaAndCode M c
          (rawFormulaAndCode M d
            (rawFormulaAndCode M f (rawFormulaAndCode M g h))))
        tail1Root htail1) as hb;
      pose proof (raw_codedPALocalProofOf_andE2 M hPA context b
        (rawFormulaAndCode M c
          (rawFormulaAndCode M d
            (rawFormulaAndCode M f (rawFormulaAndCode M g h))))
        tail1Root htail1) as htail2
  end.
  lazymatch type of htail2 with
  | RawCodedPALocalProofOf _ _ _ ?tail2Root =>
      pose proof (raw_codedPALocalProofOf_andE1 M hPA context c
        (rawFormulaAndCode M d
          (rawFormulaAndCode M f (rawFormulaAndCode M g h)))
        tail2Root htail2) as hc;
      pose proof (raw_codedPALocalProofOf_andE2 M hPA context c
        (rawFormulaAndCode M d
          (rawFormulaAndCode M f (rawFormulaAndCode M g h)))
        tail2Root htail2) as htail3
  end.
  lazymatch type of htail3 with
  | RawCodedPALocalProofOf _ _ _ ?tail3Root =>
      pose proof (raw_codedPALocalProofOf_andE1 M hPA context d
        (rawFormulaAndCode M f (rawFormulaAndCode M g h))
        tail3Root htail3) as hd;
      pose proof (raw_codedPALocalProofOf_andE2 M hPA context d
        (rawFormulaAndCode M f (rawFormulaAndCode M g h))
        tail3Root htail3) as htail4
  end.
  lazymatch type of htail4 with
  | RawCodedPALocalProofOf _ _ _ ?tail4Root =>
      pose proof (raw_codedPALocalProofOf_andE1 M hPA context f
        (rawFormulaAndCode M g h) tail4Root htail4) as hf;
      pose proof (raw_codedPALocalProofOf_andE2 M hPA context f
        (rawFormulaAndCode M g h) tail4Root htail4) as htail5
  end.
  lazymatch type of htail5 with
  | RawCodedPALocalProofOf _ _ _ ?tail5Root =>
      pose proof (raw_codedPALocalProofOf_andE1 M hPA context g h
        tail5Root htail5) as hg;
      pose proof (raw_codedPALocalProofOf_andE2 M hPA context g h
        tail5Root htail5) as hh
  end.
  constructor.
  - eexists. exact ha.
  - eexists. exact hb.
  - eexists. exact hc.
  - eexists. exact hd.
  - eexists. exact hf.
  - eexists. exact hg.
  - eexists. exact hh.
Qed.

End PABoundedRawCodedPALocalProofConjunction.
