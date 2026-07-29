(** Conjunction introduction in an arbitrary model-coded proof context. *)

From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors RawCodedProofEndpoints
  RawCodedProofRuleCoverage RawCodedProofAndIConstructor
  RawCodedPALocalProofExistential.

Module PABoundedRawCodedPALocalProofAndIntroduction.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedProofEndpoints.
Import PABoundedRawCodedProofRuleCoverage.
Import PABoundedRawCodedProofAndIConstructor.
Import PABoundedRawCodedPALocalProofExistential.

(** Combine two already covered local proofs without imposing any standardness
    condition on their common context or formula codes. *)
Theorem raw_codedPALocalProofOf_andI : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      context left right leftChild rightChild,
  RawCodedPALocalProofOf M context left leftChild ->
  RawCodedPALocalProofOf M context right rightChild ->
  RawCodedPALocalProofOf M context
    (rawFormulaAndCode M left right)
    (rawProofAndIRoot M context left right leftChild rightChild).
Proof.
  intros M hPA context left right leftChild rightChild
    [hleftCoverage hleftEndpoint]
    [hrightCoverage hrightEndpoint].
  split.
  - exact (raw_proofAndI_ruleCoverage M hPA
      context left right leftChild rightChild
      hleftCoverage hleftEndpoint hrightCoverage hrightEndpoint).
  - exact (raw_proofAndI_endpoint M
      context left right leftChild rightChild).
Qed.

(** Assemble the right-associated seven-field records used by the fixed-level
    truth traversals.  The result hides the six constructor roots: clients
    should depend on the logical record shape, not on the implementation's
    particular nesting of [And-I] proof nodes.  No adequacy or realizability
    hypothesis is needed because all seven input proofs already live in the
    same literal context. *)
Theorem raw_codedPALocalProofOf_and7I : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      context a b c d f g h
      aRoot bRoot cRoot dRoot fRoot gRoot hRoot,
  RawCodedPALocalProofOf M context a aRoot ->
  RawCodedPALocalProofOf M context b bRoot ->
  RawCodedPALocalProofOf M context c cRoot ->
  RawCodedPALocalProofOf M context d dRoot ->
  RawCodedPALocalProofOf M context f fRoot ->
  RawCodedPALocalProofOf M context g gRoot ->
  RawCodedPALocalProofOf M context h hRoot ->
  exists root,
    RawCodedPALocalProofOf M context
      (rawFormulaAndCode M a
        (rawFormulaAndCode M b
          (rawFormulaAndCode M c
            (rawFormulaAndCode M d
              (rawFormulaAndCode M f
                (rawFormulaAndCode M g h)))))) root.
Proof.
  intros M hPA context a b c d f g h
    aRoot bRoot cRoot dRoot fRoot gRoot hRoot
    ha hb hc hd hf hg hh.
  pose proof (raw_codedPALocalProofOf_andI M hPA context
    g h gRoot hRoot hg hh) as hgh.
  lazymatch type of hgh with
  | RawCodedPALocalProofOf _ _ _ ?ghRoot =>
      pose proof (raw_codedPALocalProofOf_andI M hPA context
        f (rawFormulaAndCode M g h) fRoot ghRoot hf hgh) as hfgh
  end.
  lazymatch type of hfgh with
  | RawCodedPALocalProofOf _ _ _ ?fghRoot =>
      pose proof (raw_codedPALocalProofOf_andI M hPA context
        d (rawFormulaAndCode M f (rawFormulaAndCode M g h))
        dRoot fghRoot hd hfgh) as hdfgh
  end.
  lazymatch type of hdfgh with
  | RawCodedPALocalProofOf _ _ _ ?dfghRoot =>
      pose proof (raw_codedPALocalProofOf_andI M hPA context
        c (rawFormulaAndCode M d
          (rawFormulaAndCode M f (rawFormulaAndCode M g h)))
        cRoot dfghRoot hc hdfgh) as hcdfgh
  end.
  lazymatch type of hcdfgh with
  | RawCodedPALocalProofOf _ _ _ ?cdfghRoot =>
      pose proof (raw_codedPALocalProofOf_andI M hPA context
        b (rawFormulaAndCode M c
          (rawFormulaAndCode M d
            (rawFormulaAndCode M f (rawFormulaAndCode M g h))))
        bRoot cdfghRoot hb hcdfgh) as hbcdfgh
  end.
  lazymatch type of hbcdfgh with
  | RawCodedPALocalProofOf _ _ _ ?bcdfghRoot =>
      exists (rawProofAndIRoot M context a
        (rawFormulaAndCode M b
          (rawFormulaAndCode M c
            (rawFormulaAndCode M d
              (rawFormulaAndCode M f
                (rawFormulaAndCode M g h)))))
        aRoot bcdfghRoot);
      exact (raw_codedPALocalProofOf_andI M hPA context
        a (rawFormulaAndCode M b
          (rawFormulaAndCode M c
            (rawFormulaAndCode M d
              (rawFormulaAndCode M f
                (rawFormulaAndCode M g h)))))
        aRoot bcdfghRoot ha hbcdfgh)
  end.
Qed.

End PABoundedRawCodedPALocalProofAndIntroduction.
