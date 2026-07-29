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

End PABoundedRawCodedPALocalProofAndIntroduction.
