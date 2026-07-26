(** Public opening/opening interchange obtained from represented induction. *)

From Stdlib Require Import Arith.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelector CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawModelCompleteness RawCodedAssignment RawCodedFormulaOperations
  RawCodedTermOpeningOpeningInterchange
  RawCodedTermOpeningOpeningInterchangeInvariant.

Module PABoundedRawCodedTermOpeningOpeningInterchangeInduction.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelector.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawModelCompleteness.
Import PABoundedRawCodedAssignment.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedTermOpeningOpeningInterchange.
Import PABoundedRawCodedTermOpeningOpeningInterchangeInvariant.

Theorem raw_codedTermOpeningOpeningInterchangeIndexBelow_all : forall
    (M : RawPAModel), RawPASatisfies M -> forall current,
  RawCodedTermOpeningOpeningInterchangeIndexBelow M current.
Proof.
  intros M hPA.
  set (parameterEnv := fun _ : nat => raw_zero M).
  set (phi :=
    codedTermOpeningOpeningInterchangeIndexBelowTermAt (tVar 0)).
  assert (hall : forall current,
      raw_formula_sat M (scons M current parameterEnv) phi).
  {
    apply (raw_definable_induction M hPA phi parameterEnv).
    - unfold phi.
      apply (proj2
        (raw_sat_codedTermOpeningOpeningInterchangeIndexBelowTermAt_iff M
          (scons M (raw_zero M) parameterEnv) (tVar 0))).
      cbn [raw_term_eval scons].
      intros depth openingDepth outerAtDepth outerAtSucc
        replacement transformedReplacement
        sourceCode sourceStep targetCode targetStep bound rootIndex
        input transformedInput output transformedOutput hrootIndex.
      exfalso. exact (raw_not_lt_zero M hPA rootIndex hrootIndex).
    - intros current hcurrent.
      unfold phi in hcurrent |- *.
      pose proof (proj1
        (raw_sat_codedTermOpeningOpeningInterchangeIndexBelowTermAt_iff M
          (scons M current parameterEnv) (tVar 0)) hcurrent) as hraw.
      apply (proj2
        (raw_sat_codedTermOpeningOpeningInterchangeIndexBelowTermAt_iff M
          (scons M (raw_succ M current) parameterEnv) (tVar 0))).
      cbn [raw_term_eval scons] in hraw |- *.
      exact (raw_codedTermOpeningOpeningInterchangeIndexBelow_succ
        M hPA current hraw).
  }
  intro current. unfold phi in hall.
  pose proof (proj1
    (raw_sat_codedTermOpeningOpeningInterchangeIndexBelowTermAt_iff M
      (scons M current parameterEnv) (tVar 0)) (hall current)) as hraw.
  cbn [raw_term_eval scons] in hraw. exact hraw.
Qed.

Theorem raw_codedTermOpening_opening_interchange_with_cancellation : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      depth openingDepth outerAtDepth outerAtSucc
      replacement transformedReplacement
      input transformedInput output transformedOutput,
  rawLe M openingDepth depth ->
  RawCodedTermOpening M depth outerAtDepth
    replacement transformedReplacement ->
  RawCodedTermOpening M openingDepth transformedReplacement
    outerAtSucc outerAtDepth ->
  RawCodedTermOpening M (raw_succ M depth) outerAtSucc
    input transformedInput ->
  RawCodedTermOpening M openingDepth replacement input output ->
  RawCodedTermOpening M openingDepth transformedReplacement
    transformedInput transformedOutput ->
  RawCodedTermOpening M depth outerAtDepth output transformedOutput.
Proof.
  intros M hPA depth openingDepth outerAtDepth outerAtSucc
    replacement transformedReplacement input transformedInput
    output transformedOutput hdepth hreplacement hcancellation
    (sourceCode & sourceStep & targetCode & targetStep &
     bound & rootIndex & htopTrace) hleft hright.
  exact (raw_codedTermOpeningOpeningInterchangeIndexBelow_all M hPA
    (raw_succ M rootIndex)
    depth openingDepth outerAtDepth outerAtSucc
    replacement transformedReplacement
    sourceCode sourceStep targetCode targetStep bound rootIndex
    input transformedInput output transformedOutput
    (raw_assignment_lt_self_succ M hPA rootIndex)
    hdepth hreplacement hcancellation htopTrace hleft hright).
Qed.

End PABoundedRawCodedTermOpeningOpeningInterchangeInduction.
