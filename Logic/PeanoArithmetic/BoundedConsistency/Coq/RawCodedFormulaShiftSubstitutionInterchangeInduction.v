(**
  Public formula shift/substitution interchange laws.

  This small final layer runs the represented induction supplied by
  [RawCodedFormulaShiftSubstitutionInterchangeInvariant] and exports the
  operation contract consumed by ternary template application.
*)

From Stdlib Require Import List Arith Lia.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAListCoding Require Import Representability ListFormulas.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelector CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawModelCompleteness PolynomialPairInjectivity RawCodedAdditionLaws
  RawCodedAssignment RawCodedSyntaxConstructors RawCodedFormulaOperations
  RawCodedFormulaShiftTreeRealization RawCodedFormulaShiftTotality
  RawCodedTemplateTernaryApplicationFunctionality
  RawCodedFormulaShiftSubstitutionInterchange
  RawCodedFormulaShiftSubstitutionInterchangeInvariant.

Module PABoundedRawCodedFormulaShiftSubstitutionInterchangeInduction.

Import PA.
Import PAListRepresentability.
Import PAListFormulas.
Import PAHierarchyReduction.
Import PACanonicalSelector.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawModelCompleteness.
Import PABoundedPolynomialPairInjectivity.
Import PABoundedRawCodedAdditionLaws.
Import PABoundedRawCodedAssignment.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedFormulaShiftTreeRealization.
Import PABoundedRawCodedFormulaShiftTotality.
Import PABoundedRawCodedTemplateTernaryApplicationFunctionality.
Import PABoundedRawCodedFormulaShiftSubstitutionInterchange.
Import PABoundedRawCodedFormulaShiftSubstitutionInterchangeInvariant.

Theorem raw_codedFormulaShiftSubstitutionInterchangeIndexBelow_all : forall
    (M : RawPAModel), RawPASatisfies M -> forall current,
  RawCodedFormulaShiftSubstitutionInterchangeIndexBelow M current.
Proof.
  intros M hPA.
  set (parameterEnv := fun _ : nat => raw_zero M).
  set (phi :=
    codedFormulaShiftSubstitutionInterchangeIndexBelowTermAt (tVar 0)).
  assert (hall : forall current,
      raw_formula_sat M (scons M current parameterEnv) phi).
  {
    apply (raw_definable_induction M hPA phi parameterEnv).
    - unfold phi.
      apply (proj2
        (raw_sat_codedFormulaShiftSubstitutionInterchangeIndexBelowTermAt_iff
          M (scons M (raw_zero M) parameterEnv) (tVar 0))).
      cbn [raw_term_eval scons].
      intros depth amount openingDepth replacement transformedReplacement
        sourceCode sourceStep targetCode targetStep depthCode depthStep
        bound rootIndex input transformedInput output transformedOutput
        hrootIndex.
      exfalso. exact (raw_not_lt_zero M hPA rootIndex hrootIndex).
    - intros current hcurrent.
      unfold phi in hcurrent |- *.
      pose proof (proj1
        (raw_sat_codedFormulaShiftSubstitutionInterchangeIndexBelowTermAt_iff
          M (scons M current parameterEnv) (tVar 0)) hcurrent) as hraw.
      apply (proj2
        (raw_sat_codedFormulaShiftSubstitutionInterchangeIndexBelowTermAt_iff
          M (scons M (raw_succ M current) parameterEnv) (tVar 0))).
      cbn [raw_term_eval scons] in hraw |- *.
      exact (raw_codedFormulaShiftSubstitutionInterchangeIndexBelow_succ
        M hPA current hraw).
  }
  intro current. unfold phi in hall.
  pose proof (proj1
    (raw_sat_codedFormulaShiftSubstitutionInterchangeIndexBelowTermAt_iff
      M (scons M current parameterEnv) (tVar 0)) (hall current)) as hraw.
  cbn [raw_term_eval scons] in hraw. exact hraw.
Qed.

Theorem raw_codedFormulaShift_substitution_interchange_at : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      depth amount openingDepth replacement transformedReplacement
      input transformedInput output transformedOutput,
  RawCodedTermShift M depth amount replacement transformedReplacement ->
  RawCodedFormulaShift M
    (raw_succ M (raw_add M depth openingDepth)) amount
    input transformedInput ->
  RawCodedFormulaOperation M (RawCodedFormulaSubstitutionAtom M)
    replacement openingDepth input output ->
  RawCodedFormulaOperation M (RawCodedFormulaSubstitutionAtom M)
    transformedReplacement openingDepth transformedInput transformedOutput ->
  RawCodedFormulaShift M (raw_add M depth openingDepth) amount
    output transformedOutput.
Proof.
  intros M hPA depth amount openingDepth replacement
    transformedReplacement input transformedInput output transformedOutput
    hreplacement
    (sourceCode & sourceStep & targetCode & targetStep &
     depthCode & depthStep & bound & rootIndex & htopTrace)
    hleft hright.
  exact (raw_codedFormulaShiftSubstitutionInterchangeIndexBelow_all M hPA
    (raw_succ M rootIndex)
    depth amount openingDepth replacement transformedReplacement
    sourceCode sourceStep targetCode targetStep depthCode depthStep
    bound rootIndex input transformedInput output transformedOutput
    (raw_assignment_lt_self_succ M hPA rootIndex)
    hreplacement htopTrace hleft hright).
Qed.

(** Exact contract used three times by the ternary application assembly. *)
Theorem raw_codedFormulaShiftAtom_singleSubstitutionInterchange : forall
    (M : RawPAModel), RawPASatisfies M -> forall amount,
  RawCodedFormulaOperationSingleSubstitutionInterchange M
    (RawCodedFormulaShiftAtom M) amount.
Proof.
  intros M hPA amount depth replacement transformedReplacement
    input transformedInput output transformedOutput
    hreplacement htop hleft hright.
  unfold RawCodedFormulaShiftAtom in hreplacement.
  unfold RawCodedFormulaShift in htop |- *.
  unfold RawCodedFormulaSingleSubstitution in hleft, hright.
  assert (htopZero : RawCodedFormulaShift M
      (raw_succ M (raw_add M depth (raw_zero M))) amount
      input transformedInput).
  {
    rewrite raw_add_zero_right by exact hPA. exact htop.
  }
  pose proof (raw_codedFormulaShift_substitution_interchange_at M hPA
    depth amount (raw_zero M) replacement transformedReplacement
    input transformedInput output transformedOutput
    hreplacement htopZero hleft hright) as hresult.
  rewrite raw_add_zero_right in hresult by exact hPA.
  exact hresult.
Qed.

End PABoundedRawCodedFormulaShiftSubstitutionInterchangeInduction.
