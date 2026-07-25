(**
  Arbitrary-model totality of the dynamic-truth ternary application graph.

  The graph performs the three represented substitutions by the fixed
  variable codes [#6], [#4], and [#0].  Each is an ordinary quoted term and
  hence has a model-internal syntax certificate under the universally
  defined zero assignment.  The unconditional three-substitution theorem
  then supplies both intermediate codes, the output code, and atomic
  adequacy at every stage, even when the input code is nonstandard.
*)

From PAHF Require Import PAHF.
From FirstOrder Require Import Fol.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelector CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  CodedSyntax RawCodedSyntaxConstructors RawCodedAssignmentTotality
  RawCodedTermEvaluationRealization
  RawCodedFormulaOperations RawCodedFixedLevelTruthTotality
  RawCodedFormulaOperationsStandardRealization
  RawCodedProofAtomicAdequacyStandard
  RawCodedDynamicTruthTernaryApplicationGraph
  RawCodedTermOpeningAfterShiftSyntaxStability.

Module PABoundedRawCodedDynamicTruthTernaryApplicationTotality.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelector.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedCodedSyntax.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedAssignmentTotality.
Import PABoundedRawCodedTermEvaluationRealization.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedFixedLevelTruthTotality.
Import PABoundedRawCodedFormulaOperationsStandardRealization.
Import PABoundedRawCodedProofAtomicAdequacyStandard.
Import PABoundedRawCodedDynamicTruthTernaryApplicationGraph.
Import PABoundedRawCodedTermOpeningAfterShiftSyntaxStability.

(** The zero beta assignment is defined at every carrier bound, so it is a
    canonical assignment witness for each fixed quoted variable term. *)
Lemma raw_dynamicTruthApplication_fixedReplacement_syntax : forall
    (M : RawPAModel), RawPASatisfies M -> forall replacement,
  RawTermSyntaxRealizable M
    (rawNumeralValue M (termCode replacement))
    (raw_zero M) (raw_zero M).
Proof.
  intros M hPA replacement.
  rewrite <- (rawQuotedTermCode_standard M hPA replacement).
  apply (raw_quotedTerm_syntax_realizable_of_assignment M hPA
    replacement (raw_zero M) (raw_zero M)).
  exact (raw_codedZeroAssignment_defined_all M hPA
    (raw_succ M (rawQuotedTermCode M replacement))).
Qed.

(** This strengthened graph witness exposes the two intermediate formula
    codes and records adequacy after every substitution. *)
Definition RawDynamicTruthTernaryApplicationAdequateChain
    (M : RawPAModel) (input output : M) : Prop :=
  exists first second : M,
    RawCodedFormulaSingleSubstitution M
      (rawNumeralValue M
        (termCode dynamicTruthApplicationFirstReplacement))
      input first /\
    RawCodedFormulaAtomicallyAdequate M first /\
    RawCodedFormulaSingleSubstitution M
      (rawNumeralValue M
        (termCode dynamicTruthApplicationSecondReplacement))
      first second /\
    RawCodedFormulaAtomicallyAdequate M second /\
    RawCodedFormulaSingleSubstitution M
      (rawNumeralValue M
        (termCode dynamicTruthApplicationThirdReplacement))
      second output /\
    RawCodedFormulaAtomicallyAdequate M output.

Arguments RawDynamicTruthTernaryApplicationAdequateChain
  M input output : clear implicits.

Theorem raw_dynamicTruthTernaryApplication_exists_adequate : forall
    (M : RawPAModel), RawPASatisfies M -> forall input,
  RawCodedFormulaAtomicallyAdequate M input ->
  exists output,
    RawDynamicTruthTernaryApplicationAdequateChain M input output.
Proof.
  intros M hPA input hinput.
  pose proof
    (raw_dynamicTruthApplication_fixedReplacement_syntax M hPA
      dynamicTruthApplicationFirstReplacement) as hfirstReplacement.
  pose proof
    (raw_dynamicTruthApplication_fixedReplacement_syntax M hPA
      dynamicTruthApplicationSecondReplacement) as hsecondReplacement.
  pose proof
    (raw_dynamicTruthApplication_fixedReplacement_syntax M hPA
      dynamicTruthApplicationThirdReplacement) as hthirdReplacement.
  destruct (raw_codedFormulaSingleSubstitution_three_exists_total M hPA
    input hinput
    (rawNumeralValue M
      (termCode dynamicTruthApplicationFirstReplacement))
    (raw_zero M) (raw_zero M) hfirstReplacement
    (rawNumeralValue M
      (termCode dynamicTruthApplicationSecondReplacement))
    (raw_zero M) (raw_zero M) hsecondReplacement
    (rawNumeralValue M
      (termCode dynamicTruthApplicationThirdReplacement))
    (raw_zero M) (raw_zero M) hthirdReplacement) as
    (first & second & output & hfirst & hfirstAdequate &
     hsecond & hsecondAdequate & hthird & houtputAdequate).
  exists output, first, second.
  repeat split; assumption.
Qed.

Corollary raw_dynamicTruthTernaryApplication_total : forall
    (M : RawPAModel), RawPASatisfies M -> forall input,
  RawCodedFormulaAtomicallyAdequate M input ->
  exists output,
    RawDynamicTruthTernaryApplication M input output /\
    RawCodedFormulaAtomicallyAdequate M output.
Proof.
  intros M hPA input hinput.
  destruct (raw_dynamicTruthTernaryApplication_exists_adequate
    M hPA input hinput) as
    (output & first & second & hfirst & hfirstAdequate &
     hsecond & hsecondAdequate & hthird & houtputAdequate).
  exists output. split.
  - exists first, second. repeat split; assumption.
  - exact houtputAdequate.
Qed.

(** Exact output-first totality interface for the actual formula graph. *)
Definition RawDynamicTruthTernaryApplicationGraphTotalOnAdequate
    (M : RawPAModel) : Prop :=
  forall (tail : nat -> M) input,
    RawCodedFormulaAtomicallyAdequate M input ->
    exists output,
      raw_formula_sat M (scons M output (scons M input tail))
        dynamicTruthTernaryApplicationGraph /\
      RawCodedFormulaAtomicallyAdequate M output.

Arguments RawDynamicTruthTernaryApplicationGraphTotalOnAdequate M
  : clear implicits.

Theorem dynamicTruthTernaryApplicationGraph_raw_total_on_adequate : forall
    (M : RawPAModel), RawPASatisfies M ->
  RawDynamicTruthTernaryApplicationGraphTotalOnAdequate M.
Proof.
  intros M hPA tail input hinput.
  destruct (raw_dynamicTruthTernaryApplication_total M hPA input hinput)
    as [output [happlication houtput]].
  exists output. split; [|exact houtput].
  apply (proj2 (raw_sat_dynamicTruthTernaryApplicationGraph_iff
    M tail input output)).
  exact happlication.
Qed.

End PABoundedRawCodedDynamicTruthTernaryApplicationTotality.
