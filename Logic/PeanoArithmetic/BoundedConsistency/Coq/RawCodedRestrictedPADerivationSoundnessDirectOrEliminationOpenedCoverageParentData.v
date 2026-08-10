(** Decode the common Or-E parent once, before selecting a recursive child. *)

From Stdlib Require Import List.

From BoundedPAConsistency Require Import
  RawCodedRestrictedPADerivationSoundnessDirectOrEliminationOpenedCoverageValiditySupport.

Module
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrEliminationOpenedCoverageParentData.

Import ListNotations.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrEliminationOpenedCoverageValiditySupport.

Definition rawOrEliminationOpenedShiftedVariables
    {M : RawPAModel} (variables : nat -> M) : nat -> M :=
  fun index => variables (S (index + 8)).

Record RawCoqRestrictedPAOrEliminationOpenedParentData
    (M : RawPAModel) (variables : nat -> M)
    (parameters : TemplateParameterName -> M) : Prop := {
  rawOrOpened_parentRestricted :
    RawCarrierRestrictedProofAt M
      (rawOrEliminationOpenedShiftedVariables variables)
      (parameters coqRestrictedPASoundnessLowerLevelParameterName)
      (variables 13);
  rawOrOpened_parentAtomic :
    RawProofAtomicallyAdequate M (variables 13);
  rawOrOpened_parentFormulaCoverage :
    RawProofFormulaCoverage M (variables 13) (variables 0);
  rawOrOpened_parentRuleCoverage :
    RawProofRuleCoverage M (variables 13);
  rawOrOpened_assignmentCoverage :
    RawCodedAssignmentDefinedThrough M
      (variables 10) (variables 9) (variables 0);
  rawOrOpened_code :
    variables 13 = rawProofOrERoot M
      (variables 8) (variables 7) (variables 6) (variables 5)
      (variables 3) (variables 2) (variables 1);
  rawOrOpened_constructor :
    RawProofConstructorCode M (variables 13)
      (variables 8) (variables 7) (variables 6) (variables 5)
      (raw_zero M) (variables 3) (variables 2) (variables 1);
  rawOrOpened_entry : In
    ([rawNumeralValue M 10; variables 8; variables 7; variables 6;
        variables 5; variables 3; variables 2; variables 1],
      [variables 3; variables 2; variables 1])
    (rawProofRecursiveCases M
      (variables 8) (variables 7) (variables 6) (variables 5)
      (raw_zero M) (variables 3) (variables 2) (variables 1));
  rawOrOpened_disjunctionEndpoint :
    RawProofEndpoint M (variables 3) (variables 8) (variables 4);
  rawOrOpened_leftEndpoint :
    RawProofEndpoint M (variables 2)
      (rawListNode M (variables 7) (variables 8)) (variables 5);
  rawOrOpened_rightEndpoint :
    RawProofEndpoint M (variables 1)
      (rawListNode M (variables 6) (variables 8)) (variables 5)
}.

Arguments RawCoqRestrictedPAOrEliminationOpenedParentData
  M variables parameters : clear implicits.

Theorem raw_orElimination_openedParentData_of_semantic_premises : forall
    (M : RawPAModel), RawPASatisfies M -> forall variables parameters predicates,
  rawTemplateFormulaSat M variables parameters predicates
    coqRestrictedPADirectAndIntroductionOpenedRestrictedTemplate ->
  rawTemplateFormulaSat M variables parameters predicates
    coqRestrictedPADirectAndIntroductionOpenedAtomicTemplate ->
  rawTemplateFormulaSat M variables parameters predicates
    coqRestrictedPADirectAndIntroductionOpenedRuleCoverageTemplate ->
  rawTemplateFormulaSat M variables parameters predicates
    coqRestrictedPADirectAndIntroductionOpenedCommonCoverageTemplate ->
  rawTemplateFormulaSat M variables parameters predicates
    (templateFormulaRename S
      coqRestrictedPADirectOrEliminationCaseTemplate) ->
  RawCoqRestrictedPAOrEliminationOpenedParentData M variables parameters.
Proof.
  intros M hPA variables parameters predicates hrestricted hatomic
    hruleCoverage hcommonCoverage hcase.
  pose proof (raw_sameContextUnary_opened_parent_facts M variables
    parameters predicates hrestricted hatomic hruleCoverage
    hcommonCoverage) as hparent.
  destruct hparent as
    [hparentRestricted hparentAtomic hparentRuleCoverage
      hparentFormulaCoverage hassignmentCoverage].

  rewrite rawTemplateFormulaSat_rename in hcase.
  rewrite coqRestrictedPADirectOrElimination_case_shape in hcase.
  cbn [rawTemplateFormulaSat] in hcase.
  destruct hcase as
    [hcode [_ [_ [hdisjunctionEndpoint
      [hleftEndpoint [hrightEndpoint _]]]]]].
  unfold coqRestrictedPADirectOrEliminationCodeEqualityTemplate in hcode.
  rewrite rawTemplateFormulaSat_embedPA in hcode.
  cbn [raw_formula_sat raw_term_eval] in hcode.
  change (variables 13 = rawProofOrERoot M
    (variables 8) (variables 7) (variables 6) (variables 5)
    (variables 3) (variables 2) (variables 1)) in hcode.

  unfold coqRestrictedPADirectOrEliminationDisjunctionEndpointTemplate
    in hdisjunctionEndpoint.
  rewrite rawTemplateFormulaSat_embedPA,
    raw_sat_proofEndpointTermAt_iff in hdisjunctionEndpoint.
  cbn [raw_term_eval] in hdisjunctionEndpoint.
  unfold coqRestrictedPADirectOrEliminationLeftEndpointTemplate
    in hleftEndpoint.
  rewrite rawTemplateFormulaSat_embedPA,
    raw_sat_proofEndpointTermAt_iff in hleftEndpoint.
  cbn [raw_term_eval] in hleftEndpoint.
  unfold coqRestrictedPADirectOrEliminationRightEndpointTemplate
    in hrightEndpoint.
  rewrite rawTemplateFormulaSat_embedPA,
    raw_sat_proofEndpointTermAt_iff in hrightEndpoint.
  cbn [raw_term_eval] in hrightEndpoint.

  assert (hconstructor : RawProofConstructorCode M (variables 13)
      (variables 8) (variables 7) (variables 6) (variables 5)
      (raw_zero M) (variables 3) (variables 2) (variables 1)).
  {
    unfold RawProofConstructorCode. rewrite hcode.
    do 10 right. left. reflexivity.
  }
  assert (hentry : In
      ([rawNumeralValue M 10; variables 8; variables 7; variables 6;
          variables 5; variables 3; variables 2; variables 1],
        [variables 3; variables 2; variables 1])
      (rawProofRecursiveCases M
        (variables 8) (variables 7) (variables 6) (variables 5)
        (raw_zero M) (variables 3) (variables 2) (variables 1))).
  { unfold rawProofRecursiveCases. cbn. tauto. }

  constructor; assumption.
Qed.

End
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrEliminationOpenedCoverageParentData.
