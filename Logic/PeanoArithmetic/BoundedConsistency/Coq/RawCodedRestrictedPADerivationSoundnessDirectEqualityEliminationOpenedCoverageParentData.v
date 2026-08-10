(** Decode the common Eq-E parent once before descending to either child. *)

From Stdlib Require Import List.

From BoundedPAConsistency Require Import
  RawCodedRestrictedPADerivationSoundnessDirectEqualityEliminationOpenedCoverageValiditySupport.

Module
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectEqualityEliminationOpenedCoverageParentData.

Import ListNotations.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectEqualityEliminationOpenedCoverageValiditySupport.

(** The opened coverage law contributes eight local witnesses in front of the
    parent proof environment.  This spelling is shared by both child descents. *)
Definition rawEqualityEliminationOpenedShiftedVariables
    {M : RawPAModel} (variables : nat -> M) : nat -> M :=
  fun index => variables (S (index + 8)).

Record RawCoqRestrictedPAEqualityEliminationOpenedParentData
    (M : RawPAModel) (variables : nat -> M)
    (parameters : TemplateParameterName -> M) : Prop := {
  rawEqualityOpened_parentRestricted :
    RawCarrierRestrictedProofAt M
      (rawEqualityEliminationOpenedShiftedVariables variables)
      (parameters coqRestrictedPASoundnessLowerLevelParameterName)
      (variables 13);
  rawEqualityOpened_parentAtomic :
    RawProofAtomicallyAdequate M (variables 13);
  rawEqualityOpened_parentFormulaCoverage :
    RawProofFormulaCoverage M (variables 13) (variables 0);
  rawEqualityOpened_parentRuleCoverage :
    RawProofRuleCoverage M (variables 13);
  rawEqualityOpened_assignmentCoverage :
    RawCodedAssignmentDefinedThrough M
      (variables 10) (variables 9) (variables 0);
  rawEqualityOpened_code :
    variables 13 = rawProofEqElimRoot M
      (variables 8) (variables 7) (variables 6) (variables 5)
      (variables 3) (variables 2);
  rawEqualityOpened_constructor :
    RawProofConstructorCode M (variables 13)
      (variables 8) (variables 7) (variables 6) (variables 5)
      (raw_zero M) (variables 3) (variables 2) (raw_zero M);
  rawEqualityOpened_entry : In
    ([rawNumeralValue M 16; variables 8; variables 7; variables 6;
        variables 5; variables 3; variables 2],
      [variables 3; variables 2])
    (rawProofRecursiveCases M
      (variables 8) (variables 7) (variables 6) (variables 5)
      (raw_zero M) (variables 3) (variables 2) (raw_zero M));
  rawEqualityOpened_equalityEndpoint :
    RawProofEndpoint M (variables 3) (variables 8) (variables 4);
  rawEqualityOpened_motiveEndpoint :
    RawProofEndpoint M (variables 2) (variables 8) (variables 1)
}.

Arguments RawCoqRestrictedPAEqualityEliminationOpenedParentData
  M variables parameters : clear implicits.

(** The formula-coverage and admissibility premises are consumed by the
    reusable opened-parent extractor.  Only the five facts below are needed
    explicitly to reconstruct the tag-16 constructor and its endpoints. *)
Theorem raw_equalityElimination_openedParentData_of_semantic_premises : forall
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
      coqRestrictedPADirectEqualityEliminationCaseTemplate) ->
  RawCoqRestrictedPAEqualityEliminationOpenedParentData
    M variables parameters.
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
  rewrite coqRestrictedPADirectEqualityElimination_case_shape in hcase.
  cbn [rawTemplateFormulaSat] in hcase.
  destruct hcase as
    [hcode [_ [_ [hequalityEndpoint [_ [hmotiveEndpoint _]]]]]].

  unfold coqRestrictedPADirectEqualityEliminationCodeEqualityTemplate
    in hcode.
  rewrite rawTemplateFormulaSat_embedPA in hcode.
  cbn [raw_formula_sat raw_term_eval] in hcode.
  change (variables 13 = rawProofEqElimRoot M
    (variables 8) (variables 7) (variables 6) (variables 5)
    (variables 3) (variables 2)) in hcode.

  unfold coqRestrictedPADirectEqualityEliminationEqualityChildEndpointTemplate
    in hequalityEndpoint.
  rewrite rawTemplateFormulaSat_embedPA,
    raw_sat_proofEndpointTermAt_iff in hequalityEndpoint.
  cbn [raw_term_eval] in hequalityEndpoint.
  unfold coqRestrictedPADirectEqualityEliminationMotiveChildEndpointTemplate
    in hmotiveEndpoint.
  rewrite rawTemplateFormulaSat_embedPA,
    raw_sat_proofEndpointTermAt_iff in hmotiveEndpoint.
  cbn [raw_term_eval] in hmotiveEndpoint.

  assert (hconstructor : RawProofConstructorCode M (variables 13)
      (variables 8) (variables 7) (variables 6) (variables 5)
      (raw_zero M) (variables 3) (variables 2) (raw_zero M)).
  {
    rewrite hcode.
    apply raw_proofEqElimRoot_constructor.
  }
  assert (hentry : In
      ([rawNumeralValue M 16; variables 8; variables 7; variables 6;
          variables 5; variables 3; variables 2],
        [variables 3; variables 2])
      (rawProofRecursiveCases M
        (variables 8) (variables 7) (variables 6) (variables 5)
        (raw_zero M) (variables 3) (variables 2) (raw_zero M))).
  { unfold rawProofRecursiveCases. cbn. tauto. }

  constructor; assumption.
Qed.

End
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectEqualityEliminationOpenedCoverageParentData.
