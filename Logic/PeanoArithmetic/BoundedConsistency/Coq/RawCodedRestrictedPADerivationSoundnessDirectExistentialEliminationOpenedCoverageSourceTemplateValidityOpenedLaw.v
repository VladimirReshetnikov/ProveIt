(**
  One opened arithmetic source for both recursive children of Ex-E.

  The existential child keeps the parent context, whereas the body child is
  checked in [body :: shift context].  The constructor-generic descent lemma
  previously identified those two contexts.  We first record the harmless
  generalization which separates the constructor's parent context from the
  endpoint context of the selected child, then instantiate it twice.

  The represented source exposes the common formula-coverage witness once
  and returns the two complete child interfaces as a conjunction.  Hence the
  two later recursive-law compilers start on one synchronized PA witness
  suffix rather than selecting unrelated arithmetic sources.
*)

From Stdlib Require Import List Lia.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAListCoding Require Import Representability ListFormulas.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelector CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawModelCompleteness
  RawCodedAssignment
  RawCodedSyntaxConstructors
  RawCodedFormulaOperations
  RawCodedProofConstructors
  RawCodedProofDescent
  RawCodedProofEndpoints
  RawCodedProofRules
  RawCodedProofAtomicAdequacy
  RawCodedProofFormulaCoverage
  RawCodedProofRuleCoverage
  RawCodedRestrictedPAProof
  RawCodedFixedLevelTruthTotality
  RawCodedRestrictedPAConsistencyFormulaCode
  RawCodedTemplateSyntax
  RawCodedTemplateSemantics
  RawCodedTemplateEmbeddedUniversalValidity
  RawCodedTemplateStructuralTranslation
  RawCodedTemplateStructuralPAAgreement
  RawCodedTemplateParameterAbstraction
  RawCodedTemplateDirectStructuralTranslation
  RawCodedRestrictedTargetTemplateContext
  RawCodedRestrictedTargetTemplateSemantics
  RawCodedCarrierRestrictedProofReroot
  RawCodedRestrictedPAConsistencyFromUniversalSoundness
  RawCodedRestrictedPADerivationSoundnessDirectAssumptionCase
  RawCodedRestrictedPADerivationSoundnessDirectAndIntroductionCase
  RawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftRecursiveChildCompilation
  RawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftDynamicRerootValidity
  RawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftOpenedCoverageValidity
  RawCodedRestrictedPADerivationSoundnessDirectAndIntroductionOpenedCoverageValidity
  RawCodedRestrictedPADerivationSoundnessRecursiveChildInterface
  RawCodedRestrictedPADerivationSoundnessRecursiveChildEndpointContextInterface
  RawCodedRestrictedPADerivationSoundnessSameContextUnaryChildInterfaceOpenedCoverageSource
  RawCodedProofExEConstructor
  RawCodedRestrictedPADerivationSoundnessDirectExistentialEliminationCase
  RawCodedRestrictedPADerivationSoundnessDirectExistentialEliminationOpenedCoverageDefinitions.

From BoundedPAConsistency Require Import
  RawCodedRestrictedPADerivationSoundnessDirectExistentialEliminationOpenedCoverageSourceTemplateValidityChildShapes
  RawCodedRestrictedPADerivationSoundnessDirectExistentialEliminationOpenedCoverageSourceTemplateValidityExistentialChildView
  RawCodedRestrictedPADerivationSoundnessDirectExistentialEliminationOpenedCoverageSourceTemplateValidityBodyChildView.

Import ListNotations.

Module
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectExistentialEliminationOpenedCoverageSourceTemplateValidityOpenedLaw.

Import PA.
Import PAListRepresentability.
Import PAListFormulas.
Import PAHierarchyReduction.
Import PACanonicalSelector.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawModelCompleteness.
Import PABoundedRawCodedAssignment.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedProofConstructors.
Import PABoundedRawCodedProofDescent.
Import PABoundedRawCodedProofEndpoints.
Import PABoundedRawCodedProofRules.
Import PABoundedRawCodedProofAtomicAdequacy.
Import PABoundedRawCodedProofFormulaCoverage.
Import PABoundedRawCodedProofRuleCoverage.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedFixedLevelTruthTotality.
Import PABoundedRawCodedRestrictedPAConsistencyFormulaCode.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateSemantics.
Import PABoundedRawCodedTemplateEmbeddedUniversalValidity.
Import PABoundedRawCodedTemplateStructuralTranslation.
Import PABoundedRawCodedTemplateStructuralPAAgreement.
Import PABoundedRawCodedTemplateParameterAbstraction.
Import PABoundedRawCodedTemplateDirectStructuralTranslation.
Import PABoundedRawCodedRestrictedTargetTemplateContext.
Import PABoundedRawCodedRestrictedTargetTemplateSemantics.
Import PABoundedRawCodedCarrierRestrictedProofReroot.
Import PABoundedRawCodedRestrictedPAConsistencyFromUniversalSoundness.
Import PABoundedRawCodedRestrictedPADerivationSoundnessDirectAssumptionCase.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndIntroductionCase.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftRecursiveChildCompilation.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftDynamicRerootValidity.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftOpenedCoverageValidity.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndIntroductionOpenedCoverageValidity.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessRecursiveChildInterface.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessRecursiveChildEndpointContextInterface.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessSameContextUnaryChildInterfaceOpenedCoverageSource.
Import PABoundedRawCodedProofExEConstructor.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectExistentialEliminationCase.
Export
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectExistentialEliminationOpenedCoverageDefinitions.


Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectExistentialEliminationOpenedCoverageSourceTemplateValidityChildShapes.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectExistentialEliminationOpenedCoverageSourceTemplateValidityExistentialChildView.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectExistentialEliminationOpenedCoverageSourceTemplateValidityBodyChildView.

(** ------------------------------------------------------------------
    Model validity and PA reification of the paired source. *)

Theorem raw_existentialElimination_openedCoverageLaw_valid : forall
    (M : RawPAModel), RawPASatisfies M ->
  forall variables parameters predicates,
  rawTemplateFormulaSat M variables parameters predicates
    coqRestrictedPADirectExistentialEliminationOpenedCoverageLawTemplate.
Proof.
  intros M hPA variables parameters predicates.
  unfold
    coqRestrictedPADirectExistentialEliminationOpenedCoverageLawTemplate.
  cbn [rawTemplateFormulaSat].
  intros hrestricted hatomic _ hruleCoverage _ hcommonCoverage hcase.
  pose proof (raw_sameContextUnary_opened_parent_facts M variables
    parameters predicates hrestricted hatomic hruleCoverage
    hcommonCoverage) as hparent.
  destruct hparent as
    [hparentRestricted hparentAtomic hparentRuleCoverage
      hparentFormulaCoverage hassignmentCoverage].

  rewrite rawTemplateFormulaSat_rename in hcase.
  rewrite coqRestrictedPADirectExistentialElimination_case_shape in hcase.
  cbn [rawTemplateFormulaSat] in hcase.
  destruct hcase as
    [hcode [_ [hformulaCode
      [hexistentialEndpoint [hcontextShift
        [hconclusionShift [hbodyEndpoint _]]]]]]].
  unfold coqRestrictedPADirectExistentialEliminationCodeEqualityTemplate
    in hcode.
  rewrite rawTemplateFormulaSat_embedPA in hcode.
  cbn [raw_formula_sat raw_term_eval] in hcode.
  change (variables 13 = rawProofExERoot M
    (variables 8) (variables 7) (variables 6)
    (variables 3) (variables 2)) in hcode.

  unfold
    coqRestrictedPADirectExistentialEliminationExistentialEndpointTemplate
    in hexistentialEndpoint.
  rewrite rawTemplateFormulaSat_embedPA,
    raw_sat_proofEndpointTermAt_iff in hexistentialEndpoint.
  cbn [raw_term_eval] in hexistentialEndpoint.
  unfold coqRestrictedPADirectExistentialEliminationBodyEndpointTemplate
    in hbodyEndpoint.
  rewrite rawTemplateFormulaSat_embedPA,
    raw_sat_proofEndpointTermAt_iff in hbodyEndpoint.
  cbn [raw_term_eval] in hbodyEndpoint.

  assert (hconstructor : RawProofConstructorCode M (variables 13)
      (variables 8) (variables 7) (variables 6)
      (raw_zero M) (raw_zero M) (variables 3) (variables 2)
      (raw_zero M)).
  {
    unfold RawProofConstructorCode. rewrite hcode.
    do 14 right. left. reflexivity.
  }
  assert (hentry : In
      ([rawNumeralValue M 14; variables 8; variables 7; variables 6;
          variables 3; variables 2], [variables 3; variables 2])
      (rawProofRecursiveCases M (variables 8) (variables 7) (variables 6)
        (raw_zero M) (raw_zero M) (variables 3) (variables 2)
        (raw_zero M))).
  { unfold rawProofRecursiveCases. cbn. tauto. }

  destruct (raw_recursive_constructor_child_interface_at_endpoint_context
    M hPA (fun index => variables (S (index + 8)))
    (parameters coqRestrictedPASoundnessLowerLevelParameterName)
    (variables 13) (variables 0) (variables 8) (variables 7)
    (variables 6) (raw_zero M) (raw_zero M)
    (variables 3) (variables 2) (raw_zero M)
    [rawNumeralValue M 14; variables 8; variables 7; variables 6;
      variables 3; variables 2]
    [variables 3; variables 2] (variables 3) (variables 8)
    (variables 1) (variables 10) (variables 9)
    hparentRestricted hparentAtomic hparentFormulaCoverage
    hparentRuleCoverage hconstructor hentry hcode
    (ltac:(left; reflexivity)) hexistentialEndpoint hassignmentCoverage)
    as [hexBelow [hexRestricted [hexAtomic [hexFormulaCoverage
      [hexRuleCoverage [hexRuleValid [hexConclusionAtomic
        [hexConclusionDefined hexConclusionBounded]]]]]]]].

  destruct (raw_recursive_constructor_child_interface_at_endpoint_context
    M hPA (fun index => variables (S (index + 8)))
    (parameters coqRestrictedPASoundnessLowerLevelParameterName)
    (variables 13) (variables 0) (variables 8) (variables 7)
    (variables 6) (raw_zero M) (raw_zero M)
    (variables 3) (variables 2) (raw_zero M)
    [rawNumeralValue M 14; variables 8; variables 7; variables 6;
      variables 3; variables 2]
    [variables 3; variables 2] (variables 2)
    (rawListNode M (variables 7) (variables 5))
    (variables 4) (variables 10) (variables 9)
    hparentRestricted hparentAtomic hparentFormulaCoverage
    hparentRuleCoverage hconstructor hentry hcode
    (ltac:(right; left; reflexivity)) hbodyEndpoint hassignmentCoverage)
    as [hbodyBelow [hbodyRestricted [hbodyAtomic [hbodyFormulaCoverage
      [hbodyRuleCoverage [hbodyRuleValid [hbodyConclusionAtomic
        [hbodyConclusionDefined hbodyConclusionBounded]]]]]]]].

  assert (hexSat :
      rawTemplateFormulaSat M variables parameters predicates
        (templateFormulaRename S
          coqRestrictedPADirectExistentialEliminationExistentialChildInterfaceTemplate)).
  {
    apply (proj2 (raw_exE_existential_child_interface_renamed_sat_iff
      M variables parameters predicates)).
    repeat split; try assumption.
    + exists (variables 0). exact hexFormulaCoverage.
    + exists (variables 0). split; assumption.
  }
  assert (hbodySat :
      rawTemplateFormulaSat M variables parameters predicates
        (templateFormulaRename S
          coqRestrictedPADirectExistentialEliminationBodyChildInterfaceTemplate)).
  {
    apply (proj2 (raw_exE_body_child_interface_renamed_sat_iff
      M variables parameters predicates)).
    repeat split; try assumption.
    + exists (variables 0). exact hbodyFormulaCoverage.
    + exists (variables 0). split; assumption.
  }
  (** As in the Or-E source, reduce only the outer renamed conjunction.
      Keeping the two already-certified child formulas opaque avoids a deep
      conversion between renamed syntax and a shifted environment. *)
  change
    (rawTemplateFormulaSat M variables parameters predicates
        (templateFormulaRename S
          coqRestrictedPADirectExistentialEliminationExistentialChildInterfaceTemplate) /\
      rawTemplateFormulaSat M variables parameters predicates
        (templateFormulaRename S
          coqRestrictedPADirectExistentialEliminationBodyChildInterfaceTemplate)).
  exact (conj hexSat hbodySat).
Qed.


End
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectExistentialEliminationOpenedCoverageSourceTemplateValidityOpenedLaw.
