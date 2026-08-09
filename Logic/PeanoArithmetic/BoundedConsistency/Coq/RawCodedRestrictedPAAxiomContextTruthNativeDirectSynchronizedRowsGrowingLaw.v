(**
  Closed logical law for the growing synchronized axiom-row compiler.

  The pointwise module needs one additional closed PA helper--universal
  assignment definedness--beneath all nineteen table witnesses.  This file
  re-closes those witnesses and abstracts that helper together with the five
  assumptions already used by the original row shape.  The resulting law is
  an empty-context template proof, ready to be compiled over any witnessed
  PA tail selected by the carrier-facing helper compilers.
*)

From Stdlib Require Import List.
From PAHF Require Import PAHF.
From BoundedPAConsistency Require Import
  RawCodedTemplateSyntax
  RawCodedTemplateNestedExistentialElimination
  RawCodedDynamicTruthSigmaOrFixedProductionTemplate
  RawCodedRestrictedPADerivationSoundnessDirectRuleDispatchFrontier
  RawCodedRestrictedPADerivationSoundnessDirectAssumptionCase
  RawCodedRestrictedPAAxiomContextTruthNativeDirectSynchronizedRowsWitnessShapes
  RawCodedRestrictedPAAxiomContextTruthNativeDirectSynchronizedRowsWitnessComposition
  RawCodedRestrictedPAAxiomContextTruthNativeDirectSynchronizedRowsPointwise.

Import ListNotations.

Module
  PABoundedRawCodedRestrictedPAAxiomContextTruthNativeDirectSynchronizedRowsGrowingLaw.

Import PA.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateNestedExistentialElimination.
Import PABoundedRawCodedDynamicTruthSigmaOrFixedProductionTemplate.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectRuleDispatchFrontier.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectAssumptionCase.
Import
  PABoundedRawCodedRestrictedPAAxiomContextTruthNativeDirectSynchronizedRowsWitnessShapes.
Import
  PABoundedRawCodedRestrictedPAAxiomContextTruthNativeDirectSynchronizedRowsWitnessComposition.
Import
  PABoundedRawCodedRestrictedPAAxiomContextTruthNativeDirectSynchronizedRowsPointwise.

(** ------------------------------------------------------------------
    Exact contexts while re-closing the nineteen witnesses. *)

Definition coqRestrictedPANativeAxiomRowsGrowingReadyContext :
    TemplateContext :=
  coqRestrictedPANativeAxiomRowsReadyContext ++
    [coqRestrictedPANativeAxiomRowsDefinedUniversalTemplate].

Definition coqRestrictedPANativeAxiomRowsGrowingAfterWitnessContext :
    TemplateContext :=
  coqRestrictedPANativeAxiomRowsAfterWitnessContext ++
    [rawCoqTemplateRenameN 9
      coqRestrictedPANativeAxiomRowsDefinedUniversalTemplate].

Definition coqRestrictedPANativeAxiomRowsGrowingAfterBoundedContext :
    TemplateContext :=
  coqRestrictedPANativeAxiomRowsAfterBoundedContext ++
    [rawCoqTemplateRenameN 14
      coqRestrictedPANativeAxiomRowsDefinedUniversalTemplate].

Lemma coqRestrictedPANativeAxiomRowsGrowingAfterWitness_context :
  coqRestrictedPANativeAxiomRowsGrowingAfterWitnessContext =
  rawCoqTemplateNestedExContext 9
    coqRestrictedPANativeAxiomRowsWitnessBodyTemplate
    [coqRestrictedPANativeAxiomRowsBoundedContextTemplate;
     coqRestrictedPANativeAxiomRowsAdequateContextTemplate;
     coqRestrictedPANativeAxiomRowsFieldTemplate;
     coqRestrictedPANativeAxiomRowsTransferSourceTemplate;
     coqRestrictedPANativeAxiomRowsDefinedUniversalTemplate].
Proof. vm_compute. reflexivity. Qed.

Lemma coqRestrictedPANativeAxiomRowsGrowingAfterBounded_context :
  coqRestrictedPANativeAxiomRowsGrowingAfterBoundedContext =
  rawCoqTemplateNestedExContext 4
    coqRestrictedPANativeAxiomRowsShiftedBoundedBodyTemplate
    (templateContextShift
      coqRestrictedPANativeAxiomRowsGrowingAfterWitnessContext).
Proof. vm_compute. reflexivity. Qed.

Lemma coqRestrictedPANativeAxiomRowsGrowingDeep_context :
  coqRestrictedPANativeAxiomRowsPointwiseDeepContext =
  rawCoqTemplateNestedExContext 4
    coqRestrictedPANativeAxiomRowsShiftedAdequateBodyTemplate
    (templateContextShift
      coqRestrictedPANativeAxiomRowsGrowingAfterBoundedContext).
Proof. vm_compute. reflexivity. Qed.

Lemma coqRestrictedPANativeAxiomRowsGrowing_shifted_bounded_in :
  In coqRestrictedPANativeAxiomRowsShiftedBoundedTemplate
    coqRestrictedPANativeAxiomRowsGrowingAfterWitnessContext.
Proof. vm_compute. tauto. Qed.

Lemma coqRestrictedPANativeAxiomRowsGrowing_shifted_adequate_in :
  In coqRestrictedPANativeAxiomRowsShiftedAdequateTemplate
    coqRestrictedPANativeAxiomRowsGrowingAfterBoundedContext.
Proof. vm_compute. tauto. Qed.

(** ------------------------------------------------------------------
    Introduce the five selected traversal witnesses around the pointwise
    proof and then eliminate all three table packages. *)

Definition coqRestrictedPANativeAxiomRowsGrowingFinalWitnessBodyRoot :=
  trpAss coqRestrictedPANativeAxiomRowsPointwiseDeepContext
    coqRestrictedPANativeAxiomRowsFinalWitnessBodyTemplate.

Definition coqRestrictedPANativeAxiomRowsGrowingAxiomTraversalPairRoot :=
  trpAndE2 coqRestrictedPANativeAxiomRowsPointwiseDeepContext
    coqRestrictedPANativeAxiomRowsWitnessTraversalTemplate
    (tfAnd coqRestrictedPANativeAxiomRowsAxiomTraversalTemplate
      coqRestrictedPANativeAxiomRowsWitnessedRowsTemplate)
    coqRestrictedPANativeAxiomRowsGrowingFinalWitnessBodyRoot.

Definition coqRestrictedPANativeAxiomRowsGrowingAxiomTraversalRoot :=
  trpAndE1 coqRestrictedPANativeAxiomRowsPointwiseDeepContext
    coqRestrictedPANativeAxiomRowsAxiomTraversalTemplate
    coqRestrictedPANativeAxiomRowsWitnessedRowsTemplate
    coqRestrictedPANativeAxiomRowsGrowingAxiomTraversalPairRoot.

Lemma coqRestrictedPANativeAxiomRowsGrowing_final_witness_body_in :
  In coqRestrictedPANativeAxiomRowsFinalWitnessBodyTemplate
    coqRestrictedPANativeAxiomRowsPointwiseDeepContext.
Proof. vm_compute. tauto. Qed.

Theorem coqRestrictedPANativeAxiomRowsGrowingAxiomTraversalRoot_derives :
  TemplateRawDerives coqRestrictedPANativeAxiomRowsPointwiseDeepContext
    coqRestrictedPANativeAxiomRowsAxiomTraversalTemplate
    coqRestrictedPANativeAxiomRowsGrowingAxiomTraversalRoot.
Proof.
  unfold coqRestrictedPANativeAxiomRowsGrowingAxiomTraversalRoot,
    coqRestrictedPANativeAxiomRowsGrowingAxiomTraversalPairRoot.
  apply coqRestrictedPADirect_templateRawDerives_andE1.
  apply coqRestrictedPADirect_templateRawDerives_andE2.
  rewrite <- coqRestrictedPANativeAxiomRowsFinalWitnessBody_shape.
  apply templateRawDerives_assumption.
  exact coqRestrictedPANativeAxiomRowsGrowing_final_witness_body_in.
Qed.

Definition coqRestrictedPANativeAxiomRowsGrowingOpenedTargetRoot :=
  trpAndI coqRestrictedPANativeAxiomRowsPointwiseDeepContext
    coqRestrictedPANativeAxiomRowsAxiomTraversalTemplate
    coqRestrictedPANativeAxiomRowsPointwiseTemplate
    coqRestrictedPANativeAxiomRowsGrowingAxiomTraversalRoot
    coqRestrictedPANativeAxiomRowsPointwiseRoot.

Theorem coqRestrictedPANativeAxiomRowsGrowingOpenedTargetRoot_derives :
  TemplateRawDerives coqRestrictedPANativeAxiomRowsPointwiseDeepContext
    coqRestrictedPANativeAxiomRowsOpenedTargetTemplate
    coqRestrictedPANativeAxiomRowsGrowingOpenedTargetRoot.
Proof.
  rewrite coqRestrictedPANativeAxiomRowsOpenedTarget_shape.
  unfold coqRestrictedPANativeAxiomRowsGrowingOpenedTargetRoot.
  apply coqRestrictedPANativeAxiomRows_templateRawDerives_andI.
  - exact coqRestrictedPANativeAxiomRowsGrowingAxiomTraversalRoot_derives.
  - exact coqRestrictedPANativeAxiomRowsPointwiseRoot_derives.
Qed.

Definition coqRestrictedPANativeAxiomRowsGrowingTargetRoot :=
  templateExistentialWitnessIntroductionFrom
    coqRestrictedPANativeAxiomRowsPointwiseDeepContext
    coqRestrictedPANativeAxiomRowsTargetWitnesses
    coqRestrictedPANativeAxiomRowsShiftedTargetTemplate
    coqRestrictedPANativeAxiomRowsGrowingOpenedTargetRoot.

Theorem coqRestrictedPANativeAxiomRowsGrowingTargetRoot_derives :
  TemplateRawDerives coqRestrictedPANativeAxiomRowsPointwiseDeepContext
    coqRestrictedPANativeAxiomRowsShiftedTargetTemplate
    coqRestrictedPANativeAxiomRowsGrowingTargetRoot.
Proof.
  unfold coqRestrictedPANativeAxiomRowsGrowingTargetRoot.
  apply templateExistentialWitnessIntroductionFrom_derives.
  rewrite coqRestrictedPANativeAxiomRowsTarget_total_open_ready.
  exact coqRestrictedPANativeAxiomRowsGrowingOpenedTargetRoot_derives.
Qed.

Definition coqRestrictedPANativeAxiomRowsGrowingAdequacyRoot :=
  rawCoqTemplateNestedExEliminationFromRoot 5
    coqRestrictedPANativeAxiomRowsShiftedAdequateBodyTemplate
    (rawCoqTemplateRenameN 14
      coqRestrictedPANativeAxiomRowsTargetTemplate)
    coqRestrictedPANativeAxiomRowsGrowingAfterBoundedContext
    (trpAss coqRestrictedPANativeAxiomRowsGrowingAfterBoundedContext
      coqRestrictedPANativeAxiomRowsShiftedAdequateTemplate)
    coqRestrictedPANativeAxiomRowsGrowingTargetRoot.

Definition coqRestrictedPANativeAxiomRowsGrowingBoundedRoot :=
  rawCoqTemplateNestedExEliminationFromRoot 5
    coqRestrictedPANativeAxiomRowsShiftedBoundedBodyTemplate
    (rawCoqTemplateRenameN 9
      coqRestrictedPANativeAxiomRowsTargetTemplate)
    coqRestrictedPANativeAxiomRowsGrowingAfterWitnessContext
    (trpAss coqRestrictedPANativeAxiomRowsGrowingAfterWitnessContext
      coqRestrictedPANativeAxiomRowsShiftedBoundedTemplate)
    coqRestrictedPANativeAxiomRowsGrowingAdequacyRoot.

Definition coqRestrictedPANativeAxiomRowsGrowingAllWitnessesRoot :=
  rawCoqTemplateNestedExEliminationRoot 9
    coqRestrictedPANativeAxiomRowsWitnessBodyTemplate
    coqRestrictedPANativeAxiomRowsTargetTemplate
    [coqRestrictedPANativeAxiomRowsBoundedContextTemplate;
     coqRestrictedPANativeAxiomRowsAdequateContextTemplate;
     coqRestrictedPANativeAxiomRowsFieldTemplate;
     coqRestrictedPANativeAxiomRowsTransferSourceTemplate;
     coqRestrictedPANativeAxiomRowsDefinedUniversalTemplate]
    coqRestrictedPANativeAxiomRowsGrowingBoundedRoot.

Theorem coqRestrictedPANativeAxiomRowsGrowingAllWitnessesRoot_derives :
  TemplateRawDerives coqRestrictedPANativeAxiomRowsGrowingReadyContext
    coqRestrictedPANativeAxiomRowsTargetTemplate
    coqRestrictedPANativeAxiomRowsGrowingAllWitnessesRoot.
Proof.
  unfold coqRestrictedPANativeAxiomRowsGrowingAllWitnessesRoot,
    coqRestrictedPANativeAxiomRowsGrowingReadyContext.
  apply rawCoqTemplateNestedExEliminationRoot_derives.
  unfold coqRestrictedPANativeAxiomRowsGrowingBoundedRoot.
  apply rawCoqTemplateNestedExEliminationFromRoot_derives.
  - rewrite <- coqRestrictedPANativeAxiomRowsShiftedBounded_shape.
    apply templateRawDerives_assumption.
    exact coqRestrictedPANativeAxiomRowsGrowing_shifted_bounded_in.
  - rewrite coqRestrictedPANativeAxiomRowsTarget_rename_9_5.
    unfold coqRestrictedPANativeAxiomRowsGrowingAdequacyRoot.
    apply rawCoqTemplateNestedExEliminationFromRoot_derives.
    + rewrite <- coqRestrictedPANativeAxiomRowsShiftedAdequate_shape.
      apply templateRawDerives_assumption.
      exact coqRestrictedPANativeAxiomRowsGrowing_shifted_adequate_in.
    + rewrite coqRestrictedPANativeAxiomRowsTarget_rename_14_5.
      rewrite <- coqRestrictedPANativeAxiomRowsGrowingDeep_context.
      exact coqRestrictedPANativeAxiomRowsGrowingTargetRoot_derives.
Qed.

(** ------------------------------------------------------------------
    Empty-context law consumed by the carrier wrapper. *)

Definition coqRestrictedPANativeAxiomRowsGrowingLawTemplate :
    TemplateFormula :=
  tfImp coqRestrictedPANativeAxiomRowsDefinedUniversalTemplate
    (tfImp coqRestrictedPANativeAxiomRowsTransferSourceTemplate
      (tfImp coqRestrictedPANativeAxiomRowsFieldTemplate
        (tfImp coqRestrictedPANativeAxiomRowsAdequateContextTemplate
          (tfImp coqRestrictedPANativeAxiomRowsBoundedContextTemplate
            (tfImp coqRestrictedPANativeAxiomRowsWitnessContextTemplate
              coqRestrictedPANativeAxiomRowsTargetTemplate))))).

Definition coqRestrictedPANativeAxiomRowsGrowingLawRoot : TemplateRawProof :=
  trpImpI [] coqRestrictedPANativeAxiomRowsDefinedUniversalTemplate
    (tfImp coqRestrictedPANativeAxiomRowsTransferSourceTemplate
      (tfImp coqRestrictedPANativeAxiomRowsFieldTemplate
        (tfImp coqRestrictedPANativeAxiomRowsAdequateContextTemplate
          (tfImp coqRestrictedPANativeAxiomRowsBoundedContextTemplate
            (tfImp coqRestrictedPANativeAxiomRowsWitnessContextTemplate
              coqRestrictedPANativeAxiomRowsTargetTemplate)))))
    (trpImpI [coqRestrictedPANativeAxiomRowsDefinedUniversalTemplate]
      coqRestrictedPANativeAxiomRowsTransferSourceTemplate
      (tfImp coqRestrictedPANativeAxiomRowsFieldTemplate
        (tfImp coqRestrictedPANativeAxiomRowsAdequateContextTemplate
          (tfImp coqRestrictedPANativeAxiomRowsBoundedContextTemplate
            (tfImp coqRestrictedPANativeAxiomRowsWitnessContextTemplate
              coqRestrictedPANativeAxiomRowsTargetTemplate))))
      (trpImpI
        [coqRestrictedPANativeAxiomRowsTransferSourceTemplate;
         coqRestrictedPANativeAxiomRowsDefinedUniversalTemplate]
        coqRestrictedPANativeAxiomRowsFieldTemplate
        (tfImp coqRestrictedPANativeAxiomRowsAdequateContextTemplate
          (tfImp coqRestrictedPANativeAxiomRowsBoundedContextTemplate
            (tfImp coqRestrictedPANativeAxiomRowsWitnessContextTemplate
              coqRestrictedPANativeAxiomRowsTargetTemplate)))
        (trpImpI
          [coqRestrictedPANativeAxiomRowsFieldTemplate;
           coqRestrictedPANativeAxiomRowsTransferSourceTemplate;
           coqRestrictedPANativeAxiomRowsDefinedUniversalTemplate]
          coqRestrictedPANativeAxiomRowsAdequateContextTemplate
          (tfImp coqRestrictedPANativeAxiomRowsBoundedContextTemplate
            (tfImp coqRestrictedPANativeAxiomRowsWitnessContextTemplate
              coqRestrictedPANativeAxiomRowsTargetTemplate))
          (trpImpI
            [coqRestrictedPANativeAxiomRowsAdequateContextTemplate;
             coqRestrictedPANativeAxiomRowsFieldTemplate;
             coqRestrictedPANativeAxiomRowsTransferSourceTemplate;
             coqRestrictedPANativeAxiomRowsDefinedUniversalTemplate]
            coqRestrictedPANativeAxiomRowsBoundedContextTemplate
            (tfImp coqRestrictedPANativeAxiomRowsWitnessContextTemplate
              coqRestrictedPANativeAxiomRowsTargetTemplate)
            (trpImpI
              [coqRestrictedPANativeAxiomRowsBoundedContextTemplate;
               coqRestrictedPANativeAxiomRowsAdequateContextTemplate;
               coqRestrictedPANativeAxiomRowsFieldTemplate;
               coqRestrictedPANativeAxiomRowsTransferSourceTemplate;
               coqRestrictedPANativeAxiomRowsDefinedUniversalTemplate]
              coqRestrictedPANativeAxiomRowsWitnessContextTemplate
              coqRestrictedPANativeAxiomRowsTargetTemplate
              coqRestrictedPANativeAxiomRowsGrowingAllWitnessesRoot))))).

Theorem coqRestrictedPANativeAxiomRowsGrowingLawRoot_derives :
  TemplateRawDerives [] coqRestrictedPANativeAxiomRowsGrowingLawTemplate
    coqRestrictedPANativeAxiomRowsGrowingLawRoot.
Proof.
  unfold coqRestrictedPANativeAxiomRowsGrowingLawRoot,
    coqRestrictedPANativeAxiomRowsGrowingLawTemplate.
  repeat apply coqRestrictedPADirect_templateRawDerives_impI.
  exact coqRestrictedPANativeAxiomRowsGrowingAllWitnessesRoot_derives.
Qed.

End
  PABoundedRawCodedRestrictedPAAxiomContextTruthNativeDirectSynchronizedRowsGrowingLaw.
