(**
  Exact finite witness layout for native PA axiom-context truth.

  The carrier-facing traversal residual hides three independent table
  packages: nine witnesses for the synchronized axiom/witness lists, five
  for quantifier boundedness, and five for atomic adequacy.  Before building
  the represented proof tree it is useful to freeze the corresponding
  transparent template syntax and, in particular, the de Bruijn layout after
  all nineteen witnesses have been opened.

  This module contains no proof-producing premise.  Every theorem below is a
  computation on finite template syntax.  The important normalization is the
  last one: reusing the axiom traversal tuple from the nine-witness package
  opens the five witnesses of native context truth to exactly that traversal
  conjoined with its pointwise successor-Sigma obligation.
*)

From Stdlib Require Import List.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From BoundedPAConsistency Require Import
  RawCodedContextLists
  RawCodedAssignment
  RawCodedFixedLevelTruthTotality
  RawCodedProofAtomicAdequacy
  RawCodedPAAxiomWitness
  RawCodedDynamicTruthAxiomSoundnessBaseGraph
  RawCodedRestrictedPAConsistencyFormulaCode
  RawCodedRestrictedTargetTemplateContext
  RawCodedRestrictedPAProof
  RawCodedTemplateSyntax
  RawCodedPALocalProofExistentialIntroductionChain
  RawCodedRestrictedPAConsistencyFromUniversalSoundness
  RawCodedRestrictedPADerivationSoundnessDirectRuleDispatchFrontier
  RawCodedRestrictedPADerivationSoundnessAssumptionContextTruthExpansion
  RawCodedRestrictedPATemplateTernaryApplicationCompilation
  RawCodedContextMembershipTransferPA.

Import ListNotations.

Module
  PABoundedRawCodedRestrictedPAAxiomContextTruthNativeDirectSynchronizedRowsWitnessShapes.

Import PA.
Import PABoundedRawCodedContextLists.
Import PABoundedRawCodedAssignment.
Import PABoundedRawCodedFixedLevelTruthTotality.
Import PABoundedRawCodedProofAtomicAdequacy.
Import PABoundedRawCodedPAAxiomWitness.
Import PABoundedRawCodedDynamicTruthAxiomSoundnessBaseGraph.
Import PABoundedRawCodedRestrictedPAConsistencyFormulaCode.
Import PABoundedRawCodedRestrictedTargetTemplateContext.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedPALocalProofExistentialIntroductionChain.
Import PABoundedRawCodedRestrictedPAConsistencyFromUniversalSoundness.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectRuleDispatchFrontier.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessAssumptionContextTruthExpansion.
Import
  PABoundedRawCodedRestrictedPATemplateTernaryApplicationCompilation.
Import PABoundedRawCodedContextMembershipTransferPA.

(** ------------------------------------------------------------------
    The five formulas used by the purely logical row theorem. *)

Definition coqRestrictedPANativeAxiomRowsTransferSourceTemplate
    : TemplateFormula :=
  embedPAFormula contextListMemberTransferUniversalFormula.

Definition coqRestrictedPANativeAxiomRowsWitnessContextTemplate
    : TemplateFormula :=
  embedPAFormula
    (codedPAAxiomWitnessContextTermAt (tVar 1) (tVar 0)).

Definition coqRestrictedPANativeAxiomRowsBoundedContextTemplate
    : TemplateFormula :=
  restrictedTargetTemplateFormulaContext
    coqRestrictedPASoundnessLowerLevelTerm
    (restrictedTargetContextAllBoundedContext (tVar 0)).

Definition coqRestrictedPANativeAxiomRowsAdequateContextTemplate
    : TemplateFormula :=
  embedPAFormula (contextAllAtomicallyAdequateTermAt (tVar 0)).

(** The selected conclusion predicate ignores its two displayed hierarchy
    arguments.  Zeros make that irrelevance explicit and match the native
    context selector's pointwise Sigma leaf. *)
Definition coqRestrictedPANativeAxiomRowsSigmaLeafTemplate
    : TemplateFormula :=
  tfOpaque coqRestrictedPAConclusionTruthPredicateName
    [ttZero; ttZero; ttVar 0; ttZero; ttZero].

Definition coqRestrictedPANativeAxiomRowsRecognitionTemplate
    : TemplateFormula :=
  embedPAFormula (witnessedPAAxiomRecognitionTermAt (tVar 0)).

Definition coqRestrictedPANativeAxiomRowsAtomicTemplate
    : TemplateFormula :=
  embedPAFormula (codedFormulaAtomicallyAdequateTermAt (tVar 0)).

Definition coqRestrictedPANativeAxiomRowsDefinedTemplate
    : TemplateFormula :=
  embedPAFormula
    (codedAssignmentDefinedThroughTermAt tZero tZero (tVar 0)).

Definition coqRestrictedPANativeAxiomRowsDomainTemplate
    : TemplateFormula :=
  restrictedTargetTemplateFormulaContext
    coqRestrictedPASoundnessLowerLevelTerm
    (restrictedTargetFormulaQuantifierBoundedContext (tVar 0)).

(** Transparent view of the graph-selected axiom field.  A later carrier
    module must justify that the concrete shifted field has this code; that
    is precisely where canonical direct-input and conclusion-leaf coherence
    enter. *)
Definition coqRestrictedPANativeAxiomRowsFieldTemplate
    : TemplateFormula :=
  tfAll
    (tfImp
      (tfAnd coqRestrictedPANativeAxiomRowsRecognitionTemplate
        (tfAnd coqRestrictedPANativeAxiomRowsAtomicTemplate
          (tfAnd coqRestrictedPANativeAxiomRowsDefinedTemplate
            coqRestrictedPANativeAxiomRowsDomainTemplate)))
      coqRestrictedPANativeAxiomRowsSigmaLeafTemplate).

Definition coqRestrictedPANativeAxiomRowsTargetTemplate
    : TemplateFormula :=
  coqRestrictedPATemplateTernaryApplication
    coqRestrictedPADynamicContextPredicateTemplate
    ttZero ttZero (ttVar 0).

(** ------------------------------------------------------------------
    Package bodies and the exact nineteen-witness context. *)

Definition coqRestrictedPANativeAxiomRowsWitnessBodyTemplate
    : TemplateFormula :=
  match coqRestrictedPANativeAxiomRowsWitnessContextTemplate with
  | tfEx (tfEx (tfEx (tfEx (tfEx (tfEx (tfEx (tfEx (tfEx body)))))))) =>
      body
  | _ => tfBot
  end.

Definition coqRestrictedPANativeAxiomRowsBoundedBodyTemplate
    : TemplateFormula :=
  match coqRestrictedPANativeAxiomRowsBoundedContextTemplate with
  | tfEx (tfEx (tfEx (tfEx (tfEx body)))) => body
  | _ => tfBot
  end.

Definition coqRestrictedPANativeAxiomRowsAdequateBodyTemplate
    : TemplateFormula :=
  match coqRestrictedPANativeAxiomRowsAdequateContextTemplate with
  | tfEx (tfEx (tfEx (tfEx (tfEx body)))) => body
  | _ => tfBot
  end.

Lemma coqRestrictedPANativeAxiomRowsWitnessContext_shape :
  coqRestrictedPANativeAxiomRowsWitnessContextTemplate =
  rawCoqTemplateExN 9
    coqRestrictedPANativeAxiomRowsWitnessBodyTemplate.
Proof. vm_compute. reflexivity. Qed.

Lemma coqRestrictedPANativeAxiomRowsBoundedContext_shape :
  coqRestrictedPANativeAxiomRowsBoundedContextTemplate =
  rawCoqTemplateExN 5
    coqRestrictedPANativeAxiomRowsBoundedBodyTemplate.
Proof. vm_compute. reflexivity. Qed.

Lemma coqRestrictedPANativeAxiomRowsAdequateContext_shape :
  coqRestrictedPANativeAxiomRowsAdequateContextTemplate =
  rawCoqTemplateExN 5
    coqRestrictedPANativeAxiomRowsAdequateBodyTemplate.
Proof. vm_compute. reflexivity. Qed.

(** The implication-introduction order below will make the witnessed package
    the first assumption, followed by boundedness, adequacy, the selected
    axiom field, and finally the PA traversal-transfer source. *)
Definition coqRestrictedPANativeAxiomRowsReadyContext
    : TemplateContext :=
  [coqRestrictedPANativeAxiomRowsWitnessContextTemplate;
   coqRestrictedPANativeAxiomRowsBoundedContextTemplate;
   coqRestrictedPANativeAxiomRowsAdequateContextTemplate;
   coqRestrictedPANativeAxiomRowsFieldTemplate;
   coqRestrictedPANativeAxiomRowsTransferSourceTemplate].

Definition coqRestrictedPANativeAxiomRowsAfterWitnessContext
    : TemplateContext :=
  rawCoqTemplateNestedExContext 9
    coqRestrictedPANativeAxiomRowsWitnessBodyTemplate
    [coqRestrictedPANativeAxiomRowsBoundedContextTemplate;
     coqRestrictedPANativeAxiomRowsAdequateContextTemplate;
     coqRestrictedPANativeAxiomRowsFieldTemplate;
     coqRestrictedPANativeAxiomRowsTransferSourceTemplate].

Definition coqRestrictedPANativeAxiomRowsShiftedBoundedTemplate
    : TemplateFormula :=
  rawCoqTemplateRenameN 9
    coqRestrictedPANativeAxiomRowsBoundedContextTemplate.

Definition coqRestrictedPANativeAxiomRowsShiftedBoundedBodyTemplate
    : TemplateFormula :=
  match coqRestrictedPANativeAxiomRowsShiftedBoundedTemplate with
  | tfEx (tfEx (tfEx (tfEx (tfEx body)))) => body
  | _ => tfBot
  end.

(** [FromRoot] performs the first elimination explicitly, hence four rather
    than five remaining calls to [rawCoqTemplateNestedExContext]. *)
Definition coqRestrictedPANativeAxiomRowsAfterBoundedContext
    : TemplateContext :=
  rawCoqTemplateNestedExContext 4
    coqRestrictedPANativeAxiomRowsShiftedBoundedBodyTemplate
    (templateContextShift
      coqRestrictedPANativeAxiomRowsAfterWitnessContext).

Definition coqRestrictedPANativeAxiomRowsShiftedAdequateTemplate
    : TemplateFormula :=
  rawCoqTemplateRenameN 14
    coqRestrictedPANativeAxiomRowsAdequateContextTemplate.

Definition coqRestrictedPANativeAxiomRowsShiftedAdequateBodyTemplate
    : TemplateFormula :=
  match coqRestrictedPANativeAxiomRowsShiftedAdequateTemplate with
  | tfEx (tfEx (tfEx (tfEx (tfEx body)))) => body
  | _ => tfBot
  end.

Definition coqRestrictedPANativeAxiomRowsDeepContext
    : TemplateContext :=
  rawCoqTemplateNestedExContext 4
    coqRestrictedPANativeAxiomRowsShiftedAdequateBodyTemplate
    (templateContextShift
      coqRestrictedPANativeAxiomRowsAfterBoundedContext).

(** ------------------------------------------------------------------
    Deep package projections. *)

Definition coqRestrictedPANativeAxiomRowsFinalWitnessBodyTemplate
    : TemplateFormula :=
  rawCoqTemplateRenameN 10
    coqRestrictedPANativeAxiomRowsWitnessBodyTemplate.

Definition coqRestrictedPANativeAxiomRowsFinalBoundedBodyTemplate
    : TemplateFormula :=
  rawCoqTemplateRenameN 5
    coqRestrictedPANativeAxiomRowsShiftedBoundedBodyTemplate.

Definition coqRestrictedPANativeAxiomRowsFinalAdequateBodyTemplate
    : TemplateFormula :=
  coqRestrictedPANativeAxiomRowsShiftedAdequateBodyTemplate.

Definition coqRestrictedPANativeAxiomRowsWitnessTraversalTemplate
    : TemplateFormula :=
  match coqRestrictedPANativeAxiomRowsFinalWitnessBodyTemplate with
  | tfAnd traversal _ => traversal
  | _ => tfBot
  end.

Definition coqRestrictedPANativeAxiomRowsAxiomTraversalTemplate
    : TemplateFormula :=
  match coqRestrictedPANativeAxiomRowsFinalWitnessBodyTemplate with
  | tfAnd _ (tfAnd traversal _) => traversal
  | _ => tfBot
  end.

Definition coqRestrictedPANativeAxiomRowsWitnessedRowsTemplate
    : TemplateFormula :=
  match coqRestrictedPANativeAxiomRowsFinalWitnessBodyTemplate with
  | tfAnd _ (tfAnd _ rows) => rows
  | _ => tfBot
  end.

Definition coqRestrictedPANativeAxiomRowsBoundedTraversalTemplate
    : TemplateFormula :=
  match coqRestrictedPANativeAxiomRowsFinalBoundedBodyTemplate with
  | tfAnd traversal _ => traversal
  | _ => tfBot
  end.

Definition coqRestrictedPANativeAxiomRowsBoundedRowsTemplate
    : TemplateFormula :=
  match coqRestrictedPANativeAxiomRowsFinalBoundedBodyTemplate with
  | tfAnd _ rows => rows
  | _ => tfBot
  end.

Definition coqRestrictedPANativeAxiomRowsAdequateTraversalTemplate
    : TemplateFormula :=
  match coqRestrictedPANativeAxiomRowsFinalAdequateBodyTemplate with
  | tfAnd traversal _ => traversal
  | _ => tfBot
  end.

Definition coqRestrictedPANativeAxiomRowsAdequateRowsTemplate
    : TemplateFormula :=
  match coqRestrictedPANativeAxiomRowsFinalAdequateBodyTemplate with
  | tfAnd _ rows => rows
  | _ => tfBot
  end.

Lemma coqRestrictedPANativeAxiomRowsFinalWitnessBody_shape :
  coqRestrictedPANativeAxiomRowsFinalWitnessBodyTemplate =
  tfAnd coqRestrictedPANativeAxiomRowsWitnessTraversalTemplate
    (tfAnd coqRestrictedPANativeAxiomRowsAxiomTraversalTemplate
      coqRestrictedPANativeAxiomRowsWitnessedRowsTemplate).
Proof. vm_compute. reflexivity. Qed.

Lemma coqRestrictedPANativeAxiomRowsFinalBoundedBody_shape :
  coqRestrictedPANativeAxiomRowsFinalBoundedBodyTemplate =
  tfAnd coqRestrictedPANativeAxiomRowsBoundedTraversalTemplate
    coqRestrictedPANativeAxiomRowsBoundedRowsTemplate.
Proof. vm_compute. reflexivity. Qed.

Lemma coqRestrictedPANativeAxiomRowsFinalAdequateBody_shape :
  coqRestrictedPANativeAxiomRowsFinalAdequateBodyTemplate =
  tfAnd coqRestrictedPANativeAxiomRowsAdequateTraversalTemplate
    coqRestrictedPANativeAxiomRowsAdequateRowsTemplate.
Proof. vm_compute. reflexivity. Qed.

(** At the deepest scope the witness package occupies [#18..#10].  Its
    axiom traversal therefore supplies exactly the five witnesses displayed
    below: common bound, axiom tail code/step, and axiom head code/step. *)
Definition coqRestrictedPANativeAxiomRowsTargetWitnesses
    : list TemplateTerm :=
  [ttVar 18; ttVar 13; ttVar 12; ttVar 11; ttVar 10].

Definition coqRestrictedPANativeAxiomRowsShiftedTargetTemplate
    : TemplateFormula :=
  rawCoqTemplateRenameN 19
    coqRestrictedPANativeAxiomRowsTargetTemplate.

Definition coqRestrictedPANativeAxiomRowsOpenedTargetTemplate
    : TemplateFormula :=
  match templateExistentialOpenMany
      coqRestrictedPANativeAxiomRowsShiftedTargetTemplate
      coqRestrictedPANativeAxiomRowsTargetWitnesses with
  | Some target => target
  | None => tfBot
  end.

Definition coqRestrictedPANativeAxiomRowsPointwiseTemplate
    : TemplateFormula :=
  match coqRestrictedPANativeAxiomRowsOpenedTargetTemplate with
  | tfAnd _ pointwise => pointwise
  | _ => tfBot
  end.

Lemma coqRestrictedPANativeAxiomRowsTarget_open_ready :
  templateExistentialOpenMany
    coqRestrictedPANativeAxiomRowsShiftedTargetTemplate
    coqRestrictedPANativeAxiomRowsTargetWitnesses =
  Some coqRestrictedPANativeAxiomRowsOpenedTargetTemplate.
Proof. vm_compute. reflexivity. Qed.

Lemma coqRestrictedPANativeAxiomRowsOpenedTarget_shape :
  coqRestrictedPANativeAxiomRowsOpenedTargetTemplate =
  tfAnd coqRestrictedPANativeAxiomRowsAxiomTraversalTemplate
    coqRestrictedPANativeAxiomRowsPointwiseTemplate.
Proof. vm_compute. reflexivity. Qed.

(** The closed arithmetic transfer source and the closed axiom field survive
    all nineteen package binders at these exact inherited slots.  These
    membership facts are the inputs used by the forthcoming proof-tree
    compiler. *)
Lemma coqRestrictedPANativeAxiomRows_final_witness_body_in :
  In coqRestrictedPANativeAxiomRowsFinalWitnessBodyTemplate
    coqRestrictedPANativeAxiomRowsDeepContext.
Proof. vm_compute. tauto. Qed.

Lemma coqRestrictedPANativeAxiomRows_final_bounded_body_in :
  In coqRestrictedPANativeAxiomRowsFinalBoundedBodyTemplate
    coqRestrictedPANativeAxiomRowsDeepContext.
Proof. vm_compute. tauto. Qed.

Lemma coqRestrictedPANativeAxiomRows_final_adequate_body_in :
  In coqRestrictedPANativeAxiomRowsFinalAdequateBodyTemplate
    coqRestrictedPANativeAxiomRowsDeepContext.
Proof. vm_compute. tauto. Qed.

Lemma coqRestrictedPANativeAxiomRows_final_field_in :
  In (rawCoqTemplateRenameN 19
        coqRestrictedPANativeAxiomRowsFieldTemplate)
    coqRestrictedPANativeAxiomRowsDeepContext.
Proof. vm_compute. tauto. Qed.

Lemma coqRestrictedPANativeAxiomRows_final_transfer_source_in :
  In (rawCoqTemplateRenameN 19
        coqRestrictedPANativeAxiomRowsTransferSourceTemplate)
    coqRestrictedPANativeAxiomRowsDeepContext.
Proof. vm_compute. tauto. Qed.

End
  PABoundedRawCodedRestrictedPAAxiomContextTruthNativeDirectSynchronizedRowsWitnessShapes.
