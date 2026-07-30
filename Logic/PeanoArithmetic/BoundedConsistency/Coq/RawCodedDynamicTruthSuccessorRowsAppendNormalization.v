(**
  Normalize the native dynamic-truth successor rows for append traversal.

  The generalized append compiler accepts arbitrary opaque row templates,
  but its concrete equality branch still performs two purely syntactic
  operations: it replaces the four row-field parameters and later opens the
  row beneath thirteen de Bruijn slots.  Native Sigma/Pi successor rows use
  only level parameters zero and one, while their free indices are already
  below that scope.  This module proves those facts once for the relocated
  two-predicate spelling used by the shared direct translator.

  Scope is checked through the reflected Boolean predicate.  This keeps the
  kernel proof term compact even though each fixed row contains many quoted
  arithmetic subformulae.
*)

From BoundedPAConsistency Require Import
  RawCodedTemplateSyntax
  RawCodedTemplateRenamingSubstitution
  RawCodedPALocalProofEquality
  RawCodedTemplateTripleUniversalOpening
  RawCodedFourStateTableAppendRowLtSuccCases
  RawCodedDynamicTruthUniversalLeafSourceTemplate
  RawCodedDynamicTruthPiUniversalLeafSourceTemplate
  RawCodedRestrictedPADerivationSoundnessExtendedDirectInputs
  RawCodedFourStateTableAppendTemplateGlobalTraversalAssembly.

Module PABoundedRawCodedDynamicTruthSuccessorRowsAppendNormalization.

Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateRenamingSubstitution.
Import PABoundedRawCodedPALocalProofEquality.
Import PABoundedRawCodedTemplateTripleUniversalOpening.
Import PABoundedRawCodedDynamicTruthUniversalLeafSourceTemplate.
Import PABoundedRawCodedDynamicTruthPiUniversalLeafSourceTemplate.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessExtendedDirectInputs.
Import PABoundedRawCodedFourStateTableAppendRowLtSuccCases.
Import
  PABoundedRawCodedFourStateTableAppendTemplateGlobalTraversalAssembly.

Definition coqDynamicTruthSharedSigmaSuccessorRowTemplate : TemplateFormula :=
  coqDynamicTruthSigmaSuccessorRowTemplateAt
    coqRestrictedPALowerPiTruthPredicateName.

Definition coqDynamicTruthSharedPiSuccessorRowTemplate : TemplateFormula :=
  coqDynamicTruthPiSuccessorRowTemplateAt
    coqRestrictedPALowerSigmaTruthPredicateName.

Lemma coqDynamicTruthSharedSigmaSuccessorRowTemplate_scoped_13 :
  TemplateFormulaScoped 13
    coqDynamicTruthSharedSigmaSuccessorRowTemplate.
Proof.
  apply (proj1 (templateFormulaScopedBool_iff 13
    coqDynamicTruthSharedSigmaSuccessorRowTemplate)).
  vm_compute.
  reflexivity.
Qed.

Lemma coqDynamicTruthSharedPiSuccessorRowTemplate_scoped_13 :
  TemplateFormulaScoped 13
    coqDynamicTruthSharedPiSuccessorRowTemplate.
Proof.
  apply (proj1 (templateFormulaScopedBool_iff 13
    coqDynamicTruthSharedPiSuccessorRowTemplate)).
  vm_compute.
  reflexivity.
Qed.

(** Append replaces only named parameters 2--5.  The two native rows reserve
    names 0 and 1 for the lower and upper hierarchy numerals, hence the
    replacement is inert. *)
Lemma coqDynamicTruthSharedSigmaSuccessorRowTemplate_append_fields_inert :
  templateFormulaReplaceParametersDirect
      coqFourStateTableAppendConcreteRowFieldBindings
      coqDynamicTruthSharedSigmaSuccessorRowTemplate =
    coqDynamicTruthSharedSigmaSuccessorRowTemplate.
Proof. vm_compute. reflexivity. Qed.

Lemma coqDynamicTruthSharedPiSuccessorRowTemplate_append_fields_inert :
  templateFormulaReplaceParametersDirect
      coqFourStateTableAppendConcreteRowFieldBindings
      coqDynamicTruthSharedPiSuccessorRowTemplate =
    coqDynamicTruthSharedPiSuccessorRowTemplate.
Proof. vm_compute. reflexivity. Qed.

(** The concrete equality-branch production is therefore definitionally the
    production extracted from either generalized global source. *)
Theorem coqDynamicTruthSharedSuccessorRows_append_production : forall
    rootMode bound,
  coqFourStateTableAppendConcreteClosedRowProductionTemplate
      coqDynamicTruthSharedSigmaSuccessorRowTemplate
      coqDynamicTruthSharedPiSuccessorRowTemplate =
    coqFourStateTableAppendOpenedTemplateGlobalRowProduction
      rootMode
      coqDynamicTruthSharedSigmaSuccessorRowTemplate
      coqDynamicTruthSharedPiSuccessorRowTemplate bound.
Proof.
  intros rootMode bound.
  apply coqFourStateTableAppendTemplateClosedRowProduction_eq_opened.
  - exact coqDynamicTruthSharedSigmaSuccessorRowTemplate_scoped_13.
  - exact coqDynamicTruthSharedPiSuccessorRowTemplate_scoped_13.
  - exact
      coqDynamicTruthSharedSigmaSuccessorRowTemplate_append_fields_inert.
  - exact coqDynamicTruthSharedPiSuccessorRowTemplate_append_fields_inert.
Qed.

End PABoundedRawCodedDynamicTruthSuccessorRowsAppendNormalization.
