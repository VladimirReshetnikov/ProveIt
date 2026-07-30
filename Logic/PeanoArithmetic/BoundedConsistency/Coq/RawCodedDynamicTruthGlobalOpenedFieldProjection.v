(**
  Project every field of an opened dynamic global traversal.

  Ten existential eliminations leave the traversal body as the head of the
  deepest eigenvariable context.  This module proves that syntactic fact and
  immediately turns the head assumption into seven represented conjunction
  projections.  Later row clients can therefore consume the root bound,
  selected-state lookup, and universal row law without rebuilding either an
  assumption leaf or the right-associated [And-E] spine.
*)

From Stdlib Require Import List.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedContextLists
  RawCodedRestrictedPAProof
  RawCodedProofAssumptionLeaf
  RawCodedPALocalProofWitnessedContextMerge
  RawCodedPALocalProofExistential
  RawCodedPALocalProofExistentialEliminationChain
  RawCodedPALocalProofConjunction
  RawCodedTemplateSyntax
  RawCodedTemplateProofCompiler
  RawCodedTemplateProofCompilerSelfShiftTail
  RawCodedDynamicTruthPairedGlobalSuccessorGraph
  RawCodedDynamicTruthPredecessorGlobalExistentialElimination.

Module PABoundedRawCodedDynamicTruthGlobalOpenedFieldProjection.

Import ListNotations.
Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedContextLists.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedProofAssumptionLeaf.
Import PABoundedRawCodedPALocalProofWitnessedContextMerge.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPALocalProofExistentialEliminationChain.
Import PABoundedRawCodedPALocalProofConjunction.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedTemplateProofCompilerSelfShiftTail.
Import PABoundedRawCodedDynamicTruthPairedGlobalSuccessorGraph.
Import
  PABoundedRawCodedDynamicTruthPredecessorGlobalExistentialElimination.

(** Named templates for the seven literal fields exposed after all ten
    traversal witnesses have been opened. *)
Definition coqDynamicTruthGlobalOpenedModeDefined : TemplateFormula :=
  embedPAFormula dynamicTruthGlobalModeDefinedFormula.

Definition coqDynamicTruthGlobalOpenedFormulaDefined : TemplateFormula :=
  embedPAFormula dynamicTruthGlobalFormulaDefinedFormula.

Definition coqDynamicTruthGlobalOpenedAssignmentCodeDefined
    : TemplateFormula :=
  embedPAFormula dynamicTruthGlobalAssignmentCodeDefinedFormula.

Definition coqDynamicTruthGlobalOpenedAssignmentStepDefined
    : TemplateFormula :=
  embedPAFormula dynamicTruthGlobalAssignmentStepDefinedFormula.

Definition coqDynamicTruthGlobalOpenedRootBound : TemplateFormula :=
  embedPAFormula dynamicTruthGlobalRootBoundFormula.

Definition coqDynamicTruthGlobalOpenedRootLookup
    (rootMode : nat) : TemplateFormula :=
  embedPAFormula
    (dynamicTruthGlobalRootLookupFormula (Term.numeral rootMode)).

Definition coqDynamicTruthGlobalOpenedRows
    (localSigma localPi : formula) : TemplateFormula :=
  embedPAFormula (dynamicTruthGlobalRowsFormula localSigma localPi).

Definition coqDynamicTruthGlobalOpenedTraversalBody
    (rootMode : nat) (localSigma localPi : formula) : TemplateFormula :=
  embedPAFormula
    (dynamicTruthGlobalTraversalBodyFormula (Term.numeral rootMode)
      localSigma localPi).

Lemma coqDynamicTruthGlobalOpenedTraversalBody_and7_shape : forall
    rootMode localSigma localPi,
  coqDynamicTruthGlobalOpenedTraversalBody rootMode localSigma localPi =
  tfAnd coqDynamicTruthGlobalOpenedModeDefined
    (tfAnd coqDynamicTruthGlobalOpenedFormulaDefined
      (tfAnd coqDynamicTruthGlobalOpenedAssignmentCodeDefined
        (tfAnd coqDynamicTruthGlobalOpenedAssignmentStepDefined
          (tfAnd coqDynamicTruthGlobalOpenedRootBound
            (tfAnd (coqDynamicTruthGlobalOpenedRootLookup rootMode)
              (coqDynamicTruthGlobalOpenedRows localSigma localPi)))))).
Proof.
  intros. reflexivity.
Qed.

(** The body at the end of the ten-binder spine is the literal traversal
    body, with no additional renaming. *)
Lemma coqDynamicTruthGlobalExistentialBodyMany_ten : forall
    rootMode localSigma localPi,
  templateExistentialBodyMany 10
    (coqDynamicTruthGlobalExistentialSource
      rootMode localSigma localPi) =
  Some (coqDynamicTruthGlobalOpenedTraversalBody
    rootMode localSigma localPi).
Proof.
  intros. reflexivity.
Qed.

(** More operationally, that body is the head assumption of the exact deep
    context computed by the elimination module. *)
Lemma coqDynamicTruthGlobalExistentialDeepContext_head : forall
    rootMode localSigma localPi,
  exists tail,
    coqDynamicTruthGlobalExistentialDeepContext
      rootMode localSigma localPi =
    coqDynamicTruthGlobalOpenedTraversalBody
      rootMode localSigma localPi :: tail.
Proof.
  intros. eexists. reflexivity.
Qed.

(** Produce all seven honest projections from the deep-context head.  The
    witness package is used only to establish realizability of the PA tail;
    the projections themselves are pure represented natural-deduction
    steps. *)
Theorem raw_codedPALocalProofOf_dynamicTruthGlobal_opened_and7_fields :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M)
    witnessList baseContext rootMode localSigma localPi,
  RawCodedPAAxiomWitnessContext M witnessList baseContext ->
  RawCodedPALocalProofAnd7FieldsAt M
    (rawTemplateContextCodeOnTail translation baseContext
      (coqDynamicTruthGlobalExistentialDeepContext
        rootMode localSigma localPi))
    (rawTemplateFormula translation
      coqDynamicTruthGlobalOpenedModeDefined)
    (rawTemplateFormula translation
      coqDynamicTruthGlobalOpenedFormulaDefined)
    (rawTemplateFormula translation
      coqDynamicTruthGlobalOpenedAssignmentCodeDefined)
    (rawTemplateFormula translation
      coqDynamicTruthGlobalOpenedAssignmentStepDefined)
    (rawTemplateFormula translation
      coqDynamicTruthGlobalOpenedRootBound)
    (rawTemplateFormula translation
      (coqDynamicTruthGlobalOpenedRootLookup rootMode))
    (rawTemplateFormula translation
      (coqDynamicTruthGlobalOpenedRows localSigma localPi)).
Proof.
  intros M hPA translation witnessList baseContext rootMode
    localSigma localPi hwitnessed.
  destruct
    (coqDynamicTruthGlobalExistentialDeepContext_head
      rootMode localSigma localPi) as [tail hdeep].
  assert (htail : RawContextListRealizable M
      (rawTemplateContextCodeOnTail translation baseContext tail)).
  {
    apply (raw_templateContextOnTail_realizable M hPA).
    exact (raw_codedPAAxiomWitnessContext_context_realizable M
      witnessList baseContext hwitnessed).
  }
  assert (hbody : RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation baseContext
        (coqDynamicTruthGlobalExistentialDeepContext
          rootMode localSigma localPi))
      (rawTemplateFormula translation
        (coqDynamicTruthGlobalOpenedTraversalBody
          rootMode localSigma localPi))
      (rawProofAssumptionRoot M
        (rawTemplateContextCodeOnTail translation baseContext
          (coqDynamicTruthGlobalExistentialDeepContext
            rootMode localSigma localPi))
        (rawTemplateFormula translation
          (coqDynamicTruthGlobalOpenedTraversalBody
            rootMode localSigma localPi)))).
  {
    rewrite hdeep. cbn [rawTemplateContextCodeOnTail].
    exact (raw_codedPALocalProofOf_assumption M hPA
      (rawTemplateContextCodeOnTail translation baseContext tail)
      (rawTemplateFormula translation
        (coqDynamicTruthGlobalOpenedTraversalBody
          rootMode localSigma localPi)) htail).
  }
  rewrite coqDynamicTruthGlobalOpenedTraversalBody_and7_shape in hbody.
  rewrite !rawTemplateFormula_and in hbody.
  lazymatch type of hbody with
  | RawCodedPALocalProofOf _ _ _ ?bodyRoot =>
      exact (raw_codedPALocalProofOf_and7E M hPA
        (rawTemplateContextCodeOnTail translation baseContext
          (coqDynamicTruthGlobalExistentialDeepContext
            rootMode localSigma localPi))
        (rawTemplateFormula translation
          coqDynamicTruthGlobalOpenedModeDefined)
        (rawTemplateFormula translation
          coqDynamicTruthGlobalOpenedFormulaDefined)
        (rawTemplateFormula translation
          coqDynamicTruthGlobalOpenedAssignmentCodeDefined)
        (rawTemplateFormula translation
          coqDynamicTruthGlobalOpenedAssignmentStepDefined)
        (rawTemplateFormula translation
          coqDynamicTruthGlobalOpenedRootBound)
        (rawTemplateFormula translation
          (coqDynamicTruthGlobalOpenedRootLookup rootMode))
        (rawTemplateFormula translation
          (coqDynamicTruthGlobalOpenedRows localSigma localPi))
        bodyRoot hbody)
  end.
Qed.

End PABoundedRawCodedDynamicTruthGlobalOpenedFieldProjection.
