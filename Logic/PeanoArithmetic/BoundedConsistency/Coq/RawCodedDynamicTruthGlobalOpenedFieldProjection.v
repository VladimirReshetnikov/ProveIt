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
  RawCodedPALocalProofComposition
  RawCodedPALocalProofExistentialEliminationChain
  RawCodedPALocalProofUniversalEliminationChain
  RawCodedPALocalProofConjunction
  RawCodedTemplateSyntax
  RawCodedTemplateProofCompiler
  RawCodedTemplateProofCompilerSelfShiftTail
  RawCodedFixedLevelTruthTraversal
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
Import PABoundedRawCodedPALocalProofComposition.
Import PABoundedRawCodedPALocalProofExistentialEliminationChain.
Import PABoundedRawCodedPALocalProofUniversalEliminationChain.
Import PABoundedRawCodedPALocalProofConjunction.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedTemplateProofCompilerSelfShiftTail.
Import PABoundedRawCodedFixedLevelTruthTraversal.
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

(** Open the five row binders at the root tuple carried by the ten global
    witnesses.  Binder order is index, mode, formula, assignment code, then
    assignment step; this is the reverse of their de Bruijn order in the row
    body. *)
Definition coqDynamicTruthGlobalOpenedRootRowReplacements
    (rootMode : nat) : list TemplateTerm :=
  [ ttVar 8;
    embedPATerm (Term.numeral rootMode);
    ttVar 10;
    ttVar 11;
    ttVar 12 ].

Definition coqDynamicTruthGlobalOpenedRootRowFormula
    (rootMode : nat) (localSigma localPi : formula) : TemplateFormula :=
  templateUniversalOpenManyOrBot
    (coqDynamicTruthGlobalOpenedRows localSigma localPi)
    (coqDynamicTruthGlobalOpenedRootRowReplacements rootMode).

Definition coqDynamicTruthGlobalOpenedRootRowChoice
    (rootMode : nat) (localSigma localPi : formula) : TemplateFormula :=
  templateImpConsequent (templateImpConsequent
    (coqDynamicTruthGlobalOpenedRootRowFormula
      rootMode localSigma localPi)).

Lemma coqDynamicTruthGlobalOpenedRootRowFormula_success : forall
    rootMode localSigma localPi,
  templateUniversalOpenMany
    (coqDynamicTruthGlobalOpenedRows localSigma localPi)
    (coqDynamicTruthGlobalOpenedRootRowReplacements rootMode) =
  Some (coqDynamicTruthGlobalOpenedRootRowFormula
    rootMode localSigma localPi).
Proof.
  intros. reflexivity.
Qed.

Lemma coqDynamicTruthGlobalOpenedRootRowFormula_imp2_shape : forall
    rootMode localSigma localPi,
  coqDynamicTruthGlobalOpenedRootRowFormula rootMode localSigma localPi =
  tfImp
    (templateImpAntecedent
      (coqDynamicTruthGlobalOpenedRootRowFormula
        rootMode localSigma localPi))
    (tfImp
      (templateImpAntecedent (templateImpConsequent
        (coqDynamicTruthGlobalOpenedRootRowFormula
          rootMode localSigma localPi)))
      (coqDynamicTruthGlobalOpenedRootRowChoice
        rootMode localSigma localPi)).
Proof.
  intros. reflexivity.
Qed.

(** The two opened antecedents are not merely equivalent to the stable
    traversal fields: they are definitionally the same templates. *)
Lemma coqDynamicTruthGlobalOpenedRootRowFormula_bound : forall
    rootMode localSigma localPi,
  templateImpAntecedent
    (coqDynamicTruthGlobalOpenedRootRowFormula
      rootMode localSigma localPi) =
  coqDynamicTruthGlobalOpenedRootBound.
Proof.
  intros. reflexivity.
Qed.

Lemma coqDynamicTruthGlobalOpenedRootRowFormula_lookup : forall
    rootMode localSigma localPi,
  rootMode = 0 \/ rootMode = 1 ->
  templateImpAntecedent (templateImpConsequent
    (coqDynamicTruthGlobalOpenedRootRowFormula
      rootMode localSigma localPi)) =
  coqDynamicTruthGlobalOpenedRootLookup rootMode.
Proof.
  intros rootMode localSigma localPi [-> | ->]; reflexivity.
Qed.

(** Consume fields five through seven to obtain the selected root-row choice
    in the unchanged deepest context.  All five [All-E] nodes and both
    [Imp-E] nodes are compiled by the generic finite-chain endpoint. *)
Theorem raw_codedPALocalProofOf_dynamicTruthGlobal_opened_root_row_choice :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M)
    witnessList baseContext rootMode localSigma localPi,
  RawCodedPAAxiomWitnessContext M witnessList baseContext ->
  rootMode = 0 \/ rootMode = 1 ->
  exists root,
    RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation baseContext
        (coqDynamicTruthGlobalExistentialDeepContext
          rootMode localSigma localPi))
      (rawTemplateFormula translation
        (coqDynamicTruthGlobalOpenedRootRowChoice
          rootMode localSigma localPi)) root.
Proof.
  intros M hPA translation witnessList baseContext rootMode
    localSigma localPi hwitnessed hrootMode.
  pose proof
    (raw_codedPALocalProofOf_dynamicTruthGlobal_opened_and7_fields
      M hPA translation witnessList baseContext rootMode
      localSigma localPi hwitnessed) as hfields.
  destruct hfields as
    [hmode hformula hassignmentCode hassignmentStep
      [boundRoot hbound] [lookupRoot hlookup] [rowsRoot hrows]].
  rewrite <- (coqDynamicTruthGlobalOpenedRootRowFormula_bound
    rootMode localSigma localPi) in hbound.
  rewrite <- (coqDynamicTruthGlobalOpenedRootRowFormula_lookup
    rootMode localSigma localPi hrootMode) in hlookup.
  exact
    (raw_codedPALocalProofOf_templateUniversalOpenMany_impE2
      M hPA translation
      (rawTemplateContextCodeOnTail translation baseContext
        (coqDynamicTruthGlobalExistentialDeepContext
          rootMode localSigma localPi))
      (coqDynamicTruthGlobalOpenedRows localSigma localPi)
      (coqDynamicTruthGlobalOpenedRootRowReplacements rootMode)
      (templateImpAntecedent
        (coqDynamicTruthGlobalOpenedRootRowFormula
          rootMode localSigma localPi))
      (templateImpAntecedent (templateImpConsequent
        (coqDynamicTruthGlobalOpenedRootRowFormula
          rootMode localSigma localPi)))
      (coqDynamicTruthGlobalOpenedRootRowChoice
        rootMode localSigma localPi)
      rowsRoot boundRoot lookupRoot
      (eq_trans
        (coqDynamicTruthGlobalOpenedRootRowFormula_success
          rootMode localSigma localPi)
        (f_equal (@Some TemplateFormula)
          (coqDynamicTruthGlobalOpenedRootRowFormula_imp2_shape
            rootMode localSigma localPi)))
      hrows hbound hlookup).
Qed.

End PABoundedRawCodedDynamicTruthGlobalOpenedFieldProjection.
