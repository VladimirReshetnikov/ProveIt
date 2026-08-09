(**
  Scope-correct seven-case boundary for the selected Sigma bottom law.

  The local Sigma constructor formulae are bodies below the eight local-row
  witnesses.  Except for the QF leaf, they still mention the five row fields
  and the eight global-traversal fields, and therefore are not ternary
  predicates.  Applying those open Ex8 sources directly at bottom/zero/zero
  loses ten de Bruijn slots.

  This module records the honest order of operations:

  1. apply the genuine mode-zero global Ex10 formula at bottom/zero/zero;
  2. open its ten traversal witnesses;
  3. open the five universally quantified row fields at the selected root;
  4. select the Sigma payload using the impossible [0 = 1] Pi tag;
  5. open the eight local Sigma witnesses; and
  6. expose the resulting right-associated Or7 and its seven leaves.

  The final interface deliberately leaves only the seven branch refutations
  as a residual.  No [RawCodedTernaryApplication] trace is requested for a
  local Ex8 branch.
*)

From Stdlib Require Import List.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedContextLists
  RawCodedRestrictedPAProof
  RawCodedSyntaxConstructors
  RawCodedFormulaOperations
  RawCodedFixedLevelTruthTotality
  RawCodedProofAssumptionLeaf
  RawCodedProofImpIConstructor
  RawCodedPAAxiomWitnessPrefix
  RawCodedPALocalProofExistential
  RawCodedPALocalProofExistentialEliminationChain
  RawCodedPALocalProofComposition
  RawCodedPALocalProofPropositionalRules
  RawCodedPALocalProofConjunction
  RawCodedPALocalProofWitnessedContextMerge
  RawCodedPALocalProofTaggedChoice
  RawCodedPALocalProofUniversalEliminationChain
  RawCodedPALocalProofFiniteDisjunction
  RawCodedPALocalProofFiniteDisjunctionDerivedCases
  RawCodedTemplateSyntax
  RawCodedTemplateProofCompiler
  RawCodedTemplateProofCompilerSelfShiftTail
  RawCodedTemplatePAEmbedding
  RawCodedTemplateFormulaAtomicAdequacy
  RawCodedTemplateLocalProofWitnessedTailTransport
  RawCodedTemplateTernaryApplication
  RawCodedRestrictedPATemplateTernaryApplicationCompilation
  RawCodedDynamicTruthSigmaSuccessorRowGraph
  RawCodedDynamicTruthSuccessorRowsAppendNormalization
  RawCodedDynamicTruthLocalCollisionMatrixAssembly
  RawCodedFourStateTableAppendGlobalTraversalAssembly
  RawCodedFourStateTableAppendRowLtSuccCases
  RawCodedDynamicTruthPredecessorGlobalExistentialElimination
  RawCodedDynamicTruthGlobalOpenedFieldProjection
  RawCodedDynamicTruthGlobalOpenedRowSelection
  RawCodedZeroOneDistinctnessProofCompilation
  RawCodedStandardFormulaScopeDecision.

Import ListNotations.

Module
  PABoundedRawCodedRestrictedPASelectedSigmaBottomGlobalOpenedSevenCaseBoundary.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedContextLists.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedFixedLevelTruthTotality.
Import PABoundedRawCodedProofAssumptionLeaf.
Import PABoundedRawCodedProofImpIConstructor.
Import PABoundedRawCodedPAAxiomWitnessPrefix.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPALocalProofExistentialEliminationChain.
Import PABoundedRawCodedPALocalProofComposition.
Import PABoundedRawCodedPALocalProofPropositionalRules.
Import PABoundedRawCodedPALocalProofConjunction.
Import PABoundedRawCodedPALocalProofWitnessedContextMerge.
Import PABoundedRawCodedPALocalProofTaggedChoice.
Import PABoundedRawCodedPALocalProofUniversalEliminationChain.
Import PABoundedRawCodedPALocalProofFiniteDisjunction.
Import PABoundedRawCodedPALocalProofFiniteDisjunctionDerivedCases.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedTemplateProofCompilerSelfShiftTail.
Import PABoundedRawCodedTemplatePAEmbedding.
Import PABoundedRawCodedTemplateFormulaAtomicAdequacy.
Import PABoundedRawCodedTemplateLocalProofWitnessedTailTransport.
Import PABoundedRawCodedTemplateTernaryApplication.
Import PABoundedRawCodedRestrictedPATemplateTernaryApplicationCompilation.
Import PABoundedRawCodedDynamicTruthSigmaSuccessorRowGraph.
Import PABoundedRawCodedDynamicTruthSuccessorRowsAppendNormalization.
Import PABoundedRawCodedDynamicTruthLocalCollisionMatrixAssembly.
Import PABoundedRawCodedFourStateTableAppendGlobalTraversalAssembly.
Import PABoundedRawCodedFourStateTableAppendRowLtSuccCases.
Import
  PABoundedRawCodedDynamicTruthPredecessorGlobalExistentialElimination.
Import PABoundedRawCodedDynamicTruthGlobalOpenedFieldProjection.
Import PABoundedRawCodedDynamicTruthGlobalOpenedRowSelection.
Import PABoundedRawCodedZeroOneDistinctnessProofCompilation.
Import PABoundedRawCodedStandardFormulaScopeDecision.

(** ------------------------------------------------------------------
    The genuine selected global application. *)

Definition coqRestrictedPASelectedSigmaBottomGlobalFirstArgument
    : TemplateTerm :=
  embedPATerm rawFormulaBotCodeTerm.

Definition coqRestrictedPASelectedSigmaBottomGlobalZeroArgument
    : TemplateTerm :=
  embedPATerm tZero.

Definition coqRestrictedPASelectedSigmaBottomGlobalSource
    (localSigma localPi : TemplateFormula) : TemplateFormula :=
  coqDynamicTruthGlobalExistentialSource 0 localSigma localPi.

Definition coqRestrictedPASelectedSigmaBottomAppliedGlobalSource
    (localSigma localPi : TemplateFormula) : TemplateFormula :=
  coqRestrictedPATemplateTernaryApplication
    (coqRestrictedPASelectedSigmaBottomGlobalSource localSigma localPi)
    coqRestrictedPASelectedSigmaBottomGlobalFirstArgument
    coqRestrictedPASelectedSigmaBottomGlobalZeroArgument
    coqRestrictedPASelectedSigmaBottomGlobalZeroArgument.

(** The represented five-operation trace is built for the *global* source.
    These two protected shifts are the only translation-specific premises. *)
Theorem raw_codedTemplateTernaryApplication_selectedSigmaBottom_global :
    forall (M : RawPAModel)
      (translation : RawCodedTemplateTranslation M)
      localSigma localPi,
  RawCodedTermShift M
    (raw_zero M) (rawNumeralValue M 2)
    (rawTemplateTerm translation
      coqRestrictedPASelectedSigmaBottomGlobalFirstArgument)
    (rawTemplateTerm translation
      (coqRestrictedPATemplateTernaryFirstLifted
        coqRestrictedPASelectedSigmaBottomGlobalFirstArgument)) ->
  RawCodedTermShift M
    (raw_zero M) (rawNumeralValue M 1)
    (rawTemplateTerm translation
      coqRestrictedPASelectedSigmaBottomGlobalZeroArgument)
    (rawTemplateTerm translation
      (coqRestrictedPATemplateTernarySecondLifted
        coqRestrictedPASelectedSigmaBottomGlobalZeroArgument)) ->
  RawCodedTernaryApplication M
    (rawTemplateFormula translation
      (coqRestrictedPASelectedSigmaBottomGlobalSource
        localSigma localPi))
    (rawTemplateTerm translation
      coqRestrictedPASelectedSigmaBottomGlobalFirstArgument)
    (rawTemplateTerm translation
      coqRestrictedPASelectedSigmaBottomGlobalZeroArgument)
    (rawTemplateTerm translation
      coqRestrictedPASelectedSigmaBottomGlobalZeroArgument)
    (rawTemplateFormula translation
      (coqRestrictedPASelectedSigmaBottomAppliedGlobalSource
        localSigma localPi)).
Proof.
  intros M translation localSigma localPi hfirst hsecond.
  exact
    (raw_codedTemplateTernaryApplication_trace_of_protected_shifts
      M translation
      (coqRestrictedPASelectedSigmaBottomGlobalSource localSigma localPi)
      coqRestrictedPASelectedSigmaBottomGlobalFirstArgument
      coqRestrictedPASelectedSigmaBottomGlobalZeroArgument
      coqRestrictedPASelectedSigmaBottomGlobalZeroArgument
      hfirst hsecond).
Qed.

(** ------------------------------------------------------------------
    The computed ten-witness context of the applied Ex10 source. *)

Definition coqRestrictedPASelectedSigmaBottomAppliedGlobalTraversalBody
    (localSigma localPi : TemplateFormula) : TemplateFormula :=
  match templateExistentialBodyMany 10
    (coqRestrictedPASelectedSigmaBottomAppliedGlobalSource
      localSigma localPi) with
  | Some body => body
  | None => tfBot
  end.

Lemma
    coqRestrictedPASelectedSigmaBottomAppliedGlobalTraversalBody_success :
  forall localSigma localPi,
  templateExistentialBodyMany 10
    (coqRestrictedPASelectedSigmaBottomAppliedGlobalSource
      localSigma localPi) =
  Some
    (coqRestrictedPASelectedSigmaBottomAppliedGlobalTraversalBody
      localSigma localPi).
Proof. intros. reflexivity. Qed.

Definition coqRestrictedPASelectedSigmaBottomAppliedGlobalDeepContextOn
    (localSigma localPi : TemplateFormula)
    (sourcePrefix : TemplateContext) : TemplateContext :=
  match templateExistentialEliminationContext 10
    (coqRestrictedPASelectedSigmaBottomAppliedGlobalSource
      localSigma localPi) sourcePrefix with
  | Some context => context
  | None => []
  end.

Lemma coqRestrictedPASelectedSigmaBottomAppliedGlobalDeepContextOn_success :
  forall localSigma localPi sourcePrefix,
  templateExistentialEliminationContext 10
    (coqRestrictedPASelectedSigmaBottomAppliedGlobalSource
      localSigma localPi) sourcePrefix =
  Some (coqRestrictedPASelectedSigmaBottomAppliedGlobalDeepContextOn
    localSigma localPi sourcePrefix).
Proof. intros. reflexivity. Qed.

Lemma coqRestrictedPASelectedSigmaBottomAppliedGlobalDeepContextOn_head :
  forall localSigma localPi sourcePrefix,
  exists tail,
    coqRestrictedPASelectedSigmaBottomAppliedGlobalDeepContextOn
      localSigma localPi sourcePrefix =
    coqRestrictedPASelectedSigmaBottomAppliedGlobalTraversalBody
      localSigma localPi :: tail.
Proof. intros. eexists. reflexivity. Qed.

(** The seven fields are named by total destructors.  This formulation keeps
    the definitions compact while the following shape lemma certifies that
    the applied body really is a right-associated And7. *)
Definition coqRestrictedPASelectedSigmaBottomAppliedGlobalModeDefined
    localSigma localPi : TemplateFormula :=
  templateAnd7First
    (coqRestrictedPASelectedSigmaBottomAppliedGlobalTraversalBody
      localSigma localPi).

Definition coqRestrictedPASelectedSigmaBottomAppliedGlobalFormulaDefined
    localSigma localPi : TemplateFormula :=
  templateAnd7Second
    (coqRestrictedPASelectedSigmaBottomAppliedGlobalTraversalBody
      localSigma localPi).

Definition
    coqRestrictedPASelectedSigmaBottomAppliedGlobalAssignmentCodeDefined
    localSigma localPi : TemplateFormula :=
  templateAnd7Third
    (coqRestrictedPASelectedSigmaBottomAppliedGlobalTraversalBody
      localSigma localPi).

Definition
    coqRestrictedPASelectedSigmaBottomAppliedGlobalAssignmentStepDefined
    localSigma localPi : TemplateFormula :=
  templateAnd7Fourth
    (coqRestrictedPASelectedSigmaBottomAppliedGlobalTraversalBody
      localSigma localPi).

Definition coqRestrictedPASelectedSigmaBottomAppliedGlobalRootBound
    localSigma localPi : TemplateFormula :=
  templateAnd7Fifth
    (coqRestrictedPASelectedSigmaBottomAppliedGlobalTraversalBody
      localSigma localPi).

Definition coqRestrictedPASelectedSigmaBottomAppliedGlobalRootLookup
    localSigma localPi : TemplateFormula :=
  templateAnd7Sixth
    (coqRestrictedPASelectedSigmaBottomAppliedGlobalTraversalBody
      localSigma localPi).

Definition coqRestrictedPASelectedSigmaBottomAppliedGlobalRows
    localSigma localPi : TemplateFormula :=
  templateAnd7Seventh
    (coqRestrictedPASelectedSigmaBottomAppliedGlobalTraversalBody
      localSigma localPi).

Lemma coqRestrictedPASelectedSigmaBottomAppliedGlobalTraversalBody_shape :
  forall localSigma localPi,
  coqRestrictedPASelectedSigmaBottomAppliedGlobalTraversalBody
      localSigma localPi =
  tfAnd
    (coqRestrictedPASelectedSigmaBottomAppliedGlobalModeDefined
      localSigma localPi)
    (tfAnd
      (coqRestrictedPASelectedSigmaBottomAppliedGlobalFormulaDefined
        localSigma localPi)
      (tfAnd
        (coqRestrictedPASelectedSigmaBottomAppliedGlobalAssignmentCodeDefined
          localSigma localPi)
        (tfAnd
          (coqRestrictedPASelectedSigmaBottomAppliedGlobalAssignmentStepDefined
            localSigma localPi)
          (tfAnd
            (coqRestrictedPASelectedSigmaBottomAppliedGlobalRootBound
              localSigma localPi)
            (tfAnd
              (coqRestrictedPASelectedSigmaBottomAppliedGlobalRootLookup
                localSigma localPi)
              (coqRestrictedPASelectedSigmaBottomAppliedGlobalRows
                localSigma localPi)))))).
Proof. intros. reflexivity. Qed.

Theorem
    raw_codedPALocalProofOf_selectedSigmaBottom_applied_global_fields :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M)
    witnessList baseContext sourcePrefix localSigma localPi,
  RawCodedPAAxiomWitnessContext M witnessList baseContext ->
  RawCodedPALocalProofAnd7FieldsAt M
    (rawTemplateContextCodeOnTail translation baseContext
      (coqRestrictedPASelectedSigmaBottomAppliedGlobalDeepContextOn
        localSigma localPi sourcePrefix))
    (rawTemplateFormula translation
      (coqRestrictedPASelectedSigmaBottomAppliedGlobalModeDefined
        localSigma localPi))
    (rawTemplateFormula translation
      (coqRestrictedPASelectedSigmaBottomAppliedGlobalFormulaDefined
        localSigma localPi))
    (rawTemplateFormula translation
      (coqRestrictedPASelectedSigmaBottomAppliedGlobalAssignmentCodeDefined
        localSigma localPi))
    (rawTemplateFormula translation
      (coqRestrictedPASelectedSigmaBottomAppliedGlobalAssignmentStepDefined
        localSigma localPi))
    (rawTemplateFormula translation
      (coqRestrictedPASelectedSigmaBottomAppliedGlobalRootBound
        localSigma localPi))
    (rawTemplateFormula translation
      (coqRestrictedPASelectedSigmaBottomAppliedGlobalRootLookup
        localSigma localPi))
    (rawTemplateFormula translation
      (coqRestrictedPASelectedSigmaBottomAppliedGlobalRows
        localSigma localPi)).
Proof.
  intros M hPA translation witnessList baseContext sourcePrefix
    localSigma localPi hwitnessed.
  destruct
    (coqRestrictedPASelectedSigmaBottomAppliedGlobalDeepContextOn_head
      localSigma localPi sourcePrefix) as [tail hdeep].
  assert (htail : RawContextListRealizable M
      (rawTemplateContextCodeOnTail translation baseContext tail)).
  {
    apply (raw_templateContextOnTail_realizable M hPA).
    exact (raw_codedPAAxiomWitnessContext_context_realizable M
      witnessList baseContext hwitnessed).
  }
  assert (hbody : RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation baseContext
        (coqRestrictedPASelectedSigmaBottomAppliedGlobalDeepContextOn
          localSigma localPi sourcePrefix))
      (rawTemplateFormula translation
        (coqRestrictedPASelectedSigmaBottomAppliedGlobalTraversalBody
          localSigma localPi))
      (rawProofAssumptionRoot M
        (rawTemplateContextCodeOnTail translation baseContext
          (coqRestrictedPASelectedSigmaBottomAppliedGlobalDeepContextOn
            localSigma localPi sourcePrefix))
        (rawTemplateFormula translation
          (coqRestrictedPASelectedSigmaBottomAppliedGlobalTraversalBody
            localSigma localPi)))).
  {
    rewrite hdeep. cbn [rawTemplateContextCodeOnTail].
    exact (raw_codedPALocalProofOf_assumption M hPA
      (rawTemplateContextCodeOnTail translation baseContext tail)
      (rawTemplateFormula translation
        (coqRestrictedPASelectedSigmaBottomAppliedGlobalTraversalBody
          localSigma localPi)) htail).
  }
  rewrite
    coqRestrictedPASelectedSigmaBottomAppliedGlobalTraversalBody_shape
    in hbody.
  rewrite !rawTemplateFormula_and in hbody.
  lazymatch type of hbody with
  | RawCodedPALocalProofOf _ _ _ ?bodyRoot =>
      exact (raw_codedPALocalProofOf_and7E M hPA
        (rawTemplateContextCodeOnTail translation baseContext
          (coqRestrictedPASelectedSigmaBottomAppliedGlobalDeepContextOn
            localSigma localPi sourcePrefix))
        (rawTemplateFormula translation
          (coqRestrictedPASelectedSigmaBottomAppliedGlobalModeDefined
            localSigma localPi))
        (rawTemplateFormula translation
          (coqRestrictedPASelectedSigmaBottomAppliedGlobalFormulaDefined
            localSigma localPi))
        (rawTemplateFormula translation
          (coqRestrictedPASelectedSigmaBottomAppliedGlobalAssignmentCodeDefined
            localSigma localPi))
        (rawTemplateFormula translation
          (coqRestrictedPASelectedSigmaBottomAppliedGlobalAssignmentStepDefined
            localSigma localPi))
        (rawTemplateFormula translation
          (coqRestrictedPASelectedSigmaBottomAppliedGlobalRootBound
            localSigma localPi))
        (rawTemplateFormula translation
          (coqRestrictedPASelectedSigmaBottomAppliedGlobalRootLookup
            localSigma localPi))
        (rawTemplateFormula translation
          (coqRestrictedPASelectedSigmaBottomAppliedGlobalRows
            localSigma localPi))
        bodyRoot hbody)
  end.
Qed.

(** ------------------------------------------------------------------
    Open the root row and select its mode-zero Sigma payload. *)

(** After applying the outer ternary interface there are no public variables
    above the ten traversal witnesses.  Consequently the selected row must
    be opened with the *closed applied arguments* themselves.  Reusing the
    historical unapplied replacements [#10,#11,#12] here is precisely the
    ten-slot scope error corrected by this module. *)
Definition coqRestrictedPASelectedSigmaBottomAppliedRootRowReplacements
    : list TemplateTerm :=
  [ ttVar 8;
    embedPATerm (Term.numeral 0);
    coqRestrictedPASelectedSigmaBottomGlobalFirstArgument;
    coqRestrictedPASelectedSigmaBottomGlobalZeroArgument;
    coqRestrictedPASelectedSigmaBottomGlobalZeroArgument ].

Definition coqRestrictedPASelectedSigmaBottomAppliedRootRowFormula
    (localSigma localPi : TemplateFormula) : TemplateFormula :=
  templateUniversalOpenManyOrBot
    (coqRestrictedPASelectedSigmaBottomAppliedGlobalRows
      localSigma localPi)
    coqRestrictedPASelectedSigmaBottomAppliedRootRowReplacements.

Definition coqRestrictedPASelectedSigmaBottomAppliedRootRowChoice
    (localSigma localPi : TemplateFormula) : TemplateFormula :=
  templateImpConsequent (templateImpConsequent
    (coqRestrictedPASelectedSigmaBottomAppliedRootRowFormula
      localSigma localPi)).

Definition coqRestrictedPASelectedSigmaBottomAppliedRootRowLeftBranch
    (localSigma localPi : TemplateFormula) : TemplateFormula :=
  templateOrLeftOrBot
    (coqRestrictedPASelectedSigmaBottomAppliedRootRowChoice
      localSigma localPi).

Definition coqRestrictedPASelectedSigmaBottomAppliedRootRowRightBranch
    (localSigma localPi : TemplateFormula) : TemplateFormula :=
  templateOrRightOrBot
    (coqRestrictedPASelectedSigmaBottomAppliedRootRowChoice
      localSigma localPi).

Definition coqRestrictedPASelectedSigmaBottomAppliedRootRowLeftTag
    (localSigma localPi : TemplateFormula) : TemplateFormula :=
  templateAndLeftOrBot
    (coqRestrictedPASelectedSigmaBottomAppliedRootRowLeftBranch
      localSigma localPi).

Definition coqRestrictedPASelectedSigmaBottomAppliedRootRowSelectedPayload
    (localSigma localPi : TemplateFormula) : TemplateFormula :=
  templateAndRightOrBot
    (coqRestrictedPASelectedSigmaBottomAppliedRootRowLeftBranch
      localSigma localPi).

Definition coqRestrictedPASelectedSigmaBottomAppliedRootRowRightTag
    (localSigma localPi : TemplateFormula) : TemplateFormula :=
  templateAndLeftOrBot
    (coqRestrictedPASelectedSigmaBottomAppliedRootRowRightBranch
      localSigma localPi).

Definition coqRestrictedPASelectedSigmaBottomAppliedRootRowRightPayload
    (localSigma localPi : TemplateFormula) : TemplateFormula :=
  templateAndRightOrBot
    (coqRestrictedPASelectedSigmaBottomAppliedRootRowRightBranch
      localSigma localPi).

Lemma coqRestrictedPASelectedSigmaBottomAppliedRootRowFormula_success :
  forall localSigma localPi,
  templateUniversalOpenMany
    (coqRestrictedPASelectedSigmaBottomAppliedGlobalRows
      localSigma localPi)
    coqRestrictedPASelectedSigmaBottomAppliedRootRowReplacements =
  Some (coqRestrictedPASelectedSigmaBottomAppliedRootRowFormula
    localSigma localPi).
Proof. intros. reflexivity. Qed.

Lemma coqRestrictedPASelectedSigmaBottomAppliedRootRowFormula_shape :
  forall localSigma localPi,
  coqRestrictedPASelectedSigmaBottomAppliedRootRowFormula
      localSigma localPi =
  tfImp
    (coqRestrictedPASelectedSigmaBottomAppliedGlobalRootBound
      localSigma localPi)
    (tfImp
      (coqRestrictedPASelectedSigmaBottomAppliedGlobalRootLookup
        localSigma localPi)
      (coqRestrictedPASelectedSigmaBottomAppliedRootRowChoice
        localSigma localPi)).
Proof. intros. reflexivity. Qed.

Lemma coqRestrictedPASelectedSigmaBottomAppliedRootRowChoice_shape :
  forall localSigma localPi,
  coqRestrictedPASelectedSigmaBottomAppliedRootRowChoice
      localSigma localPi =
  tfOr
    (tfAnd
      (coqRestrictedPASelectedSigmaBottomAppliedRootRowLeftTag
        localSigma localPi)
      (coqRestrictedPASelectedSigmaBottomAppliedRootRowSelectedPayload
        localSigma localPi))
    (tfAnd
      (coqRestrictedPASelectedSigmaBottomAppliedRootRowRightTag
        localSigma localPi)
      (coqRestrictedPASelectedSigmaBottomAppliedRootRowRightPayload
        localSigma localPi)).
Proof. intros. reflexivity. Qed.

Lemma coqRestrictedPASelectedSigmaBottomAppliedRootRowRightTag_zero :
  forall localSigma localPi,
  coqRestrictedPASelectedSigmaBottomAppliedRootRowRightTag
      localSigma localPi =
  embedPAFormula zeroEqualsOneFormula.
Proof. intros. reflexivity. Qed.

Theorem
    raw_codedPALocalProofOf_selectedSigmaBottom_applied_root_row_choice :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M)
    witnessList baseContext sourcePrefix localSigma localPi,
  RawCodedPAAxiomWitnessContext M witnessList baseContext ->
  exists root,
    RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation baseContext
        (coqRestrictedPASelectedSigmaBottomAppliedGlobalDeepContextOn
          localSigma localPi sourcePrefix))
      (rawTemplateFormula translation
        (coqRestrictedPASelectedSigmaBottomAppliedRootRowChoice
          localSigma localPi)) root.
Proof.
  intros M hPA translation witnessList baseContext sourcePrefix
    localSigma localPi hwitnessed.
  pose proof
    (raw_codedPALocalProofOf_selectedSigmaBottom_applied_global_fields
      M hPA translation witnessList baseContext sourcePrefix
      localSigma localPi hwitnessed) as hfields.
  destruct hfields as
    [_hmode _hformula _hassignmentCode _hassignmentStep
      [boundRoot hbound] [lookupRoot hlookup] [rowsRoot hrows]].
  exact
    (raw_codedPALocalProofOf_templateUniversalOpenMany_impE2
      M hPA translation
      (rawTemplateContextCodeOnTail translation baseContext
        (coqRestrictedPASelectedSigmaBottomAppliedGlobalDeepContextOn
          localSigma localPi sourcePrefix))
      (coqRestrictedPASelectedSigmaBottomAppliedGlobalRows
        localSigma localPi)
      coqRestrictedPASelectedSigmaBottomAppliedRootRowReplacements
      (coqRestrictedPASelectedSigmaBottomAppliedGlobalRootBound
        localSigma localPi)
      (coqRestrictedPASelectedSigmaBottomAppliedGlobalRootLookup
        localSigma localPi)
      (coqRestrictedPASelectedSigmaBottomAppliedRootRowChoice
        localSigma localPi)
      rowsRoot boundRoot lookupRoot
      (eq_trans
        (coqRestrictedPASelectedSigmaBottomAppliedRootRowFormula_success
          localSigma localPi)
        (f_equal (@Some TemplateFormula)
          (coqRestrictedPASelectedSigmaBottomAppliedRootRowFormula_shape
            localSigma localPi)))
      hrows hbound hlookup).
Qed.

(** Mode selection may need the two closed numeral contradictions.  As in
    the generic global-row selector, they are compiled on one witnessed PA
    extension and the caller's tail inclusion is returned explicitly. *)
Theorem
    raw_codedPALocalProofOf_selectedSigmaBottom_applied_root_row_selected :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall witnessList baseContext sourcePrefix localSigma localPi,
  RawCodedPAAxiomWitnessContext M witnessList baseContext ->
  exists witnesses selectedRoot,
    RawCodedPAAxiomWitnessContext M
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        witnesses witnessList)
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses baseContext) /\
    RawContextListIncluded M baseContext
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses baseContext) /\
    RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation
        (rawStandardPAAxiomWitnessPrefixContextCode M
          witnesses baseContext)
        (coqRestrictedPASelectedSigmaBottomAppliedGlobalDeepContextOn
          localSigma localPi sourcePrefix))
      (rawTemplateFormula translation
        (coqRestrictedPASelectedSigmaBottomAppliedRootRowSelectedPayload
          localSigma localPi)) selectedRoot.
Proof.
  intros M hPA translation hagreement witnessList baseContext
    sourcePrefix localSigma localPi hwitnessed.
  destruct
    (raw_codedZeroOneDistinctness_roots_on_witnessed_extension
      M hPA translation hagreement witnessList baseContext hwitnessed)
    as (witnesses & zeroNotOneRoot & _oneNotZeroRoot &
      hextended & hincluded & hzeroNotOne & _honeNotZero).
  set (extendedContext :=
    rawStandardPAAxiomWitnessPrefixContextCode M witnesses baseContext).
  set (deepPrefix :=
    coqRestrictedPASelectedSigmaBottomAppliedGlobalDeepContextOn
      localSigma localPi sourcePrefix).
  assert (hextendedRealizable :
      RawContextListRealizable M extendedContext).
  {
    exact (raw_codedPAAxiomWitnessContext_context_realizable M
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        witnesses witnessList)
      extendedContext hextended).
  }
  assert (hdeepPrefixAdequate :
      RawCodedTemplatePrefixAtomicallyAdequate M translation deepPrefix).
  {
    intros input _.
    exact (raw_codedTemplateFormula_atomically_adequate_core
      M hPA translation input).
  }
  destruct (raw_codedPALocalProof_templatePrefix M hPA translation
    extendedContext deepPrefix _ zeroNotOneRoot hextendedRealizable
    hdeepPrefixAdequate hzeroNotOne)
    as [deepZeroNotOneRoot hdeepZeroNotOne].
  destruct
    (raw_codedPALocalProofOf_selectedSigmaBottom_applied_root_row_choice
      M hPA translation
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        witnesses witnessList)
      extendedContext sourcePrefix localSigma localPi hextended)
    as [choiceRoot hchoice].
  assert (hdeepRealizable : RawContextListRealizable M
      (rawTemplateContextCodeOnTail translation
        extendedContext deepPrefix)).
  {
    exact (raw_templateContextOnTail_realizable M hPA translation
      extendedContext deepPrefix hextendedRealizable).
  }
  assert (hchoiceZero := hchoice).
  rewrite coqRestrictedPASelectedSigmaBottomAppliedRootRowChoice_shape,
    rawTemplateFormula_or, !rawTemplateFormula_and in hchoiceZero.
  assert (hnotRight : RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation extendedContext deepPrefix)
      (rawFormulaImpCode M
        (rawTemplateFormula translation
          (coqRestrictedPASelectedSigmaBottomAppliedRootRowRightTag
            localSigma localPi))
        (rawFormulaBotCode M)) deepZeroNotOneRoot).
  {
    change (RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation extendedContext deepPrefix)
      (rawTemplateFormula translation
        (tfImp (embedPAFormula zeroEqualsOneFormula) tfBot))
      deepZeroNotOneRoot) in hdeepZeroNotOne.
    rewrite rawTemplateFormula_imp, rawTemplateFormula_bot
      in hdeepZeroNotOne.
    rewrite
      coqRestrictedPASelectedSigmaBottomAppliedRootRowRightTag_zero.
    exact hdeepZeroNotOne.
  }
  assert (hrightAdequate : RawCodedFormulaAtomicallyAdequate M
      (rawFormulaAndCode M
        (rawTemplateFormula translation
          (coqRestrictedPASelectedSigmaBottomAppliedRootRowRightTag
            localSigma localPi))
        (rawTemplateFormula translation
          (coqRestrictedPASelectedSigmaBottomAppliedRootRowRightPayload
            localSigma localPi)))).
  {
    rewrite <- rawTemplateFormula_and.
    exact (raw_codedTemplateFormula_atomically_adequate_core
      M hPA translation
      (tfAnd
        (coqRestrictedPASelectedSigmaBottomAppliedRootRowRightTag
          localSigma localPi)
        (coqRestrictedPASelectedSigmaBottomAppliedRootRowRightPayload
          localSigma localPi))).
  }
  destruct (raw_codedPALocalProofOf_taggedChoice_left M hPA
    (rawTemplateContextCodeOnTail translation extendedContext deepPrefix)
    (rawTemplateFormula translation
      (coqRestrictedPASelectedSigmaBottomAppliedRootRowLeftTag
        localSigma localPi))
    (rawTemplateFormula translation
      (coqRestrictedPASelectedSigmaBottomAppliedRootRowSelectedPayload
        localSigma localPi))
    (rawTemplateFormula translation
      (coqRestrictedPASelectedSigmaBottomAppliedRootRowRightTag
        localSigma localPi))
    (rawTemplateFormula translation
      (coqRestrictedPASelectedSigmaBottomAppliedRootRowRightPayload
        localSigma localPi))
    choiceRoot deepZeroNotOneRoot hdeepRealizable hrightAdequate
    hchoiceZero hnotRight) as [selectedRoot hselected].
  exists witnesses, selectedRoot.
  split; [exact hextended |].
  split; [exact hincluded |].
  exact hselected.
Qed.

(** ------------------------------------------------------------------
    Native successor-row specialization and the eight local witnesses. *)

Definition coqRestrictedPASelectedSigmaBottomNativeAppliedGlobalSource :
    TemplateFormula :=
  coqRestrictedPASelectedSigmaBottomAppliedGlobalSource
    coqDynamicTruthSharedSigmaSuccessorRowTemplate
    coqDynamicTruthSharedPiSuccessorRowTemplate.

Definition
    coqRestrictedPASelectedSigmaBottomNativeAppliedGlobalDeepContextOn
    (sourcePrefix : TemplateContext) : TemplateContext :=
  coqRestrictedPASelectedSigmaBottomAppliedGlobalDeepContextOn
    coqDynamicTruthSharedSigmaSuccessorRowTemplate
    coqDynamicTruthSharedPiSuccessorRowTemplate sourcePrefix.

Definition coqRestrictedPASelectedSigmaBottomNativeOpenedSigmaRow :
    TemplateFormula :=
  coqRestrictedPASelectedSigmaBottomAppliedRootRowSelectedPayload
    coqDynamicTruthSharedSigmaSuccessorRowTemplate
    coqDynamicTruthSharedPiSuccessorRowTemplate.

(** The local row begins with exactly eight existentials. *)
Definition coqRestrictedPASelectedSigmaBottomNativeOpenedSigmaBody :
    TemplateFormula :=
  match templateExistentialBodyMany 8
    coqRestrictedPASelectedSigmaBottomNativeOpenedSigmaRow with
  | Some body => body
  | None => tfBot
  end.

Lemma coqRestrictedPASelectedSigmaBottomNativeOpenedSigmaBody_success :
  templateExistentialBodyMany 8
    coqRestrictedPASelectedSigmaBottomNativeOpenedSigmaRow =
  Some coqRestrictedPASelectedSigmaBottomNativeOpenedSigmaBody.
Proof. reflexivity. Qed.

Definition coqRestrictedPASelectedSigmaBottomNativeLocalDeepContextOn
    (sourcePrefix : TemplateContext) : TemplateContext :=
  match templateExistentialEliminationContext 8
    coqRestrictedPASelectedSigmaBottomNativeOpenedSigmaRow
    (coqRestrictedPASelectedSigmaBottomNativeAppliedGlobalDeepContextOn
      sourcePrefix) with
  | Some context => context
  | None => []
  end.

Lemma coqRestrictedPASelectedSigmaBottomNativeLocalDeepContextOn_success :
  forall sourcePrefix,
  templateExistentialEliminationContext 8
    coqRestrictedPASelectedSigmaBottomNativeOpenedSigmaRow
    (coqRestrictedPASelectedSigmaBottomNativeAppliedGlobalDeepContextOn
      sourcePrefix) =
  Some
    (coqRestrictedPASelectedSigmaBottomNativeLocalDeepContextOn
      sourcePrefix).
Proof. intros. reflexivity. Qed.

Lemma coqRestrictedPASelectedSigmaBottomNativeLocalDeepContextOn_head :
  forall sourcePrefix,
  exists tail,
    coqRestrictedPASelectedSigmaBottomNativeLocalDeepContextOn
      sourcePrefix =
    coqRestrictedPASelectedSigmaBottomNativeOpenedSigmaBody :: tail.
Proof. intros. eexists. reflexivity. Qed.

Definition coqRestrictedPASelectedSigmaBottomNativeOpenedSigmaDomain :
    TemplateFormula :=
  templateAndLeftOrBot
    coqRestrictedPASelectedSigmaBottomNativeOpenedSigmaBody.

Definition coqRestrictedPASelectedSigmaBottomNativeOpenedSigmaOr7 :
    TemplateFormula :=
  templateAndRightOrBot
    coqRestrictedPASelectedSigmaBottomNativeOpenedSigmaBody.

Lemma coqRestrictedPASelectedSigmaBottomNativeOpenedSigmaBody_shape :
  coqRestrictedPASelectedSigmaBottomNativeOpenedSigmaBody =
  tfAnd coqRestrictedPASelectedSigmaBottomNativeOpenedSigmaDomain
    coqRestrictedPASelectedSigmaBottomNativeOpenedSigmaOr7.
Proof. reflexivity. Qed.

(** Total projections of the six right-associated [Or] tails. *)
Definition coqRestrictedPASelectedSigmaBottomNativeOpenedSigmaOrTail1 :=
  templateOrRightOrBot
    coqRestrictedPASelectedSigmaBottomNativeOpenedSigmaOr7.
Definition coqRestrictedPASelectedSigmaBottomNativeOpenedSigmaOrTail2 :=
  templateOrRightOrBot
    coqRestrictedPASelectedSigmaBottomNativeOpenedSigmaOrTail1.
Definition coqRestrictedPASelectedSigmaBottomNativeOpenedSigmaOrTail3 :=
  templateOrRightOrBot
    coqRestrictedPASelectedSigmaBottomNativeOpenedSigmaOrTail2.
Definition coqRestrictedPASelectedSigmaBottomNativeOpenedSigmaOrTail4 :=
  templateOrRightOrBot
    coqRestrictedPASelectedSigmaBottomNativeOpenedSigmaOrTail3.
Definition coqRestrictedPASelectedSigmaBottomNativeOpenedSigmaOrTail5 :=
  templateOrRightOrBot
    coqRestrictedPASelectedSigmaBottomNativeOpenedSigmaOrTail4.
Definition coqRestrictedPASelectedSigmaBottomNativeOpenedSigmaOrTail6 :=
  templateOrRightOrBot
    coqRestrictedPASelectedSigmaBottomNativeOpenedSigmaOrTail5.

Definition coqRestrictedPASelectedSigmaBottomNativeOpenedSigmaBranch
    (branch : DynamicTruthLocalSigmaBranch) : TemplateFormula :=
  match branch with
  | DTLocalSigmaQF => templateOrLeftOrBot
      coqRestrictedPASelectedSigmaBottomNativeOpenedSigmaOr7
  | DTLocalSigmaImpFalseLeft => templateOrLeftOrBot
      coqRestrictedPASelectedSigmaBottomNativeOpenedSigmaOrTail1
  | DTLocalSigmaImpTrueRight => templateOrLeftOrBot
      coqRestrictedPASelectedSigmaBottomNativeOpenedSigmaOrTail2
  | DTLocalSigmaAnd => templateOrLeftOrBot
      coqRestrictedPASelectedSigmaBottomNativeOpenedSigmaOrTail3
  | DTLocalSigmaOr => templateOrLeftOrBot
      coqRestrictedPASelectedSigmaBottomNativeOpenedSigmaOrTail4
  | DTLocalSigmaEx => templateOrLeftOrBot
      coqRestrictedPASelectedSigmaBottomNativeOpenedSigmaOrTail5
  | DTLocalSigmaAll =>
      coqRestrictedPASelectedSigmaBottomNativeOpenedSigmaOrTail6
  end.

Definition coqRestrictedPASelectedSigmaBottomNativeOpenedSigmaBranches :
    list TemplateFormula :=
  map coqRestrictedPASelectedSigmaBottomNativeOpenedSigmaBranch
    dynamicTruthLocalSigmaBranchOrder.

Lemma coqRestrictedPASelectedSigmaBottomNativeOpenedSigmaOr7_shape :
  coqRestrictedPASelectedSigmaBottomNativeOpenedSigmaOr7 =
  tfOr
    (coqRestrictedPASelectedSigmaBottomNativeOpenedSigmaBranch
      DTLocalSigmaQF)
    (tfOr
      (coqRestrictedPASelectedSigmaBottomNativeOpenedSigmaBranch
        DTLocalSigmaImpFalseLeft)
      (tfOr
        (coqRestrictedPASelectedSigmaBottomNativeOpenedSigmaBranch
          DTLocalSigmaImpTrueRight)
        (tfOr
          (coqRestrictedPASelectedSigmaBottomNativeOpenedSigmaBranch
            DTLocalSigmaAnd)
          (tfOr
            (coqRestrictedPASelectedSigmaBottomNativeOpenedSigmaBranch
              DTLocalSigmaOr)
            (tfOr
              (coqRestrictedPASelectedSigmaBottomNativeOpenedSigmaBranch
                DTLocalSigmaEx)
              (coqRestrictedPASelectedSigmaBottomNativeOpenedSigmaBranch
                DTLocalSigmaAll)))))).
Proof. reflexivity. Qed.

Lemma rawFiniteRightDisjunctionCode_selectedSigmaBottom_opened_branches :
  forall (M : RawPAModel)
    (translation : RawCodedTemplateTranslation M),
  rawFiniteRightDisjunctionCode M
    (map (rawTemplateFormula translation)
      coqRestrictedPASelectedSigmaBottomNativeOpenedSigmaBranches) =
  rawTemplateFormula translation
    coqRestrictedPASelectedSigmaBottomNativeOpenedSigmaOr7.
Proof.
  intros M translation.
  unfold coqRestrictedPASelectedSigmaBottomNativeOpenedSigmaBranches,
    dynamicTruthLocalSigmaBranchOrder.
  cbn [map rawFiniteRightDisjunctionCode].
  rewrite
    coqRestrictedPASelectedSigmaBottomNativeOpenedSigmaOr7_shape,
    !rawTemplateFormula_or.
  reflexivity.
Qed.

(** And-E2 from the head created by the eight local Ex-E steps exposes the
    honest Or7 in the exact global-plus-local eigenvariable context. *)
Theorem raw_codedPALocalProofOf_selectedSigmaBottom_native_opened_or7 :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M)
    witnessList baseContext sourcePrefix,
  RawCodedPAAxiomWitnessContext M witnessList baseContext ->
  exists root,
    RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation baseContext
        (coqRestrictedPASelectedSigmaBottomNativeLocalDeepContextOn
          sourcePrefix))
      (rawTemplateFormula translation
        coqRestrictedPASelectedSigmaBottomNativeOpenedSigmaOr7) root.
Proof.
  intros M hPA translation witnessList baseContext sourcePrefix hwitnessed.
  destruct
    (coqRestrictedPASelectedSigmaBottomNativeLocalDeepContextOn_head
      sourcePrefix) as [tail hdeep].
  assert (htail : RawContextListRealizable M
      (rawTemplateContextCodeOnTail translation baseContext tail)).
  {
    apply (raw_templateContextOnTail_realizable M hPA).
    exact (raw_codedPAAxiomWitnessContext_context_realizable M
      witnessList baseContext hwitnessed).
  }
  assert (hbody : RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation baseContext
        (coqRestrictedPASelectedSigmaBottomNativeLocalDeepContextOn
          sourcePrefix))
      (rawTemplateFormula translation
        coqRestrictedPASelectedSigmaBottomNativeOpenedSigmaBody)
      (rawProofAssumptionRoot M
        (rawTemplateContextCodeOnTail translation baseContext
          (coqRestrictedPASelectedSigmaBottomNativeLocalDeepContextOn
            sourcePrefix))
        (rawTemplateFormula translation
          coqRestrictedPASelectedSigmaBottomNativeOpenedSigmaBody))).
  {
    rewrite hdeep. cbn [rawTemplateContextCodeOnTail].
    exact (raw_codedPALocalProofOf_assumption M hPA
      (rawTemplateContextCodeOnTail translation baseContext tail)
      (rawTemplateFormula translation
        coqRestrictedPASelectedSigmaBottomNativeOpenedSigmaBody) htail).
  }
  rewrite coqRestrictedPASelectedSigmaBottomNativeOpenedSigmaBody_shape,
    rawTemplateFormula_and in hbody.
  lazymatch type of hbody with
  | RawCodedPALocalProofOf _ _ _ ?bodyRoot =>
      pose proof (raw_codedPALocalProofOf_andE2 M hPA
        (rawTemplateContextCodeOnTail translation baseContext
          (coqRestrictedPASelectedSigmaBottomNativeLocalDeepContextOn
            sourcePrefix))
        (rawTemplateFormula translation
          coqRestrictedPASelectedSigmaBottomNativeOpenedSigmaDomain)
        (rawTemplateFormula translation
          coqRestrictedPASelectedSigmaBottomNativeOpenedSigmaOr7)
        bodyRoot hbody) as hor;
      eexists; exact hor
  end.
Qed.

(** ------------------------------------------------------------------
    The exact seven residuals and the two nested Ex-E chains. *)

Definition rawRestrictedPASelectedSigmaBottomNativeOpenedSigmaBranches
    (M : RawPAModel) (translation : RawCodedTemplateTranslation M)
    : list M :=
  map
    (fun branch => rawTemplateFormula translation
      (coqRestrictedPASelectedSigmaBottomNativeOpenedSigmaBranch branch))
    dynamicTruthLocalSigmaBranchOrder.

Arguments rawRestrictedPASelectedSigmaBottomNativeOpenedSigmaBranches
  M translation : clear implicits.

Lemma
    rawRestrictedPASelectedSigmaBottomNativeOpenedSigmaBranches_disjunction :
  forall (M : RawPAModel)
    (translation : RawCodedTemplateTranslation M),
  rawFiniteRightDisjunctionCode M
    (rawRestrictedPASelectedSigmaBottomNativeOpenedSigmaBranches
      M translation) =
  rawTemplateFormula translation
    coqRestrictedPASelectedSigmaBottomNativeOpenedSigmaOr7.
Proof.
  intros M translation.
  unfold rawRestrictedPASelectedSigmaBottomNativeOpenedSigmaBranches,
    dynamicTruthLocalSigmaBranchOrder.
  cbn [map rawFiniteRightDisjunctionCode].
  rewrite
    coqRestrictedPASelectedSigmaBottomNativeOpenedSigmaOr7_shape,
    !rawTemplateFormula_or.
  reflexivity.
Qed.

Record RawRestrictedPASelectedSigmaBottomGlobalOpenedSevenCaseSupportAt
    (M : RawPAModel) (translation : RawCodedTemplateTranslation M)
    (baseContext : M) (sourcePrefix : TemplateContext) : Prop := {
  rawRestrictedPASelectedSigmaBottomGlobalOpened_caseResources :
    RawFiniteDisjunctionDerivedCaseResources M
      (rawRestrictedPASelectedSigmaBottomNativeOpenedSigmaBranches
        M translation)
      (rawTemplateContextCodeOnTail translation baseContext
        (coqRestrictedPASelectedSigmaBottomNativeLocalDeepContextOn
          sourcePrefix));
  rawRestrictedPASelectedSigmaBottomGlobalOpened_branchRoots :
    forall branch : DynamicTruthLocalSigmaBranch,
      exists root,
        RawCodedPALocalProofOf M
          (rawTemplateContextCodeOnTail translation baseContext
            (coqRestrictedPASelectedSigmaBottomNativeLocalDeepContextOn
              sourcePrefix))
          (rawFormulaImpCode M
            (rawTemplateFormula translation
              (coqRestrictedPASelectedSigmaBottomNativeOpenedSigmaBranch
                branch))
            (rawFormulaBotCode M)) root
}.

Arguments RawRestrictedPASelectedSigmaBottomGlobalOpenedSevenCaseSupportAt
  M translation baseContext sourcePrefix : clear implicits.

Theorem
    raw_codedPALocalProofOf_selectedSigmaBottom_native_local_bottom_of_cases :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M)
    witnessList baseContext sourcePrefix,
  RawCodedPAAxiomWitnessContext M witnessList baseContext ->
  RawRestrictedPASelectedSigmaBottomGlobalOpenedSevenCaseSupportAt
    M translation baseContext sourcePrefix ->
  exists root,
    RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation baseContext
        (coqRestrictedPASelectedSigmaBottomNativeLocalDeepContextOn
          sourcePrefix))
      (rawFormulaBotCode M) root.
Proof.
  intros M hPA translation witnessList baseContext sourcePrefix
    hwitnessed hsupport.
  destruct hsupport as [hresources hbranchRoots].
  destruct
    (raw_codedPALocalProofOf_selectedSigmaBottom_native_opened_or7
      M hPA translation witnessList baseContext sourcePrefix hwitnessed)
    as [orRoot hor].
  assert (hrow : RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation baseContext
        (coqRestrictedPASelectedSigmaBottomNativeLocalDeepContextOn
          sourcePrefix))
      (rawFiniteRightDisjunctionCode M
        (rawRestrictedPASelectedSigmaBottomNativeOpenedSigmaBranches
          M translation)) orRoot).
  {
    rewrite
      rawRestrictedPASelectedSigmaBottomNativeOpenedSigmaBranches_disjunction.
    exact hor.
  }
  assert (hcases : RawCodedPALocalFiniteDisjunctionCaseFamily M
      (rawTemplateContextCodeOnTail translation baseContext
        (coqRestrictedPASelectedSigmaBottomNativeLocalDeepContextOn
          sourcePrefix))
      (rawRestrictedPASelectedSigmaBottomNativeOpenedSigmaBranches
        M translation)
      (rawFormulaBotCode M)).
  {
    intros selected hselected.
    unfold rawRestrictedPASelectedSigmaBottomNativeOpenedSigmaBranches
      in hselected.
    apply in_map_iff in hselected.
    destruct hselected as [branch [hselected _hinOrder]].
    subst selected.
    exact (hbranchRoots branch).
  }
  exact
    (raw_codedPALocalProofOf_finiteDisjunctionDerivedCases
      M hPA
      (rawRestrictedPASelectedSigmaBottomNativeOpenedSigmaBranches
        M translation)
      (rawFormulaBotCode M)
      (rawTemplateContextCodeOnTail translation baseContext
        (coqRestrictedPASelectedSigmaBottomNativeLocalDeepContextOn
          sourcePrefix))
      orRoot hresources hrow hcases).
Qed.

(** Eliminate the eight local-row witnesses.  The conclusion is bottom, so
    its eightfold eigenvariable shift is definitionally itself. *)
Theorem
    raw_codedPALocalProofOf_selectedSigmaBottom_native_global_deep_bottom :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M)
    witnessList baseContext sourcePrefix selectedRoot,
  RawCodedPAAxiomWitnessContext M witnessList baseContext ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail translation baseContext
      (coqRestrictedPASelectedSigmaBottomNativeAppliedGlobalDeepContextOn
        sourcePrefix))
    (rawTemplateFormula translation
      coqRestrictedPASelectedSigmaBottomNativeOpenedSigmaRow)
    selectedRoot ->
  RawRestrictedPASelectedSigmaBottomGlobalOpenedSevenCaseSupportAt
    M translation baseContext sourcePrefix ->
  exists root,
    RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation baseContext
        (coqRestrictedPASelectedSigmaBottomNativeAppliedGlobalDeepContextOn
          sourcePrefix))
      (rawFormulaBotCode M) root.
Proof.
  intros M hPA translation witnessList baseContext sourcePrefix
    selectedRoot hwitnessed hselected hsupport.
  destruct
    (raw_codedPALocalProofOf_selectedSigmaBottom_native_local_bottom_of_cases
      M hPA translation witnessList baseContext sourcePrefix
      hwitnessed hsupport) as [deepRoot hdeep].
  assert (hdeepTemplate : RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation baseContext
        (coqRestrictedPASelectedSigmaBottomNativeLocalDeepContextOn
          sourcePrefix))
      (rawTemplateFormula translation
        (templateFormulaShiftMany 8 tfBot)) deepRoot).
  {
    cbn [templateFormulaShiftMany templateFormulaRename].
    rewrite rawTemplateFormula_bot.
    exact hdeep.
  }
  destruct
    (raw_codedPALocalProofOf_existential_elimination_chain_on_witnessed_tail
      M hPA translation witnessList baseContext 8
      coqRestrictedPASelectedSigmaBottomNativeOpenedSigmaRow
      (coqRestrictedPASelectedSigmaBottomNativeAppliedGlobalDeepContextOn
        sourcePrefix)
      tfBot
      (coqRestrictedPASelectedSigmaBottomNativeLocalDeepContextOn
        sourcePrefix)
      selectedRoot deepRoot hwitnessed
      (coqRestrictedPASelectedSigmaBottomNativeLocalDeepContextOn_success
        sourcePrefix)
      hselected hdeepTemplate) as [root hroot].
  exists root.
  rewrite rawTemplateFormula_bot in hroot.
  exact hroot.
Qed.

(** The outer source is assumed once, and only the genuine applied Ex10
    formula is eliminated.  Imp-I then discharges that exact assumption. *)
Theorem
    raw_codedPALocalProofOf_selectedSigmaBottom_native_applied_refutation :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M)
    witnessList baseContext selectedRoot,
  RawCodedPAAxiomWitnessContext M witnessList baseContext ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail translation baseContext
      (coqRestrictedPASelectedSigmaBottomNativeAppliedGlobalDeepContextOn
        [coqRestrictedPASelectedSigmaBottomNativeAppliedGlobalSource]))
    (rawTemplateFormula translation
      coqRestrictedPASelectedSigmaBottomNativeOpenedSigmaRow)
    selectedRoot ->
  RawRestrictedPASelectedSigmaBottomGlobalOpenedSevenCaseSupportAt
    M translation baseContext
      [coqRestrictedPASelectedSigmaBottomNativeAppliedGlobalSource] ->
  exists root,
    RawCodedPALocalProofOf M baseContext
      (rawFormulaImpCode M
        (rawTemplateFormula translation
          coqRestrictedPASelectedSigmaBottomNativeAppliedGlobalSource)
        (rawFormulaBotCode M)) root.
Proof.
  intros M hPA translation witnessList baseContext selectedRoot
    hwitnessed hselected hsupport.
  set (source :=
    coqRestrictedPASelectedSigmaBottomNativeAppliedGlobalSource).
  set (sourcePrefix := ([source] : TemplateContext)).
  assert (hbaseRealizable : RawContextListRealizable M baseContext).
  {
    exact (raw_codedPAAxiomWitnessContext_context_realizable M
      witnessList baseContext hwitnessed).
  }
  assert (hsource : RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation baseContext sourcePrefix)
      (rawTemplateFormula translation source)
      (rawProofAssumptionRoot M
        (rawTemplateContextCodeOnTail translation baseContext sourcePrefix)
        (rawTemplateFormula translation source))).
  {
    unfold sourcePrefix. cbn [rawTemplateContextCodeOnTail].
    exact (raw_codedPALocalProofOf_assumption M hPA baseContext
      (rawTemplateFormula translation source) hbaseRealizable).
  }
  destruct
    (raw_codedPALocalProofOf_selectedSigmaBottom_native_global_deep_bottom
      M hPA translation witnessList baseContext sourcePrefix selectedRoot
      hwitnessed hselected hsupport) as [deepRoot hdeep].
  assert (hdeepTemplate : RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation baseContext
        (coqRestrictedPASelectedSigmaBottomNativeAppliedGlobalDeepContextOn
          sourcePrefix))
      (rawTemplateFormula translation
        (templateFormulaShiftMany 10 tfBot)) deepRoot).
  {
    cbn [templateFormulaShiftMany templateFormulaRename].
    rewrite rawTemplateFormula_bot.
    exact hdeep.
  }
  destruct
    (raw_codedPALocalProofOf_existential_elimination_chain_on_witnessed_tail
      M hPA translation witnessList baseContext 10 source sourcePrefix
      tfBot
      (coqRestrictedPASelectedSigmaBottomNativeAppliedGlobalDeepContextOn
        sourcePrefix)
      (rawProofAssumptionRoot M
        (rawTemplateContextCodeOnTail translation baseContext sourcePrefix)
        (rawTemplateFormula translation source))
      deepRoot hwitnessed
      (coqRestrictedPASelectedSigmaBottomAppliedGlobalDeepContextOn_success
        coqDynamicTruthSharedSigmaSuccessorRowTemplate
        coqDynamicTruthSharedPiSuccessorRowTemplate sourcePrefix)
      hsource hdeepTemplate) as [bottomRoot hbottom].
  exists (rawProofImpIRoot M baseContext
    (rawTemplateFormula translation source) (rawFormulaBotCode M)
    bottomRoot).
  rewrite rawTemplateFormula_bot in hbottom.
  unfold sourcePrefix in hbottom.
  cbn [rawTemplateContextCodeOnTail] in hbottom.
  exact (raw_codedPALocalProofOf_impI M hPA baseContext
    (rawTemplateFormula translation source) (rawFormulaBotCode M)
    bottomRoot hbottom).
Qed.

(** A dependency-ordered caller supplies only the seven case package on the
    witnessed extension chosen by mode selection. *)
Definition RawRestrictedPASelectedSigmaBottomGlobalOpenedSevenCaseCompiler
    (M : RawPAModel) (translation : RawCodedTemplateTranslation M)
    (witnessList baseContext : M) : Prop :=
  forall witnesses,
    RawCodedPAAxiomWitnessContext M
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        witnesses witnessList)
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses baseContext) ->
    RawContextListIncluded M baseContext
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses baseContext) ->
    RawRestrictedPASelectedSigmaBottomGlobalOpenedSevenCaseSupportAt
      M translation
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses baseContext)
      [coqRestrictedPASelectedSigmaBottomNativeAppliedGlobalSource].

Arguments RawRestrictedPASelectedSigmaBottomGlobalOpenedSevenCaseCompiler
  M translation witnessList baseContext : clear implicits.

Theorem
    raw_codedPALocalProofOf_selectedSigmaBottom_native_applied_refutation_growing :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall witnessList baseContext,
  RawCodedPAAxiomWitnessContext M witnessList baseContext ->
  RawRestrictedPASelectedSigmaBottomGlobalOpenedSevenCaseCompiler
    M translation witnessList baseContext ->
  exists witnesses root,
    RawCodedPAAxiomWitnessContext M
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        witnesses witnessList)
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses baseContext) /\
    RawContextListIncluded M baseContext
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses baseContext) /\
    RawCodedPALocalProofOf M
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses baseContext)
      (rawFormulaImpCode M
        (rawTemplateFormula translation
          coqRestrictedPASelectedSigmaBottomNativeAppliedGlobalSource)
        (rawFormulaBotCode M)) root.
Proof.
  intros M hPA translation hagreement witnessList baseContext
    hwitnessed hcompiler.
  destruct
    (raw_codedPALocalProofOf_selectedSigmaBottom_applied_root_row_selected
      M hPA translation hagreement witnessList baseContext
      [coqRestrictedPASelectedSigmaBottomNativeAppliedGlobalSource]
      coqDynamicTruthSharedSigmaSuccessorRowTemplate
      coqDynamicTruthSharedPiSuccessorRowTemplate hwitnessed)
    as (witnesses & selectedRoot & hextended & hincluded & hselected).
  pose proof (hcompiler witnesses hextended hincluded) as hsupport.
  destruct
    (raw_codedPALocalProofOf_selectedSigmaBottom_native_applied_refutation
      M hPA translation
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        witnesses witnessList)
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses baseContext)
      selectedRoot hextended hselected hsupport)
    as [root hroot].
  exists witnesses, root.
  split; [exact hextended |].
  split; [exact hincluded |].
  exact hroot.
Qed.

End
  PABoundedRawCodedRestrictedPASelectedSigmaBottomGlobalOpenedSevenCaseBoundary.
