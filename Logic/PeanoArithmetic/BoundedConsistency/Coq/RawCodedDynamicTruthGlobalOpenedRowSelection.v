(** Select the polarity-correct payload from the opened global root row. *)

From Stdlib Require Import List.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedContextLists
  RawCodedRestrictedPAProof
  RawCodedSyntaxConstructors
  RawCodedFixedLevelTruthTotality
  RawCodedFixedLevelTruthTraversal
  RawCodedPAAxiomWitnessPrefix
  RawCodedPALocalProofExistential
  RawCodedPALocalProofComposition
  RawCodedPALocalProofWitnessedContextMerge
  RawCodedPALocalProofTaggedChoice
  RawCodedPALocalProofUniversalEliminationChain
  RawCodedTemplateSyntax
  RawCodedTemplateProofCompiler
  RawCodedTemplateProofCompilerSelfShiftTail
  RawCodedTemplatePAEmbedding
  RawCodedTemplateFormulaAtomicAdequacy
  RawCodedTemplateLocalProofWitnessedTailTransport
  RawCodedDynamicTruthPairedGlobalSuccessorGraph
  RawCodedDynamicTruthPredecessorGlobalExistentialElimination
  RawCodedDynamicTruthGlobalOpenedFieldProjection
  RawCodedZeroOneDistinctnessProofCompilation.

Module PABoundedRawCodedDynamicTruthGlobalOpenedRowSelection.

Import ListNotations.
Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedContextLists.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedFixedLevelTruthTotality.
Import PABoundedRawCodedFixedLevelTruthTraversal.
Import PABoundedRawCodedPAAxiomWitnessPrefix.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPALocalProofComposition.
Import PABoundedRawCodedPALocalProofWitnessedContextMerge.
Import PABoundedRawCodedPALocalProofTaggedChoice.
Import PABoundedRawCodedPALocalProofUniversalEliminationChain.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedTemplateProofCompilerSelfShiftTail.
Import PABoundedRawCodedTemplatePAEmbedding.
Import PABoundedRawCodedTemplateFormulaAtomicAdequacy.
Import PABoundedRawCodedTemplateLocalProofWitnessedTailTransport.
Import PABoundedRawCodedDynamicTruthPairedGlobalSuccessorGraph.
Import
  PABoundedRawCodedDynamicTruthPredecessorGlobalExistentialElimination.
Import PABoundedRawCodedDynamicTruthGlobalOpenedFieldProjection.
Import PABoundedRawCodedZeroOneDistinctnessProofCompilation.

(** These total destructors make the four components of the concrete opened
    row available under stable names.  Their fallback is irrelevant because
    the following shape lemma computes the concrete row to [Or] of two
    [And] branches. *)
Definition templateOrLeftOrBot (input : TemplateFormula) : TemplateFormula :=
  match input with
  | tfOr lhs _ => lhs
  | _ => tfBot
  end.

Definition templateOrRightOrBot (input : TemplateFormula) : TemplateFormula :=
  match input with
  | tfOr _ rhs => rhs
  | _ => tfBot
  end.

Definition templateAndLeftOrBot (input : TemplateFormula) : TemplateFormula :=
  match input with
  | tfAnd lhs _ => lhs
  | _ => tfBot
  end.

Definition templateAndRightOrBot (input : TemplateFormula) : TemplateFormula :=
  match input with
  | tfAnd _ rhs => rhs
  | _ => tfBot
  end.

Definition coqDynamicTruthGlobalOpenedRootRowLeftBranch
    (rootMode : nat) (localSigma localPi : formula) : TemplateFormula :=
  templateOrLeftOrBot
    (coqDynamicTruthGlobalOpenedRootRowChoice
      rootMode localSigma localPi).

Definition coqDynamicTruthGlobalOpenedRootRowRightBranch
    (rootMode : nat) (localSigma localPi : formula) : TemplateFormula :=
  templateOrRightOrBot
    (coqDynamicTruthGlobalOpenedRootRowChoice
      rootMode localSigma localPi).

Definition coqDynamicTruthGlobalOpenedRootRowLeftTag
    (rootMode : nat) (localSigma localPi : formula) : TemplateFormula :=
  templateAndLeftOrBot
    (coqDynamicTruthGlobalOpenedRootRowLeftBranch
      rootMode localSigma localPi).

Definition coqDynamicTruthGlobalOpenedRootRowLeftPayload
    (rootMode : nat) (localSigma localPi : formula) : TemplateFormula :=
  templateAndRightOrBot
    (coqDynamicTruthGlobalOpenedRootRowLeftBranch
      rootMode localSigma localPi).

Definition coqDynamicTruthGlobalOpenedRootRowRightTag
    (rootMode : nat) (localSigma localPi : formula) : TemplateFormula :=
  templateAndLeftOrBot
    (coqDynamicTruthGlobalOpenedRootRowRightBranch
      rootMode localSigma localPi).

Definition coqDynamicTruthGlobalOpenedRootRowRightPayload
    (rootMode : nat) (localSigma localPi : formula) : TemplateFormula :=
  templateAndRightOrBot
    (coqDynamicTruthGlobalOpenedRootRowRightBranch
      rootMode localSigma localPi).

Lemma coqDynamicTruthGlobalOpenedRootRowChoice_tagged_shape : forall
    rootMode localSigma localPi,
  coqDynamicTruthGlobalOpenedRootRowChoice rootMode localSigma localPi =
  tfOr
    (tfAnd
      (coqDynamicTruthGlobalOpenedRootRowLeftTag
        rootMode localSigma localPi)
      (coqDynamicTruthGlobalOpenedRootRowLeftPayload
        rootMode localSigma localPi))
    (tfAnd
      (coqDynamicTruthGlobalOpenedRootRowRightTag
        rootMode localSigma localPi)
      (coqDynamicTruthGlobalOpenedRootRowRightPayload
        rootMode localSigma localPi)).
Proof.
  intros. reflexivity.
Qed.

(** At mode zero the impossible right tag is [0 = 1]; at mode one the
    impossible left tag is [1 = 0].  These are literal template equalities,
    not merely semantic equivalences. *)
Lemma coqDynamicTruthGlobalOpenedRootRowRightTag_zero : forall
    localSigma localPi,
  coqDynamicTruthGlobalOpenedRootRowRightTag 0 localSigma localPi =
  embedPAFormula zeroEqualsOneFormula.
Proof.
  intros. reflexivity.
Qed.

Lemma coqDynamicTruthGlobalOpenedRootRowLeftTag_one : forall
    localSigma localPi,
  coqDynamicTruthGlobalOpenedRootRowLeftTag 1 localSigma localPi =
  embedPAFormula oneEqualsZeroFormula.
Proof.
  intros. reflexivity.
Qed.

(** Lift a substitution through a fixed number of still-unopened binders. *)
Fixpoint templateTermSubstitutionLiftMany (depth : nat)
    (substitution : nat -> TemplateTerm) : nat -> TemplateTerm :=
  match depth with
  | 0 => substitution
  | S remaining => templateTermUpSubst
      (templateTermSubstitutionLiftMany remaining substitution)
  end.

(** Opening a subformula sitting beneath an entire universal tower is not a
    naive sequence of direct openings.  The first replacement must cross all
    remaining binders, the second all but one, and so on.  Encoding that lift
    count here keeps later payload calculations capture-safe. *)
Fixpoint templateFormulaOpenSequenceUnderBinders
    (input : TemplateFormula) (replacements : list TemplateTerm)
    : TemplateFormula :=
  match replacements with
  | [] => input
  | replacement :: tail =>
      templateFormulaOpenSequenceUnderBinders
        (templateFormulaSubst
          (templateTermSubstitutionLiftMany (length tail)
            (templateInstTerm replacement)) input) tail
  end.

Lemma coqDynamicTruthGlobalOpenedRootRowLeftPayload_open_sequence : forall
    rootMode localSigma localPi,
  coqDynamicTruthGlobalOpenedRootRowLeftPayload
      rootMode localSigma localPi =
  templateFormulaOpenSequenceUnderBinders (embedPAFormula localSigma)
    (coqDynamicTruthGlobalOpenedRootRowReplacements rootMode).
Proof.
  intros.
  unfold coqDynamicTruthGlobalOpenedRootRowLeftPayload,
    coqDynamicTruthGlobalOpenedRootRowLeftBranch,
    templateAndRightOrBot, templateOrLeftOrBot,
    coqDynamicTruthGlobalOpenedRootRowChoice,
    templateImpConsequent,
    coqDynamicTruthGlobalOpenedRootRowFormula,
    coqDynamicTruthGlobalOpenedRows,
    templateUniversalOpenManyOrBot,
    coqDynamicTruthGlobalOpenedRootRowReplacements,
    dynamicTruthGlobalRowsFormula, fixedTruthTraversalAll5.
  cbn [embedPAFormula templateUniversalOpenMany
    templateFormulaOpenSequenceUnderBinders
    templateTermSubstitutionLiftMany templateFormulaOpen
    templateFormulaSubst templateTermSubst templateTermUpSubst length].
  reflexivity.
Qed.

Lemma coqDynamicTruthGlobalOpenedRootRowRightPayload_open_sequence : forall
    rootMode localSigma localPi,
  coqDynamicTruthGlobalOpenedRootRowRightPayload
      rootMode localSigma localPi =
  templateFormulaOpenSequenceUnderBinders (embedPAFormula localPi)
    (coqDynamicTruthGlobalOpenedRootRowReplacements rootMode).
Proof.
  intros.
  unfold coqDynamicTruthGlobalOpenedRootRowRightPayload,
    coqDynamicTruthGlobalOpenedRootRowRightBranch,
    templateAndRightOrBot, templateOrRightOrBot,
    coqDynamicTruthGlobalOpenedRootRowChoice,
    templateImpConsequent,
    coqDynamicTruthGlobalOpenedRootRowFormula,
    coqDynamicTruthGlobalOpenedRows,
    templateUniversalOpenManyOrBot,
    coqDynamicTruthGlobalOpenedRootRowReplacements,
    dynamicTruthGlobalRowsFormula, fixedTruthTraversalAll5.
  cbn [embedPAFormula templateUniversalOpenMany
    templateFormulaOpenSequenceUnderBinders
    templateTermSubstitutionLiftMany templateFormulaOpen
    templateFormulaSubst templateTermSubst templateTermUpSubst length].
  reflexivity.
Qed.

Definition coqDynamicTruthGlobalOpenedRootRowSelectedPayload
    (rootMode : nat) (localSigma localPi : formula) : TemplateFormula :=
  match rootMode with
  | 0 => coqDynamicTruthGlobalOpenedRootRowLeftPayload
      0 localSigma localPi
  | S _ => coqDynamicTruthGlobalOpenedRootRowRightPayload
      rootMode localSigma localPi
  end.

(** Grow the witnessed PA tail once, insert both closed contradictions under
    the complete ten-witness prefix, and select the mode-correct payload.
    The endpoint deliberately retains the enlarged witnessed tail and the
    inclusion of the caller's tail: predecessor elimination will run over
    this same extension and can weaken its incoming global proof exactly
    once. *)
Theorem
    raw_codedPALocalProofOf_dynamicTruthGlobal_opened_root_row_selected :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall witnessList baseContext rootMode localSigma localPi,
  RawCodedPAAxiomWitnessContext M witnessList baseContext ->
  rootMode = 0 \/ rootMode = 1 ->
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
        (coqDynamicTruthGlobalExistentialDeepContext
          rootMode localSigma localPi))
      (rawTemplateFormula translation
        (coqDynamicTruthGlobalOpenedRootRowSelectedPayload
          rootMode localSigma localPi)) selectedRoot.
Proof.
  intros M hPA translation hagreement witnessList baseContext
    rootMode localSigma localPi hwitnessed hrootMode.
  destruct
    (raw_codedZeroOneDistinctness_roots_on_witnessed_extension
      M hPA translation hagreement witnessList baseContext hwitnessed)
    as (witnesses & zeroNotOneRoot & oneNotZeroRoot &
      hextended & hincluded & hzeroNotOne & honeNotZero).
  set (extendedContext :=
    rawStandardPAAxiomWitnessPrefixContextCode M witnesses baseContext).
  set (deepPrefix := coqDynamicTruthGlobalExistentialDeepContext
    rootMode localSigma localPi).
  assert (hextendedRealizable : RawContextListRealizable M extendedContext).
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
  destruct (raw_codedPALocalProof_templatePrefix M hPA translation
    extendedContext deepPrefix _ oneNotZeroRoot hextendedRealizable
    hdeepPrefixAdequate honeNotZero)
    as [deepOneNotZeroRoot hdeepOneNotZero].
  destruct
    (raw_codedPALocalProofOf_dynamicTruthGlobal_opened_root_row_choice
      M hPA translation
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        witnesses witnessList)
      extendedContext rootMode localSigma localPi hextended hrootMode)
    as [choiceRoot hchoice].
  assert (hdeepRealizable : RawContextListRealizable M
      (rawTemplateContextCodeOnTail translation extendedContext deepPrefix)).
  {
    exact (raw_templateContextOnTail_realizable M hPA translation
      extendedContext deepPrefix hextendedRealizable).
  }
  destruct hrootMode as [hzero | hone].
  - subst rootMode.
    assert (hchoiceZero := hchoice).
    rewrite coqDynamicTruthGlobalOpenedRootRowChoice_tagged_shape,
      rawTemplateFormula_or, !rawTemplateFormula_and in hchoiceZero.
    assert (hnotRight : RawCodedPALocalProofOf M
        (rawTemplateContextCodeOnTail translation extendedContext deepPrefix)
        (rawFormulaImpCode M
          (rawTemplateFormula translation
            (coqDynamicTruthGlobalOpenedRootRowRightTag
              0 localSigma localPi))
          (rawFormulaBotCode M)) deepZeroNotOneRoot).
    {
      change (RawCodedPALocalProofOf M
        (rawTemplateContextCodeOnTail translation extendedContext deepPrefix)
        (rawTemplateFormula translation
          (tfImp (embedPAFormula zeroEqualsOneFormula) tfBot))
        deepZeroNotOneRoot) in hdeepZeroNotOne.
      rewrite rawTemplateFormula_imp, rawTemplateFormula_bot
        in hdeepZeroNotOne.
      rewrite coqDynamicTruthGlobalOpenedRootRowRightTag_zero.
      exact hdeepZeroNotOne.
    }
    assert (hrightAdequate : RawCodedFormulaAtomicallyAdequate M
        (rawFormulaAndCode M
          (rawTemplateFormula translation
            (coqDynamicTruthGlobalOpenedRootRowRightTag
              0 localSigma localPi))
          (rawTemplateFormula translation
            (coqDynamicTruthGlobalOpenedRootRowRightPayload
              0 localSigma localPi)))).
    {
      rewrite <- rawTemplateFormula_and.
      exact (raw_codedTemplateFormula_atomically_adequate_core
        M hPA translation
        (tfAnd
          (coqDynamicTruthGlobalOpenedRootRowRightTag
            0 localSigma localPi)
          (coqDynamicTruthGlobalOpenedRootRowRightPayload
            0 localSigma localPi))).
    }
    destruct (raw_codedPALocalProofOf_taggedChoice_left M hPA
      (rawTemplateContextCodeOnTail translation extendedContext deepPrefix)
      (rawTemplateFormula translation
        (coqDynamicTruthGlobalOpenedRootRowLeftTag 0 localSigma localPi))
      (rawTemplateFormula translation
        (coqDynamicTruthGlobalOpenedRootRowLeftPayload 0 localSigma localPi))
      (rawTemplateFormula translation
        (coqDynamicTruthGlobalOpenedRootRowRightTag 0 localSigma localPi))
      (rawTemplateFormula translation
        (coqDynamicTruthGlobalOpenedRootRowRightPayload 0 localSigma localPi))
      choiceRoot deepZeroNotOneRoot hdeepRealizable hrightAdequate
      hchoiceZero hnotRight) as [selectedRoot hselected].
    exists witnesses, selectedRoot.
    split; [exact hextended |].
    split; [exact hincluded |].
    exact hselected.
  - subst rootMode.
    assert (hchoiceOne := hchoice).
    rewrite coqDynamicTruthGlobalOpenedRootRowChoice_tagged_shape,
      rawTemplateFormula_or, !rawTemplateFormula_and in hchoiceOne.
    assert (hnotLeft : RawCodedPALocalProofOf M
        (rawTemplateContextCodeOnTail translation extendedContext deepPrefix)
        (rawFormulaImpCode M
          (rawTemplateFormula translation
            (coqDynamicTruthGlobalOpenedRootRowLeftTag
              1 localSigma localPi))
          (rawFormulaBotCode M)) deepOneNotZeroRoot).
    {
      change (RawCodedPALocalProofOf M
        (rawTemplateContextCodeOnTail translation extendedContext deepPrefix)
        (rawTemplateFormula translation
          (tfImp (embedPAFormula oneEqualsZeroFormula) tfBot))
        deepOneNotZeroRoot) in hdeepOneNotZero.
      rewrite rawTemplateFormula_imp, rawTemplateFormula_bot
        in hdeepOneNotZero.
      rewrite coqDynamicTruthGlobalOpenedRootRowLeftTag_one.
      exact hdeepOneNotZero.
    }
    assert (hleftAdequate : RawCodedFormulaAtomicallyAdequate M
        (rawFormulaAndCode M
          (rawTemplateFormula translation
            (coqDynamicTruthGlobalOpenedRootRowLeftTag
              1 localSigma localPi))
          (rawTemplateFormula translation
            (coqDynamicTruthGlobalOpenedRootRowLeftPayload
              1 localSigma localPi)))).
    {
      rewrite <- rawTemplateFormula_and.
      exact (raw_codedTemplateFormula_atomically_adequate_core
        M hPA translation
        (tfAnd
          (coqDynamicTruthGlobalOpenedRootRowLeftTag
            1 localSigma localPi)
          (coqDynamicTruthGlobalOpenedRootRowLeftPayload
            1 localSigma localPi))).
    }
    destruct (raw_codedPALocalProofOf_taggedChoice_right M hPA
      (rawTemplateContextCodeOnTail translation extendedContext deepPrefix)
      (rawTemplateFormula translation
        (coqDynamicTruthGlobalOpenedRootRowLeftTag 1 localSigma localPi))
      (rawTemplateFormula translation
        (coqDynamicTruthGlobalOpenedRootRowLeftPayload 1 localSigma localPi))
      (rawTemplateFormula translation
        (coqDynamicTruthGlobalOpenedRootRowRightTag 1 localSigma localPi))
      (rawTemplateFormula translation
        (coqDynamicTruthGlobalOpenedRootRowRightPayload 1 localSigma localPi))
      choiceRoot deepOneNotZeroRoot hdeepRealizable hleftAdequate
      hchoiceOne hnotLeft) as [selectedRoot hselected].
    exists witnesses, selectedRoot.
    split; [exact hextended |].
    split; [exact hincluded |].
    exact hselected.
Qed.

End PABoundedRawCodedDynamicTruthGlobalOpenedRowSelection.
