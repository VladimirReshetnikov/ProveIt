(**
  Package the genuine selected Sigma/Or case with its correlated domain.

  The selected-bottom compiler first applies the global Ex10 source, opens
  its traversal witnesses, and substitutes the root row fields with

      [#8; 0; code(bottom); 0; 0].

  Its local Or leaf is therefore a capture-safe substitution instance of the
  generic Sigma/Or leaf, not the historical append-side [#2] instance.  This
  module follows that substitution through the eight local binders and, in
  the Or case only, packages the selected domain and Or leaf beneath one
  shared Ex8 spine.  The result is the substituted instance of the
  correlated constructor source consumed by the honest Sigma/Or compiler.
*)

From Stdlib Require Import List.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedContextLists
  RawCodedProofAssumptionLeaf
  RawCodedProofBinaryConstructors
  RawCodedProofImpIConstructor
  RawCodedRestrictedPAProof
  RawCodedPAAxiomWitnessPrefix
  RawCodedPALocalProofExistential
  RawCodedPALocalProofComposition
  RawCodedPALocalProofConjunction
  RawCodedPALocalProofPropositionalRules
  RawCodedPALocalProofExistentialIntroductionChain
  RawCodedPALocalProofExistentialEliminationChain
  RawCodedPALocalProofUniversalEliminationChain
  RawCodedTemplateSyntax
  RawCodedTemplateProofCompiler
  RawCodedTemplateProofCompilerSelfShiftTail
  RawCodedRestrictedPADerivationSoundnessDirectRuleDispatchFrontier
  RawCodedRestrictedPATemplateTernaryApplicationCompilation
  RawCodedFourStateTableAppendProofCompilation
  RawCodedFourStateTableAppendRowLtSuccCases
  RawCodedFourStateTableAppendGlobalTraversalAssembly
  RawCodedDynamicTruthPredecessorGlobalExistentialElimination
  RawCodedDynamicTruthGlobalOpenedRowSelection
  RawCodedDynamicTruthUniversalLeafSourceTemplate
  RawCodedDynamicTruthSuccessorRowsAppendNormalization
  RawCodedDynamicTruthSigmaOrFixedProductionTemplate
  RawCodedDynamicTruthLocalCollisionMatrixAssembly
  RawCodedDynamicTruthSigmaOrCorrelatedConstructorConsumer
  RawCodedRestrictedPASelectedSigmaBottomGlobalOpenedSevenCaseBoundary.

Module
  PABoundedRawCodedRestrictedPASelectedSigmaBottomOrCorrelatedSourceBridge.

Import ListNotations.
Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedContextLists.
Import PABoundedRawCodedProofAssumptionLeaf.
Import PABoundedRawCodedProofBinaryConstructors.
Import PABoundedRawCodedProofImpIConstructor.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedPAAxiomWitnessPrefix.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPALocalProofComposition.
Import PABoundedRawCodedPALocalProofConjunction.
Import PABoundedRawCodedPALocalProofPropositionalRules.
Import PABoundedRawCodedPALocalProofExistentialIntroductionChain.
Import PABoundedRawCodedPALocalProofExistentialEliminationChain.
Import PABoundedRawCodedPALocalProofUniversalEliminationChain.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedTemplateProofCompilerSelfShiftTail.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectRuleDispatchFrontier.
Import PABoundedRawCodedRestrictedPATemplateTernaryApplicationCompilation.
Import PABoundedRawCodedFourStateTableAppendProofCompilation.
Import PABoundedRawCodedFourStateTableAppendRowLtSuccCases.
Import PABoundedRawCodedFourStateTableAppendGlobalTraversalAssembly.
Import
  PABoundedRawCodedDynamicTruthPredecessorGlobalExistentialElimination.
Import PABoundedRawCodedDynamicTruthGlobalOpenedRowSelection.
Import PABoundedRawCodedDynamicTruthUniversalLeafSourceTemplate.
Import PABoundedRawCodedDynamicTruthSuccessorRowsAppendNormalization.
Import PABoundedRawCodedDynamicTruthSigmaOrFixedProductionTemplate.
Import PABoundedRawCodedDynamicTruthLocalCollisionMatrixAssembly.
Import
  PABoundedRawCodedDynamicTruthSigmaOrCorrelatedConstructorConsumer.
Import
  PABoundedRawCodedRestrictedPASelectedSigmaBottomGlobalOpenedSevenCaseBoundary.

(** Give the substitution a bridge-local name so every identity below visibly
    uses the same tuple as the genuine applied global row. *)
Definition coqRestrictedPASelectedSigmaBottomOrRowReplacements
    : list TemplateTerm :=
  coqRestrictedPASelectedSigmaBottomAppliedRootRowReplacements.

Lemma coqRestrictedPASelectedSigmaBottomOrRowReplacements_exact :
  coqRestrictedPASelectedSigmaBottomOrRowReplacements =
  [ ttVar 8;
    embedPATerm (Term.numeral 0);
    coqRestrictedPASelectedSigmaBottomGlobalFirstArgument;
    coqRestrictedPASelectedSigmaBottomGlobalZeroArgument;
    coqRestrictedPASelectedSigmaBottomGlobalZeroArgument ].
Proof. reflexivity. Qed.

(** The global ternary application happens outside ten existential and five
    universal binders.  Its three substitutions therefore reach a local row
    through fifteen [up] operations.  Naming that transformation separately
    records the part which precedes the five root-row openings. *)
Definition coqRestrictedPASelectedSigmaBottomApplyGlobalTernaryToLocal
    (input : TemplateFormula) : TemplateFormula :=
  templateFormulaSubst
    (templateTermSubstitutionLiftMany 15
      (templateInstTerm
        coqRestrictedPASelectedSigmaBottomGlobalZeroArgument))
    (templateFormulaSubst
      (templateTermSubstitutionLiftMany 15
        (templateInstTerm
          (coqRestrictedPATemplateTernarySecondLifted
            coqRestrictedPASelectedSigmaBottomGlobalZeroArgument)))
      (templateFormulaSubst
        (templateTermSubstitutionLiftMany 15
          (templateInstTerm
            (coqRestrictedPATemplateTernaryFirstLifted
              coqRestrictedPASelectedSigmaBottomGlobalFirstArgument)))
        input)).

Definition coqRestrictedPASelectedSigmaBottomSubstituteLocal
    (input : TemplateFormula) : TemplateFormula :=
  templateFormulaOpenSequenceUnderBinders
    (coqRestrictedPASelectedSigmaBottomApplyGlobalTernaryToLocal input)
    coqRestrictedPASelectedSigmaBottomOrRowReplacements.

(** Capture-safe substitution acts on a complete Ex8 source, rather than on
    its bare body.  This lifts every row replacement past the eight local
    binders and leaves their variables [#7] through [#0] untouched. *)
Definition coqRestrictedPASelectedSigmaBottomSubstituteLocalEx8
    (body : TemplateFormula) : TemplateFormula :=
  coqRestrictedPASelectedSigmaBottomSubstituteLocal
    (rawCoqTemplateExN 8 body).

Definition coqRestrictedPASelectedSigmaBottomSubstitutedLocalBody
    (body : TemplateFormula) : TemplateFormula :=
  match templateExistentialBodyMany 8
    (coqRestrictedPASelectedSigmaBottomSubstituteLocalEx8 body) with
  | Some opened => opened
  | None => tfBot
  end.

Definition
    coqRestrictedPASelectedSigmaBottomOrCorrelatedSourceTemplate
    : TemplateFormula :=
  coqRestrictedPASelectedSigmaBottomSubstituteLocal
    coqDynamicTruthSigmaOrCorrelatedConstructorSourceTemplate.

Definition
    coqRestrictedPASelectedSigmaBottomOrCorrelatedBodyTemplate
    : TemplateFormula :=
  tfAnd coqRestrictedPASelectedSigmaBottomNativeOpenedSigmaDomain
    (coqRestrictedPASelectedSigmaBottomNativeOpenedSigmaBranch
      DTLocalSigmaOr).

Lemma
    coqRestrictedPASelectedSigmaBottomAppliedRootRowSelectedPayload_open_sequence :
  forall localSigma localPi,
  coqRestrictedPASelectedSigmaBottomAppliedRootRowSelectedPayload
      localSigma localPi =
  coqRestrictedPASelectedSigmaBottomSubstituteLocal localSigma.
Proof.
  intros localSigma localPi.
  unfold
    coqRestrictedPASelectedSigmaBottomAppliedRootRowSelectedPayload,
    coqRestrictedPASelectedSigmaBottomAppliedRootRowLeftBranch,
    coqRestrictedPASelectedSigmaBottomAppliedRootRowChoice,
    coqRestrictedPASelectedSigmaBottomAppliedRootRowFormula,
    coqRestrictedPASelectedSigmaBottomAppliedGlobalRows,
    coqRestrictedPASelectedSigmaBottomAppliedGlobalTraversalBody,
    coqRestrictedPASelectedSigmaBottomAppliedGlobalSource,
    coqRestrictedPASelectedSigmaBottomGlobalSource,
    coqRestrictedPASelectedSigmaBottomOrRowReplacements,
    coqRestrictedPASelectedSigmaBottomAppliedRootRowReplacements,
    coqDynamicTruthGlobalExistentialSource,
    coqDynamicTruthGlobalTraversalBodyTemplate,
    coqDynamicTruthGlobalRowsTemplate,
    templateAnd7Seventh, templateAndSecond,
    templateOrLeftOrBot, templateAndRightOrBot,
    templateImpConsequent, templateUniversalOpenManyOrBot,
    coqRestrictedPASelectedSigmaBottomAppliedGlobalSource,
    coqRestrictedPATemplateTernaryApplication,
    coqRestrictedPATemplateTernarySecondResult,
    coqRestrictedPATemplateTernaryFirstResult,
    coqRestrictedPASelectedSigmaBottomSubstituteLocal,
    coqRestrictedPASelectedSigmaBottomApplyGlobalTernaryToLocal.
  cbn [templateExistentialBodyMany templateUniversalOpenMany
    templateFormulaOpenSequenceUnderBinders
    templateTermSubstitutionLiftMany templateFormulaOpen
    templateFormulaSubst templateTermSubst templateTermUpSubst
    templateInstTerm].
  reflexivity.
Qed.

(** The selected global payload is literally the same five-field
    substitution applied to the shared local Sigma row. *)
Lemma coqRestrictedPASelectedSigmaBottomNativeOpenedSigmaRow_substitution :
  coqRestrictedPASelectedSigmaBottomNativeOpenedSigmaRow =
  coqRestrictedPASelectedSigmaBottomSubstituteLocal
    coqDynamicTruthSharedSigmaSuccessorRowTemplate.
Proof.
  apply
    coqRestrictedPASelectedSigmaBottomAppliedRootRowSelectedPayload_open_sequence.
Qed.

(** Component identities are stated through complete Ex8 wrappers, making
    the binder lifting explicit rather than silently substituting into the
    local witness slots. *)
Lemma coqRestrictedPASelectedSigmaBottomNativeOpenedSigmaDomain_substitution :
  coqRestrictedPASelectedSigmaBottomNativeOpenedSigmaDomain =
  coqRestrictedPASelectedSigmaBottomSubstitutedLocalBody
    coqDynamicTruthSigmaDomainLeafTemplate.
Proof. reflexivity. Qed.

Lemma coqRestrictedPASelectedSigmaBottomNativeOpenedSigmaOr_substitution :
  coqRestrictedPASelectedSigmaBottomNativeOpenedSigmaBranch
      DTLocalSigmaOr =
  coqRestrictedPASelectedSigmaBottomSubstitutedLocalBody
    coqDynamicTruthSigmaOrLeafTemplate.
Proof. reflexivity. Qed.

(** This is the exact bridge to the generic correlated source: after the
    five global-row replacements, its body is the selected domain conjoined
    with the selected Or leaf, still sharing all eight local witnesses. *)
Lemma
    coqRestrictedPASelectedSigmaBottomOrCorrelatedSourceTemplate_ex8_shape :
  coqRestrictedPASelectedSigmaBottomOrCorrelatedSourceTemplate =
  rawCoqTemplateExN 8
    coqRestrictedPASelectedSigmaBottomOrCorrelatedBodyTemplate.
Proof. reflexivity. Qed.

(** The same rename/open cancellation used by the generic consumer now
    applies to the substituted body without inspecting that large formula. *)
Lemma
    coqRestrictedPASelectedSigmaBottomOrCorrelatedSource_opened_rename8 :
  templateExistentialWitnessOpeningMany
    coqDynamicTruthSigmaOrHonestConstructorWitnesses
    (rawCoqTemplateRenameN 8
      coqRestrictedPASelectedSigmaBottomOrCorrelatedSourceTemplate) =
  coqRestrictedPASelectedSigmaBottomOrCorrelatedBodyTemplate.
Proof.
  rewrite
    coqRestrictedPASelectedSigmaBottomOrCorrelatedSourceTemplate_ex8_shape.
  apply coqDynamicTruthSigmaOr_open_fresh_after_rename8_ex8.
Qed.

(** The Or case has one additional literal branch assumption above the
    eight-witness local context.  The selected row body remains immediately
    below it, so both the domain and Or leaf refer to the same eigenvariables. *)
Definition coqRestrictedPASelectedSigmaBottomOrCaseContextOn
    (sourcePrefix : TemplateContext) : TemplateContext :=
  coqRestrictedPASelectedSigmaBottomNativeOpenedSigmaBranch DTLocalSigmaOr
  :: coqRestrictedPASelectedSigmaBottomNativeLocalDeepContextOn sourcePrefix.

Definition coqRestrictedPASelectedSigmaBottomOrCaseBodyAssumption
    (sourcePrefix : TemplateContext) : TemplateRawProof :=
  trpAss (coqRestrictedPASelectedSigmaBottomOrCaseContextOn sourcePrefix)
    coqRestrictedPASelectedSigmaBottomNativeOpenedSigmaBody.

Definition coqRestrictedPASelectedSigmaBottomOrCaseDomainProof
    (sourcePrefix : TemplateContext) : TemplateRawProof :=
  trpAndE1
    (coqRestrictedPASelectedSigmaBottomOrCaseContextOn sourcePrefix)
    coqRestrictedPASelectedSigmaBottomNativeOpenedSigmaDomain
    coqRestrictedPASelectedSigmaBottomNativeOpenedSigmaOr7
    (coqRestrictedPASelectedSigmaBottomOrCaseBodyAssumption sourcePrefix).

Definition coqRestrictedPASelectedSigmaBottomOrCaseLeafAssumption
    (sourcePrefix : TemplateContext) : TemplateRawProof :=
  trpAss (coqRestrictedPASelectedSigmaBottomOrCaseContextOn sourcePrefix)
    (coqRestrictedPASelectedSigmaBottomNativeOpenedSigmaBranch
      DTLocalSigmaOr).

Definition coqRestrictedPASelectedSigmaBottomOrCaseCorrelatedBodyProof
    (sourcePrefix : TemplateContext) : TemplateRawProof :=
  trpAndI
    (coqRestrictedPASelectedSigmaBottomOrCaseContextOn sourcePrefix)
    coqRestrictedPASelectedSigmaBottomNativeOpenedSigmaDomain
    (coqRestrictedPASelectedSigmaBottomNativeOpenedSigmaBranch
      DTLocalSigmaOr)
    (coqRestrictedPASelectedSigmaBottomOrCaseDomainProof sourcePrefix)
    (coqRestrictedPASelectedSigmaBottomOrCaseLeafAssumption sourcePrefix).

Definition coqRestrictedPASelectedSigmaBottomOrCaseRenamedSourceProof
    (sourcePrefix : TemplateContext) : TemplateRawProof :=
  templateExistentialWitnessIntroductionFrom
    (coqRestrictedPASelectedSigmaBottomOrCaseContextOn sourcePrefix)
    coqDynamicTruthSigmaOrHonestConstructorWitnesses
    (rawCoqTemplateRenameN 8
      coqRestrictedPASelectedSigmaBottomOrCorrelatedSourceTemplate)
    (coqRestrictedPASelectedSigmaBottomOrCaseCorrelatedBodyProof
      sourcePrefix).

Lemma coqRestrictedPASelectedSigmaBottomOrCaseBodyAssumption_derives :
  forall sourcePrefix,
  TemplateRawDerives
    (coqRestrictedPASelectedSigmaBottomOrCaseContextOn sourcePrefix)
    coqRestrictedPASelectedSigmaBottomNativeOpenedSigmaBody
    (coqRestrictedPASelectedSigmaBottomOrCaseBodyAssumption sourcePrefix).
Proof.
  intro sourcePrefix.
  apply templateRawDerives_assumption.
  right.
  destruct
    (coqRestrictedPASelectedSigmaBottomNativeLocalDeepContextOn_head
      sourcePrefix) as [tail ->].
  left. reflexivity.
Qed.

Lemma coqRestrictedPASelectedSigmaBottomOrCaseDomainProof_derives :
  forall sourcePrefix,
  TemplateRawDerives
    (coqRestrictedPASelectedSigmaBottomOrCaseContextOn sourcePrefix)
    coqRestrictedPASelectedSigmaBottomNativeOpenedSigmaDomain
    (coqRestrictedPASelectedSigmaBottomOrCaseDomainProof sourcePrefix).
Proof.
  intro sourcePrefix.
  destruct
    (coqRestrictedPASelectedSigmaBottomOrCaseBodyAssumption_derives
      sourcePrefix) as [hvalid [hcontext hconclusion]].
  unfold coqRestrictedPASelectedSigmaBottomOrCaseDomainProof,
    TemplateRawDerives.
  cbn [TemplateRawProofValid templateRawContext templateRawConclusion].
  repeat split; assumption || reflexivity.
Qed.

Lemma coqRestrictedPASelectedSigmaBottomOrCaseLeafAssumption_derives :
  forall sourcePrefix,
  TemplateRawDerives
    (coqRestrictedPASelectedSigmaBottomOrCaseContextOn sourcePrefix)
    (coqRestrictedPASelectedSigmaBottomNativeOpenedSigmaBranch
      DTLocalSigmaOr)
    (coqRestrictedPASelectedSigmaBottomOrCaseLeafAssumption sourcePrefix).
Proof.
  intro sourcePrefix.
  apply templateRawDerives_assumption.
  left. reflexivity.
Qed.

Lemma
    coqRestrictedPASelectedSigmaBottomOrCaseCorrelatedBodyProof_derives :
  forall sourcePrefix,
  TemplateRawDerives
    (coqRestrictedPASelectedSigmaBottomOrCaseContextOn sourcePrefix)
    coqRestrictedPASelectedSigmaBottomOrCorrelatedBodyTemplate
    (coqRestrictedPASelectedSigmaBottomOrCaseCorrelatedBodyProof
      sourcePrefix).
Proof.
  intro sourcePrefix.
  unfold
    coqRestrictedPASelectedSigmaBottomOrCaseCorrelatedBodyProof,
    coqRestrictedPASelectedSigmaBottomOrCorrelatedBodyTemplate.
  apply coqDynamicTruthSigmaOr_templateRawDerives_andI.
  - apply coqRestrictedPASelectedSigmaBottomOrCaseDomainProof_derives.
  - apply coqRestrictedPASelectedSigmaBottomOrCaseLeafAssumption_derives.
Qed.

Theorem coqRestrictedPASelectedSigmaBottomOrCaseRenamedSourceProof_derives :
  forall sourcePrefix,
  TemplateRawDerives
    (coqRestrictedPASelectedSigmaBottomOrCaseContextOn sourcePrefix)
    (rawCoqTemplateRenameN 8
      coqRestrictedPASelectedSigmaBottomOrCorrelatedSourceTemplate)
    (coqRestrictedPASelectedSigmaBottomOrCaseRenamedSourceProof
      sourcePrefix).
Proof.
  intro sourcePrefix.
  apply templateExistentialWitnessIntroductionFrom_derives.
  rewrite
    coqRestrictedPASelectedSigmaBottomOrCorrelatedSource_opened_rename8.
  apply
    coqRestrictedPASelectedSigmaBottomOrCaseCorrelatedBodyProof_derives.
Qed.

(** Compile the Or-case proof and discharge only its literal Or-leaf head.
    The resulting represented implication lives in the genuine local
    eight-witness context selected from the applied global row. *)
Theorem
    raw_codedPALocalProofOf_selectedSigmaBottom_or_case_correlated_source_imp :
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
        (tfImp
          (coqRestrictedPASelectedSigmaBottomNativeOpenedSigmaBranch
            DTLocalSigmaOr)
          (rawCoqTemplateRenameN 8
            coqRestrictedPASelectedSigmaBottomOrCorrelatedSourceTemplate)))
      root.
Proof.
  intros M hPA translation witnessList baseContext sourcePrefix
    hwitnessed.
  set (caseProof :=
    coqRestrictedPASelectedSigmaBottomOrCaseRenamedSourceProof
      sourcePrefix).
  pose proof
    (raw_templateProofOnPAAxiomContext_localProof
      M hPA translation witnessList baseContext caseProof hwitnessed
      (proj1
        (coqRestrictedPASelectedSigmaBottomOrCaseRenamedSourceProof_derives
          sourcePrefix))) as hcase.
  unfold caseProof in hcase.
  lazymatch type of hcase with
  | RawCodedPALocalProofOf _ _ _ ?caseRoot =>
      change (RawCodedPALocalProofOf M
        (rawTemplateContextCodeOnTail translation baseContext
          (coqRestrictedPASelectedSigmaBottomOrCaseContextOn sourcePrefix))
        (rawTemplateFormula translation
          (rawCoqTemplateRenameN 8
            coqRestrictedPASelectedSigmaBottomOrCorrelatedSourceTemplate))
        caseRoot) in hcase
  end.
  unfold coqRestrictedPASelectedSigmaBottomOrCaseContextOn in hcase.
  cbn [rawTemplateContextCodeOnTail] in hcase.
  lazymatch type of hcase with
  | RawCodedPALocalProofOf _ _ _ ?caseRoot =>
      exists
        (rawProofImpIRoot M
          (rawTemplateContextCodeOnTail translation baseContext
            (coqRestrictedPASelectedSigmaBottomNativeLocalDeepContextOn
              sourcePrefix))
          (rawTemplateFormula translation
            (coqRestrictedPASelectedSigmaBottomNativeOpenedSigmaBranch
              DTLocalSigmaOr))
          (rawTemplateFormula translation
            (rawCoqTemplateRenameN 8
              coqRestrictedPASelectedSigmaBottomOrCorrelatedSourceTemplate))
          caseRoot);
      rewrite rawTemplateFormula_imp;
      exact
        (raw_codedPALocalProofOf_impI M hPA
          (rawTemplateContextCodeOnTail translation baseContext
            (coqRestrictedPASelectedSigmaBottomNativeLocalDeepContextOn
              sourcePrefix))
          (rawTemplateFormula translation
            (coqRestrictedPASelectedSigmaBottomNativeOpenedSigmaBranch
              DTLocalSigmaOr))
          (rawTemplateFormula translation
            (rawCoqTemplateRenameN 8
              coqRestrictedPASelectedSigmaBottomOrCorrelatedSourceTemplate))
          caseRoot hcase)
  end.
Qed.

(** Applying the compiled adapter to the actual Or residual preserves the
    local eigenvariable context and produces the shifted Ex8 package needed
    as the continuation of the selected-row elimination. *)
Theorem
    raw_codedPALocalProofOf_selectedSigmaBottom_or_case_correlated_source_of_root :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M)
    witnessList baseContext sourcePrefix orRoot,
  RawCodedPAAxiomWitnessContext M witnessList baseContext ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail translation baseContext
      (coqRestrictedPASelectedSigmaBottomNativeLocalDeepContextOn
        sourcePrefix))
    (rawTemplateFormula translation
      (coqRestrictedPASelectedSigmaBottomNativeOpenedSigmaBranch
        DTLocalSigmaOr)) orRoot ->
  exists root,
    RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation baseContext
        (coqRestrictedPASelectedSigmaBottomNativeLocalDeepContextOn
          sourcePrefix))
      (rawTemplateFormula translation
        (rawCoqTemplateRenameN 8
          coqRestrictedPASelectedSigmaBottomOrCorrelatedSourceTemplate))
      root.
Proof.
  intros M hPA translation witnessList baseContext sourcePrefix orRoot
    hwitnessed hor.
  destruct
    (raw_codedPALocalProofOf_selectedSigmaBottom_or_case_correlated_source_imp
      M hPA translation witnessList baseContext sourcePrefix hwitnessed)
    as [impRoot himp].
  rewrite rawTemplateFormula_imp in himp.
  lazymatch type of himp with
  | RawCodedPALocalProofOf _ _ _ ?actualImpRoot =>
      exists
        (rawProofImpERoot M
          (rawTemplateContextCodeOnTail translation baseContext
            (coqRestrictedPASelectedSigmaBottomNativeLocalDeepContextOn
              sourcePrefix))
          (rawTemplateFormula translation
            (coqRestrictedPASelectedSigmaBottomNativeOpenedSigmaBranch
              DTLocalSigmaOr))
          (rawTemplateFormula translation
            (rawCoqTemplateRenameN 8
              coqRestrictedPASelectedSigmaBottomOrCorrelatedSourceTemplate))
          actualImpRoot orRoot);
      exact
        (raw_codedPALocalProofOf_impE M hPA
          (rawTemplateContextCodeOnTail translation baseContext
            (coqRestrictedPASelectedSigmaBottomNativeLocalDeepContextOn
              sourcePrefix))
          (rawTemplateFormula translation
            (coqRestrictedPASelectedSigmaBottomNativeOpenedSigmaBranch
              DTLocalSigmaOr))
          (rawTemplateFormula translation
            (rawCoqTemplateRenameN 8
              coqRestrictedPASelectedSigmaBottomOrCorrelatedSourceTemplate))
          actualImpRoot orRoot himp hor)
  end.
Qed.

(** Close the eight local existential eliminations against the genuine
    selected row root.  The conclusion is the unshifted substituted Ex8
    source in the same applied-global Ex10 eigencontext where that selected
    row was obtained.  Thus the adapter neither invents a replacement tuple
    nor transports between the honest parent-code slot [#10] and the
    historical append-side slot [#2]. *)
Theorem
    raw_codedPALocalProofOf_selectedSigmaBottom_native_applied_or_correlated_source :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M)
    witnessList baseContext sourcePrefix selectedRoot orRoot,
  RawCodedPAAxiomWitnessContext M witnessList baseContext ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail translation baseContext
      (coqRestrictedPASelectedSigmaBottomNativeAppliedGlobalDeepContextOn
        sourcePrefix))
    (rawTemplateFormula translation
      coqRestrictedPASelectedSigmaBottomNativeOpenedSigmaRow)
    selectedRoot ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail translation baseContext
      (coqRestrictedPASelectedSigmaBottomNativeLocalDeepContextOn
        sourcePrefix))
    (rawTemplateFormula translation
      (coqRestrictedPASelectedSigmaBottomNativeOpenedSigmaBranch
        DTLocalSigmaOr)) orRoot ->
  exists root,
    RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation baseContext
        (coqRestrictedPASelectedSigmaBottomNativeAppliedGlobalDeepContextOn
          sourcePrefix))
      (rawTemplateFormula translation
        coqRestrictedPASelectedSigmaBottomOrCorrelatedSourceTemplate)
      root.
Proof.
  intros M hPA translation witnessList baseContext sourcePrefix
    selectedRoot orRoot hwitnessed hselected hor.
  destruct
    (raw_codedPALocalProofOf_selectedSigmaBottom_or_case_correlated_source_of_root
      M hPA translation witnessList baseContext sourcePrefix orRoot
      hwitnessed hor) as [deepRoot hdeep].
  assert (hdeepShifted : RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation baseContext
        (coqRestrictedPASelectedSigmaBottomNativeLocalDeepContextOn
          sourcePrefix))
      (rawTemplateFormula translation
        (templateFormulaShiftMany 8
          coqRestrictedPASelectedSigmaBottomOrCorrelatedSourceTemplate))
      deepRoot).
  {
    rewrite <- raw_coqTemplateRenameN_eq_shiftMany.
    exact hdeep.
  }
  exact
    (raw_codedPALocalProofOf_existential_elimination_chain_on_witnessed_tail
      M hPA translation witnessList baseContext 8
      coqRestrictedPASelectedSigmaBottomNativeOpenedSigmaRow
      (coqRestrictedPASelectedSigmaBottomNativeAppliedGlobalDeepContextOn
        sourcePrefix)
      coqRestrictedPASelectedSigmaBottomOrCorrelatedSourceTemplate
      (coqRestrictedPASelectedSigmaBottomNativeLocalDeepContextOn
        sourcePrefix)
      selectedRoot deepRoot hwitnessed
      (coqRestrictedPASelectedSigmaBottomNativeLocalDeepContextOn_success
        sourcePrefix)
      hselected hdeepShifted).
Qed.

End
  PABoundedRawCodedRestrictedPASelectedSigmaBottomOrCorrelatedSourceBridge.
