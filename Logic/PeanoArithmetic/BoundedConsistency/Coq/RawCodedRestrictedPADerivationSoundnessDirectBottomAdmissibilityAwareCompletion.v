(**
  Admissibility-aware completion of the direct Bottom-E case.

  Recursive Bottom truth is produced at the live assignment coordinates
  [(#9,#8)].  The arbitrary-assignment Sigma refutation proves that this
  very atom implies falsity once aligned native structural inputs identify
  the represented global source with the direct truth selector.  This file
  synchronizes those two compilers on one standard PA witness tail.

  The order of discharge is essential.  From current truth and its
  refutation we obtain bottom in

      [WitnessContextTruth; Admissible; Case; DeepTail].

  Imp-I first discharges witness-context truth and then admissibility.  A
  small checked propositional proof combines the resulting

      Admissible -> (WitnessContextTruth -> bottom)

  with the existing outer-to-witness context-truth transport.  Bot-E then
  supplies conclusion truth.  Thus admissibility remains exactly where the
  public remaining formula requires it; no closed-assignment normalization
  and no premise erasure is involved.
*)

From Stdlib Require Import List.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAListCoding Require Import Representability.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  CodedProof
  RawCodedSyntaxConstructors
  RawCodedContextLists
  RawCodedContextStructure
  RawCodedRestrictedPAProof
  RawCodedPALocalProofExistential
  RawCodedPALocalProofComposition
  RawCodedPALocalProofWitnessedContextMerge
  RawCodedPALocalProofPropositionalRules
  RawCodedProofImpIConstructor
  RawCodedPAAxiomWitnessPrefix
  RawCodedTemplateSyntax
  RawCodedTemplateProofCompiler
  RawCodedTemplatePAEmbedding
  RawCodedTemplatePAEmbeddingSelfShiftTail
  RawCodedTemplateFormulaAtomicAdequacy
  RawCodedTemplateLocalProofWitnessedTailTransport
  RawCodedTemplateLocalProofStandardWitnessTailTransport
  RawCodedTemplateDirectStructuralTranslation
  RawCodedTemplateDirectStructuralPAAgreement
  RawCodedRestrictedPADerivationSoundnessDirectRuleDispatchFrontier
  RawCodedRestrictedPADerivationSoundnessDirectStrongStepShell
  RawCodedRestrictedPADerivationSoundnessDirectAndIntroductionCase
  RawCodedRestrictedPADerivationSoundnessDirectBottomEliminationCase
  RawCodedRestrictedPADerivationSoundnessDirectBottomRecursiveTruthAdmissibleBoundary
  RawCodedRestrictedPASelectedSigmaBottomArbitraryAssignmentRefutation
  RawCodedDynamicTruthNativeLocalStagedCallbackCompilation
  RawCodedDynamicTruthNativeAlignedStrongStepLogicalRootsCompilation.

Import ListNotations.

Module
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectBottomAdmissibilityAwareCompletion.

Import PA.
Import PAListRepresentability.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedCodedProof.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedContextLists.
Import PABoundedRawCodedContextStructure.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPALocalProofComposition.
Import PABoundedRawCodedPALocalProofWitnessedContextMerge.
Import PABoundedRawCodedPALocalProofPropositionalRules.
Import PABoundedRawCodedProofImpIConstructor.
Import PABoundedRawCodedPAAxiomWitnessPrefix.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedTemplatePAEmbedding.
Import PABoundedRawCodedTemplatePAEmbeddingSelfShiftTail.
Import PABoundedRawCodedTemplateFormulaAtomicAdequacy.
Import PABoundedRawCodedTemplateLocalProofWitnessedTailTransport.
Import PABoundedRawCodedTemplateLocalProofStandardWitnessTailTransport.
Import PABoundedRawCodedTemplateDirectStructuralTranslation.
Import PABoundedRawCodedTemplateDirectStructuralPAAgreement.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectRuleDispatchFrontier.
Import PABoundedRawCodedRestrictedPADerivationSoundnessDirectStrongStepShell.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndIntroductionCase.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectBottomEliminationCase.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectBottomRecursiveTruthAdmissibleBoundary.
Import
  PABoundedRawCodedRestrictedPASelectedSigmaBottomArbitraryAssignmentRefutation.
Import
  PABoundedRawCodedDynamicTruthNativeLocalStagedCallbackCompilation.
Import
  PABoundedRawCodedDynamicTruthNativeAlignedStrongStepLogicalRootsCompilation.

(** ------------------------------------------------------------------
    Pure propositional completion with admissibility retained. *)

Definition coqRestrictedPADirectBottomAdmissibilityAwareCompletionTemplate
    : TemplateFormula :=
  tfImp
    (tfImp coqRestrictedPADirectBottomAdmissibleTemplate
      coqRestrictedPADirectBottomAfterEndpointTemplate)
    (tfImp
      (tfImp coqRestrictedPADirectBottomOuterContextTruthTemplate
        coqRestrictedPADirectBottomWitnessContextTruthTemplate)
      coqRestrictedPADirectBottomRemainingTemplate).

Definition coqRestrictedPADirectBottomAdmissibilityAwareContext1 tail :=
  (tfImp coqRestrictedPADirectBottomAdmissibleTemplate
    coqRestrictedPADirectBottomAfterEndpointTemplate) ::
  coqRestrictedPADirectBottomCaseContext tail.

Definition coqRestrictedPADirectBottomAdmissibilityAwareContext2 tail :=
  (tfImp coqRestrictedPADirectBottomOuterContextTruthTemplate
    coqRestrictedPADirectBottomWitnessContextTruthTemplate) ::
  coqRestrictedPADirectBottomAdmissibilityAwareContext1 tail.

Definition coqRestrictedPADirectBottomAdmissibilityAwareContext3 tail :=
  coqRestrictedPADirectBottomAdmissibleTemplate ::
  coqRestrictedPADirectBottomAdmissibilityAwareContext2 tail.

Definition coqRestrictedPADirectBottomAdmissibilityAwareContext4 tail :=
  coqRestrictedPADirectBottomOuterContextTruthTemplate ::
  coqRestrictedPADirectBottomAdmissibilityAwareContext3 tail.

Definition coqRestrictedPADirectBottomAdmissibilityAwareLawRoot tail
    : TemplateRawProof :=
  trpAss (coqRestrictedPADirectBottomAdmissibilityAwareContext4 tail)
    (tfImp coqRestrictedPADirectBottomAdmissibleTemplate
      coqRestrictedPADirectBottomAfterEndpointTemplate).

Definition coqRestrictedPADirectBottomAdmissibilityAwareTransportRoot tail
    : TemplateRawProof :=
  trpAss (coqRestrictedPADirectBottomAdmissibilityAwareContext4 tail)
    (tfImp coqRestrictedPADirectBottomOuterContextTruthTemplate
      coqRestrictedPADirectBottomWitnessContextTruthTemplate).

Definition coqRestrictedPADirectBottomAdmissibilityAwareAdmissibleRoot tail
    : TemplateRawProof :=
  trpAss (coqRestrictedPADirectBottomAdmissibilityAwareContext4 tail)
    coqRestrictedPADirectBottomAdmissibleTemplate.

Definition coqRestrictedPADirectBottomAdmissibilityAwareOuterRoot tail
    : TemplateRawProof :=
  trpAss (coqRestrictedPADirectBottomAdmissibilityAwareContext4 tail)
    coqRestrictedPADirectBottomOuterContextTruthTemplate.

Definition coqRestrictedPADirectBottomAdmissibilityAwareAfterEndpointRoot tail
    : TemplateRawProof :=
  trpImpE (coqRestrictedPADirectBottomAdmissibilityAwareContext4 tail)
    coqRestrictedPADirectBottomAdmissibleTemplate
    coqRestrictedPADirectBottomAfterEndpointTemplate
    (coqRestrictedPADirectBottomAdmissibilityAwareLawRoot tail)
    (coqRestrictedPADirectBottomAdmissibilityAwareAdmissibleRoot tail).

Definition coqRestrictedPADirectBottomAdmissibilityAwareWitnessRoot tail
    : TemplateRawProof :=
  trpImpE (coqRestrictedPADirectBottomAdmissibilityAwareContext4 tail)
    coqRestrictedPADirectBottomOuterContextTruthTemplate
    coqRestrictedPADirectBottomWitnessContextTruthTemplate
    (coqRestrictedPADirectBottomAdmissibilityAwareTransportRoot tail)
    (coqRestrictedPADirectBottomAdmissibilityAwareOuterRoot tail).

Definition coqRestrictedPADirectBottomAdmissibilityAwareBottomRoot tail
    : TemplateRawProof :=
  trpImpE (coqRestrictedPADirectBottomAdmissibilityAwareContext4 tail)
    coqRestrictedPADirectBottomWitnessContextTruthTemplate tfBot
    (coqRestrictedPADirectBottomAdmissibilityAwareAfterEndpointRoot tail)
    (coqRestrictedPADirectBottomAdmissibilityAwareWitnessRoot tail).

Definition coqRestrictedPADirectBottomAdmissibilityAwareConclusionRoot tail
    : TemplateRawProof :=
  trpBotE (coqRestrictedPADirectBottomAdmissibilityAwareContext4 tail)
    coqRestrictedPADirectBottomConclusionTruthTemplate
    (coqRestrictedPADirectBottomAdmissibilityAwareBottomRoot tail).

Definition coqRestrictedPADirectBottomAdmissibilityAwareOuterImpRoot tail
    : TemplateRawProof :=
  trpImpI (coqRestrictedPADirectBottomAdmissibilityAwareContext3 tail)
    coqRestrictedPADirectBottomOuterContextTruthTemplate
    coqRestrictedPADirectBottomConclusionTruthTemplate
    (coqRestrictedPADirectBottomAdmissibilityAwareConclusionRoot tail).

Definition coqRestrictedPADirectBottomAdmissibilityAwareAdmissibleImpRoot tail
    : TemplateRawProof :=
  trpImpI (coqRestrictedPADirectBottomAdmissibilityAwareContext2 tail)
    coqRestrictedPADirectBottomAdmissibleTemplate
    (tfImp coqRestrictedPADirectBottomOuterContextTruthTemplate
      coqRestrictedPADirectBottomConclusionTruthTemplate)
    (coqRestrictedPADirectBottomAdmissibilityAwareOuterImpRoot tail).

Definition coqRestrictedPADirectBottomAdmissibilityAwareTransportImpRoot tail
    : TemplateRawProof :=
  trpImpI (coqRestrictedPADirectBottomAdmissibilityAwareContext1 tail)
    (tfImp coqRestrictedPADirectBottomOuterContextTruthTemplate
      coqRestrictedPADirectBottomWitnessContextTruthTemplate)
    coqRestrictedPADirectBottomRemainingTemplate
    (coqRestrictedPADirectBottomAdmissibilityAwareAdmissibleImpRoot tail).

Definition coqRestrictedPADirectBottomAdmissibilityAwareCompletionRoot tail
    : TemplateRawProof :=
  trpImpI (coqRestrictedPADirectBottomCaseContext tail)
    (tfImp coqRestrictedPADirectBottomAdmissibleTemplate
      coqRestrictedPADirectBottomAfterEndpointTemplate)
    (tfImp
      (tfImp coqRestrictedPADirectBottomOuterContextTruthTemplate
        coqRestrictedPADirectBottomWitnessContextTruthTemplate)
      coqRestrictedPADirectBottomRemainingTemplate)
    (coqRestrictedPADirectBottomAdmissibilityAwareTransportImpRoot tail).

Lemma coqRestrictedPADirectBottomAdmissibilityAwareCompletionRoot_valid :
    forall tail,
  TemplateRawDerives (coqRestrictedPADirectBottomCaseContext tail)
    coqRestrictedPADirectBottomAdmissibilityAwareCompletionTemplate
    (coqRestrictedPADirectBottomAdmissibilityAwareCompletionRoot tail).
Proof.
  intro tail.
  unfold coqRestrictedPADirectBottomAdmissibilityAwareCompletionRoot,
    coqRestrictedPADirectBottomAdmissibilityAwareCompletionTemplate.
  apply coqRestrictedPADirectBottom_templateRawDerives_impI.
  unfold coqRestrictedPADirectBottomAdmissibilityAwareTransportImpRoot.
  apply coqRestrictedPADirectBottom_templateRawDerives_impI.
  unfold coqRestrictedPADirectBottomAdmissibilityAwareAdmissibleImpRoot,
    coqRestrictedPADirectBottomRemainingTemplate.
  apply coqRestrictedPADirectBottom_templateRawDerives_impI.
  unfold coqRestrictedPADirectBottomAdmissibilityAwareOuterImpRoot.
  apply coqRestrictedPADirectBottom_templateRawDerives_impI.
  unfold coqRestrictedPADirectBottomAdmissibilityAwareConclusionRoot.
  apply coqRestrictedPADirectBottom_templateRawDerives_botE.
  unfold coqRestrictedPADirectBottomAdmissibilityAwareBottomRoot.
  apply coqRestrictedPADirectBottom_templateRawDerives_impE.
  - unfold coqRestrictedPADirectBottomAdmissibilityAwareAfterEndpointRoot.
    apply coqRestrictedPADirectBottom_templateRawDerives_impE.
    + apply templateRawDerives_assumption.
      unfold coqRestrictedPADirectBottomAdmissibilityAwareContext4,
        coqRestrictedPADirectBottomAdmissibilityAwareContext3,
        coqRestrictedPADirectBottomAdmissibilityAwareContext2,
        coqRestrictedPADirectBottomAdmissibilityAwareContext1.
      right. right. right. left. reflexivity.
    + apply templateRawDerives_assumption.
      unfold coqRestrictedPADirectBottomAdmissibilityAwareContext4.
      right. left. reflexivity.
  - unfold coqRestrictedPADirectBottomAdmissibilityAwareWitnessRoot.
    apply coqRestrictedPADirectBottom_templateRawDerives_impE.
    + apply templateRawDerives_assumption.
      unfold coqRestrictedPADirectBottomAdmissibilityAwareContext4,
        coqRestrictedPADirectBottomAdmissibilityAwareContext3,
        coqRestrictedPADirectBottomAdmissibilityAwareContext2.
      right. right. left. reflexivity.
    + apply templateRawDerives_assumption.
      unfold coqRestrictedPADirectBottomAdmissibilityAwareContext4.
      left. reflexivity.
Qed.

(** ------------------------------------------------------------------
    Exact current-assignment source identification. *)

Definition RawCoqRestrictedPADirectBottomCurrentSourceIdentification
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M) : Prop :=
  rawTemplateFormula
    (rawDirectStructuralTemplateTranslation M hPA inputs)
    (coqRestrictedPASelectedSigmaBottomAssignmentSourceAt 9 8) =
  rawTemplateFormula
    (rawDirectStructuralTemplateTranslation M hPA inputs)
    coqRestrictedPADirectBottomCurrentTruthTemplate.

Arguments RawCoqRestrictedPADirectBottomCurrentSourceIdentification
  M hPA inputs : clear implicits.

(** The first public compiler returns the literal remaining formula in the
    case context.  Its caller chooses an already accumulated standard PA
    prefix; all witnesses introduced here are returned as one suffix. *)
Definition
    RawCoqRestrictedPADirectBottomAdmissibilityAwareRemainingStandardTailCompiler
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M) : Prop :=
  forall baseWitnesses : StandardPAAxiomWitnessPrefix,
  exists (suffix : StandardPAAxiomWitnessPrefix) (remainingRoot : M),
    RawCodedPALocalProofOf M
      (rawTemplateContextCode
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        (coqRestrictedPADirectBottomCaseContext
          (embedPAContext
            (map witnessedAxiom (baseWitnesses ++ suffix)))))
      (rawTemplateFormula
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        coqRestrictedPADirectBottomRemainingTemplate)
      remainingRoot.

Arguments
  RawCoqRestrictedPADirectBottomAdmissibilityAwareRemainingStandardTailCompiler
  M hPA inputs : clear implicits.

Definition
    RawCoqRestrictedPADirectBottomAdmissibilityAwareCaseStandardTailCompiler
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M) : Prop :=
  forall baseWitnesses : StandardPAAxiomWitnessPrefix,
  exists (suffix : StandardPAAxiomWitnessPrefix) (caseRoot : M),
    RawCodedPALocalProofOf M
      (rawTemplateContextCode
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        (coqRestrictedPADirectBottomDeepContext
          (embedPAContext
            (map witnessedAxiom (baseWitnesses ++ suffix)))))
      (rawFormulaImpCode M
        (rawTemplateFormula
          (rawDirectStructuralTemplateTranslation M hPA inputs)
          coqRestrictedPADirectBottomCaseTemplate)
        (rawTemplateFormula
          (rawDirectStructuralTemplateTranslation M hPA inputs)
          coqRestrictedPADirectBottomRemainingTemplate))
      caseRoot.

Arguments
  RawCoqRestrictedPADirectBottomAdmissibilityAwareCaseStandardTailCompiler
  M hPA inputs : clear implicits.

(** Synchronization proof.

    The falsity compiler is first run over the empty PA tail, yielding its
    fixed helper prefix [refutationWitnesses].  Recursive current truth is
    then requested after [baseWitnesses ++ refutationWitnesses], yielding
    [truthSuffix].  Standard-tail transport moves the refutation to

      baseWitnesses ++ (refutationWitnesses ++ truthSuffix),

    exactly the tail at which current truth was produced. *)
Theorem
    raw_bottomAdmissibilityAwareRemaining_standardTail_of_current_source_identification :
  forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (inputs : RawCodedTemplateDirectStructuralInputs M),
  RawCoqRestrictedPADirectBottomCurrentSourceIdentification
    M hPA inputs ->
  RawCoqRestrictedPADirectBottomAdmissibilityAwareRemainingStandardTailCompiler
    M hPA inputs.
Proof.
  intros M hPA inputs hidentification baseWitnesses.
  set (translation :=
    rawDirectStructuralTemplateTranslation M hPA inputs).
  assert (hagreement : RawCodedTemplatePAAgreement M translation).
  {
    unfold translation.
    exact (rawDirectStructuralTemplatePAAgreement M hPA inputs).
  }
  assert (hempty : RawCodedPAAxiomWitnessContext M
      (raw_zero M) (raw_zero M)).
  {
    pose proof (raw_codedPAAxiomWitnessContext_standard M hPA []) as h.
    cbn [rawQuotedPAAxiomWitnessList rawListCode map] in h.
    exact h.
  }

  (** Compile [CurrentTruth -> bottom] before surrounding it with the
      caller's tail. *)
  destruct
    (raw_codedPALocalProofOf_selectedSigmaBottomCurrentAssignment_template_refutation_compiled_growing
      M hPA translation hagreement (raw_zero M) (raw_zero M) hempty)
    as (refutationWitnesses & refutationRoot &
      _hrefutationWitnessed & _hrefutationIncluded & hrefutation).
  assert (hrefutationTail : RawCodedPALocalProofOf M
      (rawTemplateContextCode translation
        (embedPAContext (map witnessedAxiom refutationWitnesses)))
      (rawTemplateFormula translation
        (tfImp
          (coqRestrictedPASelectedSigmaBottomAssignmentSourceAt 9 8)
          tfBot))
      refutationRoot).
  {
    change (RawCodedPALocalProofOf M
      (rawStandardPAAxiomWitnessPrefixContextCode M
        refutationWitnesses (raw_zero M))
      (rawTemplateFormula translation
        (tfImp
          (coqRestrictedPASelectedSigmaBottomAssignmentSourceAt 9 8)
          tfBot))
      refutationRoot) in hrefutation.
    rewrite raw_templateContextCode_as_on_tail_general.
    rewrite (raw_templateContextCodeOnTail_embedPAAxiomWitnesses
      M translation hagreement refutationWitnesses (raw_zero M)).
    exact hrefutation.
  }

  (** The recursive producer keeps both object assumptions visible. *)
  destruct
    (raw_bottomCurrentTruthUnderAdmissibility_standardTail
      M hPA inputs (baseWitnesses ++ refutationWitnesses))
    as (truthSuffix & currentTruthRoot & hcurrentTruth).
  set (suffix := refutationWitnesses ++ truthSuffix).
  set (combinedWitnesses := baseWitnesses ++ suffix).
  assert (hcombinedWitnessed : RawCodedPAAxiomWitnessContext M
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        combinedWitnesses (raw_zero M))
      (rawTemplateContextCode translation
        (embedPAContext (map witnessedAxiom combinedWitnesses)))).
  {
    unfold translation.
    exact (raw_templateEmbeddedPAAxiomWitnessContext
      M hPA (rawDirectStructuralTemplateTranslation M hPA inputs)
      (rawDirectStructuralTemplatePAAgreement M hPA inputs)
      combinedWitnesses).
  }
  assert (hcombinedRealizable : RawContextListRealizable M
      (rawTemplateContextCode translation
        (embedPAContext (map witnessedAxiom combinedWitnesses)))).
  {
    exact
      (PABoundedRawCodedPALocalProofWitnessedContextMerge.raw_codedPAAxiomWitnessContext_context_realizable M
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        combinedWitnesses (raw_zero M))
      (rawTemplateContextCode translation
        (embedPAContext (map witnessedAxiom combinedWitnesses)))
      hcombinedWitnessed).
  }

  (** Surround the refutation by the caller's prefix and the recursive
      producer's suffix, then insert the fixed recursive-ready formulas. *)
  destruct
    (raw_codedPALocalProof_standardWitnessTail_surround_under_prefix
      M hPA translation hagreement
      [] baseWitnesses refutationWitnesses truthSuffix
      (rawTemplateFormula translation
        (tfImp
          (coqRestrictedPASelectedSigmaBottomAssignmentSourceAt 9 8)
          tfBot))
      refutationRoot hrefutationTail)
    as [transportedRefutationRoot htransportedRefutation].
  cbn [List.app] in htransportedRefutation.
  fold suffix in htransportedRefutation.
  fold combinedWitnesses in htransportedRefutation.
  destruct
    (raw_codedPALocalProof_templatePrefix M hPA translation
      (rawTemplateContextCode translation
        (embedPAContext (map witnessedAxiom combinedWitnesses)))
      (coqRestrictedPADirectBottomRecursiveReadyContext [])
      (rawTemplateFormula translation
        (tfImp
          (coqRestrictedPASelectedSigmaBottomAssignmentSourceAt 9 8)
          tfBot))
      transportedRefutationRoot hcombinedRealizable
      (fun formula _ =>
        raw_codedTemplateFormula_atomically_adequate_core
          M hPA translation formula)
      htransportedRefutation)
    as [readyRefutationRoot hreadyRefutation].
  rewrite <- raw_templateContextCode_app_on_tail_general
    in hreadyRefutation.
  rewrite <- coqRestrictedPADirectBottomRecursiveReadyContext_app_witnesses
    in hreadyRefutation.
  unfold RawCoqRestrictedPADirectBottomCurrentSourceIdentification
    in hidentification.
  change (rawTemplateFormula translation
      (coqRestrictedPASelectedSigmaBottomAssignmentSourceAt 9 8) =
    rawTemplateFormula translation
      coqRestrictedPADirectBottomCurrentTruthTemplate)
    in hidentification.
  rewrite rawTemplateFormula_imp, rawTemplateFormula_bot
    in hreadyRefutation.
  rewrite hidentification in hreadyRefutation.

  (** The recursive producer writes its tail with left-associated append;
      the returned suffix uses the canonical right-associated form. *)
  change (RawCodedPALocalProofOf M
    (rawTemplateContextCode translation
      (coqRestrictedPADirectBottomRecursiveReadyContext
        (embedPAContext
          (map witnessedAxiom
            ((baseWitnesses ++ refutationWitnesses) ++ truthSuffix)))))
    (rawTemplateFormula translation
      coqRestrictedPADirectBottomCurrentTruthTemplate)
    currentTruthRoot) in hcurrentTruth.
  assert (hcurrentTail :
      ((baseWitnesses ++ refutationWitnesses) ++ truthSuffix) =
      combinedWitnesses).
  {
    unfold combinedWitnesses, suffix.
    symmetry. apply List.app_assoc.
  }
  rewrite hcurrentTail in hcurrentTruth.

  set (readyCode := rawTemplateContextCode translation
    (coqRestrictedPADirectBottomRecursiveReadyContext
      (embedPAContext (map witnessedAxiom combinedWitnesses)))).
  set (admissibleCode := rawTemplateContextCode translation
    (coqRestrictedPADirectBottomAdmissibleContext
      (embedPAContext (map witnessedAxiom combinedWitnesses)))).
  set (caseCode := rawTemplateContextCode translation
    (coqRestrictedPADirectBottomCaseContext
      (embedPAContext (map witnessedAxiom combinedWitnesses)))).

  (** Current truth meets its assignment-preserving refutation. *)
  pose proof
    (raw_codedPALocalProofOf_impE M hPA readyCode
      (rawTemplateFormula translation
        coqRestrictedPADirectBottomCurrentTruthTemplate)
      (rawFormulaBotCode M)
      readyRefutationRoot currentTruthRoot
      hreadyRefutation hcurrentTruth) as hbottom.

  (** These are the only two discharges.  In particular, admissibility is
      retained as an antecedent rather than removed. *)
  pose proof
    (raw_codedPALocalProofOf_impI M hPA admissibleCode
      (rawTemplateFormula translation
        coqRestrictedPADirectBottomWitnessContextTruthTemplate)
      (rawFormulaBotCode M) _ hbottom) as hwitnessLaw.
  (** Rocq's strict kernel checker does not infer anonymous proof-root
      carriers in proposition annotations.  Preserve the root already
      synthesized by [impI] and expose only the equivalent template view. *)
  lazymatch type of hwitnessLaw with
  | RawCodedPALocalProofOf _ _ _ ?witnessLawRoot =>
      assert (hwitnessLawTemplate : RawCodedPALocalProofOf M admissibleCode
        (rawTemplateFormula translation
          coqRestrictedPADirectBottomAfterEndpointTemplate)
        witnessLawRoot)
  end.
  {
    unfold coqRestrictedPADirectBottomAfterEndpointTemplate.
    rewrite rawTemplateFormula_imp, rawTemplateFormula_bot.
    exact hwitnessLaw.
  }
  pose proof
    (raw_codedPALocalProofOf_impI M hPA caseCode
      (rawTemplateFormula translation
        coqRestrictedPADirectBottomAdmissibleTemplate)
      (rawTemplateFormula translation
        coqRestrictedPADirectBottomAfterEndpointTemplate)
      _ hwitnessLawTemplate) as hadmissibleLaw.
  lazymatch type of hadmissibleLaw with
  | RawCodedPALocalProofOf _ _ _ ?admissibleLawRoot =>
      assert (hadmissibleLawTemplate : RawCodedPALocalProofOf M caseCode
        (rawTemplateFormula translation
          (tfImp coqRestrictedPADirectBottomAdmissibleTemplate
            coqRestrictedPADirectBottomAfterEndpointTemplate))
        admissibleLawRoot)
  end.
  {
    rewrite rawTemplateFormula_imp.
    exact hadmissibleLaw.
  }

  (** Compile and apply the checked propositional completion.  Its Bot-E
      node is the sole conversion from object-level bottom to conclusion
      truth. *)
  pose proof
    (raw_templateProof_localProof M hPA translation
      (coqRestrictedPADirectBottomAdmissibilityAwareCompletionRoot
        (embedPAContext (map witnessedAxiom combinedWitnesses)))
      (proj1
        (coqRestrictedPADirectBottomAdmissibilityAwareCompletionRoot_valid
          (embedPAContext (map witnessedAxiom combinedWitnesses)))))
    as hcompletion.
  unfold coqRestrictedPADirectBottomAdmissibilityAwareCompletionTemplate
    in hcompletion.
  pose proof
    (PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndIntroductionCase.raw_codedPALocalProofOf_coqRestrictedPADirect_templateImpE
      M hPA translation
      (coqRestrictedPADirectBottomCaseContext
        (embedPAContext (map witnessedAxiom combinedWitnesses)))
      (tfImp coqRestrictedPADirectBottomAdmissibleTemplate
        coqRestrictedPADirectBottomAfterEndpointTemplate)
      (tfImp
        (tfImp coqRestrictedPADirectBottomOuterContextTruthTemplate
          coqRestrictedPADirectBottomWitnessContextTruthTemplate)
        coqRestrictedPADirectBottomRemainingTemplate)
      _ _ hcompletion hadmissibleLawTemplate) as hafterLaw.
  pose proof
    (raw_templateProof_localProof M hPA translation
      (coqRestrictedPADirectBottomContextTruthTransportRoot
        (embedPAContext (map witnessedAxiom combinedWitnesses)))
      (proj1
        (coqRestrictedPADirectBottomContextTruthTransportRoot_valid
          (embedPAContext (map witnessedAxiom combinedWitnesses)))))
    as htransport.
  pose proof
    (PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndIntroductionCase.raw_codedPALocalProofOf_coqRestrictedPADirect_templateImpE
      M hPA translation
      (coqRestrictedPADirectBottomCaseContext
        (embedPAContext (map witnessedAxiom combinedWitnesses)))
      (tfImp coqRestrictedPADirectBottomOuterContextTruthTemplate
        coqRestrictedPADirectBottomWitnessContextTruthTemplate)
      coqRestrictedPADirectBottomRemainingTemplate
      _ _ hafterLaw htransport) as hremaining.
  exists suffix.
  lazymatch type of hremaining with
  | RawCodedPALocalProofOf _ _ _ ?root => exists root
  end.
  unfold caseCode in hremaining.
  unfold translation in hremaining.
  exact hremaining.
Qed.

(** Discharge the literal case assumption.  This is the compact public form
    consumed by constructor dispatchers before their definitional view is
    expanded. *)
Theorem
    raw_bottomAdmissibilityAwareCase_standardTail_of_current_source_identification :
  forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (inputs : RawCodedTemplateDirectStructuralInputs M),
  RawCoqRestrictedPADirectBottomCurrentSourceIdentification
    M hPA inputs ->
  RawCoqRestrictedPADirectBottomAdmissibilityAwareCaseStandardTailCompiler
    M hPA inputs.
Proof.
  intros M hPA inputs hidentification baseWitnesses.
  destruct
    (raw_bottomAdmissibilityAwareRemaining_standardTail_of_current_source_identification
      M hPA inputs hidentification baseWitnesses)
    as (suffix & remainingRoot & hremaining).
  set (translation :=
    rawDirectStructuralTemplateTranslation M hPA inputs).
  set (caseTail :=
    embedPAContext (map witnessedAxiom (baseWitnesses ++ suffix))).
  exists suffix.
  exists (rawProofImpIRoot M
    (rawTemplateContextCode translation
      (coqRestrictedPADirectBottomDeepContext caseTail))
    (rawTemplateFormula translation coqRestrictedPADirectBottomCaseTemplate)
    (rawTemplateFormula translation coqRestrictedPADirectBottomRemainingTemplate)
    remainingRoot).
  apply (raw_codedPALocalProofOf_impI M hPA
    (rawTemplateContextCode translation
      (coqRestrictedPADirectBottomDeepContext caseTail))
    (rawTemplateFormula translation coqRestrictedPADirectBottomCaseTemplate)
    (rawTemplateFormula translation coqRestrictedPADirectBottomRemainingTemplate)
    remainingRoot).
  unfold caseTail, translation.
  exact hremaining.
Qed.

(** Structural alignment provides precisely the identification used above.
    Both sides retain [(#9,#8)]; the proof is only the already-verified
    global-evidence reroot followed by the definitional opaque-leaf shape. *)
Theorem raw_bottomCurrentSourceIdentification_of_aligned_structural_inputs :
  forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (tail : nat -> M) predecessorLevel baseContext currentLocal
    nextInputGlobalSigma nextInputGlobalPi
    (aligned : RawDynamicTruthNativeLocalAlignedPredecessorAt M tail
      predecessorLevel baseContext currentLocal
      nextInputGlobalSigma nextInputGlobalPi)
    inputLevelNumeral
    (inputs : RawCodedTemplateDirectStructuralInputs M),
  RawDynamicTruthNativeAlignedStrongStepStructuralInputsAt
      M hPA tail predecessorLevel baseContext currentLocal
      nextInputGlobalSigma nextInputGlobalPi aligned
      inputLevelNumeral inputs ->
  RawCoqRestrictedPADirectBottomCurrentSourceIdentification M hPA inputs.
Proof.
  intros M hPA tail predecessorLevel baseContext currentLocal
    nextInputGlobalSigma nextInputGlobalPi aligned inputLevelNumeral
    inputs hstructural.
  unfold RawCoqRestrictedPADirectBottomCurrentSourceIdentification.
  change (rawDirectTemplateFormula inputs
      (coqRestrictedPASelectedSigmaBottomAssignmentSourceAt 9 8) =
    rawDirectTemplateFormula inputs
      coqRestrictedPADirectBottomCurrentTruthTemplate).
  rewrite
    (raw_selectedSigmaBottomCurrentAssignmentSource_aligned_reroot
      M hPA tail predecessorLevel baseContext currentLocal
      nextInputGlobalSigma nextInputGlobalPi aligned inputLevelNumeral
      inputs hstructural).
  rewrite
    coqRestrictedPASelectedSigmaBottomCurrentAssignmentAlignedTruth_shape.
  reflexivity.
Qed.

Theorem raw_bottomAdmissibilityAwareRemaining_standardTail_of_aligned :
  forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (tail : nat -> M) predecessorLevel baseContext currentLocal
    nextInputGlobalSigma nextInputGlobalPi
    (aligned : RawDynamicTruthNativeLocalAlignedPredecessorAt M tail
      predecessorLevel baseContext currentLocal
      nextInputGlobalSigma nextInputGlobalPi)
    inputLevelNumeral
    (inputs : RawCodedTemplateDirectStructuralInputs M),
  RawDynamicTruthNativeAlignedStrongStepStructuralInputsAt
      M hPA tail predecessorLevel baseContext currentLocal
      nextInputGlobalSigma nextInputGlobalPi aligned
      inputLevelNumeral inputs ->
  RawCoqRestrictedPADirectBottomAdmissibilityAwareRemainingStandardTailCompiler
    M hPA inputs.
Proof.
  intros M hPA tail predecessorLevel baseContext currentLocal
    nextInputGlobalSigma nextInputGlobalPi aligned inputLevelNumeral
    inputs hstructural.
  apply
    raw_bottomAdmissibilityAwareRemaining_standardTail_of_current_source_identification.
  exact
    (raw_bottomCurrentSourceIdentification_of_aligned_structural_inputs
      M hPA tail predecessorLevel baseContext currentLocal
      nextInputGlobalSigma nextInputGlobalPi aligned inputLevelNumeral
      inputs hstructural).
Qed.

Theorem raw_bottomAdmissibilityAwareCase_standardTail_of_aligned :
  forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (tail : nat -> M) predecessorLevel baseContext currentLocal
    nextInputGlobalSigma nextInputGlobalPi
    (aligned : RawDynamicTruthNativeLocalAlignedPredecessorAt M tail
      predecessorLevel baseContext currentLocal
      nextInputGlobalSigma nextInputGlobalPi)
    inputLevelNumeral
    (inputs : RawCodedTemplateDirectStructuralInputs M),
  RawDynamicTruthNativeAlignedStrongStepStructuralInputsAt
      M hPA tail predecessorLevel baseContext currentLocal
      nextInputGlobalSigma nextInputGlobalPi aligned
      inputLevelNumeral inputs ->
  RawCoqRestrictedPADirectBottomAdmissibilityAwareCaseStandardTailCompiler
    M hPA inputs.
Proof.
  intros M hPA tail predecessorLevel baseContext currentLocal
    nextInputGlobalSigma nextInputGlobalPi aligned inputLevelNumeral
    inputs hstructural.
  apply
    raw_bottomAdmissibilityAwareCase_standardTail_of_current_source_identification.
  exact
    (raw_bottomCurrentSourceIdentification_of_aligned_structural_inputs
      M hPA tail predecessorLevel baseContext currentLocal
      nextInputGlobalSigma nextInputGlobalPi aligned inputLevelNumeral
      inputs hstructural).
Qed.

(** Exact expanded dispatcher slot.  Its conclusion matches the Bottom
    component type of
    [RawCoqRestrictedPADirectStrongStepRuleCaseImplicationRoots], with a
    synchronized standard witness suffix made explicit.  Assembling it with
    the other sixteen rule roots is deliberately left to the later dispatcher
    integration. *)
Theorem
    raw_coqRestrictedPADirectStrongStepBottomAdmissibilityAwareCaseRoot_standardTail :
  forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (tail : nat -> M) predecessorLevel baseContext currentLocal
    nextInputGlobalSigma nextInputGlobalPi
    (aligned : RawDynamicTruthNativeLocalAlignedPredecessorAt M tail
      predecessorLevel baseContext currentLocal
      nextInputGlobalSigma nextInputGlobalPi)
    inputLevelNumeral
    (inputs : RawCodedTemplateDirectStructuralInputs M),
  RawDynamicTruthNativeAlignedStrongStepStructuralInputsAt
      M hPA tail predecessorLevel baseContext currentLocal
      nextInputGlobalSigma nextInputGlobalPi aligned
      inputLevelNumeral inputs ->
  forall baseWitnesses : StandardPAAxiomWitnessPrefix,
  exists (suffix : StandardPAAxiomWitnessPrefix) (root : M),
    RawCodedPALocalProofOf M
      (rawTemplateContextCode
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        (rawCoqRestrictedPADirectEndpointWitnessBodyTemplate ::
          rawCoqRestrictedPADirectEndpointDeepTail
            (rawCoqRestrictedPADirectStrongStepEndpointTail
              (embedPAContext
                (map witnessedAxiom (baseWitnesses ++ suffix))))))
      (rawFormulaImpCode M
        (rawTemplateFormula
          (rawDirectStructuralTemplateTranslation M hPA inputs)
          (rawCoqRestrictedPAProofRuleCaseTemplate
            rawCoqRuleBottomElimination
            (liftTerm 8 (tVar 4)) (tVar 7) (liftTerm 8 (tVar 2))
            (tVar 6) (tVar 5) (tVar 4) (tVar 3)
            (tVar 2) (tVar 1) (tVar 0)))
        (rawTemplateFormula
          (rawDirectStructuralTemplateTranslation M hPA inputs)
          (rawCoqTemplateRenameN 8
            rawCoqRestrictedPADirectStrongStepRemainingTemplate)))
      root.
Proof.
  intros M hPA tail predecessorLevel baseContext currentLocal
    nextInputGlobalSigma nextInputGlobalPi aligned inputLevelNumeral
    inputs hstructural baseWitnesses.
  destruct
    (raw_bottomAdmissibilityAwareCase_standardTail_of_aligned
      M hPA tail predecessorLevel baseContext currentLocal
      nextInputGlobalSigma nextInputGlobalPi aligned inputLevelNumeral
      inputs hstructural baseWitnesses)
    as (suffix & root & hroot).
  exists suffix, root.
  unfold coqRestrictedPADirectBottomDeepContext in hroot.
  rewrite raw_coqRestrictedPADirectEndpointDeepContext_shape in hroot.
  rewrite <- coqRestrictedPADirectBottom_remaining_shape.
  exact hroot.
Qed.

End
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectBottomAdmissibilityAwareCompletion.
