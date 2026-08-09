(**
  Honest native reduction of the direct Bottom-E contradiction core.

  The historical selected core is indexed by an arbitrary direct structural
  input record.  Such a record controls its opaque conclusion-truth leaf, so
  no unconditional refutation of that leaf can hold: an arbitrary selector
  may map the displayed bottom arguments to a PA theorem.  The native truth
  package supplies the missing information as a literal code identification.

  This module isolates that one unavoidable selector equation.  Below it,
  the already checked global-opened Sigma compiler eliminates all seven
  constructor rows and produces the bottom-truth refutation on a growing
  standard-PA tail.  A small finite implication-composition proof then shows
  that the old contradiction core follows from only the genuinely recursive
  child-truth law.  In particular, neither the selected contradiction core
  nor a bottom-refutation root is assumed.
*)

From Stdlib Require Import List.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  CodedProof
  RawCodedSyntaxConstructors
  RawCodedFormulaOperations
  RawCodedContextLists
  RawCodedRestrictedPAProof
  RawCodedPALocalProofExistential
  RawCodedPALocalProofComposition
  RawCodedPALocalProofWitnessedContextMerge
  RawCodedPAAxiomWitness
  RawCodedPAAxiomWitnessPrefix
  RawCodedTemplateSyntax
  RawCodedTemplateNumeralParameters
  RawCodedTemplateProofCompiler
  RawCodedTemplatePAEmbedding
  RawCodedTemplatePAEmbeddingSelfShiftTail
  RawCodedTemplateFormulaAtomicAdequacy
  RawCodedTemplateDirectStructuralTranslation
  RawCodedTemplateStructuralPAAgreement
  RawCodedTemplateDirectStructuralPAAgreement
  RawCodedTemplateLocalProofWitnessedTailTransport
  RawCodedTemplateLocalProofStandardWitnessTailTransport
  RawCodedTemplateTernaryApplication
  RawCodedTemplateTernaryApplicationFunctionality
  RawCodedRestrictedPADerivationSoundnessTemplateDirectInputs
  RawCodedRestrictedPADerivationSoundnessConclusionTruthDirectSelector
  RawCodedRestrictedPAConsistencyFromUniversalSoundness
  RawCodedRestrictedPAConsistencyFromUniversalSoundnessDirect
  RawCodedRestrictedPABottomTruthNativeDirectRefutationLink
  RawCodedRestrictedPASelectedSigmaBottomGlobalOpenedSevenCaseBoundary
  RawCodedRestrictedPASelectedSigmaBottomGlobalOpenedBranchRefutations
  RawCodedRestrictedPADerivationSoundnessDirectBottomEliminationCase
  RawCodedRestrictedPADerivationSoundnessDirectRuleCasesAfterBottomElimination.

Import ListNotations.

Module
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectBottomCoreNativeReduction.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedCodedProof.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedContextLists.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPALocalProofComposition.
Import PABoundedRawCodedPALocalProofWitnessedContextMerge.
Import PABoundedRawCodedPAAxiomWitness.
Import PABoundedRawCodedPAAxiomWitnessPrefix.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateNumeralParameters.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedTemplatePAEmbedding.
Import PABoundedRawCodedTemplatePAEmbeddingSelfShiftTail.
Import PABoundedRawCodedTemplateFormulaAtomicAdequacy.
Import PABoundedRawCodedTemplateDirectStructuralTranslation.
Import PABoundedRawCodedTemplateStructuralPAAgreement.
Import PABoundedRawCodedTemplateDirectStructuralPAAgreement.
Import PABoundedRawCodedTemplateLocalProofWitnessedTailTransport.
Import PABoundedRawCodedTemplateLocalProofStandardWitnessTailTransport.
Import PABoundedRawCodedTemplateTernaryApplication.
Import PABoundedRawCodedTemplateTernaryApplicationFunctionality.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessTemplateDirectInputs.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessConclusionTruthDirectSelector.
Import PABoundedRawCodedRestrictedPAConsistencyFromUniversalSoundness.
Import
  PABoundedRawCodedRestrictedPAConsistencyFromUniversalSoundnessDirect.
Import PABoundedRawCodedRestrictedPABottomTruthNativeDirectRefutationLink.
Import
  PABoundedRawCodedRestrictedPASelectedSigmaBottomGlobalOpenedSevenCaseBoundary.
Import
  PABoundedRawCodedRestrictedPASelectedSigmaBottomGlobalOpenedBranchRefutations.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectBottomEliminationCase.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectRuleCasesAfterBottomElimination.

(** ------------------------------------------------------------------
    The exact native-source identification. *)

Definition coqRestrictedPADirectBottomClosedTruthTemplate
    : TemplateFormula :=
  tfOpaque coqRestrictedPAConclusionTruthPredicateName
    [coqRestrictedPASoundnessLowerLevelTerm;
     coqRestrictedPASoundnessUpperLevelTerm;
     embedPATerm rawFormulaBotCodeTerm; ttZero; ttZero].

Lemma coqRestrictedPADirectBottomTruthRefutation_shape :
  coqRestrictedPABottomTruthRefutationTemplate =
  tfImp coqRestrictedPADirectBottomClosedTruthTemplate tfBot.
Proof. reflexivity. Qed.

(** This equality is the weakest honest interface between an arbitrary
    direct selector and the concrete native successor-Sigma source. *)
Definition RawCoqRestrictedPADirectBottomNativeSourceIdentification
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M) : Prop :=
  rawDirectTemplateFormula inputs
    coqRestrictedPADirectBottomClosedTruthTemplate =
  rawTemplateFormula
    (rawDirectStructuralTemplateTranslation M hPA inputs)
    coqRestrictedPASelectedSigmaBottomNativeAppliedGlobalSource.

Arguments RawCoqRestrictedPADirectBottomNativeSourceIdentification
  M hPA inputs : clear implicits.

(** A native conclusion selector and a represented application of the
    concrete source prove the identification by functionality of ternary
    application.  The first two soundness arguments do not occur in the
    ternary output, exactly as required by the direct conclusion selector. *)
Theorem
    raw_bottomNativeSourceIdentification_of_selector_application : forall
    (M : RawPAModel) (hPA : RawPASatisfies M), forall
      (parameters : RawCodedTemplateNumeralParameters M)
      (inputs : RawCodedTemplateDirectStructuralInputs M)
      nextGlobalSigma
      (sigmaApplicationSelector :
        RawCodedTernaryApplicationSelector M nextGlobalSigma),
  RawCoqRestrictedPANativeConclusionTruthSelectorLinkAt
    M parameters inputs nextGlobalSigma sigmaApplicationSelector ->
  RawCodedTernaryApplication M nextGlobalSigma
    (rawQuotedTermCode M rawFormulaBotCodeTerm)
    (rawQuotedTermCode M tZero)
    (rawQuotedTermCode M tZero)
    (rawTemplateFormula
      (rawDirectStructuralTemplateTranslation M hPA inputs)
      coqRestrictedPASelectedSigmaBottomNativeAppliedGlobalSource) ->
  RawCoqRestrictedPADirectBottomNativeSourceIdentification
    M hPA inputs.
Proof.
  intros M hPA parameters inputs nextGlobalSigma
    sigmaApplicationSelector hselector happlication.
  pose proof
    (rawTernaryApplicationOutput_unique M hPA nextGlobalSigma
      sigmaApplicationSelector
      (rawQuotedTermCode M rawFormulaBotCodeTerm)
      (rawQuotedTermCode M tZero)
      (rawQuotedTermCode M tZero)
      (rawTemplateFormula
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        coqRestrictedPASelectedSigmaBottomNativeAppliedGlobalSource)
      (raw_coqRestrictedPAConclusionTruth_quotedTerm_syntax
        M hPA rawFormulaBotCodeTerm)
      (raw_coqRestrictedPAConclusionTruth_quotedTerm_syntax M hPA tZero)
      (raw_coqRestrictedPAConclusionTruth_quotedTerm_syntax M hPA tZero)
      happlication) as houtput.
  unfold RawCoqRestrictedPADirectBottomNativeSourceIdentification,
    coqRestrictedPADirectBottomClosedTruthTemplate.
  rewrite (hselector
    coqRestrictedPASoundnessLowerLevelTerm
    coqRestrictedPASoundnessUpperLevelTerm
    (embedPATerm rawFormulaBotCodeTerm) ttZero ttZero).
  unfold rawCoqRestrictedPADerivationSoundnessTemplateTermView.
  repeat rewrite rawStructuralTemplateTermWith_embedPA.
  exact houtput.
Qed.

(** ------------------------------------------------------------------
    Compile the seven native falsity rows on a selected standard tail. *)

Definition RawCoqRestrictedPADirectSelectedBottomTruthRefutationTail
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M) : Prop :=
  exists witnesses : StandardPAAxiomWitnessPrefix,
    RawCodedPAAxiomWitnessContext M
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        witnesses (raw_zero M))
      (rawTemplateContextCode
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        (embedPAContext (map witnessedAxiom witnesses))) /\
    exists root : M,
      RawCodedPALocalProofOf M
        (rawTemplateContextCode
          (rawDirectStructuralTemplateTranslation M hPA inputs)
          (embedPAContext (map witnessedAxiom witnesses)))
        (rawCoqRestrictedPABottomTruthRefutationDirectCode M inputs)
        root.

Arguments RawCoqRestrictedPADirectSelectedBottomTruthRefutationTail
  M hPA inputs : clear implicits.

Theorem raw_selectedBottomTruthRefutationTail_of_native_identification :
  forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (inputs : RawCodedTemplateDirectStructuralInputs M),
  RawCoqRestrictedPADirectBottomNativeSourceIdentification M hPA inputs ->
  RawCoqRestrictedPADirectSelectedBottomTruthRefutationTail M hPA inputs.
Proof.
  intros M hPA inputs hidentification.
  set (translation :=
    rawDirectStructuralTemplateTranslation M hPA inputs).
  assert (hagreement : RawCodedTemplatePAAgreement M translation).
  {
    unfold translation. apply rawDirectStructuralTemplatePAAgreement.
  }
  assert (hempty : RawCodedPAAxiomWitnessContext M
      (raw_zero M) (raw_zero M)).
  {
    pose proof (raw_codedPAAxiomWitnessContext_standard M hPA []) as h.
    cbn [rawQuotedPAAxiomWitnessList rawListCode map] in h.
    exact h.
  }
  destruct
    (raw_codedPALocalProofOf_selectedSigmaBottom_native_applied_refutation_compiled_growing
      M hPA translation hagreement (raw_zero M) (raw_zero M) hempty)
    as (witnesses & root & hwitnessed & _hincluded & hroot).
  exists witnesses.
  split.
  - unfold translation.
    exact (raw_templateEmbeddedPAAxiomWitnessContext
      M hPA
      (rawDirectStructuralTemplateTranslation M hPA inputs)
      (rawDirectStructuralTemplatePAAgreement M hPA inputs)
      witnesses).
  - exists root.
    unfold translation in hroot.
    rewrite <- hidentification in hroot.
    change (RawCodedPALocalProofOf M
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses (raw_zero M))
      (rawCoqRestrictedPABottomTruthRefutationDirectCode M inputs)
      root) in hroot.
    rewrite raw_templateContextCode_as_on_tail_general.
    rewrite (raw_templateContextCodeOnTail_embedPAAxiomWitnesses
      M (rawDirectStructuralTemplateTranslation M hPA inputs)
      (rawDirectStructuralTemplatePAAgreement M hPA inputs)
      witnesses (raw_zero M)).
    exact hroot.
Qed.

(** ------------------------------------------------------------------
    The strictly smaller recursive residual. *)

Definition RawCoqRestrictedPADirectBottomRecursiveClosedTruthLawRoot
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    (tail : TemplateContext) : Prop :=
  exists root : M,
    RawCodedPALocalProofOf M
      (rawTemplateContextCode
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        (coqRestrictedPADirectBottomCaseContext tail))
      (rawTemplateFormula
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        (tfImp coqRestrictedPADirectBottomWitnessContextTruthTemplate
          coqRestrictedPADirectBottomClosedTruthTemplate))
      root.

Arguments RawCoqRestrictedPADirectBottomRecursiveClosedTruthLawRoot
  M hPA inputs tail : clear implicits.

Definition
    RawCoqRestrictedPADirectBottomRecursiveClosedTruthStandardTailCompiler
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M) : Prop :=
  forall baseWitnesses : StandardPAAxiomWitnessPrefix,
  exists suffix : StandardPAAxiomWitnessPrefix,
    RawCoqRestrictedPADirectBottomRecursiveClosedTruthLawRoot
      M hPA inputs
      (embedPAContext
        (map witnessedAxiom (baseWitnesses ++ suffix))).

Arguments
  RawCoqRestrictedPADirectBottomRecursiveClosedTruthStandardTailCompiler
  M hPA inputs : clear implicits.

(** ------------------------------------------------------------------
    A checked finite proof of implication composition. *)

Definition coqRestrictedPADirectBottomCompositionTemplate :
    TemplateFormula :=
  tfImp
    (tfImp coqRestrictedPADirectBottomWitnessContextTruthTemplate
      coqRestrictedPADirectBottomClosedTruthTemplate)
    (tfImp
      (tfImp coqRestrictedPADirectBottomClosedTruthTemplate tfBot)
      (tfImp coqRestrictedPADirectBottomWitnessContextTruthTemplate tfBot)).

Definition coqRestrictedPADirectBottomCompositionContext1 tail :=
  (tfImp coqRestrictedPADirectBottomWitnessContextTruthTemplate
    coqRestrictedPADirectBottomClosedTruthTemplate) ::
  coqRestrictedPADirectBottomCaseContext tail.

Definition coqRestrictedPADirectBottomCompositionContext2 tail :=
  (tfImp coqRestrictedPADirectBottomClosedTruthTemplate tfBot) ::
  coqRestrictedPADirectBottomCompositionContext1 tail.

Definition coqRestrictedPADirectBottomCompositionContext3 tail :=
  coqRestrictedPADirectBottomWitnessContextTruthTemplate ::
  coqRestrictedPADirectBottomCompositionContext2 tail.

Definition coqRestrictedPADirectBottomCompositionImpAssumption tail :=
  trpAss (coqRestrictedPADirectBottomCompositionContext3 tail)
    (tfImp coqRestrictedPADirectBottomWitnessContextTruthTemplate
      coqRestrictedPADirectBottomClosedTruthTemplate).

Definition coqRestrictedPADirectBottomCompositionRefutationAssumption tail :=
  trpAss (coqRestrictedPADirectBottomCompositionContext3 tail)
    (tfImp coqRestrictedPADirectBottomClosedTruthTemplate tfBot).

Definition coqRestrictedPADirectBottomCompositionTruthAssumption tail :=
  trpAss (coqRestrictedPADirectBottomCompositionContext3 tail)
    coqRestrictedPADirectBottomWitnessContextTruthTemplate.

Definition coqRestrictedPADirectBottomCompositionClosedTruthRoot tail :=
  trpImpE (coqRestrictedPADirectBottomCompositionContext3 tail)
    coqRestrictedPADirectBottomWitnessContextTruthTemplate
    coqRestrictedPADirectBottomClosedTruthTemplate
    (coqRestrictedPADirectBottomCompositionImpAssumption tail)
    (coqRestrictedPADirectBottomCompositionTruthAssumption tail).

Definition coqRestrictedPADirectBottomCompositionBottomRoot tail :=
  trpImpE (coqRestrictedPADirectBottomCompositionContext3 tail)
    coqRestrictedPADirectBottomClosedTruthTemplate tfBot
    (coqRestrictedPADirectBottomCompositionRefutationAssumption tail)
    (coqRestrictedPADirectBottomCompositionClosedTruthRoot tail).

Definition coqRestrictedPADirectBottomCompositionAfterTruthRoot tail :=
  trpImpI (coqRestrictedPADirectBottomCompositionContext2 tail)
    coqRestrictedPADirectBottomWitnessContextTruthTemplate tfBot
    (coqRestrictedPADirectBottomCompositionBottomRoot tail).

Definition coqRestrictedPADirectBottomCompositionAfterRefutationRoot tail :=
  trpImpI (coqRestrictedPADirectBottomCompositionContext1 tail)
    (tfImp coqRestrictedPADirectBottomClosedTruthTemplate tfBot)
    (tfImp coqRestrictedPADirectBottomWitnessContextTruthTemplate tfBot)
    (coqRestrictedPADirectBottomCompositionAfterTruthRoot tail).

Definition coqRestrictedPADirectBottomCompositionRoot tail :=
  trpImpI (coqRestrictedPADirectBottomCaseContext tail)
    (tfImp coqRestrictedPADirectBottomWitnessContextTruthTemplate
      coqRestrictedPADirectBottomClosedTruthTemplate)
    (tfImp
      (tfImp coqRestrictedPADirectBottomClosedTruthTemplate tfBot)
      (tfImp coqRestrictedPADirectBottomWitnessContextTruthTemplate tfBot))
    (coqRestrictedPADirectBottomCompositionAfterRefutationRoot tail).

Lemma coqRestrictedPADirectBottomCompositionRoot_valid : forall tail,
  TemplateRawDerives (coqRestrictedPADirectBottomCaseContext tail)
    coqRestrictedPADirectBottomCompositionTemplate
    (coqRestrictedPADirectBottomCompositionRoot tail).
Proof.
  intro tail.
  unfold coqRestrictedPADirectBottomCompositionRoot,
    coqRestrictedPADirectBottomCompositionTemplate.
  apply coqRestrictedPADirectBottom_templateRawDerives_impI.
  unfold coqRestrictedPADirectBottomCompositionAfterRefutationRoot.
  apply coqRestrictedPADirectBottom_templateRawDerives_impI.
  unfold coqRestrictedPADirectBottomCompositionAfterTruthRoot.
  apply coqRestrictedPADirectBottom_templateRawDerives_impI.
  unfold coqRestrictedPADirectBottomCompositionBottomRoot.
  apply coqRestrictedPADirectBottom_templateRawDerives_impE.
  - apply templateRawDerives_assumption.
    unfold coqRestrictedPADirectBottomCompositionContext3,
      coqRestrictedPADirectBottomCompositionContext2,
      coqRestrictedPADirectBottomCompositionContext1.
    right. left. reflexivity.
  - unfold coqRestrictedPADirectBottomCompositionClosedTruthRoot.
    apply coqRestrictedPADirectBottom_templateRawDerives_impE.
    + apply templateRawDerives_assumption.
      unfold coqRestrictedPADirectBottomCompositionContext3,
        coqRestrictedPADirectBottomCompositionContext2,
        coqRestrictedPADirectBottomCompositionContext1.
      right. right. left. reflexivity.
    + apply templateRawDerives_assumption.
      unfold coqRestrictedPADirectBottomCompositionContext3.
      left. reflexivity.
Qed.

(** ------------------------------------------------------------------
    Eliminate native falsity and recover the historical core. *)

Theorem raw_selectedBottomContradictionCoreTail_of_native_reduction :
  forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (inputs : RawCodedTemplateDirectStructuralInputs M),
  RawCoqRestrictedPADirectBottomNativeSourceIdentification M hPA inputs ->
  RawCoqRestrictedPADirectBottomRecursiveClosedTruthStandardTailCompiler
    M hPA inputs ->
  RawCoqRestrictedPADirectSelectedBottomContradictionCoreTail M hPA inputs.
Proof.
  intros M hPA inputs hidentification hrecursiveCompiler.
  destruct
    (raw_selectedBottomTruthRefutationTail_of_native_identification
      M hPA inputs hidentification)
    as (refutationWitnesses & hrefutationWitnessed &
      refutationRoot & hrefutation).
  destruct (hrecursiveCompiler refutationWitnesses)
    as [suffix [recursiveRoot hrecursive]].
  set (translation :=
    rawDirectStructuralTemplateTranslation M hPA inputs).
  set (combinedWitnesses := refutationWitnesses ++ suffix).
  assert (hcombinedWitnessed : RawCodedPAAxiomWitnessContext M
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        combinedWitnesses (raw_zero M))
      (rawTemplateContextCode translation
        (embedPAContext (map witnessedAxiom combinedWitnesses)))).
  {
    unfold translation, combinedWitnesses.
    exact (raw_templateEmbeddedPAAxiomWitnessContext
      M hPA (rawDirectStructuralTemplateTranslation M hPA inputs)
      (rawDirectStructuralTemplatePAAgreement M hPA inputs)
      (refutationWitnesses ++ suffix)).
  }
  destruct
    (raw_codedPALocalProof_standardWitnessTail_surround_under_prefix
      M hPA translation
      (rawDirectStructuralTemplatePAAgreement M hPA inputs)
      [] [] refutationWitnesses suffix
      (rawCoqRestrictedPABottomTruthRefutationDirectCode M inputs)
      refutationRoot hrefutation)
    as [transportedRefutationRoot htransportedRefutation].
  cbn [List.app] in htransportedRefutation.
  assert (hcombinedRealizable : RawContextListRealizable M
      (rawTemplateContextCode translation
        (embedPAContext (map witnessedAxiom combinedWitnesses)))).
  {
    exact (raw_codedPAAxiomWitnessContext_context_realizable M
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        combinedWitnesses (raw_zero M))
      (rawTemplateContextCode translation
        (embedPAContext (map witnessedAxiom combinedWitnesses)))
      hcombinedWitnessed).
  }
  destruct
    (raw_codedPALocalProof_templatePrefix M hPA translation
      (rawTemplateContextCode translation
        (embedPAContext (map witnessedAxiom combinedWitnesses)))
      (coqRestrictedPADirectBottomCaseContext [])
      (rawCoqRestrictedPABottomTruthRefutationDirectCode M inputs)
      transportedRefutationRoot hcombinedRealizable
      (fun formula _ =>
        raw_codedTemplateFormula_atomically_adequate_core
          M hPA translation formula)
      htransportedRefutation)
    as [caseRefutationRoot hcaseRefutation].
  rewrite <- raw_templateContextCode_app_on_tail_general
    in hcaseRefutation.
  rewrite <- coqRestrictedPADirectBottomCaseContext_app_witnesses
    in hcaseRefutation.
  unfold combinedWitnesses in hrecursive.
  unfold translation in hrecursive.
  unfold rawCoqRestrictedPABottomTruthRefutationDirectCode in
    hcaseRefutation.
  rewrite coqRestrictedPADirectBottomTruthRefutation_shape in
    hcaseRefutation.
  set (caseTail :=
    embedPAContext (map witnessedAxiom combinedWitnesses)).
  pose proof
    (raw_templateProof_localProof M hPA translation
      (coqRestrictedPADirectBottomCompositionRoot caseTail)
      (proj1 (coqRestrictedPADirectBottomCompositionRoot_valid caseTail)))
    as hcomposition.
  unfold coqRestrictedPADirectBottomCompositionTemplate in hcomposition.
  pose proof
    (raw_codedPALocalProofOf_impE M hPA
      (rawTemplateContextCode translation
        (coqRestrictedPADirectBottomCaseContext caseTail))
      (rawTemplateFormula translation
        (tfImp coqRestrictedPADirectBottomWitnessContextTruthTemplate
          coqRestrictedPADirectBottomClosedTruthTemplate))
      (rawTemplateFormula translation
        (tfImp
          (tfImp coqRestrictedPADirectBottomClosedTruthTemplate tfBot)
          (tfImp coqRestrictedPADirectBottomWitnessContextTruthTemplate
            tfBot)))
      _ recursiveRoot hcomposition hrecursive) as hafterRecursive.
  pose proof
    (raw_codedPALocalProofOf_impE M hPA
      (rawTemplateContextCode translation
        (coqRestrictedPADirectBottomCaseContext caseTail))
      (rawTemplateFormula translation
        (tfImp coqRestrictedPADirectBottomClosedTruthTemplate tfBot))
      (rawTemplateFormula translation
        (tfImp coqRestrictedPADirectBottomWitnessContextTruthTemplate tfBot))
      _ caseRefutationRoot hafterRecursive hcaseRefutation) as hcore.
  exists combinedWitnesses. split; [exact hcombinedWitnessed |].
  unfold RawCoqRestrictedPADirectBottomContradictionCoreLawRoot.
  lazymatch type of hcore with
  | RawCodedPALocalProofOf _ _ _ ?root => exists root
  end.
  unfold caseTail in hcore.
  unfold translation in hcore.
  exact hcore.
Qed.

End
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectBottomCoreNativeReduction.
