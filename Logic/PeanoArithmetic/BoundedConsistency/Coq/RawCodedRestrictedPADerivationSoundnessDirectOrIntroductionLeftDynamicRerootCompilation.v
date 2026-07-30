(**
  Proof-code compilation of the universal Or-I-left reroot source.

  A fixed PA theorem is first compiled over an arbitrary witnessed PA base.
  Model-internal All-E instantiates its carrier-valued hierarchy variable,
  using the exact represented substitution trace established for the direct
  template translation.  Finally, finite context insertion moves the local
  proof beneath the constructor assumptions used by the recursive-child
  compiler.  The only recursion in the last step is over the finite Rocq
  template prefix; neither the carrier hierarchy value nor a coded context is
  decoded metatheoretically.
*)

From Stdlib Require Import List.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  CodedProof
  CodedSyntax
  RawCodedSyntaxConstructors
  RawCodedFormulaOperations
  RawCodedProofAllEConstructor
  RawCodedContextLists
  RawCodedContextStructure
  RawCodedFormulaBoundAllCarrierBoundary
  RawCodedPALocalProofExistential
  RawCodedPALocalProofUniversalElimination
  RawCodedPALocalProofContextInsertUnconditional
  RawCodedPALocalProofWitnessedContextMerge
  RawCodedPAAxiomWitness
  RawCodedPAAxiomWitnessPrefix
  RawCodedRestrictedPAProof
  RawCodedTemplateSyntax
  RawCodedTemplateProofCompiler
  RawCodedTemplateProofCompilerSelfShiftTail
  RawCodedTemplatePAEmbedding
  RawCodedTemplatePAEmbeddingSelfShiftTail
  RawCodedTemplateDirectStructuralTranslation
  RawCodedTemplateDirectStructuralPAAgreement
  RawCodedRestrictedPAConsistencyFromUniversalSoundness
  RawCodedRestrictedPADerivationSoundnessDirectRuleDispatchFrontier
  RawCodedRestrictedPADerivationSoundnessDirectStrongStepShell
  RawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftCase
  RawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftRecursiveChildCompilation
  RawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftDynamicRerootSource
  RawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftDynamicRerootValidity.

Import ListNotations.

Module
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftDynamicRerootCompilation.

Import PA.
Import PABoundedCodedProof.
Import PABoundedCodedSyntax.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedContextLists.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedProofAllEConstructor.
Import PABoundedRawCodedContextStructure.
Import PABoundedRawCodedFormulaBoundAllCarrierBoundary.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPALocalProofUniversalElimination.
Import PABoundedRawCodedPALocalProofContextInsertUnconditional.
Import PABoundedRawCodedPALocalProofWitnessedContextMerge.
Import PABoundedRawCodedPAAxiomWitness.
Import PABoundedRawCodedPAAxiomWitnessPrefix.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedTemplateProofCompilerSelfShiftTail.
Import PABoundedRawCodedTemplatePAEmbedding.
Import PABoundedRawCodedTemplatePAEmbeddingSelfShiftTail.
Import PABoundedRawCodedTemplateDirectStructuralTranslation.
Import PABoundedRawCodedTemplateDirectStructuralPAAgreement.
Import PABoundedRawCodedRestrictedPAConsistencyFromUniversalSoundness.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectRuleDispatchFrontier.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectStrongStepShell.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftCase.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftRecursiveChildCompilation.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftDynamicRerootSource.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftDynamicRerootValidity.

(** Insert a finite direct-template prefix above an already represented local
    proof.  Atomic adequacy is available uniformly from the represented
    structural translation, and realizability is maintained after each cons. *)
Theorem raw_codedPALocalProof_directTemplatePrefix : forall
    (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    baseContext prefix conclusion root,
  RawContextListRealizable M baseContext ->
  RawCodedPALocalProofOf M baseContext conclusion root ->
  exists prefixedRoot : M,
    RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        baseContext prefix)
      conclusion prefixedRoot.
Proof.
  intros M hPA inputs baseContext prefix.
  induction prefix as [|head tail ih]; intros conclusion root hbase hproof.
  - cbn [rawTemplateContextCodeOnTail]. exists root. exact hproof.
  - cbn [rawTemplateContextCodeOnTail].
    destruct (ih conclusion root hbase hproof)
      as [tailRoot htailProof].
    apply (raw_codedPALocalProof_adequateConsTransplant M hPA
      (rawTemplateContextCodeOnTail
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        baseContext tail)
      (rawDirectTemplateFormula inputs head)
      conclusion tailRoot).
    + apply rawDirectTemplateFormula_atomically_adequate. exact hPA.
    + apply raw_templateContextOnTail_realizable; assumption.
    + exact htailProof.
Qed.

(** Every witnessed PA axiom is a sentence, hence weakening its free-variable
    environment leaves it syntactically unchanged. *)
Lemma templateContextShift_embedPAAxiomWitnesses : forall witnesses,
  templateContextShift (embedPAContext (map witnessedAxiom witnesses)) =
  embedPAContext (map witnessedAxiom witnesses).
Proof.
  intro witnesses.
  rewrite <- embedPAContext_shift.
  unfold embedPAContext. rewrite !map_map.
  apply map_ext. intro witness.
  rewrite (Formula.rename_eq_of_sentence
    (witnessedAxiom witness)).
  - reflexivity.
  - apply Formula.sentence_ax_s.
    apply witnessedAxiom_is_Ax_s.
Qed.

(** All context constructors used by the opened Or-I-left compiler are
    affine in a self-shifting tail.  In particular a finite list of embedded
    witnessed PA axioms remains the literal suffix of the coverage
    eigencontext despite the intervening binder shifts. *)
Lemma coqRestrictedPADirectOrIntroductionLeftCoverageEigenContext_app_witnesses :
    forall witnesses,
  coqRestrictedPADirectOrIntroductionLeftCoverageEigenContext
      (embedPAContext (map witnessedAxiom witnesses)) =
  coqRestrictedPADirectOrIntroductionLeftCoverageEigenContext [] ++
    embedPAContext (map witnessedAxiom witnesses).
Proof.
  intro witnesses.
  unfold
    coqRestrictedPADirectOrIntroductionLeftCoverageEigenContext,
    coqRestrictedPADirectOrIntroductionLeftLawBodyContext,
    coqRestrictedPADirectOrIntroductionLeftLawEndpointContext,
    coqRestrictedPADirectStrongStepOrIntroductionLeftReadyContext,
    coqRestrictedPADirectStrongStepOrIntroductionLeftAdmissibleContext,
    coqRestrictedPADirectStrongStepOrIntroductionLeftCaseContext,
    coqRestrictedPADirectStrongStepOrIntroductionLeftDeepEndpointContext,
    rawCoqRestrictedPADirectEndpointDeepTail,
    rawCoqRestrictedPADirectEndpointDeepContext,
    rawCoqRestrictedPADirectStrongStepEndpointTail,
    rawCoqRestrictedPADirectStrongStepFourBinderContext.
  cbn [rawCoqTemplateNestedExContext rawCoqTemplateContextShiftN
    templateContextShift templateContextRename List.map List.app].
  repeat rewrite templateContextShift_embedPAAxiomWitnesses.
  reflexivity.
Qed.

Lemma rawTemplateContextCode_app_on_tail : forall
    (M : RawPAModel) (translation : RawCodedTemplateTranslation M)
    left right,
  rawTemplateContextCode translation (left ++ right) =
  rawTemplateContextCodeOnTail translation
    (rawTemplateContextCode translation right) left.
Proof.
  intros M translation left. induction left as [|head tail ih]; intro right.
  - reflexivity.
  - cbn [List.app rawTemplateContextCode rawTemplateContextCodeOnTail].
    f_equal. apply ih.
Qed.

Lemma rawTemplateContextCode_as_on_tail : forall
    (M : RawPAModel) (translation : RawCodedTemplateTranslation M) context,
  rawTemplateContextCode translation context =
  rawTemplateContextCodeOnTail translation (raw_zero M) context.
Proof.
  intros M translation context. induction context as [|head tail ih].
  - reflexivity.
  - cbn [rawTemplateContextCode rawTemplateContextCodeOnTail].
    now rewrite ih.
Qed.

Lemma raw_coverageEigenContext_witnessed_code : forall
    (M : RawPAModel) (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation -> forall witnesses,
  rawTemplateContextCode translation
    (coqRestrictedPADirectOrIntroductionLeftCoverageEigenContext
      (embedPAContext (map witnessedAxiom witnesses))) =
  rawTemplateContextCodeOnTail translation
    (rawStandardPAAxiomWitnessPrefixContextCode M
      witnesses (raw_zero M))
    (coqRestrictedPADirectOrIntroductionLeftCoverageEigenContext []).
Proof.
  intros M translation hagreement witnesses.
  rewrite
    coqRestrictedPADirectOrIntroductionLeftCoverageEigenContext_app_witnesses.
  rewrite rawTemplateContextCode_app_on_tail.
  assert (htail : rawTemplateContextCode translation
      (embedPAContext (map witnessedAxiom witnesses)) =
    rawStandardPAAxiomWitnessPrefixContextCode M
      witnesses (raw_zero M)).
  {
    rewrite rawTemplateContextCode_as_on_tail.
    apply (raw_templateContextCodeOnTail_embedPAAxiomWitnesses
      M translation hagreement witnesses (raw_zero M)).
  }
  now rewrite htail.
Qed.

(** The compiled source selects a finite standard PA-axiom prefix above the
    caller's witnessed base.  The result is already instantiated to the
    direct carrier level and moved below the exact finite local prefix used by
    the opened coverage compiler. *)
Theorem
    raw_codedPALocalProof_dynamicRestrictedRerootLaw_on_witnessed_base :
  forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    baseWitnessList baseContext,
  RawCodedPAAxiomWitnessContext M baseWitnessList baseContext ->
  exists (witnesses : StandardPAAxiomWitnessPrefix) (root : M),
    RawCodedPAAxiomWitnessContext M
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        witnesses baseWitnessList)
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses baseContext) /\
    RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        (rawStandardPAAxiomWitnessPrefixContextCode M
          witnesses baseContext)
        (coqRestrictedPADirectOrIntroductionLeftCoverageEigenContext []))
      (rawDirectTemplateFormula inputs
        coqRestrictedPADirectOrIntroductionLeftDynamicRestrictedRerootLawTemplate)
      root.
Proof.
  intros M hPA inputs baseWitnessList baseContext hbase.
  set (translation :=
    rawDirectStructuralTemplateTranslation M hPA inputs).
  destruct (raw_codedTemplatePALocalProofOf_of_BProv_on_witnessed_tail
    M hPA translation
    (rawDirectStructuralTemplatePAAgreement M hPA inputs)
    baseWitnessList baseContext
    coqRestrictedPADirectOrIntroductionLeftDynamicRestrictedRerootSourceFormula
    hbase
    PA_proves_coqRestrictedPADirectOrIntroductionLeftDynamicRestrictedRerootSource)
    as (witnesses & sourceRoot & hextended & hsource).
  set (extendedContext :=
    rawStandardPAAxiomWitnessPrefixContextCode M witnesses baseContext).
  set (replacement := rawDirectTemplateTerm inputs
    coqRestrictedPASoundnessLowerLevelTerm).
  set (instance := rawDirectTemplateFormula inputs
    coqRestrictedPADirectOrIntroductionLeftDynamicRestrictedRerootLawTemplate).

  assert (hall : RawCodedPALocalProofOf M extendedContext
      (rawFormulaAllCode M
        (rawQuotedFormulaCode M
          coqRestrictedPADirectOrIntroductionLeftDynamicRestrictedRerootSourceBodyFormula))
      sourceRoot).
  {
    unfold extendedContext, translation in *.
    change (RawCodedPALocalProofOf M
      (rawStandardPAAxiomWitnessPrefixContextCode M witnesses baseContext)
      (rawQuotedFormulaCode M
        coqRestrictedPADirectOrIntroductionLeftDynamicRestrictedRerootSourceFormula)
      sourceRoot).
    rewrite <- (rawTemplateFormula_embedPA
      (rawDirectStructuralTemplatePAAgreement M hPA inputs)
      coqRestrictedPADirectOrIntroductionLeftDynamicRestrictedRerootSourceFormula).
    exact hsource.
  }
  pose proof (raw_codedPALocalProofOf_allE M hPA extendedContext
    (rawQuotedFormulaCode M
      coqRestrictedPADirectOrIntroductionLeftDynamicRestrictedRerootSourceBodyFormula)
    replacement instance sourceRoot hall
    (rawDirect_dynamicRestrictedRerootSource_substitution M hPA inputs))
    as hinstance.
  destruct (raw_codedPALocalProof_directTemplatePrefix M hPA inputs
    extendedContext
    (coqRestrictedPADirectOrIntroductionLeftCoverageEigenContext [])
    instance
    (rawProofAllERoot M extendedContext
      (rawQuotedFormulaCode M
        coqRestrictedPADirectOrIntroductionLeftDynamicRestrictedRerootSourceBodyFormula)
      replacement sourceRoot)
    (raw_codedPAAxiomWitnessContext_context_realizable M
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        witnesses baseWitnessList)
      extendedContext hextended)
    hinstance) as [root hroot].
  exists witnesses, root. split; [exact hextended |].
  unfold instance. exact hroot.
Qed.

(** Empty-base specialization in the literal template-tail interface used by
    the rule-case record.  The selected witnessed PA prefix becomes the
    shared finite template tail, and the preceding context equation converts
    the on-tail proof into the exact legacy root predicate. *)
Corollary
    raw_dynamicRestrictedRerootLawRoot_on_selected_witnessed_tail :
  forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (inputs : RawCodedTemplateDirectStructuralInputs M),
  exists (witnesses : StandardPAAxiomWitnessPrefix),
    RawCodedPAAxiomWitnessContext M
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        witnesses (raw_zero M))
      (rawTemplateContextCode
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        (embedPAContext (map witnessedAxiom witnesses))) /\
    RawCoqRestrictedPADirectOrIntroductionLeftDynamicRestrictedRerootLawRoot
      M hPA inputs (embedPAContext (map witnessedAxiom witnesses)).
Proof.
  intros M hPA inputs.
  assert (hempty : RawCodedPAAxiomWitnessContext M
      (raw_zero M) (raw_zero M)).
  {
    pose proof (raw_codedPAAxiomWitnessContext_standard M hPA []) as h.
    cbn [rawQuotedPAAxiomWitnessList rawListCode map] in h.
    exact h.
  }
  destruct
    (raw_codedPALocalProof_dynamicRestrictedRerootLaw_on_witnessed_base
      M hPA inputs (raw_zero M) (raw_zero M) hempty)
    as (witnesses & root & hwitnessed & hroot).
  exists witnesses. split.
  - rewrite rawTemplateContextCode_as_on_tail.
    rewrite (raw_templateContextCodeOnTail_embedPAAxiomWitnesses M
      (rawDirectStructuralTemplateTranslation M hPA inputs)
      (rawDirectStructuralTemplatePAAgreement M hPA inputs)
      witnesses (raw_zero M)).
    exact hwitnessed.
  - unfold
      RawCoqRestrictedPADirectOrIntroductionLeftDynamicRestrictedRerootLawRoot.
    exists root.
    rewrite (raw_coverageEigenContext_witnessed_code M
      (rawDirectStructuralTemplateTranslation M hPA inputs)
      (rawDirectStructuralTemplatePAAgreement M hPA inputs)
      witnesses).
    exact hroot.
Qed.

End
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftDynamicRerootCompilation.
