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
  RawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftRecursiveChildCompilation
  RawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftDynamicRerootSource
  RawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftDynamicRerootValidity.

Import ListNotations.

Module
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftDynamicRerootCompilation.

Import PA.
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

End
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftDynamicRerootCompilation.
