(**
  Feed synchronized Sigma/Or roots into the guarded canonical append client.

  The historical guarded boundary asks for the full local-exclusive
  identification merely to project the append-bound-zero equation.  That is
  now too strong: the canonical successor row uses hierarchy coordinates
  lower=0 and upper=1, while the old record demands lower=upper.

  This module combines the synchronized identification with a growing
  producer for the three genuinely remaining Sigma/Or roots.  Its conclusion
  is the literal guarded mode-zero fixed-production callback expected by the
  canonical append assembly, with no local-exclusive premise.
*)

From Stdlib Require Import List.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedRestrictedPAProof
  RawCodedPALocalProofExistential
  RawCodedTemplateSyntax
  RawCodedTemplateProofCompiler
  RawCodedTemplateProofCompilerSelfShiftTail
  RawCodedPALocalProofUniversalIntroductionChain
  RawCodedTemplateDirectStructuralTranslation
  RawCodedPAAxiomWitnessPrefix
  RawCodedFourStateTableAppendExistentialElimination
  RawCodedFourStateTableAppendGlobalTraversalAssembly
  RawCodedDynamicTruthSuccessorRowsAppendNormalization
  RawCodedDynamicTruthSigmaOrFixedProductionTemplate
  RawCodedDynamicTruthSigmaOrFixedProductionAppendIntegration
  RawCodedDynamicTruthSigmaOrGuardedCanonicalTranslationSynchronization.

Module
  PABoundedRawCodedDynamicTruthSigmaOrGuardedCanonicalConsumerIntegration.

Import ListNotations.
Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedTemplateProofCompilerSelfShiftTail.
Import PABoundedRawCodedPALocalProofUniversalIntroductionChain.
Import PABoundedRawCodedTemplateDirectStructuralTranslation.
Import PABoundedRawCodedPAAxiomWitnessPrefix.
Import PABoundedRawCodedFourStateTableAppendExistentialElimination.
Import PABoundedRawCodedFourStateTableAppendGlobalTraversalAssembly.
Import PABoundedRawCodedDynamicTruthSuccessorRowsAppendNormalization.
Import PABoundedRawCodedDynamicTruthSigmaOrFixedProductionTemplate.
Import
  PABoundedRawCodedDynamicTruthSigmaOrFixedProductionAppendIntegration.
Import
  PABoundedRawCodedDynamicTruthSigmaOrGuardedCanonicalTranslationSynchronization.

(** The exact temporary context consumed by the guarded mode-zero fixed
    production. *)
Definition coqDynamicTruthSigmaOrGuardedCanonicalModeZeroRowPrefix
    (outerPrefix : TemplateContext) : TemplateContext :=
  templateContextShiftMany 5
    (coqFourStateTableAppendWitnessContext
      (ttVar 7) (ttVar 6) (ttVar 5) (ttVar 4)
      (ttVar 3) (ttVar 2) (ttVar 1) (ttVar 0)
      (ttParameter coqDynamicTruthAppendRowBoundParameterName)
      (embedPATerm (Term.numeral 0))
      (ttVar 2) (ttVar 6) (ttVar 5) outerPrefix).

(** A growing compiler for precisely the domain, parent-code, and selected
    left-state roots left by the synchronized fixed-production theorem. *)
Definition
    RawDynamicTruthSigmaOrGuardedCanonicalGrowingThreeRootCompilerUnderPrefixAt
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    (outerPrefix : TemplateContext) : Prop :=
  forall sourceWitnessList sourceContext,
  RawCodedPAAxiomWitnessContext M sourceWitnessList sourceContext ->
  exists (witnesses : StandardPAAxiomWitnessPrefix)
      (domainRoot codeRoot leftStateRoot : M),
    RawCodedPAAxiomWitnessContext M
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        witnesses sourceWitnessList)
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses sourceContext) /\
    RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        (rawStandardPAAxiomWitnessPrefixContextCode M
          witnesses sourceContext)
        (coqDynamicTruthSigmaOrGuardedCanonicalModeZeroRowPrefix
          outerPrefix))
      (rawTemplateFormula
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        (coqDynamicTruthSigmaOrOpenedDomainAt
          (ttVar 7) (ttVar 6) (ttVar 5) (ttVar 4)
          (ttVar 3) (ttVar 2) (ttVar 1) (ttVar 0))) domainRoot /\
    RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        (rawStandardPAAxiomWitnessPrefixContextCode M
          witnesses sourceContext)
        (coqDynamicTruthSigmaOrGuardedCanonicalModeZeroRowPrefix
          outerPrefix))
      (rawTemplateFormula
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        (coqDynamicTruthSigmaOrOpenedCodeAt
          (ttVar 7) (ttVar 6) (ttVar 5) (ttVar 4)
          (ttVar 3) (ttVar 2) (ttVar 1) (ttVar 0))) codeRoot /\
    RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        (rawStandardPAAxiomWitnessPrefixContextCode M
          witnesses sourceContext)
        (coqDynamicTruthSigmaOrGuardedCanonicalModeZeroRowPrefix
          outerPrefix))
      (rawTemplateFormula
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        (coqDynamicTruthSigmaOrOpenedLeftStateAt
          (ttVar 7) (ttVar 6) (ttVar 5) (ttVar 4)
          (ttVar 3) (ttVar 2) (ttVar 1) (ttVar 0))) leftStateRoot.

Arguments
  RawDynamicTruthSigmaOrGuardedCanonicalGrowingThreeRootCompilerUnderPrefixAt
  M hPA inputs outerPrefix : clear implicits.

(** The exact fixed-production callback consumed by the canonical append
    assembly at guarded root terms and mode zero.  It is stated locally so
    this leaf module does not import the much larger historical append source
    file; its context and conclusion are literal, not abstracted premises. *)
Definition
    RawDynamicTruthSigmaOrGuardedCanonicalGrowingFixedProductionConsumerUnderPrefixAt
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    (outerPrefix : TemplateContext) : Prop :=
  forall sourceWitnessList sourceContext,
  RawCodedPAAxiomWitnessContext M sourceWitnessList sourceContext ->
  exists (witnesses : StandardPAAxiomWitnessPrefix)
      (fixedProductionRoot : M),
    RawCodedPAAxiomWitnessContext M
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        witnesses sourceWitnessList)
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses sourceContext) /\
    RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        (rawStandardPAAxiomWitnessPrefixContextCode M
          witnesses sourceContext)
        (coqDynamicTruthSigmaOrGuardedCanonicalModeZeroRowPrefix
          outerPrefix))
      (rawTemplateFormula
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        (templateFormulaOpen (embedPATerm (Term.numeral 0))
          (coqFourStateTableAppendEmbeddedModeProductionMotive
            coqDynamicTruthSigmaOrZeroCanonicalSigmaRowFormula
            coqDynamicTruthSigmaOrZeroCanonicalPiRowFormula)))
      fixedProductionRoot.

Arguments
  RawDynamicTruthSigmaOrGuardedCanonicalGrowingFixedProductionConsumerUnderPrefixAt
  M hPA inputs outerPrefix : clear implicits.

(** The synchronized three-root producer is exactly a guarded mode-zero
    growing fixed-production compiler. *)
Theorem
    raw_dynamicTruthSigmaOrGuardedCanonical_growingFixedProductionCompilerUnderPrefixAt_of_three_roots :
  forall (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M) outerPrefix,
  RawDynamicTruthSigmaOrGuardedCanonicalTranslationIdentification
    M inputs ->
  RawDynamicTruthSigmaOrGuardedCanonicalGrowingThreeRootCompilerUnderPrefixAt
    M hPA inputs outerPrefix ->
  RawDynamicTruthSigmaOrGuardedCanonicalGrowingFixedProductionConsumerUnderPrefixAt
    M hPA inputs outerPrefix.
Proof.
  intros M hPA inputs outerPrefix hidentification hthree
    sourceWitnessList sourceContext hsource.
  destruct (hthree sourceWitnessList sourceContext hsource) as
    (witnesses & domainRoot & codeRoot & leftStateRoot &
      htarget & hdomain & hcode & hleftState).
  destruct
    (raw_dynamicTruthZeroCanonicalFixedProductionRoot_of_sigma_or_guarded_synchronized_three_roots
      M hPA inputs
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        witnesses sourceWitnessList)
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses sourceContext)
      (coqDynamicTruthSigmaOrGuardedCanonicalModeZeroRowPrefix
        outerPrefix)
      (ttVar 7) (ttVar 6) (ttVar 5) (ttVar 4)
      (ttVar 3) (ttVar 2) (ttVar 1) (ttVar 0)
      domainRoot codeRoot leftStateRoot
      hidentification htarget hdomain hcode hleftState) as
    [fixedProductionRoot hfixed].
  exists witnesses, fixedProductionRoot.
  split; [exact htarget |].
  change (RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail
      (rawDirectStructuralTemplateTranslation M hPA inputs)
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses sourceContext)
      (coqDynamicTruthSigmaOrGuardedCanonicalModeZeroRowPrefix
        outerPrefix))
    (rawTemplateFormula
      (rawDirectStructuralTemplateTranslation M hPA inputs)
      (templateFormulaOpen (embedPATerm (Term.numeral 0))
        (coqFourStateTableAppendEmbeddedModeProductionMotive
          coqDynamicTruthSigmaOrZeroCanonicalSigmaRowFormula
          coqDynamicTruthSigmaOrZeroCanonicalPiRowFormula)))
    fixedProductionRoot) in hfixed.
  exact hfixed.
Qed.

End
  PABoundedRawCodedDynamicTruthSigmaOrGuardedCanonicalConsumerIntegration.
