(**
  Arbitrary-root decision elimination for native aligned truth evidence.

  The canonical local decision compiler opens its three universal binders at
  [#2,#1,#0].  Recursive rule cases instead need to instantiate that same
  theorem at their own formula and assignment coordinates.  For Imp-I those
  coordinates are [#6,#9,#8].  This file first factors the context-safe
  carrier argument for an arbitrary opened implication.  It then presents
  the aligned decision body through the soundness direct translation and
  specializes the generic argument to the Imp-I coordinates.

  The specialization is deliberately explicit about the two represented
  arithmetic roots it consumes: atomic adequacy of the antecedent formula
  and the disjunction of its two rank domains.  Assignment definedness is
  compiled here from PA and all three roots are synchronized on one standard
  PA-witness extension.  Thus no hidden context contraction or choice of a
  nonstandard witness tail occurs.
*)

From Stdlib Require Import List Arith Lia.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  CodedSyntax
  RawCodedSyntaxConstructors
  RawCodedFormulaOperations
  RawCodedNumeralTermCode
  RawCodedAssignment
  RawCodedFixedLevelTruthTotality
  RawCodedFormulaOperationCrossTraceFunctionality
  RawCodedRestrictedPAConsistencyFormulaCode
  RawCodedContextLists
  RawCodedProofBinaryConstructors
  RawCodedProofAndIConstructor
  RawCodedRestrictedPAProof
  RawCodedPAAxiomWitnessPrefix
  RawCodedPALocalProofExistential
  RawCodedPALocalProofWitnessedContextMerge
  RawCodedPALocalProofComposition
  RawCodedPALocalProofAndIntroduction
  RawCodedPALocalProofUniversalEliminationChain
  RawCodedTemplateSyntax
  RawCodedTemplateProofCompiler
  RawCodedTemplateProofCompilerSelfShiftTail
  RawCodedTemplateStructuralTranslation
  RawCodedTemplateStructuralPAAgreement
  RawCodedTemplateDirectStructuralTranslation
  RawCodedTemplateDirectStructuralPAAgreement
  RawCodedTemplatePAEmbedding
  RawCodedTemplateTripleUniversalOpening
  RawCodedRestrictedPATemplateTernaryApplicationCompilation
  RawCodedTemplateLocalProofWitnessedTailTransport
  RawCodedTemplateLocalProofStandardWitnessTailTransport
  RawCodedAssignmentUniversalDefinednessProofCompilation
  RawCodedDynamicTruthNativeLocalPositiveGraph
  RawCodedDynamicTruthNativeLocalProofCompilation
  RawCodedDynamicTruthLocalExclusiveTemplateDirectInputs
  RawCodedDynamicTruthLocalExclusiveTemplateTraceCompilation
  RawCodedFourStateTableAppendGlobalTraversalAssembly
  RawCodedDirectTemplateTernaryApplicationCrossTranslationCongruence
  RawCodedDynamicTruthNativeLocalStagedCallbackCompilation
  RawCodedDynamicTruthNativeAlignedStrongStepLogicalRootsCompilation
  RawCodedDynamicTruthNativeAlignedRootApplicationIdentification
  RawCodedDynamicTruthNativeAlignedRootAtomicAdequacy
  RawCodedRestrictedPAConsistencyFromUniversalSoundness
  RawCodedRestrictedPADerivationSoundnessDirectImpIntroductionCase.

Module
  PABoundedRawCodedDynamicTruthNativeAlignedArbitraryRootReadyDecision.

Import ListNotations.
Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedCodedSyntax.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedNumeralTermCode.
Import PABoundedRawCodedAssignment.
Import PABoundedRawCodedFixedLevelTruthTotality.
Import PABoundedRawCodedFormulaOperationCrossTraceFunctionality.
Import PABoundedRawCodedRestrictedPAConsistencyFormulaCode.
Import PABoundedRawCodedContextLists.
Import PABoundedRawCodedProofBinaryConstructors.
Import PABoundedRawCodedProofAndIConstructor.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedPAAxiomWitnessPrefix.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPALocalProofWitnessedContextMerge.
Import PABoundedRawCodedPALocalProofComposition.
Import PABoundedRawCodedPALocalProofAndIntroduction.
Import PABoundedRawCodedPALocalProofUniversalEliminationChain.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedTemplateProofCompilerSelfShiftTail.
Import PABoundedRawCodedTemplateStructuralTranslation.
Import PABoundedRawCodedTemplateStructuralPAAgreement.
Import PABoundedRawCodedTemplateDirectStructuralTranslation.
Import PABoundedRawCodedTemplateDirectStructuralPAAgreement.
Import PABoundedRawCodedTemplatePAEmbedding.
Import PABoundedRawCodedTemplateTripleUniversalOpening.
Import
  PABoundedRawCodedRestrictedPATemplateTernaryApplicationCompilation.
Import PABoundedRawCodedTemplateLocalProofWitnessedTailTransport.
Import PABoundedRawCodedTemplateLocalProofStandardWitnessTailTransport.
Import PABoundedRawCodedAssignmentUniversalDefinednessProofCompilation.
Import PABoundedRawCodedDynamicTruthNativeLocalPositiveGraph.
Import PABoundedRawCodedDynamicTruthNativeLocalProofCompilation.
Import PABoundedRawCodedDynamicTruthLocalExclusiveTemplateDirectInputs.
Import PABoundedRawCodedDynamicTruthLocalExclusiveTemplateTraceCompilation.
Import PABoundedRawCodedFourStateTableAppendGlobalTraversalAssembly.
Import
  PABoundedRawCodedDirectTemplateTernaryApplicationCrossTranslationCongruence.
Import
  PABoundedRawCodedDynamicTruthNativeLocalStagedCallbackCompilation.
Import
  PABoundedRawCodedDynamicTruthNativeAlignedStrongStepLogicalRootsCompilation.
Import
  PABoundedRawCodedDynamicTruthNativeAlignedRootApplicationIdentification.
Import
  PABoundedRawCodedDynamicTruthNativeAlignedRootAtomicAdequacy.
Import PABoundedRawCodedRestrictedPAConsistencyFromUniversalSoundness.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectImpIntroductionCase.

(** ------------------------------------------------------------------
    Generic arbitrary-opening kernels. *)

(** Once an arbitrary All-E chain has exposed an implication and its
    antecedent is proved in the same context, ordinary modus ponens is the
    entire decision step.  The source and opened codes are unconstrained;
    in particular this theorem is not tied to the diagonal [#2,#1,#0]
    opening used by the historical local adapter. *)
Theorem
    raw_codedPALocalProofOf_openedEvidenceDecision_of_elimination_chain :
    forall (M : RawPAModel), RawPASatisfies M -> forall
    context sourceCode openedAdmissible sigmaEvidence piEvidence
    sourceRoot admissibleRoot,
  RawCodedUniversalEliminationChain M sourceCode
    (rawFormulaImpCode M openedAdmissible
      (rawFormulaOrCode M sigmaEvidence piEvidence)) ->
  RawCodedPALocalProofOf M context sourceCode sourceRoot ->
  RawCodedPALocalProofOf M context openedAdmissible admissibleRoot ->
  exists decisionRoot,
    RawCodedPALocalProofOf M context
      (rawFormulaOrCode M sigmaEvidence piEvidence) decisionRoot.
Proof.
  intros M hPA context sourceCode openedAdmissible
    sigmaEvidence piEvidence sourceRoot admissibleRoot
    hchain hsource hadmissible.
  destruct
    (raw_codedPALocalProofOf_universal_elimination_chain
      M hPA context sourceCode
      (rawFormulaImpCode M openedAdmissible
        (rawFormulaOrCode M sigmaEvidence piEvidence))
      hchain sourceRoot hsource) as [openedRoot hopened].
  exists (rawProofImpERoot M context openedAdmissible
    (rawFormulaOrCode M sigmaEvidence piEvidence)
    openedRoot admissibleRoot).
  exact (raw_codedPALocalProofOf_impE M hPA context
    openedAdmissible (rawFormulaOrCode M sigmaEvidence piEvidence)
    openedRoot admissibleRoot hopened hadmissible).
Qed.

(** Synchronize a source proof on the caller's witnessed PA tail with an
    admissibility proof already compiled on one named standard extension.
    The same finite template prefix is retained throughout. *)
Theorem
    raw_codedPALocalProofOf_openedEvidenceDecision_on_standard_witness_extension_under_prefix :
    forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M)
    baseWitnessList baseContext prefix
    (witnesses : StandardPAAxiomWitnessPrefix)
    sourceCode openedAdmissible sigmaEvidence piEvidence
    sourceRoot admissibleRoot,
  RawCodedTemplatePrefixAtomicallyAdequate M translation prefix ->
  RawCodedPAAxiomWitnessContext M baseWitnessList baseContext ->
  RawCodedPAAxiomWitnessContext M
    (rawStandardPAAxiomWitnessPrefixWitnessListCode M
      witnesses baseWitnessList)
    (rawStandardPAAxiomWitnessPrefixContextCode M
      witnesses baseContext) ->
  RawCodedUniversalEliminationChain M sourceCode
    (rawFormulaImpCode M openedAdmissible
      (rawFormulaOrCode M sigmaEvidence piEvidence)) ->
  RawCodedPALocalProofOf M baseContext sourceCode sourceRoot ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail translation
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses baseContext) prefix)
    openedAdmissible admissibleRoot ->
  exists decisionRoot,
    RawContextListIncluded M baseContext
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses baseContext) /\
    RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation
        (rawStandardPAAxiomWitnessPrefixContextCode M
          witnesses baseContext) prefix)
      (rawFormulaOrCode M sigmaEvidence piEvidence) decisionRoot.
Proof.
  intros M hPA translation baseWitnessList baseContext prefix witnesses
    sourceCode openedAdmissible sigmaEvidence piEvidence
    sourceRoot admissibleRoot hprefix hbase hextended
    hchain hsource hadmissible.
  set (extendedWitnessList :=
    rawStandardPAAxiomWitnessPrefixWitnessListCode M
      witnesses baseWitnessList).
  set (extendedContext :=
    rawStandardPAAxiomWitnessPrefixContextCode M
      witnesses baseContext).
  assert (hincluded : RawContextListIncluded M baseContext extendedContext).
  {
    unfold extendedContext.
    exact (raw_standardPAAxiomWitnessPrefixContextCode_target_included
      M hPA witnesses baseContext).
  }
  destruct
    (raw_codedPALocalProof_sameTemplatePrefix_witnessedTail_transport
      M hPA translation
      baseWitnessList baseContext extendedWitnessList extendedContext
      [] sourceCode sourceRoot hbase hextended hincluded hsource)
    as [transportedSourceRoot htransportedSource].
  cbn [rawTemplateContextCodeOnTail] in htransportedSource.
  destruct (raw_codedPALocalProof_templatePrefix M hPA translation
    extendedContext prefix sourceCode transportedSourceRoot
    (raw_codedPAAxiomWitnessContext_context_realizable
      M extendedWitnessList extendedContext hextended)
    hprefix htransportedSource) as [prefixedSourceRoot hprefixedSource].
  destruct
    (raw_codedPALocalProofOf_openedEvidenceDecision_of_elimination_chain
      M hPA
      (rawTemplateContextCodeOnTail translation extendedContext prefix)
      sourceCode openedAdmissible sigmaEvidence piEvidence
      prefixedSourceRoot admissibleRoot
      hchain hprefixedSource hadmissible)
    as [decisionRoot hdecision].
  exists decisionRoot. split; assumption.
Qed.

(** ------------------------------------------------------------------
    Aligned native decision syntax. *)

(** The aligned direct input uses the lower-level parameter for the current
    local rank domains and its two direct truth selectors for the native
    Sigma and Pi evidence predicates. *)
Definition coqDynamicTruthNativeAlignedDecisionSigmaDomainTemplate
    : TemplateFormula :=
  templateFormulaOpen coqRestrictedPASoundnessLowerLevelTerm
    (embedPAFormula dynamicTruthLocalSigmaInputDomainTemplate).

Definition coqDynamicTruthNativeAlignedDecisionPiDomainTemplate
    : TemplateFormula :=
  templateFormulaOpen coqRestrictedPASoundnessLowerLevelTerm
    (embedPAFormula dynamicTruthLocalPiInputDomainTemplate).

Definition coqDynamicTruthNativeAlignedDecisionAtomicTemplate
    : TemplateFormula :=
  embedPAFormula (codedFormulaAtomicallyAdequateTermAt (tVar 2)).

Definition coqDynamicTruthNativeAlignedDecisionAssignmentTemplate
    : TemplateFormula :=
  embedPAFormula
    (codedAssignmentDefinedThroughTermAt (tVar 1) (tVar 0) (tVar 2)).

Definition coqDynamicTruthNativeAlignedDecisionDomainTemplate
    : TemplateFormula :=
  tfOr coqDynamicTruthNativeAlignedDecisionSigmaDomainTemplate
    coqDynamicTruthNativeAlignedDecisionPiDomainTemplate.

Definition coqDynamicTruthNativeAlignedDecisionAdmissibleTemplate
    : TemplateFormula :=
  tfAnd coqDynamicTruthNativeAlignedDecisionAtomicTemplate
    (tfAnd coqDynamicTruthNativeAlignedDecisionAssignmentTemplate
      coqDynamicTruthNativeAlignedDecisionDomainTemplate).

Definition coqDynamicTruthNativeAlignedDecisionBodyTemplate
    : TemplateFormula :=
  tfImp coqDynamicTruthNativeAlignedDecisionAdmissibleTemplate
    (tfOr coqDynamicTruthNativeAlignedSigmaEvidenceConclusionTemplate
      coqDynamicTruthNativeAlignedPiEvidenceConclusionTemplate).

Lemma coqDynamicTruthNativeAlignedDecisionBodyTemplate_scoped_three :
  TemplateFormulaScoped 3
    coqDynamicTruthNativeAlignedDecisionBodyTemplate.
Proof.
  vm_compute. repeat split; lia.
Qed.

(** The two current domain codes selected by the native trace are exactly
    the lower-level domain leaves of the aligned direct translation. *)
Lemma raw_dynamicTruthNativeAlignedDecision_domains_identified : forall
    (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (tail : nat -> M) predecessorLevel baseContext currentLocal
    nextInputGlobalSigma nextInputGlobalPi
    (aligned : RawDynamicTruthNativeLocalAlignedPredecessorAt M tail
      predecessorLevel baseContext currentLocal
      nextInputGlobalSigma nextInputGlobalPi)
    inputLevelNumeral
    (inputs : RawCodedTemplateDirectStructuralInputs M),
  RawNumeralTermCodeAt M (raw_succ M predecessorLevel)
    inputLevelNumeral ->
  RawDynamicTruthNativeAlignedStrongStepStructuralInputsAt
      M hPA tail predecessorLevel baseContext currentLocal
      nextInputGlobalSigma nextInputGlobalPi aligned
      inputLevelNumeral inputs ->
  rawDirectTemplateFormula inputs
      coqDynamicTruthNativeAlignedDecisionSigmaDomainTemplate =
    rawDynamicTruthNativeLocalAligned_currentSigmaDomain M tail
      predecessorLevel baseContext currentLocal
      nextInputGlobalSigma nextInputGlobalPi aligned /\
  rawDirectTemplateFormula inputs
      coqDynamicTruthNativeAlignedDecisionPiDomainTemplate =
    rawDynamicTruthNativeLocalAligned_currentPiDomain M tail
      predecessorLevel baseContext currentLocal
      nextInputGlobalSigma nextInputGlobalPi aligned.
Proof.
  intros M hPA tail predecessorLevel baseContext currentLocal
    nextInputGlobalSigma nextInputGlobalPi aligned inputLevelNumeral
    inputs hinputNumeral hstructural.
  destruct hstructural as
    (localSigmaRow & localPiRow & _hwrapper & hlower & _hsigmaRow &
     _hpiRow & _hsigmaEvidence & _hpiEvidence &
     _hsigmaGlobal & _hpiGlobal).
  pose proof
    (rawDynamicTruthNativeLocalAligned_currentTrace M tail predecessorLevel
      baseContext currentLocal nextInputGlobalSigma nextInputGlobalPi aligned)
    as htrace.
  destruct htrace as
    (_horbit & traceInputLevel & evidenceGlobalSigma & evidenceGlobalPi &
     traceInputLevelNumeral & htraceLevel & _hsuccessor & htraceNumeral &
     hsigmaDomain & hpiDomain & _hsigmaApplication & _hpiApplication).
  subst traceInputLevel.
  pose proof (raw_numeralTermCodeAt_functional M hPA
    (raw_succ M predecessorLevel)
    traceInputLevelNumeral inputLevelNumeral
    htraceNumeral hinputNumeral) as hnumerals.
  subst traceInputLevelNumeral.
  pose proof (rawDirectTemplateFormula_open M hPA inputs
    (embedPAFormula dynamicTruthLocalSigmaInputDomainTemplate)
    coqRestrictedPASoundnessLowerLevelTerm) as hsigmaDirect.
  pose proof (rawDirectTemplateFormula_open M hPA inputs
    (embedPAFormula dynamicTruthLocalPiInputDomainTemplate)
    coqRestrictedPASoundnessLowerLevelTerm) as hpiDirect.
  assert (hsigmaSource :
    rawDirectTemplateFormula inputs
      (embedPAFormula dynamicTruthLocalSigmaInputDomainTemplate) =
    rawNumeralValue M
      (formulaCode dynamicTruthLocalSigmaInputDomainTemplate)).
  {
    unfold rawDirectTemplateFormula.
    rewrite rawStructuralTemplateFormulaWith_embedPA.
    exact (rawQuotedFormulaCode_standard M hPA
      dynamicTruthLocalSigmaInputDomainTemplate).
  }
  assert (hpiSource :
    rawDirectTemplateFormula inputs
      (embedPAFormula dynamicTruthLocalPiInputDomainTemplate) =
    rawNumeralValue M
      (formulaCode dynamicTruthLocalPiInputDomainTemplate)).
  {
    unfold rawDirectTemplateFormula.
    rewrite rawStructuralTemplateFormulaWith_embedPA.
    exact (rawQuotedFormulaCode_standard M hPA
      dynamicTruthLocalPiInputDomainTemplate).
  }
  rewrite hsigmaSource, hlower in hsigmaDirect.
  rewrite hpiSource, hlower in hpiDirect.
  split.
  - exact (raw_codedFormulaSingleSubstitution_functional M hPA
      inputLevelNumeral
      (rawNumeralValue M
        (formulaCode dynamicTruthLocalSigmaInputDomainTemplate))
      (rawDirectTemplateFormula inputs
        coqDynamicTruthNativeAlignedDecisionSigmaDomainTemplate)
      (rawDynamicTruthNativeLocalAligned_currentSigmaDomain M tail
        predecessorLevel baseContext currentLocal
        nextInputGlobalSigma nextInputGlobalPi aligned)
      hsigmaDirect hsigmaDomain).
  - exact (raw_codedFormulaSingleSubstitution_functional M hPA
      inputLevelNumeral
      (rawNumeralValue M
        (formulaCode dynamicTruthLocalPiInputDomainTemplate))
      (rawDirectTemplateFormula inputs
        coqDynamicTruthNativeAlignedDecisionPiDomainTemplate)
      (rawDynamicTruthNativeLocalAligned_currentPiDomain M tail
        predecessorLevel baseContext currentLocal
        nextInputGlobalSigma nextInputGlobalPi aligned)
      hpiDirect hpiDomain).
Qed.

(** At the canonical variables the aligned direct body is literally the
    decision conjunct projected from the native current field. *)
Theorem raw_dynamicTruthNativeAlignedDecisionBody_identified : forall
    (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (tail : nat -> M) predecessorLevel baseContext currentLocal
    nextInputGlobalSigma nextInputGlobalPi
    (aligned : RawDynamicTruthNativeLocalAlignedPredecessorAt M tail
      predecessorLevel baseContext currentLocal
      nextInputGlobalSigma nextInputGlobalPi)
    inputLevelNumeral
    (inputs : RawCodedTemplateDirectStructuralInputs M),
  RawNumeralTermCodeAt M (raw_succ M predecessorLevel)
    inputLevelNumeral ->
  RawDynamicTruthNativeAlignedStrongStepStructuralInputsAt
      M hPA tail predecessorLevel baseContext currentLocal
      nextInputGlobalSigma nextInputGlobalPi aligned
      inputLevelNumeral inputs ->
  rawDirectTemplateFormula inputs
      coqDynamicTruthNativeAlignedDecisionBodyTemplate =
    rawDynamicTruthLocalDecisionCode M
      (rawDynamicTruthNativeLocalAligned_currentSigmaDomain M tail
        predecessorLevel baseContext currentLocal
        nextInputGlobalSigma nextInputGlobalPi aligned)
      (rawDynamicTruthNativeLocalAligned_currentPiDomain M tail
        predecessorLevel baseContext currentLocal
        nextInputGlobalSigma nextInputGlobalPi aligned)
      (rawDynamicTruthNativeLocalAligned_currentSigmaEvidence M tail
        predecessorLevel baseContext currentLocal
        nextInputGlobalSigma nextInputGlobalPi aligned)
      (rawDynamicTruthNativeLocalAligned_currentPiEvidence M tail
        predecessorLevel baseContext currentLocal
        nextInputGlobalSigma nextInputGlobalPi aligned).
Proof.
  intros M hPA tail predecessorLevel baseContext currentLocal
    nextInputGlobalSigma nextInputGlobalPi aligned inputLevelNumeral
    inputs hinputNumeral hstructural.
  pose proof hstructural as hstructuralForDomains.
  destruct hstructural as
    (localSigmaRow & localPiRow & _hwrapper & _hlower & _hsigmaRow &
     _hpiRow & hsigmaEvidence & hpiEvidence &
     _hsigmaGlobal & _hpiGlobal).
  destruct
    (raw_dynamicTruthNativeAlignedDecision_domains_identified
      M hPA tail predecessorLevel baseContext currentLocal
      nextInputGlobalSigma nextInputGlobalPi aligned inputLevelNumeral
      inputs hinputNumeral hstructuralForDomains)
    as [hsigmaDomain hpiDomain].
  assert (hatomic :
    rawDirectTemplateFormula inputs
      coqDynamicTruthNativeAlignedDecisionAtomicTemplate =
    rawNumeralValue M
      (formulaCode (codedFormulaAtomicallyAdequateTermAt (tVar 2)))).
  {
    unfold coqDynamicTruthNativeAlignedDecisionAtomicTemplate,
      rawDirectTemplateFormula.
    rewrite rawStructuralTemplateFormulaWith_embedPA.
    exact (rawQuotedFormulaCode_standard M hPA
      (codedFormulaAtomicallyAdequateTermAt (tVar 2))).
  }
  assert (hassignment :
    rawDirectTemplateFormula inputs
      coqDynamicTruthNativeAlignedDecisionAssignmentTemplate =
    rawNumeralValue M
      (formulaCode
        (codedAssignmentDefinedThroughTermAt
          (tVar 1) (tVar 0) (tVar 2)))).
  {
    unfold coqDynamicTruthNativeAlignedDecisionAssignmentTemplate,
      rawDirectTemplateFormula.
    rewrite rawStructuralTemplateFormulaWith_embedPA.
    exact (rawQuotedFormulaCode_standard M hPA
      (codedAssignmentDefinedThroughTermAt
        (tVar 1) (tVar 0) (tVar 2))).
  }
  unfold coqDynamicTruthNativeAlignedDecisionBodyTemplate,
    coqDynamicTruthNativeAlignedDecisionAdmissibleTemplate,
    coqDynamicTruthNativeAlignedDecisionDomainTemplate.
  change
    (rawFormulaImpCode M
      (rawFormulaAndCode M
        (rawDirectTemplateFormula inputs
          coqDynamicTruthNativeAlignedDecisionAtomicTemplate)
        (rawFormulaAndCode M
          (rawDirectTemplateFormula inputs
            coqDynamicTruthNativeAlignedDecisionAssignmentTemplate)
          (rawFormulaOrCode M
            (rawDirectTemplateFormula inputs
              coqDynamicTruthNativeAlignedDecisionSigmaDomainTemplate)
            (rawDirectTemplateFormula inputs
              coqDynamicTruthNativeAlignedDecisionPiDomainTemplate))))
      (rawFormulaOrCode M
        (rawDirectTemplateFormula inputs
          coqDynamicTruthNativeAlignedSigmaEvidenceConclusionTemplate)
        (rawDirectTemplateFormula inputs
          coqDynamicTruthNativeAlignedPiEvidenceConclusionTemplate)) =
    rawDynamicTruthLocalDecisionCode M
      (rawDynamicTruthNativeLocalAligned_currentSigmaDomain M tail
        predecessorLevel baseContext currentLocal
        nextInputGlobalSigma nextInputGlobalPi aligned)
      (rawDynamicTruthNativeLocalAligned_currentPiDomain M tail
        predecessorLevel baseContext currentLocal
        nextInputGlobalSigma nextInputGlobalPi aligned)
      (rawDynamicTruthNativeLocalAligned_currentSigmaEvidence M tail
        predecessorLevel baseContext currentLocal
        nextInputGlobalSigma nextInputGlobalPi aligned)
      (rawDynamicTruthNativeLocalAligned_currentPiEvidence M tail
        predecessorLevel baseContext currentLocal
        nextInputGlobalSigma nextInputGlobalPi aligned)).
  rewrite hatomic, hassignment, hsigmaDomain, hpiDomain,
    hsigmaEvidence, hpiEvidence.
  reflexivity.
Qed.

Corollary raw_dynamicTruthNativeAlignedDecisionSource_identified : forall
    (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (tail : nat -> M) predecessorLevel baseContext currentLocal
    nextInputGlobalSigma nextInputGlobalPi
    (aligned : RawDynamicTruthNativeLocalAlignedPredecessorAt M tail
      predecessorLevel baseContext currentLocal
      nextInputGlobalSigma nextInputGlobalPi)
    inputLevelNumeral
    (inputs : RawCodedTemplateDirectStructuralInputs M),
  RawNumeralTermCodeAt M (raw_succ M predecessorLevel)
    inputLevelNumeral ->
  RawDynamicTruthNativeAlignedStrongStepStructuralInputsAt
      M hPA tail predecessorLevel baseContext currentLocal
      nextInputGlobalSigma nextInputGlobalPi aligned
      inputLevelNumeral inputs ->
  rawDirectTemplateFormula inputs
      (tfAll (tfAll (tfAll
        coqDynamicTruthNativeAlignedDecisionBodyTemplate))) =
    rawDynamicTruthLocalFormulaAll3Code M
      (rawDynamicTruthLocalDecisionCode M
        (rawDynamicTruthNativeLocalAligned_currentSigmaDomain M tail
          predecessorLevel baseContext currentLocal
          nextInputGlobalSigma nextInputGlobalPi aligned)
        (rawDynamicTruthNativeLocalAligned_currentPiDomain M tail
          predecessorLevel baseContext currentLocal
          nextInputGlobalSigma nextInputGlobalPi aligned)
        (rawDynamicTruthNativeLocalAligned_currentSigmaEvidence M tail
          predecessorLevel baseContext currentLocal
          nextInputGlobalSigma nextInputGlobalPi aligned)
        (rawDynamicTruthNativeLocalAligned_currentPiEvidence M tail
          predecessorLevel baseContext currentLocal
          nextInputGlobalSigma nextInputGlobalPi aligned)).
Proof.
  intros M hPA tail predecessorLevel baseContext currentLocal
    nextInputGlobalSigma nextInputGlobalPi aligned inputLevelNumeral
    inputs hinputNumeral hstructural.
  change
    (rawFormulaAllCode M
      (rawFormulaAllCode M
        (rawFormulaAllCode M
          (rawDirectTemplateFormula inputs
            coqDynamicTruthNativeAlignedDecisionBodyTemplate))) =
      rawFormulaAllCode M
        (rawFormulaAllCode M
          (rawFormulaAllCode M
            (rawDynamicTruthLocalDecisionCode M
              (rawDynamicTruthNativeLocalAligned_currentSigmaDomain M tail
                predecessorLevel baseContext currentLocal
                nextInputGlobalSigma nextInputGlobalPi aligned)
              (rawDynamicTruthNativeLocalAligned_currentPiDomain M tail
                predecessorLevel baseContext currentLocal
                nextInputGlobalSigma nextInputGlobalPi aligned)
              (rawDynamicTruthNativeLocalAligned_currentSigmaEvidence M tail
                predecessorLevel baseContext currentLocal
                nextInputGlobalSigma nextInputGlobalPi aligned)
              (rawDynamicTruthNativeLocalAligned_currentPiEvidence M tail
                predecessorLevel baseContext currentLocal
                nextInputGlobalSigma nextInputGlobalPi aligned))))).
  repeat f_equal.
  change (rawDirectTemplateFormula inputs
    coqDynamicTruthNativeAlignedDecisionBodyTemplate =
    rawDynamicTruthLocalDecisionCode M
      (rawDynamicTruthNativeLocalAligned_currentSigmaDomain M tail
        predecessorLevel baseContext currentLocal
        nextInputGlobalSigma nextInputGlobalPi aligned)
      (rawDynamicTruthNativeLocalAligned_currentPiDomain M tail
        predecessorLevel baseContext currentLocal
        nextInputGlobalSigma nextInputGlobalPi aligned)
      (rawDynamicTruthNativeLocalAligned_currentSigmaEvidence M tail
        predecessorLevel baseContext currentLocal
        nextInputGlobalSigma nextInputGlobalPi aligned)
      (rawDynamicTruthNativeLocalAligned_currentPiEvidence M tail
        predecessorLevel baseContext currentLocal
        nextInputGlobalSigma nextInputGlobalPi aligned)).
  exact (raw_dynamicTruthNativeAlignedDecisionBody_identified
    M hPA tail predecessorLevel baseContext currentLocal
    nextInputGlobalSigma nextInputGlobalPi aligned inputLevelNumeral
    inputs hinputNumeral hstructural).
Qed.

(** ------------------------------------------------------------------
    Exact Imp-I opening. *)

Definition coqDynamicTruthNativeAlignedImpIntroductionFormulaTerm
    : TemplateTerm := ttVar 6.
Definition coqDynamicTruthNativeAlignedImpIntroductionAssignmentCodeTerm
    : TemplateTerm := ttVar 9.
Definition coqDynamicTruthNativeAlignedImpIntroductionAssignmentStepTerm
    : TemplateTerm := ttVar 8.

Definition coqDynamicTruthNativeAlignedImpIntroductionOpenedAtomicTemplate
    : TemplateFormula :=
  templateAll3Open coqDynamicTruthNativeAlignedDecisionAtomicTemplate
    coqDynamicTruthNativeAlignedImpIntroductionFormulaTerm
    coqDynamicTruthNativeAlignedImpIntroductionAssignmentCodeTerm
    coqDynamicTruthNativeAlignedImpIntroductionAssignmentStepTerm.

Definition
    coqDynamicTruthNativeAlignedImpIntroductionOpenedAssignmentTemplate
    : TemplateFormula :=
  templateAll3Open coqDynamicTruthNativeAlignedDecisionAssignmentTemplate
    coqDynamicTruthNativeAlignedImpIntroductionFormulaTerm
    coqDynamicTruthNativeAlignedImpIntroductionAssignmentCodeTerm
    coqDynamicTruthNativeAlignedImpIntroductionAssignmentStepTerm.

Definition coqDynamicTruthNativeAlignedImpIntroductionOpenedDomainTemplate
    : TemplateFormula :=
  templateAll3Open coqDynamicTruthNativeAlignedDecisionDomainTemplate
    coqDynamicTruthNativeAlignedImpIntroductionFormulaTerm
    coqDynamicTruthNativeAlignedImpIntroductionAssignmentCodeTerm
    coqDynamicTruthNativeAlignedImpIntroductionAssignmentStepTerm.

Definition
    coqDynamicTruthNativeAlignedImpIntroductionOpenedAdmissibleTemplate
    : TemplateFormula :=
  templateAll3Open coqDynamicTruthNativeAlignedDecisionAdmissibleTemplate
    coqDynamicTruthNativeAlignedImpIntroductionFormulaTerm
    coqDynamicTruthNativeAlignedImpIntroductionAssignmentCodeTerm
    coqDynamicTruthNativeAlignedImpIntroductionAssignmentStepTerm.

Lemma
    coqDynamicTruthNativeAlignedImpIntroductionOpenedAssignmentTemplate_view :
  coqDynamicTruthNativeAlignedImpIntroductionOpenedAssignmentTemplate =
  coqAssignmentUniversalDefinednessInstanceTemplate
    (ttVar 9) (ttVar 8) (ttVar 6).
Proof. vm_compute. reflexivity. Qed.

Lemma
    coqDynamicTruthNativeAlignedImpIntroductionOpenedAdmissibleTemplate_shape :
  coqDynamicTruthNativeAlignedImpIntroductionOpenedAdmissibleTemplate =
  tfAnd coqDynamicTruthNativeAlignedImpIntroductionOpenedAtomicTemplate
    (tfAnd
      coqDynamicTruthNativeAlignedImpIntroductionOpenedAssignmentTemplate
      coqDynamicTruthNativeAlignedImpIntroductionOpenedDomainTemplate).
Proof. vm_compute. reflexivity. Qed.

Lemma coqDynamicTruthNativeAlignedImpIntroductionDecisionOpening_shape :
  templateAll3Open coqDynamicTruthNativeAlignedDecisionBodyTemplate
      (ttVar 6) (ttVar 9) (ttVar 8) =
  tfImp
    coqDynamicTruthNativeAlignedImpIntroductionOpenedAdmissibleTemplate
    (tfOr
      (coqDynamicTruthNativeAlignedSigmaEvidenceAtRootTerms
        (ttVar 6) (ttVar 9) (ttVar 8))
      (coqDynamicTruthNativeAlignedPiEvidenceAtRootTerms
        (ttVar 6) (ttVar 9) (ttVar 8))).
Proof. vm_compute. reflexivity. Qed.

(** Cross-translation sanity check.  The native-local selector package and
    the aligned soundness package may be unrelated, but once their canonical
    evidence codes agree, represented application functionality identifies
    their Imp-I instances.  This is useful when a caller retains the local
    identification returned by the native trace. *)
Lemma raw_dynamicTruthNativeAligned_impIntroduction_evidence_cross_identified :
    forall (M : RawPAModel), RawPASatisfies M -> forall
    (localInputs alignedInputs : RawCodedTemplateDirectStructuralInputs M),
  rawDirectTemplateFormula localInputs
      coqDynamicTruthLocalSigmaEvidenceTemplate =
    rawDirectTemplateFormula alignedInputs
      coqDynamicTruthNativeAlignedSigmaEvidenceConclusionTemplate ->
  rawDirectTemplateFormula localInputs
      coqDynamicTruthLocalPiEvidenceTemplate =
    rawDirectTemplateFormula alignedInputs
      coqDynamicTruthNativeAlignedPiEvidenceConclusionTemplate ->
  rawDirectTemplateFormula localInputs
      (coqRestrictedPATemplateTernaryApplication
        coqDynamicTruthLocalSigmaEvidenceTemplate
        (ttVar 8) (ttVar 9) (ttVar 6)) =
    rawDirectTemplateFormula alignedInputs
      (coqRestrictedPATemplateTernaryApplication
        coqDynamicTruthNativeAlignedSigmaEvidenceConclusionTemplate
        (ttVar 8) (ttVar 9) (ttVar 6)) /\
  rawDirectTemplateFormula localInputs
      (coqRestrictedPATemplateTernaryApplication
        coqDynamicTruthLocalPiEvidenceTemplate
        (ttVar 8) (ttVar 9) (ttVar 6)) =
    rawDirectTemplateFormula alignedInputs
      (coqRestrictedPATemplateTernaryApplication
        coqDynamicTruthNativeAlignedPiEvidenceConclusionTemplate
        (ttVar 8) (ttVar 9) (ttVar 6)).
Proof.
  intros M hPA localInputs alignedInputs hsigma hpi.
  split.
  - exact (raw_directTemplateTernaryApplication_congr_across_at_variables
      M hPA localInputs alignedInputs
      coqDynamicTruthLocalSigmaEvidenceTemplate
      coqDynamicTruthNativeAlignedSigmaEvidenceConclusionTemplate
      hsigma 8 9 6).
  - exact (raw_directTemplateTernaryApplication_congr_across_at_variables
      M hPA localInputs alignedInputs
      coqDynamicTruthLocalPiEvidenceTemplate
      coqDynamicTruthNativeAlignedPiEvidenceConclusionTemplate
      hpi 8 9 6).
Qed.

(** Honest Imp-I boundary.  The represented atomic and domain roots are
    explicit because their construction is constructor-specific.  This
    theorem compiles assignment coverage, transports those two roots to the
    resulting standard extension, builds the opened admissibility
    conjunction, transports the aligned projected decision source, and
    performs the arbitrary-root All-E/Imp-E chain. *)
Theorem
    raw_dynamicTruthNativeAligned_impIntroduction_readyEvidenceDecision_of_atomic_and_domain_roots :
    forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (tail : nat -> M) predecessorLevel baseContext currentLocal
    nextInputGlobalSigma nextInputGlobalPi
    (aligned : RawDynamicTruthNativeLocalAlignedPredecessorAt M tail
      predecessorLevel baseContext currentLocal
      nextInputGlobalSigma nextInputGlobalPi)
    inputLevelNumeral
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    baseWitnessList atomicRoot domainRoot,
  RawNumeralTermCodeAt M (raw_succ M predecessorLevel)
    inputLevelNumeral ->
  RawDynamicTruthNativeAlignedStrongStepStructuralInputsAt
      M hPA tail predecessorLevel baseContext currentLocal
      nextInputGlobalSigma nextInputGlobalPi aligned
      inputLevelNumeral inputs ->
  RawCodedPAAxiomWitnessContext M baseWitnessList baseContext ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail
      (rawDirectStructuralTemplateTranslation M hPA inputs)
      baseContext
      (coqRestrictedPADirectStrongStepImpIntroductionReadyContext []))
    (rawDirectTemplateFormula inputs
      coqDynamicTruthNativeAlignedImpIntroductionOpenedAtomicTemplate)
    atomicRoot ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail
      (rawDirectStructuralTemplateTranslation M hPA inputs)
      baseContext
      (coqRestrictedPADirectStrongStepImpIntroductionReadyContext []))
    (rawDirectTemplateFormula inputs
      coqDynamicTruthNativeAlignedImpIntroductionOpenedDomainTemplate)
    domainRoot ->
  exists (witnesses : StandardPAAxiomWitnessPrefix) decisionRoot,
    RawCodedPAAxiomWitnessContext M
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        witnesses baseWitnessList)
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses baseContext) /\
    RawContextListIncluded M baseContext
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses baseContext) /\
    RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        (rawStandardPAAxiomWitnessPrefixContextCode M
          witnesses baseContext)
        (coqRestrictedPADirectStrongStepImpIntroductionReadyContext []))
      (rawFormulaOrCode M
        (rawDirectTemplateFormula inputs
          (coqDynamicTruthNativeAlignedSigmaEvidenceAtRootTerms
            (ttVar 6) (ttVar 9) (ttVar 8)))
        (rawDirectTemplateFormula inputs
          (coqDynamicTruthNativeAlignedPiEvidenceAtRootTerms
            (ttVar 6) (ttVar 9) (ttVar 8))))
      decisionRoot.
Proof.
  intros M hPA tail predecessorLevel baseContext currentLocal
    nextInputGlobalSigma nextInputGlobalPi aligned inputLevelNumeral
    inputs baseWitnessList atomicRoot domainRoot
    hinputNumeral hstructural hbase hatomic hdomain.
  set (translation :=
    rawDirectStructuralTemplateTranslation M hPA inputs).
  set (readyPrefix :=
    coqRestrictedPADirectStrongStepImpIntroductionReadyContext []).
  assert (hprefix : RawCodedTemplatePrefixAtomicallyAdequate
      M translation readyPrefix).
  {
    exact (raw_codedTemplatePrefix_atomically_adequate
      M hPA translation readyPrefix).
  }
  destruct
    (raw_codedPALocalProofOf_assignmentUniversalDefinedness_instance_on_witnessed_tail_under_prefix
      M hPA translation
      (rawDirectStructuralTemplatePAAgreement M hPA inputs)
      baseWitnessList baseContext readyPrefix
      (ttVar 9) (ttVar 8) (ttVar 6)
      hprefix hbase)
    as (witnesses & assignmentRoot & hextended & hassignment).
  rewrite <-
    coqDynamicTruthNativeAlignedImpIntroductionOpenedAssignmentTemplate_view
    in hassignment.
  set (extendedWitnessList :=
    rawStandardPAAxiomWitnessPrefixWitnessListCode M
      witnesses baseWitnessList).
  set (extendedContext :=
    rawStandardPAAxiomWitnessPrefixContextCode M
      witnesses baseContext).
  assert (hincluded : RawContextListIncluded M baseContext extendedContext).
  {
    unfold extendedContext.
    exact (raw_standardPAAxiomWitnessPrefixContextCode_target_included
      M hPA witnesses baseContext).
  }
  destruct
    (raw_codedPALocalProof_sameTemplatePrefix_witnessedTail_transport
      M hPA translation
      baseWitnessList baseContext extendedWitnessList extendedContext
      readyPrefix
      (rawDirectTemplateFormula inputs
        coqDynamicTruthNativeAlignedImpIntroductionOpenedAtomicTemplate)
      atomicRoot hbase hextended hincluded hatomic)
    as [transportedAtomicRoot htransportedAtomic].
  destruct
    (raw_codedPALocalProof_sameTemplatePrefix_witnessedTail_transport
      M hPA translation
      baseWitnessList baseContext extendedWitnessList extendedContext
      readyPrefix
      (rawDirectTemplateFormula inputs
        coqDynamicTruthNativeAlignedImpIntroductionOpenedDomainTemplate)
      domainRoot hbase hextended hincluded hdomain)
    as [transportedDomainRoot htransportedDomain].
  set (decisionContext :=
    rawTemplateContextCodeOnTail translation extendedContext readyPrefix).
  set (openedAtomic := rawDirectTemplateFormula inputs
    coqDynamicTruthNativeAlignedImpIntroductionOpenedAtomicTemplate).
  set (openedAssignment := rawDirectTemplateFormula inputs
    coqDynamicTruthNativeAlignedImpIntroductionOpenedAssignmentTemplate).
  set (openedDomain := rawDirectTemplateFormula inputs
    coqDynamicTruthNativeAlignedImpIntroductionOpenedDomainTemplate).
  set (assignmentDomainRoot := rawProofAndIRoot M decisionContext
    openedAssignment openedDomain assignmentRoot transportedDomainRoot).
  assert (hassignmentDomain : RawCodedPALocalProofOf M decisionContext
      (rawFormulaAndCode M openedAssignment openedDomain)
      assignmentDomainRoot).
  {
    unfold assignmentDomainRoot.
    exact (raw_codedPALocalProofOf_andI M hPA decisionContext
      openedAssignment openedDomain assignmentRoot transportedDomainRoot
      hassignment htransportedDomain).
  }
  set (admissibleRoot := rawProofAndIRoot M decisionContext
    openedAtomic (rawFormulaAndCode M openedAssignment openedDomain)
    transportedAtomicRoot assignmentDomainRoot).
  assert (hadmissibleRaw : RawCodedPALocalProofOf M decisionContext
      (rawFormulaAndCode M openedAtomic
        (rawFormulaAndCode M openedAssignment openedDomain))
      admissibleRoot).
  {
    unfold admissibleRoot.
    exact (raw_codedPALocalProofOf_andI M hPA decisionContext
      openedAtomic (rawFormulaAndCode M openedAssignment openedDomain)
      transportedAtomicRoot assignmentDomainRoot
      htransportedAtomic hassignmentDomain).
  }
  assert (hadmissible : RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail
        translation extendedContext readyPrefix)
      (rawDirectTemplateFormula inputs
        coqDynamicTruthNativeAlignedImpIntroductionOpenedAdmissibleTemplate)
      admissibleRoot).
  {
    rewrite
      coqDynamicTruthNativeAlignedImpIntroductionOpenedAdmissibleTemplate_shape.
    change (RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail
        translation extendedContext readyPrefix)
      (rawFormulaAndCode M
        (rawDirectTemplateFormula inputs
          coqDynamicTruthNativeAlignedImpIntroductionOpenedAtomicTemplate)
        (rawFormulaAndCode M
          (rawDirectTemplateFormula inputs
            coqDynamicTruthNativeAlignedImpIntroductionOpenedAssignmentTemplate)
          (rawDirectTemplateFormula inputs
            coqDynamicTruthNativeAlignedImpIntroductionOpenedDomainTemplate)))
      admissibleRoot).
    unfold openedAtomic, openedAssignment, openedDomain,
      decisionContext in *.
    exact hadmissibleRaw.
  }
  pose proof hstructural as hstructuralForSource.
  pose proof (raw_template_all3_elimination_chain M translation
    coqDynamicTruthNativeAlignedDecisionBodyTemplate
    (ttVar 6) (ttVar 9) (ttVar 8)) as hchain.
  change (RawCodedUniversalEliminationChain M
    (rawDirectTemplateFormula inputs
      (tfAll (tfAll (tfAll
        coqDynamicTruthNativeAlignedDecisionBodyTemplate))))
    (rawDirectTemplateFormula inputs
      (templateAll3Open coqDynamicTruthNativeAlignedDecisionBodyTemplate
        (ttVar 6) (ttVar 9) (ttVar 8)))) in hchain.
  rewrite
    (raw_dynamicTruthNativeAlignedDecisionSource_identified
      M hPA tail predecessorLevel baseContext currentLocal
      nextInputGlobalSigma nextInputGlobalPi aligned inputLevelNumeral
      inputs hinputNumeral hstructuralForSource) in hchain.
  rewrite
    coqDynamicTruthNativeAlignedImpIntroductionDecisionOpening_shape,
    rawTemplateFormula_imp, rawTemplateFormula_or in hchain.
  pose proof
    (rawDynamicTruthNativeLocalAligned_decisionProjection M tail
      predecessorLevel baseContext currentLocal
      nextInputGlobalSigma nextInputGlobalPi aligned) as hdecisionSource.
  lazymatch type of hdecisionSource with
  | RawCodedPALocalProofOf _ _ _ ?decisionSourceRoot =>
    destruct
    (raw_codedPALocalProofOf_openedEvidenceDecision_on_standard_witness_extension_under_prefix
      M hPA translation baseWitnessList baseContext readyPrefix witnesses
      (rawDynamicTruthLocalFormulaAll3Code M
        (rawDynamicTruthLocalDecisionCode M
          (rawDynamicTruthNativeLocalAligned_currentSigmaDomain M tail
            predecessorLevel baseContext currentLocal
            nextInputGlobalSigma nextInputGlobalPi aligned)
          (rawDynamicTruthNativeLocalAligned_currentPiDomain M tail
            predecessorLevel baseContext currentLocal
            nextInputGlobalSigma nextInputGlobalPi aligned)
          (rawDynamicTruthNativeLocalAligned_currentSigmaEvidence M tail
            predecessorLevel baseContext currentLocal
            nextInputGlobalSigma nextInputGlobalPi aligned)
          (rawDynamicTruthNativeLocalAligned_currentPiEvidence M tail
            predecessorLevel baseContext currentLocal
            nextInputGlobalSigma nextInputGlobalPi aligned)))
      (rawDirectTemplateFormula inputs
        coqDynamicTruthNativeAlignedImpIntroductionOpenedAdmissibleTemplate)
      (rawDirectTemplateFormula inputs
        (coqDynamicTruthNativeAlignedSigmaEvidenceAtRootTerms
          (ttVar 6) (ttVar 9) (ttVar 8)))
      (rawDirectTemplateFormula inputs
        (coqDynamicTruthNativeAlignedPiEvidenceAtRootTerms
          (ttVar 6) (ttVar 9) (ttVar 8)))
      decisionSourceRoot
      admissibleRoot hprefix hbase hextended hchain
      hdecisionSource hadmissible)
    as [decisionRoot [_hincludedAgain hdecision]];
    exists witnesses, decisionRoot;
    split; [exact hextended |];
    split; [exact hincluded | exact hdecision]
  end.
Qed.

End
  PABoundedRawCodedDynamicTruthNativeAlignedArbitraryRootReadyDecision.
