(**
  Link native axiom soundness to native direct context truth.

  The fifth positive successor field is not an arbitrary implication.  Its
  consequent is the application of the successor global Sigma predicate to
  the universally bound axiom.  Independently, the native direct-input
  package constructs context truth by applying a context predicate built
  from that same successor Sigma selector.  This module keeps those two
  dependent choices together.

  The represented library does not yet contain the remaining induction over
  the synchronized PA-axiom-witness and context traversals.  We therefore
  isolate that proof-producing step only after proving all representation
  equalities: the residual root is indexed by the adequate paired-global
  orbit, its literal successor edge, both domain substitutions, the exact
  Sigma application stored in the axiom field, and the exact context leaf of
  the direct structural inputs.  It cannot be used for an unrelated opaque
  truth predicate.
*)

From Stdlib Require Import List.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  CodedSyntax
  RawCodedSyntaxConstructors
  RawCodedFormulaOperations
  RawCodedNumeralTermCode
  RawCodedProofAtomicAdequacy
  RawCodedRestrictedPAConsistencyFormulaCode
  RawCodedRestrictedTargetTemplateContext
  RawCodedRestrictedPAProof
  RawCodedProofImpIConstructor
  RawCodedPALocalProofExistential
  RawCodedTemplateSyntax
  RawCodedTemplateDirectStructuralTranslation
  RawCodedTemplateNumeralParameters
  RawCodedTemplateTernaryApplication
  RawCodedTernaryPredicateDeepClosure
  RawCodedDynamicContextTruthSelector
  RawCodedDynamicTruthPairedGlobalSuccessorGraph
  RawCodedDynamicTruthPairedGlobalFormulaCodeOrbitGraph
  RawCodedDynamicTruthPairedGlobalOrbitFunctionality
  RawCodedDynamicTruthNativeAxiomSoundnessPositiveGraph
  RawCodedDynamicTruthNativeAxiomSoundnessProofCompilation
  RawCodedRestrictedPAConsistencyFromUniversalSoundness
  RawCodedRestrictedPAConsistencyFromUniversalSoundnessDirect
  RawCodedRestrictedPADerivationSoundnessTemplateDirectInputs
  RawCodedRestrictedPADerivationSoundnessCarrierStrongPrefixDirectInductionShell
  RawCodedRestrictedPADerivationSoundnessNativeDirectClosureRemainder
  RawCodedDynamicTruthNativeFinalStagedRootCompilation
  RawCodedDynamicTruthNativeFinalGrowingUniversalSoundnessBridgeDirect.

Import ListNotations.

Module
  PABoundedRawCodedRestrictedPAAxiomContextTruthNativeDirectCoherenceLink.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedCodedSyntax.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedNumeralTermCode.
Import PABoundedRawCodedProofAtomicAdequacy.
Import PABoundedRawCodedRestrictedPAConsistencyFormulaCode.
Import PABoundedRawCodedRestrictedTargetTemplateContext.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedProofImpIConstructor.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateDirectStructuralTranslation.
Import PABoundedRawCodedTemplateNumeralParameters.
Import PABoundedRawCodedTemplateTernaryApplication.
Import PABoundedRawCodedTernaryPredicateDeepClosure.
Import PABoundedRawCodedDynamicContextTruthSelector.
Import PABoundedRawCodedDynamicTruthPairedGlobalSuccessorGraph.
Import PABoundedRawCodedDynamicTruthPairedGlobalFormulaCodeOrbitGraph.
Import PABoundedRawCodedDynamicTruthPairedGlobalOrbitFunctionality.
Import PABoundedRawCodedDynamicTruthNativeAxiomSoundnessPositiveGraph.
Import PABoundedRawCodedDynamicTruthNativeAxiomSoundnessProofCompilation.
Import PABoundedRawCodedRestrictedPAConsistencyFromUniversalSoundness.
Import
  PABoundedRawCodedRestrictedPAConsistencyFromUniversalSoundnessDirect.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessTemplateDirectInputs.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessCarrierStrongPrefixDirectInductionShell.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessNativeDirectClosureRemainder.
Import PABoundedRawCodedDynamicTruthNativeFinalStagedRootCompilation.
Import
  PABoundedRawCodedDynamicTruthNativeFinalGrowingUniversalSoundnessBridgeDirect.

(** ------------------------------------------------------------------
    Exact native context-selector link. *)

Definition RawCoqRestrictedPANativeContextTruthSelectorLinkAt
    (M : RawPAModel)
    (parameters : RawCodedTemplateNumeralParameters M)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    (nextGlobalSigma : M)
    (sigmaApplicationSelector :
      RawCodedTernaryApplicationSelector M nextGlobalSigma)
    (contextApplicationSelector :
      RawCodedTernaryApplicationSelector M
        (rawDynamicContextAllSigmaCode sigmaApplicationSelector)) : Prop :=
  forall first second third fourth fifth,
    rawDirectTemplateFormula inputs
      (tfOpaque coqRestrictedPAContextTruthPredicateName
        [first; second; third; fourth; fifth]) =
    rawTernaryApplicationOutput contextApplicationSelector
      (rawCoqRestrictedPADerivationSoundnessTemplateTermView
        M parameters fifth)
      (rawCoqRestrictedPADerivationSoundnessTemplateTermView
        M parameters fourth)
      (rawCoqRestrictedPADerivationSoundnessTemplateTermView
        M parameters third).

Arguments RawCoqRestrictedPANativeContextTruthSelectorLinkAt
  M parameters inputs nextGlobalSigma sigmaApplicationSelector
    contextApplicationSelector : clear implicits.

(** The complete graph/direct synchronization needed by the context proof.
    In particular, [nextSigmaEvidence] occurs both in the transparent fifth
    field and as the output of [sigmaApplicationSelector]. *)
Definition RawCoqRestrictedPANativeAxiomContextTruthLinkAt
    (M : RawPAModel)
    (parameters : RawCodedTemplateNumeralParameters M)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    (tail : nat -> M)
    (predecessorLevel currentGlobalSigma currentGlobalPi
      sigmaDomain piDomain nextSigmaEvidence nextAxiomSoundness
      nextGlobalSigma nextGlobalPi : M)
    (sigmaApplicationSelector :
      RawCodedTernaryApplicationSelector M nextGlobalSigma)
    (contextApplicationSelector :
      RawCodedTernaryApplicationSelector M
        (rawDynamicContextAllSigmaCode sigmaApplicationSelector)) : Prop :=
  RawDynamicTruthPairedGlobalFormulaCodeAdequateOrbitAt M
      tail (raw_succ M predecessorLevel)
      currentGlobalSigma currentGlobalPi /\
  exists currentLevel currentLevelNumeral : M,
    currentLevel = raw_succ M predecessorLevel /\
    RawDynamicTruthPairedGlobalSuccessorAt M
      currentGlobalSigma currentGlobalPi currentLevel
      nextGlobalSigma nextGlobalPi /\
    RawNumeralTermCodeAt M currentLevel currentLevelNumeral /\
    RawCodedFormulaSingleSubstitution M currentLevelNumeral
      (rawNumeralValue M
        (formulaCode dynamicTruthNativeAxiomSigmaDomainTemplate))
      sigmaDomain /\
    RawCodedFormulaSingleSubstitution M currentLevelNumeral
      (rawNumeralValue M
        (formulaCode dynamicTruthNativeAxiomPiDomainTemplate))
      piDomain /\
    RawDynamicTruthNativeAxiomApplication M
      nextGlobalSigma nextSigmaEvidence /\
    rawTernaryApplicationOutput sigmaApplicationSelector
      (rawQuotedTermCode M (tVar 0))
      (rawQuotedTermCode M tZero)
      (rawQuotedTermCode M tZero) = nextSigmaEvidence /\
    nextAxiomSoundness =
      rawDynamicTruthNativeAxiomSoundnessFieldCode M
        sigmaDomain piDomain nextSigmaEvidence /\
    RawCodedTernaryPredicateDeepClosed M nextGlobalSigma /\
    RawCodedTernaryPredicateDeepClosed M
      (rawDynamicContextAllSigmaCode sigmaApplicationSelector) /\
    RawCoqRestrictedPANativeContextTruthSelectorLinkAt
      M parameters inputs nextGlobalSigma sigmaApplicationSelector
      contextApplicationSelector.

Arguments RawCoqRestrictedPANativeAxiomContextTruthLinkAt
  M parameters inputs tail predecessorLevel currentGlobalSigma
    currentGlobalPi sigmaDomain piDomain nextSigmaEvidence
    nextAxiomSoundness nextGlobalSigma nextGlobalPi
    sigmaApplicationSelector contextApplicationSelector : clear implicits.

(** The native closure package exposes the selector equation for its exact
    existentially chosen [inputs].  Combining it with the trace aligns the
    package successor with the successor hidden in the field by functional
    uniqueness; no extensional predicate equality is assumed. *)
Theorem
    raw_coqRestrictedPANativeAxiomContextTruthLink_exists_of_trace_and_inputs :
  forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (parameters : RawCodedTemplateNumeralParameters M)
    (tail : nat -> M) predecessorLevel
    currentGlobalSigma currentGlobalPi sigmaDomain piDomain
    nextSigmaEvidence nextAxiomSoundness,
  RawDynamicTruthNativeAxiomSoundnessProofTraceAt M tail
    predecessorLevel currentGlobalSigma currentGlobalPi
    sigmaDomain piDomain nextSigmaEvidence ->
  nextAxiomSoundness =
    rawDynamicTruthNativeAxiomSoundnessFieldCode M
      sigmaDomain piDomain nextSigmaEvidence ->
  RawCoqRestrictedPANativeDirectTruthInputsWithClosureAt
    M hPA parameters currentGlobalSigma currentGlobalPi
    predecessorLevel nextSigmaEvidence ->
  exists nextGlobalSigma nextGlobalPi : M,
  exists sigmaApplicationSelector :
    RawCodedTernaryApplicationSelector M nextGlobalSigma,
  exists contextApplicationSelector :
    RawCodedTernaryApplicationSelector M
      (rawDynamicContextAllSigmaCode sigmaApplicationSelector),
  exists inputs : RawCodedTemplateDirectStructuralInputs M,
    RawCoqRestrictedPANativeAxiomContextTruthLinkAt
      M parameters inputs tail predecessorLevel
      currentGlobalSigma currentGlobalPi sigmaDomain piDomain
      nextSigmaEvidence nextAxiomSoundness
      nextGlobalSigma nextGlobalPi sigmaApplicationSelector
      contextApplicationSelector.
Proof.
  intros M hPA parameters tail predecessorLevel
    currentGlobalSigma currentGlobalPi sigmaDomain piDomain
    nextSigmaEvidence nextAxiomSoundness htrace hfield hnative.
  destruct htrace as
    [horbit (currentLevel & traceNextGlobalSigma & traceNextGlobalPi &
      currentLevelNumeral & hlevel & htraceSuccessor & hnumeral &
      hsigmaDomain & hpiDomain & htraceApplication)].
  unfold RawCoqRestrictedPANativeDirectTruthInputsWithClosureAt in hnative.
  destruct hnative as
    (nextGlobalSigma & nextGlobalPi & sigmaApplicationSelector &
     contextApplicationSelector & contextTruth & conclusionTruth & inputs &
     closureCount & axiom & hsuccessor & hsigmaDeep & hcontextDeep &
     hinputs & hcontextOutput & hconclusionOutput & hcontextLeaf &
     hconclusionLeaf & hselectorNative & hconclusionNative & happlication &
     hremainder).
  destruct (raw_dynamicTruthPairedGlobalSuccessorAt_functional M hPA
    currentGlobalSigma currentGlobalPi currentLevel
    traceNextGlobalSigma traceNextGlobalPi nextGlobalSigma nextGlobalPi
    htraceSuccessor) as hfunctional.
  rewrite hlevel in hfunctional.
  specialize (hfunctional hsuccessor).
  destruct hfunctional as [hsigma hpi].
  subst nextGlobalSigma. subst nextGlobalPi.
  exists traceNextGlobalSigma, traceNextGlobalPi,
    sigmaApplicationSelector, contextApplicationSelector, inputs.
  split; [exact horbit |].
  exists currentLevel, currentLevelNumeral.
  repeat split; try assumption.
Qed.

(** The final staged trace is already strong enough to construct such a
    linked package existentially.  The other four positive fields are used
    only to exactify the shared paired-global orbit: functionality identifies
    the axiom field's orbit with the adequate orbit selected by the local
    field.  The direct inputs are then built from that exact axiom trace. *)
Theorem
    raw_dynamicTruthNativeFinalStagedGraphTrace_axiom_context_native_link_exists
    : forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
      (tail : nat -> M) level
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
      nextFinal successorNumeralCode,
  RawDynamicTruthNativeFinalStagedGraphTraceAt M tail level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal
    nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
    nextFinal successorNumeralCode ->
  exists parameters : RawCodedTemplateNumeralParameters M,
  exists currentGlobalSigma currentGlobalPi sigmaDomain piDomain
    nextSigmaEvidence nextGlobalSigma nextGlobalPi : M,
  exists sigmaApplicationSelector :
    RawCodedTernaryApplicationSelector M nextGlobalSigma,
  exists contextApplicationSelector :
    RawCodedTernaryApplicationSelector M
      (rawDynamicContextAllSigmaCode sigmaApplicationSelector),
  exists inputs : RawCodedTemplateDirectStructuralInputs M,
    rawNumeralTemplateParameterBound parameters
      coqRestrictedPASoundnessLowerLevelParameterName =
      raw_succ M level /\
    rawNumeralTemplateParameterBound parameters
      coqRestrictedPASoundnessUpperLevelParameterName =
      raw_succ M (raw_succ M level) /\
    RawCoqRestrictedPANativeAxiomContextTruthLinkAt
      M parameters inputs tail level
      currentGlobalSigma currentGlobalPi sigmaDomain piDomain
      nextSigmaEvidence nextAxiomSoundness
      nextGlobalSigma nextGlobalPi sigmaApplicationSelector
      contextApplicationSelector.
Proof.
  intros M hPA tail level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal
    nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
    nextFinal successorNumeralCode hstaged.
  pose proof hstaged as hstagedCopy.
  destruct hstagedCopy as
    [hcurrent hnextLocal hnextCrossLevel hnextShift hnextSubstitution
      hnextAxiomSoundness hnextFinal hsource].
  pose proof
    (raw_dynamicTruthNativeFivePositiveGraphs_orbit_coherent M hPA
      tail level nextLocal nextCrossLevel nextShift nextSubstitution
      nextAxiomSoundness hnextLocal hnextCrossLevel hnextShift
      hnextSubstitution hnextAxiomSoundness) as hcoherent.
  destruct hcoherent as
    (currentGlobalSigma & currentGlobalPi & horbit & hlocalTransform &
      hcrossTransform & hshiftTransform & hsubstitutionTransform &
      haxiomTransform).
  destruct
    (raw_dynamicTruthNativeAxiomSoundnessProofTraceAt_of_transform
      M tail level currentGlobalSigma currentGlobalPi nextAxiomSoundness
      horbit haxiomTransform) as
    (sigmaDomain & piDomain & nextSigmaEvidence & hfield & htrace).
  destruct
    (raw_coqRestrictedPANativeCoherentDirectTruthInputsWithClosureAt_of_trace
      M hPA tail level currentGlobalSigma currentGlobalPi
      sigmaDomain piDomain nextSigmaEvidence htrace) as
    (parameters & hlower & hupper & hnative).
  destruct
    (raw_coqRestrictedPANativeAxiomContextTruthLink_exists_of_trace_and_inputs
      M hPA parameters tail level currentGlobalSigma currentGlobalPi
      sigmaDomain piDomain nextSigmaEvidence nextAxiomSoundness
      htrace hfield hnative) as
    (nextGlobalSigma & nextGlobalPi & sigmaApplicationSelector &
      contextApplicationSelector & inputs & hlink).
  exists parameters, currentGlobalSigma, currentGlobalPi,
    sigmaDomain, piDomain, nextSigmaEvidence,
    nextGlobalSigma, nextGlobalPi,
    sigmaApplicationSelector, contextApplicationSelector, inputs.
  repeat split; assumption.
Qed.

(** ------------------------------------------------------------------
    Exact direct code after replacing only the opaque context leaf. *)

Definition rawCoqRestrictedPASelectedAxiomContextsTruthDirectCode
    (M : RawPAModel)
    (parameters : RawCodedTemplateNumeralParameters M)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    (nextGlobalSigma : M)
    (sigmaApplicationSelector :
      RawCodedTernaryApplicationSelector M nextGlobalSigma)
    (contextApplicationSelector :
      RawCodedTernaryApplicationSelector M
        (rawDynamicContextAllSigmaCode sigmaApplicationSelector)) : M :=
  rawFormulaAllCode M (rawFormulaAllCode M
    (rawFormulaImpCode M
      (rawDirectTemplateFormula inputs
        (embedPAFormula
          (codedPAAxiomWitnessContextTermAt (tVar 1) (tVar 0))))
      (rawFormulaImpCode M
        (rawDirectTemplateFormula inputs
          (restrictedTargetTemplateFormulaContext
            coqRestrictedPASoundnessLowerLevelTerm
            (restrictedTargetContextAllBoundedContext (tVar 0))))
        (rawFormulaImpCode M
          (rawDirectTemplateFormula inputs
            (embedPAFormula
              (contextAllAtomicallyAdequateTermAt (tVar 0))))
          (rawTernaryApplicationOutput contextApplicationSelector
            (rawCoqRestrictedPADerivationSoundnessTemplateTermView
              M parameters ttZero)
            (rawCoqRestrictedPADerivationSoundnessTemplateTermView
              M parameters ttZero)
            (rawCoqRestrictedPADerivationSoundnessTemplateTermView
              M parameters (ttVar 0))))))).

Arguments rawCoqRestrictedPASelectedAxiomContextsTruthDirectCode
  M parameters inputs nextGlobalSigma sigmaApplicationSelector
    contextApplicationSelector : clear implicits.

Theorem raw_coqRestrictedPAAxiomContextsTruthDirectCode_native_view :
  forall (M : RawPAModel)
    (parameters : RawCodedTemplateNumeralParameters M)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    nextGlobalSigma
    (sigmaApplicationSelector :
      RawCodedTernaryApplicationSelector M nextGlobalSigma)
    (contextApplicationSelector :
      RawCodedTernaryApplicationSelector M
        (rawDynamicContextAllSigmaCode sigmaApplicationSelector)),
  RawCoqRestrictedPANativeContextTruthSelectorLinkAt
    M parameters inputs nextGlobalSigma sigmaApplicationSelector
    contextApplicationSelector ->
  rawCoqRestrictedPAAxiomContextsTruthDirectCode M inputs =
  rawCoqRestrictedPASelectedAxiomContextsTruthDirectCode
    M parameters inputs nextGlobalSigma sigmaApplicationSelector
    contextApplicationSelector.
Proof.
  intros M parameters inputs nextGlobalSigma sigmaApplicationSelector
    contextApplicationSelector hcontextLeaf.
  unfold rawCoqRestrictedPAAxiomContextsTruthDirectCode,
    coqRestrictedPAAxiomContextsTruthTemplate,
    rawCoqRestrictedPASelectedAxiomContextsTruthDirectCode.
  rewrite !rawDirectTemplateFormula_all_code.
  rewrite !rawDirectTemplateFormula_imp_code.
  rewrite hcontextLeaf.
  reflexivity.
Qed.

(** ------------------------------------------------------------------
    Smallest proof-producing context-traversal boundary. *)

(** The head assumption is the literal graph-selected axiom-soundness
    field.  What remains is precisely the internal synchronized-list
    argument: open the two displayed context binders, traverse the witness
    and axiom tables in lockstep, and apply the pointwise field to each live
    row.  No implication-introduction plumbing is included in this type. *)
Definition RawCoqRestrictedPANativeAxiomContextTruthBodyRootCompiler
    (M : RawPAModel) : Prop :=
  forall (parameters : RawCodedTemplateNumeralParameters M)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    (tail : nat -> M)
    predecessorLevel currentGlobalSigma currentGlobalPi
    sigmaDomain piDomain nextSigmaEvidence nextAxiomSoundness
    nextGlobalSigma nextGlobalPi
    (sigmaApplicationSelector :
      RawCodedTernaryApplicationSelector M nextGlobalSigma)
    (contextApplicationSelector :
      RawCodedTernaryApplicationSelector M
        (rawDynamicContextAllSigmaCode sigmaApplicationSelector))
    context,
  RawCoqRestrictedPANativeAxiomContextTruthLinkAt
    M parameters inputs tail predecessorLevel
    currentGlobalSigma currentGlobalPi sigmaDomain piDomain
    nextSigmaEvidence nextAxiomSoundness
    nextGlobalSigma nextGlobalPi sigmaApplicationSelector
    contextApplicationSelector ->
  exists child : M,
    RawCodedPALocalProofOf M
      (rawListNode M nextAxiomSoundness context)
      (rawCoqRestrictedPASelectedAxiomContextsTruthDirectCode
        M parameters inputs nextGlobalSigma sigmaApplicationSelector
        contextApplicationSelector)
      child.

Arguments RawCoqRestrictedPANativeAxiomContextTruthBodyRootCompiler
  M : clear implicits.

Definition RawCoqRestrictedPANativeAxiomContextTruthRootCompiler
    (M : RawPAModel) : Prop :=
  forall (parameters : RawCodedTemplateNumeralParameters M)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    (tail : nat -> M)
    predecessorLevel currentGlobalSigma currentGlobalPi
    sigmaDomain piDomain nextSigmaEvidence nextAxiomSoundness
    nextGlobalSigma nextGlobalPi
    (sigmaApplicationSelector :
      RawCodedTernaryApplicationSelector M nextGlobalSigma)
    (contextApplicationSelector :
      RawCodedTernaryApplicationSelector M
        (rawDynamicContextAllSigmaCode sigmaApplicationSelector))
    context,
  RawCoqRestrictedPANativeAxiomContextTruthLinkAt
    M parameters inputs tail predecessorLevel
    currentGlobalSigma currentGlobalPi sigmaDomain piDomain
    nextSigmaEvidence nextAxiomSoundness
    nextGlobalSigma nextGlobalPi sigmaApplicationSelector
    contextApplicationSelector ->
  exists root : M,
    RawCodedPALocalProofOf M context
      (rawFormulaImpCode M nextAxiomSoundness
        (rawCoqRestrictedPASelectedAxiomContextsTruthDirectCode
          M parameters inputs nextGlobalSigma sigmaApplicationSelector
          contextApplicationSelector))
      root.

Arguments RawCoqRestrictedPANativeAxiomContextTruthRootCompiler
  M : clear implicits.

(** Implication introduction is completely represented and unconditional
    once the body root exists.  Thus the preceding body compiler, rather
    than the implication-shaped compatibility law, is the sharp remaining
    proof-producing interface. *)
Theorem
    raw_coqRestrictedPANativeAxiomContextTruthRootCompiler_of_body :
  forall (M : RawPAModel), RawPASatisfies M ->
  RawCoqRestrictedPANativeAxiomContextTruthBodyRootCompiler M ->
  RawCoqRestrictedPANativeAxiomContextTruthRootCompiler M.
Proof.
  intros M hPA hbody parameters inputs tail predecessorLevel
    currentGlobalSigma currentGlobalPi sigmaDomain piDomain
    nextSigmaEvidence nextAxiomSoundness nextGlobalSigma nextGlobalPi
    sigmaApplicationSelector contextApplicationSelector context hlink.
  destruct (hbody parameters inputs tail predecessorLevel
    currentGlobalSigma currentGlobalPi sigmaDomain piDomain
    nextSigmaEvidence nextAxiomSoundness nextGlobalSigma nextGlobalPi
    sigmaApplicationSelector contextApplicationSelector context hlink)
    as [child hchild].
  exists (rawProofImpIRoot M context nextAxiomSoundness
    (rawCoqRestrictedPASelectedAxiomContextsTruthDirectCode
      M parameters inputs nextGlobalSigma sigmaApplicationSelector
      contextApplicationSelector) child).
  exact (raw_codedPALocalProofOf_impI M hPA context nextAxiomSoundness
    (rawCoqRestrictedPASelectedAxiomContextsTruthDirectCode
      M parameters inputs nextGlobalSigma sigmaApplicationSelector
      contextApplicationSelector) child hchild).
Qed.

(** At the package level there is no synchronization premise left: the
    staged graph itself chooses the exact direct inputs.  Once the sole
    represented list theorem is supplied, the graph-selected fifth field
    entails context truth for those very inputs in any requested context. *)
Theorem
    raw_dynamicTruthNativeFinalStagedGraphTrace_axiom_context_coherence_exists
    : forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
      (tail : nat -> M) level
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
      nextFinal successorNumeralCode context,
  RawDynamicTruthNativeFinalStagedGraphTraceAt M tail level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal
    nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
    nextFinal successorNumeralCode ->
  RawCoqRestrictedPANativeAxiomContextTruthRootCompiler M ->
  exists inputs : RawCodedTemplateDirectStructuralInputs M,
  exists root : M,
    RawCodedPALocalProofOf M context
      (rawFormulaImpCode M nextAxiomSoundness
        (rawCoqRestrictedPAAxiomContextsTruthDirectCode M inputs))
      root.
Proof.
  intros M hPA tail level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal
    nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
    nextFinal successorNumeralCode context htrace hrootCompiler.
  destruct
    (raw_dynamicTruthNativeFinalStagedGraphTrace_axiom_context_native_link_exists
      M hPA tail level
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
      nextFinal successorNumeralCode htrace) as
    (parameters & currentGlobalSigma & currentGlobalPi & sigmaDomain &
      piDomain & nextSigmaEvidence & nextGlobalSigma & nextGlobalPi &
      sigmaApplicationSelector & contextApplicationSelector & inputs &
      hlower & hupper & hlink).
  pose proof hlink as hlinkCopy.
  destruct hlinkCopy as
    (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & hcontextLeaf).
  destruct (hrootCompiler parameters inputs tail level
    currentGlobalSigma currentGlobalPi sigmaDomain piDomain
    nextSigmaEvidence nextAxiomSoundness nextGlobalSigma nextGlobalPi
    sigmaApplicationSelector contextApplicationSelector context hlink)
    as [root hroot].
  exists inputs, root.
  rewrite
    (raw_coqRestrictedPAAxiomContextsTruthDirectCode_native_view
      M parameters inputs nextGlobalSigma sigmaApplicationSelector
      contextApplicationSelector hcontextLeaf).
  exact hroot.
Qed.

Corollary
    raw_dynamicTruthNativeFinalStagedGraphTrace_axiom_context_coherence_exists_of_body
    : forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
      (tail : nat -> M) level
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
      nextFinal successorNumeralCode context,
  RawDynamicTruthNativeFinalStagedGraphTraceAt M tail level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal
    nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
    nextFinal successorNumeralCode ->
  RawCoqRestrictedPANativeAxiomContextTruthBodyRootCompiler M ->
  exists inputs : RawCodedTemplateDirectStructuralInputs M,
  exists root : M,
    RawCodedPALocalProofOf M context
      (rawFormulaImpCode M nextAxiomSoundness
        (rawCoqRestrictedPAAxiomContextsTruthDirectCode M inputs))
      root.
Proof.
  intros M hPA tail level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal
    nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
    nextFinal successorNumeralCode context htrace hbody.
  exact
    (raw_dynamicTruthNativeFinalStagedGraphTrace_axiom_context_coherence_exists
      M hPA tail level
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
      nextFinal successorNumeralCode context htrace
      (raw_coqRestrictedPANativeAxiomContextTruthRootCompiler_of_body
        M hPA hbody)).
Qed.

(** A final-staged integration must retain the native inputs selected for the
    same graph trace.  This is only a synchronization premise; unlike the
    next definition it creates no represented PA proof. *)
Definition RawDynamicTruthNativeFinalAxiomContextTruthNativeLinkCompiler
    (M : RawPAModel)
    (inputs : RawCodedTemplateDirectStructuralInputs M) : Prop :=
  forall (tail : nat -> M) level
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
      nextFinal successorNumeralCode witnessList baseContext,
    RawDynamicTruthNativeFinalStagedGraphTraceAt M tail level
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
      nextFinal successorNumeralCode ->
    RawDynamicTruthNativeFinalStagedPrerequisitesOn M
      witnessList baseContext
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift nextSubstitution
      nextAxiomSoundness ->
    rawDirectTemplateTerm inputs
      coqRestrictedPASoundnessLowerLevelTerm = successorNumeralCode ->
    exists parameters : RawCodedTemplateNumeralParameters M,
    exists currentGlobalSigma currentGlobalPi sigmaDomain piDomain
      nextSigmaEvidence nextGlobalSigma nextGlobalPi : M,
    exists sigmaApplicationSelector :
      RawCodedTernaryApplicationSelector M nextGlobalSigma,
    exists contextApplicationSelector :
      RawCodedTernaryApplicationSelector M
        (rawDynamicContextAllSigmaCode sigmaApplicationSelector),
      RawCoqRestrictedPANativeAxiomContextTruthLinkAt
        M parameters inputs tail level
        currentGlobalSigma currentGlobalPi sigmaDomain piDomain
        nextSigmaEvidence nextAxiomSoundness
        nextGlobalSigma nextGlobalPi sigmaApplicationSelector
        contextApplicationSelector.

Arguments RawDynamicTruthNativeFinalAxiomContextTruthNativeLinkCompiler
  M inputs : clear implicits.

(** The actual remaining proof obligation.  It is the synchronized
    witness/context-list theorem, expressed at the exact final bridge
    context and the exact selected context application. *)
Definition
    RawDynamicTruthNativeFinalSelectedAxiomContextTruthRootCompiler
    (M : RawPAModel)
    (inputs : RawCodedTemplateDirectStructuralInputs M) : Prop :=
  forall (tail : nat -> M) level
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
      nextFinal successorNumeralCode witnessList baseContext
      (parameters : RawCodedTemplateNumeralParameters M)
      currentGlobalSigma currentGlobalPi sigmaDomain piDomain
      nextSigmaEvidence nextGlobalSigma nextGlobalPi
      (sigmaApplicationSelector :
        RawCodedTernaryApplicationSelector M nextGlobalSigma)
      (contextApplicationSelector :
        RawCodedTernaryApplicationSelector M
          (rawDynamicContextAllSigmaCode sigmaApplicationSelector)),
    RawDynamicTruthNativeFinalStagedGraphTraceAt M tail level
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
      nextFinal successorNumeralCode ->
    RawDynamicTruthNativeFinalStagedPrerequisitesOn M
      witnessList baseContext
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift nextSubstitution
      nextAxiomSoundness ->
    rawDirectTemplateTerm inputs
      coqRestrictedPASoundnessLowerLevelTerm = successorNumeralCode ->
    RawCoqRestrictedPANativeAxiomContextTruthLinkAt
      M parameters inputs tail level
      currentGlobalSigma currentGlobalPi sigmaDomain piDomain
      nextSigmaEvidence nextAxiomSoundness
      nextGlobalSigma nextGlobalPi sigmaApplicationSelector
      contextApplicationSelector ->
    exists root : M,
      RawCodedPALocalProofOf M
        (rawCoqRestrictedPAConsistencyBridgeContextCode
          M successorNumeralCode baseContext)
        (rawFormulaImpCode M nextAxiomSoundness
          (rawCoqRestrictedPASelectedAxiomContextsTruthDirectCode
            M parameters inputs nextGlobalSigma sigmaApplicationSelector
            contextApplicationSelector))
        root.

Arguments
  RawDynamicTruthNativeFinalSelectedAxiomContextTruthRootCompiler
  M inputs : clear implicits.

Theorem
    raw_dynamicTruthNativeFinalSelectedAxiomContextTruthRootCompiler_of_native_body
    : forall (M : RawPAModel), RawPASatisfies M -> forall
      (inputs : RawCodedTemplateDirectStructuralInputs M),
  RawCoqRestrictedPANativeAxiomContextTruthBodyRootCompiler M ->
  RawDynamicTruthNativeFinalSelectedAxiomContextTruthRootCompiler M inputs.
Proof.
  intros M hPA inputs hbody tail level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal
    nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
    nextFinal successorNumeralCode witnessList baseContext
    parameters currentGlobalSigma currentGlobalPi sigmaDomain piDomain
    nextSigmaEvidence nextGlobalSigma nextGlobalPi
    sigmaApplicationSelector contextApplicationSelector
    htrace hprerequisites hlevel hlink.
  exact
    ((raw_coqRestrictedPANativeAxiomContextTruthRootCompiler_of_body
      M hPA hbody) parameters inputs tail level
      currentGlobalSigma currentGlobalPi sigmaDomain piDomain
      nextSigmaEvidence nextAxiomSoundness nextGlobalSigma nextGlobalPi
      sigmaApplicationSelector contextApplicationSelector
      (rawCoqRestrictedPAConsistencyBridgeContextCode
        M successorNumeralCode baseContext) hlink).
Qed.

(** Resolve representation first, invoke only the native list theorem, and
    finally transport along the proved direct-code identity. *)
Theorem
    raw_dynamicTruthNativeFinalSelectedAxiomContextTruthDirectCoherenceCompiler_of_native_link
    : forall (M : RawPAModel)
      (inputs : RawCodedTemplateDirectStructuralInputs M),
  RawDynamicTruthNativeFinalAxiomContextTruthNativeLinkCompiler M inputs ->
  RawDynamicTruthNativeFinalSelectedAxiomContextTruthRootCompiler M inputs ->
  RawDynamicTruthNativeFinalSelectedAxiomContextTruthDirectCoherenceCompiler
    M inputs.
Proof.
  intros M inputs hlinkCompiler hrootCompiler.
  unfold
    RawDynamicTruthNativeFinalSelectedAxiomContextTruthDirectCoherenceCompiler,
    RawDynamicTruthNativeFinalDirectBridgeFormulaRootCompiler.
  intros tail level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal
    nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
    nextFinal successorNumeralCode witnessList baseContext
    htrace hprerequisites hlevel.
  destruct (hlinkCompiler tail level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal
    nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
    nextFinal successorNumeralCode witnessList baseContext
    htrace hprerequisites hlevel) as
    (parameters & currentGlobalSigma & currentGlobalPi & sigmaDomain &
      piDomain & nextSigmaEvidence & nextGlobalSigma & nextGlobalPi &
      sigmaApplicationSelector & contextApplicationSelector & hlink).
  pose proof hlink as hlinkCopy.
  destruct hlinkCopy as
    (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & hcontextLeaf).
  destruct (hrootCompiler tail level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal
    nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
    nextFinal successorNumeralCode witnessList baseContext
    parameters currentGlobalSigma currentGlobalPi sigmaDomain piDomain
    nextSigmaEvidence nextGlobalSigma nextGlobalPi
    sigmaApplicationSelector contextApplicationSelector
    htrace hprerequisites hlevel hlink) as [root hroot].
  exists root.
  rewrite
    (raw_coqRestrictedPAAxiomContextsTruthDirectCode_native_view
      M parameters inputs nextGlobalSigma sigmaApplicationSelector
      contextApplicationSelector hcontextLeaf).
  exact hroot.
Qed.

Corollary
    raw_dynamicTruthNativeFinalSelectedAxiomContextTruthDirectCoherenceCompiler_of_native_body
    : forall (M : RawPAModel), RawPASatisfies M -> forall
      (inputs : RawCodedTemplateDirectStructuralInputs M),
  RawDynamicTruthNativeFinalAxiomContextTruthNativeLinkCompiler M inputs ->
  RawCoqRestrictedPANativeAxiomContextTruthBodyRootCompiler M ->
  RawDynamicTruthNativeFinalSelectedAxiomContextTruthDirectCoherenceCompiler
    M inputs.
Proof.
  intros M hPA inputs hlink hbody.
  exact
    (raw_dynamicTruthNativeFinalSelectedAxiomContextTruthDirectCoherenceCompiler_of_native_link
      M inputs hlink
      (raw_dynamicTruthNativeFinalSelectedAxiomContextTruthRootCompiler_of_native_body
        M hPA inputs hbody)).
Qed.

End
  PABoundedRawCodedRestrictedPAAxiomContextTruthNativeDirectCoherenceLink.
