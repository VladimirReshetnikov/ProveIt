(**
  Link native direct truth selection to the final bottom-refutation root.

  The native direct-truth package existentially chooses both its structural
  inputs and the ternary selector for the successor Sigma predicate.  The
  final consistency bridge, in contrast, is indexed by an already fixed
  [inputs] value.  Merely knowing that both objects exist is therefore not
  enough: the opaque conclusion leaf of that exact [inputs] value must be
  identified with the selected ternary application.

  This module records that identification explicitly.  It proves three
  things without decoding a carrier-valued predicate or promoting semantic
  truth to a PA proof:

  - the full native package exposes a conclusion-selector link for its very
    same existentially selected inputs;
  - under that link, the direct bottom-refutation template is literally the
    implication from the selected Sigma application at the quoted bottom
    term and the two quoted zero terms to object-level bottom;
  - a checked local root for that selected implication can be transported to
    the exact bottom-refutation code required by the final bridge.

  The final staged graph currently does not retain the earlier native package
  witnesses.  Consequently the last adapter takes a small synchronization
  compiler which supplies the linked selector for the fixed final [inputs].
  This is the precise graph-to-native-package seam; the other premise is the
  genuinely proof-producing selected-Sigma bottom-refutation compiler.
*)

From Stdlib Require Import List.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors
  RawCodedFormulaOperations
  RawCodedRestrictedPAProof
  RawCodedPALocalProofExistential
  RawCodedTemplateSyntax
  RawCodedTemplateStructuralPAAgreement
  RawCodedTemplateDirectStructuralTranslation
  RawCodedTemplateNumeralParameters
  RawCodedTemplateTernaryApplication
  RawCodedTernaryPredicateDeepClosure
  RawCodedDynamicTruthPairedGlobalSuccessorGraph
  RawCodedRestrictedPAConsistencyFromUniversalSoundness
  RawCodedRestrictedPAConsistencyFromUniversalSoundnessDirect
  RawCodedRestrictedPADerivationSoundnessTemplateDirectInputs
  RawCodedRestrictedPADerivationSoundnessCarrierStrongPrefixDirectInductionShell
  RawCodedRestrictedPADerivationSoundnessNativeDirectClosureRemainder
  RawCodedDynamicTruthNativeFinalStagedRootCompilation
  RawCodedDynamicTruthNativeFinalGrowingUniversalSoundnessBridgeDirect.

Import ListNotations.

Module PABoundedRawCodedRestrictedPABottomTruthNativeDirectRefutationLink.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateStructuralPAAgreement.
Import PABoundedRawCodedTemplateDirectStructuralTranslation.
Import PABoundedRawCodedTemplateNumeralParameters.
Import PABoundedRawCodedTemplateTernaryApplication.
Import PABoundedRawCodedTernaryPredicateDeepClosure.
Import PABoundedRawCodedDynamicTruthPairedGlobalSuccessorGraph.
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
    Exact selector linkage and code view. *)

(** This is the one projection of the native package needed by the bottom
    endpoint.  Notice that it mentions the literal direct [inputs], rather
    than merely an extensionally similar truth predicate. *)
Definition RawCoqRestrictedPANativeConclusionTruthSelectorLinkAt
    (M : RawPAModel)
    (parameters : RawCodedTemplateNumeralParameters M)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    (nextGlobalSigma : M)
    (sigmaApplicationSelector :
      RawCodedTernaryApplicationSelector M nextGlobalSigma) : Prop :=
  forall first second third fourth fifth,
    rawDirectTemplateFormula inputs
      (tfOpaque coqRestrictedPAConclusionTruthPredicateName
        [first; second; third; fourth; fifth]) =
    rawTernaryApplicationOutput sigmaApplicationSelector
      (rawCoqRestrictedPADerivationSoundnessTemplateTermView
        M parameters third)
      (rawCoqRestrictedPADerivationSoundnessTemplateTermView
        M parameters fourth)
      (rawCoqRestrictedPADerivationSoundnessTemplateTermView
        M parameters fifth).

Arguments RawCoqRestrictedPANativeConclusionTruthSelectorLinkAt
  M parameters inputs nextGlobalSigma sigmaApplicationSelector
  : clear implicits.

(** The stronger package-facing link also retains the native successor row
    from which [nextGlobalSigma] was selected.  Deep closure alone says
    nothing about the extension of an arbitrary ternary predicate, so it
    would be insufficient—and in fact false in general—to demand a bottom
    refutation from that premise alone. *)
Definition RawCoqRestrictedPANativeSuccessorConclusionTruthSelectorLinkAt
    (M : RawPAModel)
    (parameters : RawCodedTemplateNumeralParameters M)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    (currentGlobalSigma currentGlobalPi predecessorLevel
      nextGlobalSigma nextGlobalPi : M)
    (sigmaApplicationSelector :
      RawCodedTernaryApplicationSelector M nextGlobalSigma) : Prop :=
  RawDynamicTruthPairedGlobalSuccessorAt M
    currentGlobalSigma currentGlobalPi
    (raw_succ M predecessorLevel) nextGlobalSigma nextGlobalPi /\
  RawCodedTernaryPredicateDeepClosed M nextGlobalSigma /\
  RawCoqRestrictedPANativeConclusionTruthSelectorLinkAt
    M parameters inputs nextGlobalSigma sigmaApplicationSelector.

Arguments RawCoqRestrictedPANativeSuccessorConclusionTruthSelectorLinkAt
  M parameters inputs currentGlobalSigma currentGlobalPi predecessorLevel
  nextGlobalSigma nextGlobalPi sigmaApplicationSelector : clear implicits.

(** The exact selected application whose refutation is needed.  Its three
    arguments are *codes of PA terms*: the quoted term computing the bottom
    formula code, followed by two quoted zero terms.  Replacing these by the
    evaluated bottom code and the model's number zero would be a type-correct
    but mathematically wrong representation change. *)
Definition rawCoqRestrictedPASelectedSigmaBottomRefutationCode
    (M : RawPAModel) (nextGlobalSigma : M)
    (sigmaApplicationSelector :
      RawCodedTernaryApplicationSelector M nextGlobalSigma) : M :=
  rawFormulaImpCode M
    (rawTernaryApplicationOutput sigmaApplicationSelector
      (rawQuotedTermCode M rawFormulaBotCodeTerm)
      (rawQuotedTermCode M tZero)
      (rawQuotedTermCode M tZero))
    (rawFormulaBotCode M).

Arguments rawCoqRestrictedPASelectedSigmaBottomRefutationCode
  M nextGlobalSigma sigmaApplicationSelector : clear implicits.

(** Once the exact opaque leaf is linked, the complete direct template has
    no remaining representational ambiguity. *)
Theorem raw_coqRestrictedPABottomTruthRefutationDirectCode_native_view :
    forall (M : RawPAModel)
      (parameters : RawCodedTemplateNumeralParameters M)
      (inputs : RawCodedTemplateDirectStructuralInputs M)
      nextGlobalSigma
      (sigmaApplicationSelector :
        RawCodedTernaryApplicationSelector M nextGlobalSigma),
  RawCoqRestrictedPANativeConclusionTruthSelectorLinkAt
    M parameters inputs nextGlobalSigma sigmaApplicationSelector ->
  rawCoqRestrictedPABottomTruthRefutationDirectCode M inputs =
  rawCoqRestrictedPASelectedSigmaBottomRefutationCode
    M nextGlobalSigma sigmaApplicationSelector.
Proof.
  intros M parameters inputs nextGlobalSigma sigmaApplicationSelector
    hconclusionLeaf.
  unfold rawCoqRestrictedPABottomTruthRefutationDirectCode,
    coqRestrictedPABottomTruthRefutationTemplate.
  rewrite rawDirectTemplateFormula_imp_code.
  rewrite hconclusionLeaf.
  unfold rawCoqRestrictedPABottomTruthRefutationDirectCode,
    rawCoqRestrictedPASelectedSigmaBottomRefutationCode,
    rawCoqRestrictedPADerivationSoundnessTemplateTermView.
  repeat rewrite rawStructuralTemplateTermWith_embedPA.
  reflexivity.
Qed.

(** The native package really does select such a linked triple.  This lemma
    deliberately returns [inputs] together with its dependent selector, so a
    caller cannot accidentally combine the leaf equation from one package
    with the structural inputs of another. *)
Theorem
    raw_coqRestrictedPANativeDirectTruthInputsWithClosure_bottom_link_exists :
    forall (M : RawPAModel) (hPA : RawPASatisfies M)
      (parameters : RawCodedTemplateNumeralParameters M)
      currentGlobalSigma currentGlobalPi predecessorLevel nextSigmaEvidence,
  RawCoqRestrictedPANativeDirectTruthInputsWithClosureAt
    M hPA parameters currentGlobalSigma currentGlobalPi
    predecessorLevel nextSigmaEvidence ->
  exists nextGlobalSigma : M,
  exists nextGlobalPi : M,
  exists sigmaApplicationSelector :
    RawCodedTernaryApplicationSelector M nextGlobalSigma,
  exists inputs : RawCodedTemplateDirectStructuralInputs M,
    RawCoqRestrictedPANativeSuccessorConclusionTruthSelectorLinkAt
      M parameters inputs currentGlobalSigma currentGlobalPi predecessorLevel
      nextGlobalSigma nextGlobalPi sigmaApplicationSelector.
Proof.
  intros M hPA parameters currentGlobalSigma currentGlobalPi
    predecessorLevel nextSigmaEvidence hnative.
  unfold RawCoqRestrictedPANativeDirectTruthInputsWithClosureAt in hnative.
  destruct hnative as
    (nextGlobalSigma & nextGlobalPi & sigmaApplicationSelector &
     contextApplicationSelector & contextTruth & conclusionTruth & inputs &
     closureCount & axiom & hsuccessor & hsigmaDeep & hcontextDeep &
     hinputs & hcontextOutput & hconclusionOutput & hcontextLeaf &
     hconclusionLeaf & hselectorNative & hconclusionNative & happlication &
     hremainder).
  exists nextGlobalSigma, nextGlobalPi, sigmaApplicationSelector, inputs.
  unfold
    RawCoqRestrictedPANativeSuccessorConclusionTruthSelectorLinkAt.
  split; [exact hsuccessor |].
  split; [exact hsigmaDeep | exact hconclusionLeaf].
Qed.

(** ------------------------------------------------------------------
    Package-level proof-root adapter. *)

(** This is the honest proof-producing input left after representation has
    been resolved.  Deep closure is retained because a native implementation
    will normally compile the root by eliminating the seven successor-row
    branches of this very predicate. *)
Definition RawCoqRestrictedPASelectedSigmaBottomRefutationRootCompiler
    (M : RawPAModel) : Prop :=
  forall (parameters : RawCodedTemplateNumeralParameters M)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    currentGlobalSigma currentGlobalPi predecessorLevel
    nextGlobalSigma nextGlobalPi
    (sigmaApplicationSelector :
      RawCodedTernaryApplicationSelector M nextGlobalSigma)
    context,
  RawCoqRestrictedPANativeSuccessorConclusionTruthSelectorLinkAt
    M parameters inputs currentGlobalSigma currentGlobalPi predecessorLevel
    nextGlobalSigma nextGlobalPi sigmaApplicationSelector ->
  exists root : M,
    RawCodedPALocalProofOf M context
      (rawCoqRestrictedPASelectedSigmaBottomRefutationCode
        M nextGlobalSigma sigmaApplicationSelector)
      root.

Arguments RawCoqRestrictedPASelectedSigmaBottomRefutationRootCompiler
  M : clear implicits.

(** A selected-application root closes the direct endpoint for the exact
    inputs extracted from the native package.  The proof root itself is not
    rebuilt: code equality transports the already checked local derivation. *)
Theorem
    raw_coqRestrictedPANativeDirectTruthInputsWithClosure_bottom_refutation_of_selected_sigma
    : forall (M : RawPAModel) (hPA : RawPASatisfies M)
      (parameters : RawCodedTemplateNumeralParameters M)
      currentGlobalSigma currentGlobalPi predecessorLevel nextSigmaEvidence
      context,
  RawCoqRestrictedPANativeDirectTruthInputsWithClosureAt
    M hPA parameters currentGlobalSigma currentGlobalPi
    predecessorLevel nextSigmaEvidence ->
  RawCoqRestrictedPASelectedSigmaBottomRefutationRootCompiler M ->
  exists inputs : RawCodedTemplateDirectStructuralInputs M,
  exists root : M,
    RawCodedPALocalProofOf M context
      (rawCoqRestrictedPABottomTruthRefutationDirectCode M inputs)
      root.
Proof.
  intros M hPA parameters currentGlobalSigma currentGlobalPi
    predecessorLevel nextSigmaEvidence context hnative hrootCompiler.
  destruct
    (raw_coqRestrictedPANativeDirectTruthInputsWithClosure_bottom_link_exists
      M hPA parameters currentGlobalSigma currentGlobalPi
      predecessorLevel nextSigmaEvidence hnative)
    as (nextGlobalSigma & nextGlobalPi & sigmaApplicationSelector & inputs &
      hnativeLink).
  pose proof hnativeLink as hnativeLinkCopy.
  destruct hnativeLinkCopy as (_ & _ & hlink).
  destruct
    (hrootCompiler parameters inputs currentGlobalSigma currentGlobalPi
      predecessorLevel nextGlobalSigma nextGlobalPi
      sigmaApplicationSelector context hnativeLink) as [root hroot].
  exists inputs, root.
  rewrite
    (raw_coqRestrictedPABottomTruthRefutationDirectCode_native_view
      M parameters inputs nextGlobalSigma sigmaApplicationSelector hlink).
  exact hroot.
Qed.

(** ------------------------------------------------------------------
    Exact final-staged synchronization boundary. *)

(** The final staged graph stores proof-field codes but not the earlier
    [nextGlobalSigma], dependent selector, numeral parameters, or direct
    [inputs] chosen by the native package.  A graph-to-package integration
    must therefore expose this projection explicitly.  Requiring the link
    pointwise at the literal trace, prerequisites, and level equation rules
    out an unrelated selector or an extensionally different input record. *)
Definition RawDynamicTruthNativeFinalBottomTruthNativeSelectorLinkCompiler
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
    exists currentGlobalSigma currentGlobalPi predecessorLevel : M,
    exists nextGlobalSigma : M,
    exists nextGlobalPi : M,
    exists sigmaApplicationSelector :
      RawCodedTernaryApplicationSelector M nextGlobalSigma,
      RawCoqRestrictedPANativeSuccessorConclusionTruthSelectorLinkAt
        M parameters inputs currentGlobalSigma currentGlobalPi
        predecessorLevel nextGlobalSigma nextGlobalPi
        sigmaApplicationSelector.

Arguments RawDynamicTruthNativeFinalBottomTruthNativeSelectorLinkCompiler
  M inputs : clear implicits.

(** This is the narrow remaining native row-proof interface.  Unlike the
    arbitrary-input residual, its conclusion is the selected Sigma
    application itself and its hypotheses carry the exact selector/input
    link.  A future seven-branch compiler can implement this definition
    without knowing anything about the surrounding consistency template. *)
Definition
    RawDynamicTruthNativeFinalSelectedSigmaBottomRefutationRootCompiler
    (M : RawPAModel)
    (inputs : RawCodedTemplateDirectStructuralInputs M) : Prop :=
  forall (tail : nat -> M) level
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
      nextFinal successorNumeralCode witnessList baseContext
      (parameters : RawCodedTemplateNumeralParameters M)
      nativeCurrentGlobalSigma nativeCurrentGlobalPi nativePredecessorLevel
      nextGlobalSigma nextGlobalPi
      (sigmaApplicationSelector :
        RawCodedTernaryApplicationSelector M nextGlobalSigma),
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
    RawCoqRestrictedPANativeSuccessorConclusionTruthSelectorLinkAt
      M parameters inputs nativeCurrentGlobalSigma nativeCurrentGlobalPi
      nativePredecessorLevel nextGlobalSigma nextGlobalPi
      sigmaApplicationSelector ->
    exists root : M,
      RawCodedPALocalProofOf M
        (rawCoqRestrictedPAConsistencyBridgeContextCode
          M successorNumeralCode baseContext)
        (rawCoqRestrictedPASelectedSigmaBottomRefutationCode
          M nextGlobalSigma sigmaApplicationSelector)
        root.

Arguments
  RawDynamicTruthNativeFinalSelectedSigmaBottomRefutationRootCompiler
  M inputs : clear implicits.

(** Compose the exact graph/package link with the actual selected-row root.
    This is a strict refinement of the old residual boundary: neither premise
    can discharge an arbitrary opaque conclusion leaf. *)
Theorem
    raw_dynamicTruthNativeFinalBottomTruthDirectRefutationCompiler_of_native_selector
    : forall (M : RawPAModel)
      (inputs : RawCodedTemplateDirectStructuralInputs M),
  RawDynamicTruthNativeFinalBottomTruthNativeSelectorLinkCompiler M inputs ->
  RawDynamicTruthNativeFinalSelectedSigmaBottomRefutationRootCompiler
    M inputs ->
  RawDynamicTruthNativeFinalBottomTruthDirectRefutationCompiler M inputs.
Proof.
  intros M inputs hlinkCompiler hrootCompiler.
  unfold RawDynamicTruthNativeFinalBottomTruthDirectRefutationCompiler,
    RawDynamicTruthNativeFinalDirectBridgeFormulaRootCompiler.
  intros tail level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal
    nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
    nextFinal successorNumeralCode witnessList baseContext
    htrace hprerequisites hlevel.
  destruct
    (hlinkCompiler tail level
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
      nextFinal successorNumeralCode witnessList baseContext
      htrace hprerequisites hlevel)
    as (parameters & nativeCurrentGlobalSigma & nativeCurrentGlobalPi &
      nativePredecessorLevel & nextGlobalSigma & nextGlobalPi &
      sigmaApplicationSelector & hnativeLink).
  pose proof hnativeLink as hnativeLinkCopy.
  destruct hnativeLinkCopy as (_ & _ & hlink).
  destruct
    (hrootCompiler tail level
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
      nextFinal successorNumeralCode witnessList baseContext
      parameters nativeCurrentGlobalSigma nativeCurrentGlobalPi
      nativePredecessorLevel nextGlobalSigma nextGlobalPi
      sigmaApplicationSelector
      htrace hprerequisites hlevel hnativeLink)
    as [root hroot].
  exists root.
  rewrite
    (raw_coqRestrictedPABottomTruthRefutationDirectCode_native_view
      M parameters inputs nextGlobalSigma sigmaApplicationSelector hlink).
  exact hroot.
Qed.

End PABoundedRawCodedRestrictedPABottomTruthNativeDirectRefutationLink.
