(**
  The exact syntactic seam between derivation soundness and the native final
  staged compiler.

  The Lean construction reaches the final restricted-consistency coordinate
  in three logically separate steps:

    1. represented strong induction proves the universal fixed-level
       derivation-soundness invariant;
    2. the fixed consistency-from-soundness source theorem turns that
       invariant into the selected restricted-consistency target; and
    3. in the already opened candidate-proof context, that target refutes the
       candidate and hence yields falsity.

  Coq does not yet contain the arbitrary-carrier dynamic raw syntax for this
  invariant, nor compilers for the latter two links.  (A predicate indexed by
  an external standard [nat] would not fill that role.)  This module therefore
  does not pretend to prove any of them.  Instead it states their smallest
  exact same-context package and verifies the remaining proof-tree
  construction: two implication
  eliminations produce bottom, and bottom elimination produces precisely the
  curried six-field implication required by
  [RawDynamicTruthNativeFinalSourceLinkedImplicationRootCompiler].

  The abstract [soundnessCode] below is intentionally returned by the
  premise.  Once the derivation-soundness syntax is ported, it must be
  replaced there by the concrete code of the universal invariant.  No
  semantic truth-to-proof conversion, restriction-level induction, dynamic
  soundness producer, or successor consistency certificate is used here.
*)

From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors
  RawCodedProofUnaryConstructors
  RawCodedProofBinaryConstructors
  RawCodedPALocalProofExistential
  RawCodedPALocalProofComposition
  RawCodedRestrictedPAConsistencyTripleExDescent
  RawCodedRestrictedPAConsistencyShiftRealization
  RawCodedRestrictedPADynamicSoundnessComposition
  RawCodedRestrictedPAProjectedFieldRefutation
  RawCodedDynamicTruthNativeFinalStagedRootCompilation.

Module PABoundedRawCodedDynamicTruthNativeFinalUniversalSoundnessComposition.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedProofUnaryConstructors.
Import PABoundedRawCodedProofBinaryConstructors.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPALocalProofComposition.
Import PABoundedRawCodedRestrictedPAConsistencyTripleExDescent.
Import PABoundedRawCodedRestrictedPAConsistencyShiftRealization.
Import PABoundedRawCodedRestrictedPADynamicSoundnessComposition.
Import PABoundedRawCodedRestrictedPAProjectedFieldRefutation.
Import PABoundedRawCodedDynamicTruthNativeFinalStagedRootCompilation.

(** The completely explicit proof root built from the three missing links.
    The first [ImpE] applies the fixed consistency bridge to universal
    soundness.  The second opens the resulting target against the candidate
    proof already represented in [tailContext].  Only then is [BotE] used to
    obtain the precise six-field implication expected downstream. *)
Definition rawRestrictedPADynamicSoundnessFromUniversalRoot
    (M : RawPAModel) (numeralCode tailContext finalTarget soundnessCode
      soundnessRoot consistencyBridgeRoot targetRefutationRoot : M) : M :=
  let context := rawRestrictedPAFieldsContextCode M numeralCode tailContext in
  rawProofBotERoot M context
    (rawRestrictedPADynamicSoundnessImplicationCode M numeralCode)
    (rawProofImpERoot M context finalTarget (rawFormulaBotCode M)
      targetRefutationRoot
      (rawProofImpERoot M context soundnessCode finalTarget
        consistencyBridgeRoot soundnessRoot)).

Arguments rawRestrictedPADynamicSoundnessFromUniversalRoot
  M numeralCode tailContext finalTarget soundnessCode
    soundnessRoot consistencyBridgeRoot targetRefutationRoot
  : clear implicits.

(** Pure proof-tree composition at one literal context.  Each premise is an
    actual covered local PA derivation, rather than a semantic assertion.
    In particular, [hconsistencyBridge] is the raw-code counterpart of
    Lean's [compiledConsistencyFromSoundnessProof], while [hrefutation]
    records the still-missing syntactic opening of the selected sealed target
    under the candidate-proof context. *)
Theorem
    raw_restrictedPADynamicSoundnessImplicationProof_of_universal_soundness :
    forall (M : RawPAModel), RawPASatisfies M -> forall
      numeralCode tailContext finalTarget soundnessCode
      soundnessRoot consistencyBridgeRoot targetRefutationRoot,
  RawCodedPALocalProofOf M
    (rawRestrictedPAFieldsContextCode M numeralCode tailContext)
    soundnessCode soundnessRoot ->
  RawCodedPALocalProofOf M
    (rawRestrictedPAFieldsContextCode M numeralCode tailContext)
    (rawFormulaImpCode M soundnessCode finalTarget)
    consistencyBridgeRoot ->
  RawCodedPALocalProofOf M
    (rawRestrictedPAFieldsContextCode M numeralCode tailContext)
    (rawFormulaImpCode M finalTarget (rawFormulaBotCode M))
    targetRefutationRoot ->
  RawRestrictedPADynamicSoundnessImplicationProof
    M numeralCode tailContext.
Proof.
  intros M hPA numeralCode tailContext finalTarget soundnessCode
    soundnessRoot consistencyBridgeRoot targetRefutationRoot
    hsoundness hconsistencyBridge hrefutation.
  set (context :=
    rawRestrictedPAFieldsContextCode M numeralCode tailContext).
  pose proof (raw_codedPALocalProofOf_impE M hPA context
    soundnessCode finalTarget consistencyBridgeRoot soundnessRoot
    hconsistencyBridge hsoundness) as hconsistency.
  pose proof (raw_codedPALocalProofOf_impE M hPA context
    finalTarget (rawFormulaBotCode M)
    targetRefutationRoot
    (rawProofImpERoot M context soundnessCode finalTarget
      consistencyBridgeRoot soundnessRoot)
    hrefutation hconsistency) as hbottom.
  exists (rawRestrictedPADynamicSoundnessFromUniversalRoot M
    numeralCode tailContext finalTarget soundnessCode soundnessRoot
    consistencyBridgeRoot targetRefutationRoot).
  unfold rawRestrictedPADynamicSoundnessFromUniversalRoot.
  exact (raw_codedPALocalProofOf_botE M hPA context
    (rawProofImpERoot M context finalTarget (rawFormulaBotCode M)
      targetRefutationRoot
      (rawProofImpERoot M context soundnessCode finalTarget
        consistencyBridgeRoot soundnessRoot))
    hbottom
    (rawRestrictedPADynamicSoundnessImplicationCode M numeralCode)).
Qed.

(** Pointwise residual package aligned exactly with the final staged trace.

    The three local roots are deliberately separate:

    - [soundnessRoot] is the output still to be obtained by represented
      induction on derivation codes at the fixed successor truth level;
    - [consistencyBridgeRoot] is the compiled fixed source implication from
      that concrete invariant code to [nextFinal]; and
    - [targetRefutationRoot] opens [nextFinal] and applies it to the candidate
      proof already in the canonical descent context.

    Thus this premise is a roadmap, not a renamed dynamic-soundness producer:
    its endpoints expose both the intermediate invariant and the exact graph-
    selected consistency target. *)
Definition
    RawDynamicTruthNativeFinalUniversalSoundnessCompositionCompiler
    (M : RawPAModel) : Prop :=
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
    exists soundnessCode soundnessRoot
        consistencyBridgeRoot targetRefutationRoot : M,
      RawCodedPALocalProofOf M
        (rawRestrictedPAFieldsContextCode M successorNumeralCode
          (rawRestrictedPACanonicalShiftedProofContextCode
            M baseContext successorNumeralCode))
        soundnessCode soundnessRoot /\
      RawCodedPALocalProofOf M
        (rawRestrictedPAFieldsContextCode M successorNumeralCode
          (rawRestrictedPACanonicalShiftedProofContextCode
            M baseContext successorNumeralCode))
        (rawFormulaImpCode M soundnessCode nextFinal)
        consistencyBridgeRoot /\
      RawCodedPALocalProofOf M
        (rawRestrictedPAFieldsContextCode M successorNumeralCode
          (rawRestrictedPACanonicalShiftedProofContextCode
            M baseContext successorNumeralCode))
        (rawFormulaImpCode M nextFinal (rawFormulaBotCode M))
        targetRefutationRoot.

Arguments
  RawDynamicTruthNativeFinalUniversalSoundnessCompositionCompiler M
  : clear implicits.

(** The advertised adapter into the existing sole final residual.  All trace,
    target selection, numeral selection, and prerequisite synchronization
    remain unchanged; only the three named proof roots are composed. *)
Theorem
    raw_dynamicTruthNativeFinalSourceLinkedImplicationRootCompiler_of_universal_soundness :
    forall (M : RawPAModel), RawPASatisfies M ->
  RawDynamicTruthNativeFinalUniversalSoundnessCompositionCompiler M ->
  RawDynamicTruthNativeFinalSourceLinkedImplicationRootCompiler M.
Proof.
  intros M hPA hcompiler tail level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal
    nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
    nextFinal successorNumeralCode witnessList baseContext
    htrace hprerequisites.
  destruct (hcompiler tail level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal
    nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
    nextFinal successorNumeralCode witnessList baseContext
    htrace hprerequisites) as
    (soundnessCode & soundnessRoot & consistencyBridgeRoot &
      targetRefutationRoot & hsoundness & hbridge & hrefutation).
  exact
    (raw_restrictedPADynamicSoundnessImplicationProof_of_universal_soundness
      M hPA successorNumeralCode
      (rawRestrictedPACanonicalShiftedProofContextCode
        M baseContext successorNumeralCode)
      nextFinal soundnessCode soundnessRoot consistencyBridgeRoot
      targetRefutationRoot hsoundness hbridge hrefutation).
Qed.

End PABoundedRawCodedDynamicTruthNativeFinalUniversalSoundnessComposition.
