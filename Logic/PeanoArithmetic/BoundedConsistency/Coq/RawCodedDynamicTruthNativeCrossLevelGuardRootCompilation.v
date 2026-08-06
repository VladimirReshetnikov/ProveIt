(**
  Context-preserving one-root compilation for native cross-level guards.

  The preceding leaf compiler reduced adjacent-level coherence to one
  represented guarded-equivalence root for each polarity.  The first part
  of this file observes that those two roots are not independent: one proof
  of the literal coherence body, over an arbitrary visible base context,
  yields both by assumption insertion, implication elimination, and the two
  conjunction projections.

  The second part exposes the exact dependency-aware residual used by the
  production compiler.  It assembles the preceding six-field master and the
  newly compiled local field in one witnessed context, then asks for a single
  trace-linked implication from that staged antecedent to the coherence body.
  No semantic fact is converted into syntax and no nonempty context is erased.
*)

From Stdlib Require Import List.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  CodedSyntax
  RawCodedSyntaxConstructors
  RawCodedFormulaOperations
  RawCodedFixedLevelTruth
  RawCodedFixedLevelTruthTraversal
  RawCodedFixedLevelTruthTotality
  RawCodedRestrictedProofStandardAdequacy
  RawCodedRestrictedPAProof
  RawCodedContextLists
  RawCodedContextStructure
  RawCodedProofAssumptionLeaf
  RawCodedProofBinaryConstructors
  RawCodedProofImpIConstructor
  RawCodedProofAndIConstructor
  RawCodedProofAndEConstructors
  RawCodedPALocalProofExistential
  RawCodedPALocalProofComposition
  RawCodedPALocalProofConjunction
  RawCodedPALocalProofAndIntroduction
  RawCodedPALocalProofContextInsertUnconditional
  RawCodedPALocalProofWitnessedContextMerge
  RawCodedPALocalProofPropositionalRules
  RawCodedTruthCertificateFinalProjection
  RawCodedTruthCertificateMasterIntroduction
  RawCodedFixedLevelTruthCoherence
  RawCodedFixedLevelTruthAdmissibleCoherence
  RawCodedDynamicTruthNativeLocalPositiveGraph
  RawCodedDynamicTruthNativeCrossLevelPositiveGraph
  RawCodedDynamicTruthNativeCrossLevelProofCompilation
  RawCodedDynamicTruthNativeCrossLevelLeafRootCompilation.

Import ListNotations.

Module PABoundedRawCodedDynamicTruthNativeCrossLevelGuardRootCompilation.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedCodedSyntax.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedFixedLevelTruth.
Import PABoundedRawCodedFixedLevelTruthTraversal.
Import PABoundedRawCodedFixedLevelTruthTotality.
Import PABoundedRawCodedRestrictedProofStandardAdequacy.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedContextLists.
Import PABoundedRawCodedContextStructure.
Import PABoundedRawCodedProofAssumptionLeaf.
Import PABoundedRawCodedProofBinaryConstructors.
Import PABoundedRawCodedProofImpIConstructor.
Import PABoundedRawCodedProofAndIConstructor.
Import PABoundedRawCodedProofAndEConstructors.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPALocalProofComposition.
Import PABoundedRawCodedPALocalProofConjunction.
Import PABoundedRawCodedPALocalProofAndIntroduction.
Import PABoundedRawCodedPALocalProofContextInsertUnconditional.
Import PABoundedRawCodedPALocalProofWitnessedContextMerge.
Import PABoundedRawCodedPALocalProofPropositionalRules.
Import PABoundedRawCodedTruthCertificateFinalProjection.
Import PABoundedRawCodedTruthCertificateMasterIntroduction.
Import PABoundedRawCodedFixedLevelTruthCoherence.
Import PABoundedRawCodedFixedLevelTruthAdmissibleCoherence.
Import PABoundedRawCodedDynamicTruthNativeLocalPositiveGraph.
Import PABoundedRawCodedDynamicTruthNativeCrossLevelPositiveGraph.
Import PABoundedRawCodedDynamicTruthNativeCrossLevelProofCompilation.
Import PABoundedRawCodedDynamicTruthNativeCrossLevelLeafRootCompilation.

(** ------------------------------------------------------------------
    A single body root supplies both polarity guards. *)

Definition RawDynamicTruthNativeCrossLevelBodyRootOn
    (M : RawPAModel)
    (baseContext sigmaDomain piDomain
      currentSigma currentPi nextSigma nextPi : M) : Prop :=
  exists root : M,
    RawCodedPALocalProofOf M baseContext
      (rawDynamicTruthNativeCrossLevelCoherenceBodyCode M
        sigmaDomain piDomain currentSigma currentPi nextSigma nextPi)
      root.

Arguments RawDynamicTruthNativeCrossLevelBodyRootOn
  M baseContext sigmaDomain piDomain
    currentSigma currentPi nextSigma nextPi : clear implicits.

(** Insert the admissibility antecedent above the caller's literal tail,
    apply the body implication, and project its synchronized two guards. *)
Theorem raw_dynamicTruthNativeCrossLevelGuardRootsOn_of_body_root : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      baseContext sigmaDomain piDomain
      currentSigma currentPi nextSigma nextPi,
  RawContextListRealizable M baseContext ->
  RawCodedFormulaAtomicallyAdequate M
    (rawDynamicTruthLocalAdmissibleCode M sigmaDomain piDomain) ->
  RawDynamicTruthNativeCrossLevelBodyRootOn M baseContext
    sigmaDomain piDomain currentSigma currentPi nextSigma nextPi ->
  RawDynamicTruthNativeCrossLevelSigmaGuardRootOn M baseContext
      sigmaDomain piDomain currentSigma nextSigma /\
    RawDynamicTruthNativeCrossLevelPiGuardRootOn M baseContext
      sigmaDomain piDomain currentPi nextPi.
Proof.
  intros M hPA baseContext sigmaDomain piDomain
    currentSigma currentPi nextSigma nextPi hbase hadmissible
    (bodyRoot & hbody).
  set (admissible :=
    rawDynamicTruthLocalAdmissibleCode M sigmaDomain piDomain).
  set (admissibleContext :=
    rawDynamicTruthNativeCrossLevelAdmissibleContextOn M
      baseContext sigmaDomain piDomain).
  set (sigmaGuard :=
    rawDynamicTruthNativeCrossLevelGuardedEquivalenceCode M
      sigmaDomain currentSigma nextSigma).
  set (piGuard :=
    rawDynamicTruthNativeCrossLevelGuardedEquivalenceCode M
      piDomain currentPi nextPi).
  assert (hadmissibleContext :
      RawContextListRealizable M admissibleContext).
  {
    unfold admissibleContext,
      rawDynamicTruthNativeCrossLevelAdmissibleContextOn.
    exact (raw_contextList_cons_realizable M hPA baseContext
      (rawDynamicTruthLocalAdmissibleCode M sigmaDomain piDomain) hbase).
  }
  destruct (raw_codedPALocalProof_adequateConsTransplant
    M hPA baseContext admissible
    (rawDynamicTruthNativeCrossLevelCoherenceBodyCode M
      sigmaDomain piDomain currentSigma currentPi nextSigma nextPi)
    bodyRoot hadmissible hbase hbody) as
    [bodyAtAdmissible hbodyAtAdmissible].
  pose proof (raw_codedPALocalProofOf_assumption
    M hPA baseContext admissible hbase) as hadmissibleRoot.
  pose proof (raw_codedPALocalProofOf_impE M hPA
    admissibleContext admissible
    (rawFormulaAndCode M sigmaGuard piGuard)
    bodyAtAdmissible
    (rawProofAssumptionRoot M admissibleContext admissible)
    hbodyAtAdmissible hadmissibleRoot) as hguards.
  split.
  - exists (rawProofAndERoot M RawAndLeft admissibleContext
      sigmaGuard piGuard
      (rawProofImpERoot M admissibleContext admissible
        (rawFormulaAndCode M sigmaGuard piGuard)
        bodyAtAdmissible
        (rawProofAssumptionRoot M admissibleContext admissible))).
    exact (raw_codedPALocalProofOf_andE1 M hPA admissibleContext
      sigmaGuard piGuard
      (rawProofImpERoot M admissibleContext admissible
        (rawFormulaAndCode M sigmaGuard piGuard)
        bodyAtAdmissible
        (rawProofAssumptionRoot M admissibleContext admissible))
      hguards).
  - exists (rawProofAndERoot M RawAndRight admissibleContext
      sigmaGuard piGuard
      (rawProofImpERoot M admissibleContext admissible
        (rawFormulaAndCode M sigmaGuard piGuard)
        bodyAtAdmissible
        (rawProofAssumptionRoot M admissibleContext admissible))).
    exact (raw_codedPALocalProofOf_andE2 M hPA admissibleContext
      sigmaGuard piGuard
      (rawProofImpERoot M admissibleContext admissible
        (rawFormulaAndCode M sigmaGuard piGuard)
        bodyAtAdmissible
        (rawProofAssumptionRoot M admissibleContext admissible))
      hguards).
Qed.

(** A pointwise body compiler consumes the same linked rows as the preceding
    two-guard compiler, but asks for only one represented root. *)
Definition RawDynamicTruthNativeCrossLevelLinkedBodyRootCompilerOn
    (M : RawPAModel) (baseContext : M) : Prop :=
  forall (tail : nat -> M) predecessorLevel
      currentGlobalSigma currentGlobalPi
      sigmaDomain piDomain currentSigma currentPi nextSigma nextPi
      sigmaRowDomain piRowDomain
      lowerPiApplication lowerSigmaApplication,
    RawDynamicTruthNativeCrossLevelLinkedRowsAt M tail predecessorLevel
      currentGlobalSigma currentGlobalPi sigmaDomain piDomain
      currentSigma currentPi nextSigma nextPi
      sigmaRowDomain piRowDomain
      lowerPiApplication lowerSigmaApplication ->
    RawDynamicTruthNativeCrossLevelBodyRootOn M baseContext
      sigmaDomain piDomain currentSigma currentPi nextSigma nextPi.

Arguments RawDynamicTruthNativeCrossLevelLinkedBodyRootCompilerOn
  M baseContext : clear implicits.

(** The context-preserving counterpart of the original empty-base guard
    compiler.  Keeping this interface explicit lets staged constructions
    move between a body compiler and a pair of guarded roots without hiding
    the witnessed base context. *)
Definition RawDynamicTruthNativeCrossLevelLinkedGuardRootCompilerOn
    (M : RawPAModel) (baseContext : M) : Prop :=
  forall (tail : nat -> M) predecessorLevel
      currentGlobalSigma currentGlobalPi
      sigmaDomain piDomain currentSigma currentPi nextSigma nextPi
      sigmaRowDomain piRowDomain
      lowerPiApplication lowerSigmaApplication,
    RawDynamicTruthNativeCrossLevelLinkedRowsAt M tail predecessorLevel
      currentGlobalSigma currentGlobalPi sigmaDomain piDomain
      currentSigma currentPi nextSigma nextPi
      sigmaRowDomain piRowDomain
      lowerPiApplication lowerSigmaApplication ->
    RawDynamicTruthNativeCrossLevelSigmaGuardRootOn M baseContext
      sigmaDomain piDomain currentSigma nextSigma /\
    RawDynamicTruthNativeCrossLevelPiGuardRootOn M baseContext
      sigmaDomain piDomain currentPi nextPi.

Arguments RawDynamicTruthNativeCrossLevelLinkedGuardRootCompilerOn
  M baseContext : clear implicits.

Theorem
    raw_dynamicTruthNativeCrossLevelLinkedGuardRootCompilerOn_of_body :
    forall (M : RawPAModel), RawPASatisfies M -> forall baseContext,
  RawContextListRealizable M baseContext ->
  RawDynamicTruthNativeCrossLevelLinkedBodyRootCompilerOn M baseContext ->
  forall (tail : nat -> M) predecessorLevel
      currentGlobalSigma currentGlobalPi
      sigmaDomain piDomain currentSigma currentPi nextSigma nextPi
      sigmaRowDomain piRowDomain
      lowerPiApplication lowerSigmaApplication,
    RawDynamicTruthNativeCrossLevelLinkedRowsAt M tail predecessorLevel
      currentGlobalSigma currentGlobalPi sigmaDomain piDomain
      currentSigma currentPi nextSigma nextPi
      sigmaRowDomain piRowDomain
      lowerPiApplication lowerSigmaApplication ->
    RawDynamicTruthNativeCrossLevelSigmaGuardRootOn M baseContext
        sigmaDomain piDomain currentSigma nextSigma /\
      RawDynamicTruthNativeCrossLevelPiGuardRootOn M baseContext
        sigmaDomain piDomain currentPi nextPi.
Proof.
  intros M hPA baseContext hbase hbody tail predecessorLevel
    currentGlobalSigma currentGlobalPi sigmaDomain piDomain
    currentSigma currentPi nextSigma nextPi
    sigmaRowDomain piRowDomain lowerPi lowerSigma hlinked.
  destruct (raw_dynamicTruthNativeCrossLevelLinkedRowsAt_adequacy
    M hPA tail predecessorLevel currentGlobalSigma currentGlobalPi
    sigmaDomain piDomain currentSigma currentPi nextSigma nextPi
    sigmaRowDomain piRowDomain lowerPi lowerSigma hlinked) as
    (nextGlobalSigma & nextGlobalPi & hadequacy).
  exact (raw_dynamicTruthNativeCrossLevelGuardRootsOn_of_body_root
    M hPA baseContext sigmaDomain piDomain
    currentSigma currentPi nextSigma nextPi hbase
    (rawDynamicTruthNativeCrossLevel_admissible_adequate
      M currentGlobalSigma currentGlobalPi nextGlobalSigma nextGlobalPi
      sigmaDomain piDomain currentSigma currentPi nextSigma nextPi
      hadequacy)
    (hbody tail predecessorLevel currentGlobalSigma currentGlobalPi
      sigmaDomain piDomain currentSigma currentPi nextSigma nextPi
      sigmaRowDomain piRowDomain lowerPi lowerSigma hlinked)).
Qed.

(** The literal-empty specialization is a precise adapter to the compiler
    consumed by [RawCodedDynamicTruthNativeCrossLevelLeafRootCompilation]. *)
Corollary raw_dynamicTruthNativeCrossLevelLinkedGuardRootCompiler_of_body :
    forall (M : RawPAModel), RawPASatisfies M ->
  RawDynamicTruthNativeCrossLevelLinkedBodyRootCompilerOn M (raw_zero M) ->
  RawDynamicTruthNativeCrossLevelLinkedGuardRootCompiler M.
Proof.
  intros M hPA hbody.
  exact (raw_dynamicTruthNativeCrossLevelLinkedGuardRootCompilerOn_of_body
    M hPA (raw_zero M) (raw_contextList_empty_realizable M hPA) hbody).
Qed.

(** ------------------------------------------------------------------
    The dependency-aware staged boundary.

    The production Lean construction does not prove the cross-level field in
    isolation.  Its induction kernel is applied only after all six fields of
    the preceding certificate and the newly compiled local field are
    available.  The following carrier interface mirrors that order exactly.
    All seven roots live in one literal witnessed context. *)

Definition rawDynamicTruthNativeCrossLevelStagedAntecedentCode
    (M : RawPAModel)
    (currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal nextLocal : M) : M :=
  rawFormulaAndCode M
    (rawSixFieldMasterCode M
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal)
    nextLocal.

Arguments rawDynamicTruthNativeCrossLevelStagedAntecedentCode
  M currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal nextLocal : clear implicits.

Record RawDynamicTruthNativeCrossLevelStagedPrerequisitesAt
    (M : RawPAModel)
    (witnessList baseContext
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal nextLocal
      currentLocalRoot currentCrossLevelRoot currentShiftRoot
      currentSubstitutionRoot currentAxiomSoundnessRoot currentFinalRoot
      nextLocalRoot : M) : Prop := {
  rawDynamicTruthNativeCrossLevel_staged_witnessed :
    RawCodedPAAxiomWitnessContext M witnessList baseContext;
  rawDynamicTruthNativeCrossLevel_staged_currentLocal :
    RawCodedPALocalProofOf M baseContext currentLocal currentLocalRoot;
  rawDynamicTruthNativeCrossLevel_staged_currentCrossLevel :
    RawCodedPALocalProofOf M baseContext
      currentCrossLevel currentCrossLevelRoot;
  rawDynamicTruthNativeCrossLevel_staged_currentShift :
    RawCodedPALocalProofOf M baseContext currentShift currentShiftRoot;
  rawDynamicTruthNativeCrossLevel_staged_currentSubstitution :
    RawCodedPALocalProofOf M baseContext
      currentSubstitution currentSubstitutionRoot;
  rawDynamicTruthNativeCrossLevel_staged_currentAxiomSoundness :
    RawCodedPALocalProofOf M baseContext
      currentAxiomSoundness currentAxiomSoundnessRoot;
  rawDynamicTruthNativeCrossLevel_staged_currentFinal :
    RawCodedPALocalProofOf M baseContext currentFinal currentFinalRoot;
  rawDynamicTruthNativeCrossLevel_staged_nextLocal :
    RawCodedPALocalProofOf M baseContext nextLocal nextLocalRoot
}.

Arguments RawDynamicTruthNativeCrossLevelStagedPrerequisitesAt
  M witnessList baseContext
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal nextLocal
    currentLocalRoot currentCrossLevelRoot currentShiftRoot
    currentSubstitutionRoot currentAxiomSoundnessRoot currentFinalRoot
    nextLocalRoot : clear implicits.

(** This one implication is the exact object-proof analogue of the staged
    cross-level induction kernel: it may use the complete preceding master
    and the new local bundle, but nothing from the later shift,
    substitution, axiom-soundness, or consistency stages. *)
Definition RawDynamicTruthNativeCrossLevelStagedBodyImplicationRootOn
    (M : RawPAModel) (baseContext
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal nextLocal
      sigmaDomain piDomain currentSigma currentPi nextSigma nextPi : M)
    : Prop :=
  exists root : M,
    RawCodedPALocalProofOf M baseContext
      (rawFormulaImpCode M
        (rawDynamicTruthNativeCrossLevelStagedAntecedentCode M
          currentLocal currentCrossLevel currentShift currentSubstitution
          currentAxiomSoundness currentFinal nextLocal)
        (rawDynamicTruthNativeCrossLevelCoherenceBodyCode M
          sigmaDomain piDomain currentSigma currentPi nextSigma nextPi))
      root.

Arguments RawDynamicTruthNativeCrossLevelStagedBodyImplicationRootOn
  M baseContext
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal nextLocal
    sigmaDomain piDomain currentSigma currentPi nextSigma nextPi
  : clear implicits.

(**
    The empty-context proof compiler in
    [RawCodedDynamicTruthNativeCrossLevelProofCompilation] is useful for the
    original four-leaf interface, but staged callbacks retain a witnessed
    base context.  This generalized variant performs the same propositional
    shell compilation without changing that context.  The two local-root
    packages already contain the directional leaves under the exact cons
    contexts needed by implication introduction; hence the proof is entirely
    structural and requires no realizability or adequacy hypothesis.
*)
Theorem raw_dynamicTruthNativeCrossLevelBodyRootOn_of_polarity_roots_on :
    forall (M : RawPAModel), RawPASatisfies M -> forall
      baseContext sigmaDomain piDomain currentSigma currentPi nextSigma nextPi,
  RawDynamicTruthNativeCrossLevelSigmaLocalRootsOn M baseContext
      sigmaDomain piDomain currentSigma nextSigma ->
  RawDynamicTruthNativeCrossLevelPiLocalRootsOn M baseContext
      sigmaDomain piDomain currentPi nextPi ->
  RawDynamicTruthNativeCrossLevelBodyRootOn M baseContext
      sigmaDomain piDomain currentSigma currentPi nextSigma nextPi.
Proof.
  intros M hPA baseContext sigmaDomain piDomain currentSigma currentPi
    nextSigma nextPi
    (sigmaForward & sigmaBackward & hsigmaForward & hsigmaBackward)
    (piForward & piBackward & hpiForward & hpiBackward).
  set (admissibleContext :=
    rawDynamicTruthNativeCrossLevelAdmissibleContextOn M
      baseContext sigmaDomain piDomain).
  set (sigmaDomainContext :=
    rawDynamicTruthNativeCrossLevelDomainContextOn M
      baseContext sigmaDomain piDomain sigmaDomain).
  set (piDomainContext :=
    rawDynamicTruthNativeCrossLevelDomainContextOn M
      baseContext sigmaDomain piDomain piDomain).
  set (sigmaGuard :=
    rawDynamicTruthNativeCrossLevelGuardedEquivalenceCode M
      sigmaDomain currentSigma nextSigma).
  set (piGuard :=
    rawDynamicTruthNativeCrossLevelGuardedEquivalenceCode M
      piDomain currentPi nextPi).
  set (sigmaPairCode := rawFormulaAndCode M
    (rawFormulaImpCode M currentSigma nextSigma)
    (rawFormulaImpCode M nextSigma currentSigma)).
  set (piPairCode := rawFormulaAndCode M
    (rawFormulaImpCode M currentPi nextPi)
    (rawFormulaImpCode M nextPi currentPi)).
  set (pairCode := rawFormulaAndCode M sigmaGuard piGuard).
  set (admissible :=
    rawDynamicTruthLocalAdmissibleCode M sigmaDomain piDomain).
  change (RawCodedPALocalProofOf M
    (rawListNode M currentSigma sigmaDomainContext)
    nextSigma sigmaForward) in hsigmaForward.
  change (RawCodedPALocalProofOf M
    (rawListNode M nextSigma sigmaDomainContext)
    currentSigma sigmaBackward) in hsigmaBackward.
  change (RawCodedPALocalProofOf M
    (rawListNode M currentPi piDomainContext)
    nextPi piForward) in hpiForward.
  change (RawCodedPALocalProofOf M
    (rawListNode M nextPi piDomainContext)
    currentPi piBackward) in hpiBackward.
  pose proof (raw_codedPALocalProofOf_impI M hPA sigmaDomainContext
    currentSigma nextSigma
    sigmaForward
    hsigmaForward) as hsigmaForwardImp.
  pose proof (raw_codedPALocalProofOf_impI M hPA sigmaDomainContext
    nextSigma currentSigma
    sigmaBackward
    hsigmaBackward) as hsigmaBackwardImp.
  pose proof (raw_codedPALocalProofOf_andI M hPA sigmaDomainContext
    (rawFormulaImpCode M currentSigma nextSigma)
    (rawFormulaImpCode M nextSigma currentSigma)
    (rawProofImpIRoot M sigmaDomainContext currentSigma nextSigma sigmaForward)
    (rawProofImpIRoot M sigmaDomainContext nextSigma currentSigma sigmaBackward)
    hsigmaForwardImp hsigmaBackwardImp) as hsigmaPair.
  change (RawCodedPALocalProofOf M
    (rawListNode M sigmaDomain admissibleContext) sigmaPairCode
    (rawProofAndIRoot M sigmaDomainContext
      (rawFormulaImpCode M currentSigma nextSigma)
      (rawFormulaImpCode M nextSigma currentSigma)
      (rawProofImpIRoot M sigmaDomainContext currentSigma nextSigma sigmaForward)
      (rawProofImpIRoot M sigmaDomainContext nextSigma currentSigma sigmaBackward)))
    in hsigmaPair.
  pose proof (raw_codedPALocalProofOf_impI M hPA admissibleContext
    sigmaDomain sigmaPairCode
    (rawProofAndIRoot M sigmaDomainContext
      (rawFormulaImpCode M currentSigma nextSigma)
      (rawFormulaImpCode M nextSigma currentSigma)
      (rawProofImpIRoot M sigmaDomainContext currentSigma nextSigma sigmaForward)
      (rawProofImpIRoot M sigmaDomainContext nextSigma currentSigma sigmaBackward))
    hsigmaPair) as hsigmaGuard.
  pose proof (raw_codedPALocalProofOf_impI M hPA piDomainContext
    currentPi nextPi
    piForward
    hpiForward) as hpiForwardImp.
  pose proof (raw_codedPALocalProofOf_impI M hPA piDomainContext
    nextPi currentPi
    piBackward
    hpiBackward) as hpiBackwardImp.
  pose proof (raw_codedPALocalProofOf_andI M hPA piDomainContext
    (rawFormulaImpCode M currentPi nextPi)
    (rawFormulaImpCode M nextPi currentPi)
    (rawProofImpIRoot M piDomainContext currentPi nextPi piForward)
    (rawProofImpIRoot M piDomainContext nextPi currentPi piBackward)
    hpiForwardImp hpiBackwardImp) as hpiPair.
  change (RawCodedPALocalProofOf M
    (rawListNode M piDomain admissibleContext) piPairCode
    (rawProofAndIRoot M piDomainContext
      (rawFormulaImpCode M currentPi nextPi)
      (rawFormulaImpCode M nextPi currentPi)
      (rawProofImpIRoot M piDomainContext currentPi nextPi piForward)
      (rawProofImpIRoot M piDomainContext nextPi currentPi piBackward)))
    in hpiPair.
  pose proof (raw_codedPALocalProofOf_impI M hPA admissibleContext
    piDomain piPairCode
    (rawProofAndIRoot M piDomainContext
      (rawFormulaImpCode M currentPi nextPi)
      (rawFormulaImpCode M nextPi currentPi)
      (rawProofImpIRoot M piDomainContext currentPi nextPi piForward)
      (rawProofImpIRoot M piDomainContext nextPi currentPi piBackward))
    hpiPair) as hpiGuard.
  pose proof (raw_codedPALocalProofOf_andI M hPA admissibleContext
    sigmaGuard piGuard
    (rawProofImpIRoot M admissibleContext sigmaDomain sigmaPairCode
      (rawProofAndIRoot M sigmaDomainContext
        (rawFormulaImpCode M currentSigma nextSigma)
        (rawFormulaImpCode M nextSigma currentSigma)
        (rawProofImpIRoot M sigmaDomainContext currentSigma nextSigma sigmaForward)
        (rawProofImpIRoot M sigmaDomainContext nextSigma currentSigma sigmaBackward)))
    (rawProofImpIRoot M admissibleContext piDomain piPairCode
      (rawProofAndIRoot M piDomainContext
        (rawFormulaImpCode M currentPi nextPi)
        (rawFormulaImpCode M nextPi currentPi)
        (rawProofImpIRoot M piDomainContext currentPi nextPi piForward)
        (rawProofImpIRoot M piDomainContext nextPi currentPi piBackward)))
    hsigmaGuard hpiGuard) as hguards.
  pose proof (raw_codedPALocalProofOf_impI M hPA baseContext
    admissible pairCode
    (rawProofAndIRoot M admissibleContext sigmaGuard piGuard
      (rawProofImpIRoot M admissibleContext sigmaDomain sigmaPairCode
        (rawProofAndIRoot M sigmaDomainContext
          (rawFormulaImpCode M currentSigma nextSigma)
          (rawFormulaImpCode M nextSigma currentSigma)
          (rawProofImpIRoot M sigmaDomainContext currentSigma nextSigma sigmaForward)
          (rawProofImpIRoot M sigmaDomainContext nextSigma currentSigma sigmaBackward)))
      (rawProofImpIRoot M admissibleContext piDomain piPairCode
        (rawProofAndIRoot M piDomainContext
          (rawFormulaImpCode M currentPi nextPi)
          (rawFormulaImpCode M nextPi currentPi)
          (rawProofImpIRoot M piDomainContext currentPi nextPi piForward)
          (rawProofImpIRoot M piDomainContext nextPi currentPi piBackward))))
    hguards) as hbody.
  exists (rawProofImpIRoot M baseContext admissible pairCode
    (rawProofAndIRoot M admissibleContext sigmaGuard piGuard
      (rawProofImpIRoot M admissibleContext sigmaDomain sigmaPairCode
        (rawProofAndIRoot M sigmaDomainContext
          (rawFormulaImpCode M currentSigma nextSigma)
          (rawFormulaImpCode M nextSigma currentSigma)
          (rawProofImpIRoot M sigmaDomainContext currentSigma nextSigma sigmaForward)
          (rawProofImpIRoot M sigmaDomainContext nextSigma currentSigma sigmaBackward)))
      (rawProofImpIRoot M admissibleContext piDomain piPairCode
        (rawProofAndIRoot M piDomainContext
          (rawFormulaImpCode M currentPi nextPi)
          (rawFormulaImpCode M nextPi currentPi)
          (rawProofImpIRoot M piDomainContext currentPi nextPi piForward)
          (rawProofImpIRoot M piDomainContext nextPi currentPi piBackward))))).
  exact hbody.
Qed.

(** Conversely, a linked two-guard compiler is enough to build the complete
    coherence body in the same base context.  This adapter is useful when a
    predecessor construction naturally produces guarded roots first: the
    linked-row adequacy theorem supplies exactly the atomic-adequacy premises
    needed by the directional-root transport, after which the propositional
    shell above closes the body. *)
Theorem
    raw_dynamicTruthNativeCrossLevelLinkedBodyRootCompilerOn_of_guard_roots :
    forall (M : RawPAModel), RawPASatisfies M -> forall baseContext,
  RawContextListRealizable M baseContext ->
  RawDynamicTruthNativeCrossLevelLinkedGuardRootCompilerOn M baseContext ->
  RawDynamicTruthNativeCrossLevelLinkedBodyRootCompilerOn M baseContext.
Proof.
  intros M hPA baseContext hbase hguards tail predecessorLevel
    currentGlobalSigma currentGlobalPi sigmaDomain piDomain
    currentSigma currentPi nextSigma nextPi
    sigmaRowDomain piRowDomain lowerPi lowerSigma hlinked.
  destruct (raw_dynamicTruthNativeCrossLevelLinkedRowsAt_adequacy
    M hPA tail predecessorLevel currentGlobalSigma currentGlobalPi
    sigmaDomain piDomain currentSigma currentPi nextSigma nextPi
    sigmaRowDomain piRowDomain lowerPi lowerSigma hlinked) as
    (nextGlobalSigma & nextGlobalPi & hadequacy).
  destruct (hguards tail predecessorLevel
    currentGlobalSigma currentGlobalPi sigmaDomain piDomain
    currentSigma currentPi nextSigma nextPi
    sigmaRowDomain piRowDomain lowerPi lowerSigma hlinked) as
    [hsigmaGuard hpiGuard].
  apply (raw_dynamicTruthNativeCrossLevelBodyRootOn_of_polarity_roots_on
    M hPA baseContext sigmaDomain piDomain currentSigma currentPi
    nextSigma nextPi).
  - apply (raw_dynamicTruthNativeCrossLevelSigmaLocalRootsOn_of_guard_root
      M hPA baseContext sigmaDomain piDomain currentSigma nextSigma hbase).
    + exact (rawDynamicTruthNativeCrossLevel_sigmaDomain_adequate
        M currentGlobalSigma currentGlobalPi nextGlobalSigma nextGlobalPi
        sigmaDomain piDomain currentSigma currentPi nextSigma nextPi
        hadequacy).
    + exact (rawDynamicTruthNativeCrossLevel_currentSigma_adequate
        M currentGlobalSigma currentGlobalPi nextGlobalSigma nextGlobalPi
        sigmaDomain piDomain currentSigma currentPi nextSigma nextPi
        hadequacy).
    + exact (rawDynamicTruthNativeCrossLevel_nextSigma_adequate
        M currentGlobalSigma currentGlobalPi nextGlobalSigma nextGlobalPi
        sigmaDomain piDomain currentSigma currentPi nextSigma nextPi
        hadequacy).
    + exact hsigmaGuard.
  - apply (raw_dynamicTruthNativeCrossLevelPiLocalRootsOn_of_guard_root
      M hPA baseContext sigmaDomain piDomain currentPi nextPi hbase).
    + exact (rawDynamicTruthNativeCrossLevel_piDomain_adequate
        M currentGlobalSigma currentGlobalPi nextGlobalSigma nextGlobalPi
        sigmaDomain piDomain currentSigma currentPi nextSigma nextPi
        hadequacy).
    + exact (rawDynamicTruthNativeCrossLevel_currentPi_adequate
        M currentGlobalSigma currentGlobalPi nextGlobalSigma nextGlobalPi
        sigmaDomain piDomain currentSigma currentPi nextSigma nextPi
        hadequacy).
    + exact (rawDynamicTruthNativeCrossLevel_nextPi_adequate
        M currentGlobalSigma currentGlobalPi nextGlobalSigma nextGlobalPi
        sigmaDomain piDomain currentSigma currentPi nextSigma nextPi
        hadequacy).
    + exact hpiGuard.
Qed.

(** The residual compiler is trace-linked and context-preserving.  Its
    conclusion must mention the exact [baseContext] from the seven supplied
    roots; in particular, it cannot manufacture an empty-context theorem or
    select unrelated successor formulas. *)
Definition
    RawDynamicTruthNativeCrossLevelLinkedStagedBodyImplicationRootCompiler
    (M : RawPAModel) : Prop :=
  forall (tail : nat -> M) predecessorLevel
      currentGlobalSigma currentGlobalPi
      sigmaDomain piDomain currentSigma currentPi nextSigma nextPi
      sigmaRowDomain piRowDomain lowerPiApplication lowerSigmaApplication
      witnessList baseContext
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal nextLocal
      currentLocalRoot currentCrossLevelRoot currentShiftRoot
      currentSubstitutionRoot currentAxiomSoundnessRoot currentFinalRoot
      nextLocalRoot,
    RawDynamicTruthNativeCrossLevelLinkedRowsAt M tail predecessorLevel
      currentGlobalSigma currentGlobalPi sigmaDomain piDomain
      currentSigma currentPi nextSigma nextPi
      sigmaRowDomain piRowDomain
      lowerPiApplication lowerSigmaApplication ->
    RawDynamicTruthNativeCrossLevelStagedPrerequisitesAt M
      witnessList baseContext
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal nextLocal
      currentLocalRoot currentCrossLevelRoot currentShiftRoot
      currentSubstitutionRoot currentAxiomSoundnessRoot currentFinalRoot
      nextLocalRoot ->
    RawDynamicTruthNativeCrossLevelStagedBodyImplicationRootOn M
      baseContext
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal nextLocal
      sigmaDomain piDomain currentSigma currentPi nextSigma nextPi.

Arguments
  RawDynamicTruthNativeCrossLevelLinkedStagedBodyImplicationRootCompiler M
  : clear implicits.

(** Assemble the preceding six-field master and the new local proof in their
    common context, apply the single staged implication, then invoke the
    already checked one-body-to-two-guards compiler. *)
Theorem raw_dynamicTruthNativeCrossLevelStagedGuardRoots_of_body_implication :
    forall (M : RawPAModel), RawPASatisfies M ->
  RawDynamicTruthNativeCrossLevelLinkedStagedBodyImplicationRootCompiler M ->
  forall (tail : nat -> M) predecessorLevel
      currentGlobalSigma currentGlobalPi
      sigmaDomain piDomain currentSigma currentPi nextSigma nextPi
      sigmaRowDomain piRowDomain lowerPiApplication lowerSigmaApplication
      witnessList baseContext
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal nextLocal
      currentLocalRoot currentCrossLevelRoot currentShiftRoot
      currentSubstitutionRoot currentAxiomSoundnessRoot currentFinalRoot
      nextLocalRoot,
    RawDynamicTruthNativeCrossLevelLinkedRowsAt M tail predecessorLevel
      currentGlobalSigma currentGlobalPi sigmaDomain piDomain
      currentSigma currentPi nextSigma nextPi
      sigmaRowDomain piRowDomain
      lowerPiApplication lowerSigmaApplication ->
    RawDynamicTruthNativeCrossLevelStagedPrerequisitesAt M
      witnessList baseContext
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal nextLocal
      currentLocalRoot currentCrossLevelRoot currentShiftRoot
      currentSubstitutionRoot currentAxiomSoundnessRoot currentFinalRoot
      nextLocalRoot ->
    RawDynamicTruthNativeCrossLevelSigmaGuardRootOn M baseContext
        sigmaDomain piDomain currentSigma nextSigma /\
      RawDynamicTruthNativeCrossLevelPiGuardRootOn M baseContext
        sigmaDomain piDomain currentPi nextPi.
Proof.
  intros M hPA hcompiler tail predecessorLevel
    currentGlobalSigma currentGlobalPi
    sigmaDomain piDomain currentSigma currentPi nextSigma nextPi
    sigmaRowDomain piRowDomain lowerPi lowerSigma
    witnessList baseContext
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal nextLocal
    currentLocalRoot currentCrossLevelRoot currentShiftRoot
    currentSubstitutionRoot currentAxiomSoundnessRoot currentFinalRoot
    nextLocalRoot hlinked hstaged.
  destruct hstaged as
    [hwitnessed hcurrentLocal hcurrentCross hcurrentShift
      hcurrentSubstitution hcurrentAxiom hcurrentFinal hnextLocal].
  pose proof (raw_codedPALocalProofOf_sixFieldMaster_intro M hPA
    baseContext
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal
    currentLocalRoot currentCrossLevelRoot currentShiftRoot
    currentSubstitutionRoot currentAxiomSoundnessRoot currentFinalRoot
    hcurrentLocal hcurrentCross hcurrentShift hcurrentSubstitution
    hcurrentAxiom hcurrentFinal) as hcurrentMaster.
  pose proof (raw_codedPALocalProofOf_andI M hPA baseContext
    (rawSixFieldMasterCode M
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal)
    nextLocal
    (rawSixFieldMasterIntroductionRoot M baseContext
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      currentLocalRoot currentCrossLevelRoot currentShiftRoot
      currentSubstitutionRoot currentAxiomSoundnessRoot currentFinalRoot)
    nextLocalRoot hcurrentMaster hnextLocal) as hantecedent.
  assert (hstagedAgain :
      RawDynamicTruthNativeCrossLevelStagedPrerequisitesAt M
        witnessList baseContext
        currentLocal currentCrossLevel currentShift currentSubstitution
        currentAxiomSoundness currentFinal nextLocal
        currentLocalRoot currentCrossLevelRoot currentShiftRoot
        currentSubstitutionRoot currentAxiomSoundnessRoot currentFinalRoot
        nextLocalRoot).
  {
    constructor; assumption.
  }
  destruct (hcompiler tail predecessorLevel
    currentGlobalSigma currentGlobalPi sigmaDomain piDomain
    currentSigma currentPi nextSigma nextPi
    sigmaRowDomain piRowDomain lowerPi lowerSigma
    witnessList baseContext
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal nextLocal
    currentLocalRoot currentCrossLevelRoot currentShiftRoot
    currentSubstitutionRoot currentAxiomSoundnessRoot currentFinalRoot
    nextLocalRoot hlinked hstagedAgain) as [implicationRoot himplication].
  set (antecedent :=
    rawDynamicTruthNativeCrossLevelStagedAntecedentCode M
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal nextLocal).
  set (body := rawDynamicTruthNativeCrossLevelCoherenceBodyCode M
    sigmaDomain piDomain currentSigma currentPi nextSigma nextPi).
  pose proof (raw_codedPALocalProofOf_impE M hPA baseContext
    antecedent body implicationRoot
    (rawProofAndIRoot M baseContext
      (rawSixFieldMasterCode M
        currentLocal currentCrossLevel currentShift currentSubstitution
        currentAxiomSoundness currentFinal)
      nextLocal
      (rawSixFieldMasterIntroductionRoot M baseContext
        currentLocal currentCrossLevel currentShift currentSubstitution
        currentAxiomSoundness currentFinal
        currentLocalRoot currentCrossLevelRoot currentShiftRoot
        currentSubstitutionRoot currentAxiomSoundnessRoot currentFinalRoot)
      nextLocalRoot)
    himplication hantecedent) as hbody.
  apply (raw_dynamicTruthNativeCrossLevelGuardRootsOn_of_body_root
    M hPA baseContext sigmaDomain piDomain
    currentSigma currentPi nextSigma nextPi).
  - exact (raw_codedPAAxiomWitnessContext_context_realizable
      M witnessList baseContext hwitnessed).
  - destruct (raw_dynamicTruthNativeCrossLevelLinkedRowsAt_adequacy
      M hPA tail predecessorLevel currentGlobalSigma currentGlobalPi
      sigmaDomain piDomain currentSigma currentPi nextSigma nextPi
      sigmaRowDomain piRowDomain lowerPi lowerSigma hlinked) as
      (nextGlobalSigma & nextGlobalPi & hadequacy).
    exact (rawDynamicTruthNativeCrossLevel_admissible_adequate
      M currentGlobalSigma currentGlobalPi nextGlobalSigma nextGlobalPi
      sigmaDomain piDomain currentSigma currentPi nextSigma nextPi
      hadequacy).
  - exists (rawProofImpERoot M baseContext antecedent body
      implicationRoot
      (rawProofAndIRoot M baseContext
        (rawSixFieldMasterCode M
          currentLocal currentCrossLevel currentShift currentSubstitution
          currentAxiomSoundness currentFinal)
        nextLocal
        (rawSixFieldMasterIntroductionRoot M baseContext
          currentLocal currentCrossLevel currentShift currentSubstitution
          currentAxiomSoundness currentFinal
          currentLocalRoot currentCrossLevelRoot currentShiftRoot
          currentSubstitutionRoot currentAxiomSoundnessRoot currentFinalRoot)
        nextLocalRoot)).
    exact hbody.
Qed.

(** The remaining premise above is deliberately one staged implication root,
    not two unrelated guard roots.  It is the exact Coq-side boundary for the
    still-missing cross-level induction kernel: the compiler must construct a
    represented proof of [(previous six-field master /\ next local) -> body]
    over the very same witnessed PA context supplied by its prerequisites. *)

End PABoundedRawCodedDynamicTruthNativeCrossLevelGuardRootCompilation.
