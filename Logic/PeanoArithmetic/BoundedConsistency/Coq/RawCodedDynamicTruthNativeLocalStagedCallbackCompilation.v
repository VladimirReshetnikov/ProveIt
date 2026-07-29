(**
  Callback-facing compilation of the first native successor field.

  The local staged-root compiler intentionally leaves its witnessed base
  visible.  This file connects that carried result to the dependency-ordered
  successor callback without replacing the base by the empty context.

  There are two structural steps.  First, a local proof over a witnessed PA
  context is packaged directly as an ordinary [RawCodedPAProofOf], retaining
  the same witness list, context, target, and proof root.  Second, the current
  six-field package is extended automatically by the ordered forty-helper
  batch.  The sole residual root builder receives that exact current package,
  the exact extended context, and the single transform trace selected for the
  next local target.  It cannot substitute an unrelated context or unlinked
  row parameters.

  Positive-graph selection is performed through the adequate paired orbit.
  This detail matters: the law-free graph assertion by itself deliberately
  forgets atomic adequacy, while construction of the represented transform
  trace needs it.  The pointwise selector below therefore retains the exact
  adequate witness until the ordinary proof has been compiled, and only then
  exposes the public positive-graph assertion.
*)

From Stdlib Require Import List.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors
  RawCodedAssignment
  RawCodedContextLists
  RawCodedContextStructure
  RawCodedContextShift
  RawCodedRestrictedPAProof
  RawCodedPALocalProofExistential
  RawCodedPAProvability
  RawCodedTemplateSyntax
  RawCodedTemplateProofCompiler
  RawCodedTemplatePAEmbedding
  RawCodedTemplateStructuralPAAgreement
  RawCodedTruthCertificateMasterBaseBridge
  RawCodedTruthCertificateMasterSuccessorBridge
  RawCodedTruthCertificateMasterFixedHelperBatchExtension
  RawCodedDynamicTruthMixedQFOpaqueQuantifierCellCompilation
  RawCodedDynamicLocalFieldGraph
  RawCodedDynamicTruthLocalDecisionExclusiveBase
  RawCodedDynamicTruthPairedGlobalSuccessorGraph
  RawCodedDynamicTruthPairedGlobalFormulaCodeOrbitGraph
  RawCodedDynamicTruthPairedGlobalOrbitFunctionality
  RawCodedDynamicTruthNativeLocalPositiveGraph
  RawCodedDynamicTruthNativeLocalPositiveExactification
  RawCodedDynamicTruthLocalFieldProjectionCompilation
  RawCodedDynamicTruthImpBranchExclusivity
  RawCodedDynamicTruthPredecessorStateExclusivityCompilation
  RawCodedDynamicTruthNativeLocalProofCompilation
  RawCodedDynamicTruthNativeMasterEndpoint
  RawCodedDynamicTruthMasterSplicedBasePackage
  RawCodedDynamicTruthMasterSplicedSuccessorBridge
  RawCodedDynamicTruthNativeStagedPositiveSuccessor
  RawCodedDynamicTruthNativeLocalStagedRootCompilation
  RawCodedDynamicTruthNativeLocalRowProjectionCompilation.

Module PABoundedRawCodedDynamicTruthNativeLocalStagedCallbackCompilation.

Import ListNotations.
Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedAssignment.
Import PABoundedRawCodedContextLists.
Import PABoundedRawCodedContextStructure.
Import PABoundedRawCodedContextShift.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPAProvability.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedTemplatePAEmbedding.
Import PABoundedRawCodedTemplateStructuralPAAgreement.
Import PABoundedRawCodedTruthCertificateMasterBaseBridge.
Import PABoundedRawCodedTruthCertificateMasterSuccessorBridge.
Import PABoundedRawCodedTruthCertificateMasterFixedHelperBatchExtension.
Import
  PABoundedRawCodedDynamicTruthMixedQFOpaqueQuantifierCellCompilation.
Import PABoundedRawCodedDynamicLocalFieldGraph.
Import PABoundedRawCodedDynamicTruthLocalDecisionExclusiveBase.
Import PABoundedRawCodedDynamicTruthPairedGlobalSuccessorGraph.
Import PABoundedRawCodedDynamicTruthPairedGlobalFormulaCodeOrbitGraph.
Import PABoundedRawCodedDynamicTruthPairedGlobalOrbitFunctionality.
Import PABoundedRawCodedDynamicTruthNativeLocalPositiveGraph.
Import
  PABoundedRawCodedDynamicTruthNativeLocalPositiveExactification.
Import PABoundedRawCodedDynamicTruthLocalFieldProjectionCompilation.
Import PABoundedRawCodedDynamicTruthImpBranchExclusivity.
Import
  PABoundedRawCodedDynamicTruthPredecessorStateExclusivityCompilation.
Import PABoundedRawCodedDynamicTruthNativeLocalProofCompilation.
Import PABoundedRawCodedDynamicTruthNativeMasterEndpoint.
Import PABoundedRawCodedDynamicTruthMasterSplicedBasePackage.
Import PABoundedRawCodedDynamicTruthMasterSplicedSuccessorBridge.
Import PABoundedRawCodedDynamicTruthNativeStagedPositiveSuccessor.
Import PABoundedRawCodedDynamicTruthNativeLocalStagedRootCompilation.
Import PABoundedRawCodedDynamicTruthNativeLocalRowProjectionCompilation.

(** Package a carried local root without changing any of its four logical
    indices.  In particular [baseContext] is stored in the ordinary
    certificate; it is not required to be zero. *)
Theorem raw_codedPAProofOf_dynamicTruthNativeLocal_of_witnessed_root :
    forall (M : RawPAModel) witnessList baseContext target root,
  RawCodedPAAxiomWitnessContext M witnessList baseContext ->
  RawCodedPALocalProofOf M baseContext target root ->
  RawCodedPAProofOf M target
    (rawCodeList3 M (rawNumeralValue M 0) witnessList root).
Proof.
  intros M witnessList baseContext target root
    hwitness [hcoverage hendpoint].
  exists witnessList, root, baseContext.
  split; [reflexivity |].
  repeat split; assumption.
Qed.

(** Existential form used by the graph callback.  The root hidden by
    [RawDynamicTruthNativeLocalFieldRootOn] becomes the root component of
    the ordinary certificate, while the witnessed base remains literal. *)
Corollary raw_codedPAProofOf_dynamicTruthNativeLocalFieldRootOn :
    forall (M : RawPAModel) witnessList baseContext
      sigmaDomain piDomain sigmaEvidence piEvidence,
  RawCodedPAAxiomWitnessContext M witnessList baseContext ->
  RawDynamicTruthNativeLocalFieldRootOn M baseContext
    sigmaDomain piDomain sigmaEvidence piEvidence ->
  exists certificate : M,
    RawCodedPAProofOf M
      (rawDynamicTruthLocalDecisionExclusiveFieldCode M
        sigmaDomain piDomain sigmaEvidence piEvidence)
      certificate.
Proof.
  intros M witnessList baseContext
    sigmaDomain piDomain sigmaEvidence piEvidence
    hwitness [root hroot].
  exists (rawCodeList3 M (rawNumeralValue M 0) witnessList root).
  exact
    (raw_codedPAProofOf_dynamicTruthNativeLocal_of_witnessed_root
      M witnessList baseContext
      (rawDynamicTruthLocalDecisionExclusiveFieldCode M
        sigmaDomain piDomain sigmaEvidence piEvidence)
      root hwitness hroot).
Qed.

(** ------------------------------------------------------------------
    The current-package-linked helper context.

    This relation is the exact unpacking allowed at the residual boundary.
    Its first conjunct is the actual staged current package (including its
    graph witnesses).  Its second conjunct records the context produced by
    extending the proof half of that package with all forty fixed helpers.
    Every listed current target and every helper root uses that one context. *)

Definition RawDynamicTruthNativeLocalCurrentHelperContextAt
    (M : RawPAModel)
    (translation : RawCodedTemplateTranslation M)
    (tail : nat -> M) (level
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      witnessList baseContext : M) (helperRoots : list M) : Prop :=
  RawDynamicTruthNativeStagedPositiveCurrentAt M tail level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal /\
  exists currentLocalRoot currentCrossLevelRoot currentShiftRoot
      currentSubstitutionRoot currentAxiomSoundnessRoot currentFinalRoot : M,
    RawCodedPAAxiomWitnessContext M witnessList baseContext /\
    RawCodedPALocalProofOf M baseContext
      currentLocal currentLocalRoot /\
    RawCodedPALocalProofOf M baseContext
      currentCrossLevel currentCrossLevelRoot /\
    RawCodedPALocalProofOf M baseContext
      currentShift currentShiftRoot /\
    RawCodedPALocalProofOf M baseContext
      currentSubstitution currentSubstitutionRoot /\
    RawCodedPALocalProofOf M baseContext
      currentAxiomSoundness currentAxiomSoundnessRoot /\
    RawCodedPALocalProofOf M baseContext
      currentFinal currentFinalRoot /\
    RawFixedPAHelperBatchLocalProofs M translation baseContext
      rawDynamicTruthReadyAndAllMixedQFPAHelpers helperRoots.

Arguments RawDynamicTruthNativeLocalCurrentHelperContextAt
  M translation tail level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal witnessList baseContext helperRoots
  : clear implicits.

(** Consecutive exact local traces use the same paired global orbit.  The
    successor outputs hidden in the earlier transform are therefore exactly
    the input pair selected by the later trace.  Besides identifying that
    pair, retain the two ternary applications which are the Sigma/Pi evidence
    predicates of the carried current-local field. *)
Theorem raw_dynamicTruthNativeLocalProofTraceAt_consecutive_alignment :
    forall (M : RawPAModel), RawPASatisfies M -> forall
      (tail : nat -> M) predecessorLevel
      currentInputGlobalSigma currentInputGlobalPi
      currentSigmaDomain currentPiDomain
      currentSigmaEvidence currentPiEvidence
      nextInputGlobalSigma nextInputGlobalPi
      nextSigmaDomain nextPiDomain nextSigmaEvidence nextPiEvidence,
  RawDynamicTruthNativeLocalProofTraceAt M tail predecessorLevel
    currentInputGlobalSigma currentInputGlobalPi
    currentSigmaDomain currentPiDomain
    currentSigmaEvidence currentPiEvidence ->
  RawDynamicTruthNativeLocalProofTraceAt M tail
    (raw_succ M predecessorLevel)
    nextInputGlobalSigma nextInputGlobalPi
    nextSigmaDomain nextPiDomain nextSigmaEvidence nextPiEvidence ->
  RawDynamicTruthPairedGlobalSuccessorAt M
    currentInputGlobalSigma currentInputGlobalPi
    (raw_succ M predecessorLevel)
    nextInputGlobalSigma nextInputGlobalPi /\
  RawDynamicTruthLocalTernaryApplication M
    nextInputGlobalSigma currentSigmaEvidence /\
  RawDynamicTruthLocalTernaryApplication M
    nextInputGlobalPi currentPiEvidence.
Proof.
  intros M hPA tail predecessorLevel
    currentInputGlobalSigma currentInputGlobalPi
    currentSigmaDomain currentPiDomain
    currentSigmaEvidence currentPiEvidence
    nextInputGlobalSigma nextInputGlobalPi
    nextSigmaDomain nextPiDomain nextSigmaEvidence nextPiEvidence
    [hcurrentOrbit hcurrentBody] [hnextOrbit _].
  destruct hcurrentBody as
    (inputLevel & successorGlobalSigma & successorGlobalPi &
      inputLevelNumeral & hinputLevel & hsuccessor & hnumeral &
      hcurrentSigmaDomain & hcurrentPiDomain & hcurrentSigmaEvidence &
      hcurrentPiEvidence).
  rewrite hinputLevel in hsuccessor.
  assert (hsuccessorOrbit :
      RawDynamicTruthPairedGlobalFormulaCodeOrbitAt M tail
        (raw_succ M (raw_succ M predecessorLevel))
        successorGlobalSigma successorGlobalPi).
  {
    apply (proj2
      (raw_dynamicTruthPairedGlobalFormulaCodeOrbitAt_succ_iff M hPA
        tail (raw_succ M predecessorLevel)
        successorGlobalSigma successorGlobalPi)).
    exists currentInputGlobalSigma, currentInputGlobalPi.
    split; [exact (proj1 hcurrentOrbit) | exact hsuccessor].
  }
  destruct
    (raw_dynamicTruthPairedGlobalFormulaCodeOrbitAt_functional M hPA
      tail (raw_succ M (raw_succ M predecessorLevel))
      successorGlobalSigma successorGlobalPi
      nextInputGlobalSigma nextInputGlobalPi
      hsuccessorOrbit (proj1 hnextOrbit)) as [hsigma hpi].
  subst nextInputGlobalSigma. subst nextInputGlobalPi.
  split; [exact hsuccessor |].
  split; assumption.
Qed.

(** At a positive current level the public spliced graph determines an exact
    adequate local trace.  The master package did not retain adequacy as a
    field, but exactification recovers it by constructing a fresh adequate
    positive witness and using functionality to identify its output with the
    literal [currentLocal] target.  The proof root below is the one already
    carried by the common helper context; it is not regenerated. *)
Theorem raw_dynamicTruthNativeLocalCurrentHelperContextAt_successor_trace :
    forall (M : RawPAModel), RawPASatisfies M ->
  forall (translation : RawCodedTemplateTranslation M)
      (tail : nat -> M) level predecessorLevel
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      witnessList baseContext helperRoots,
  RawDynamicTruthNativeLocalCurrentHelperContextAt M translation
    tail level currentLocal currentCrossLevel currentShift
    currentSubstitution currentAxiomSoundness currentFinal
    witnessList baseContext helperRoots ->
  level = raw_succ M predecessorLevel ->
  exists inputGlobalSigma inputGlobalPi
      sigmaDomain piDomain sigmaEvidence piEvidence currentLocalRoot : M,
    currentLocal = rawDynamicTruthLocalDecisionExclusiveFieldCode M
      sigmaDomain piDomain sigmaEvidence piEvidence /\
    RawDynamicTruthNativeLocalProofTraceAt M tail predecessorLevel
      inputGlobalSigma inputGlobalPi sigmaDomain piDomain
      sigmaEvidence piEvidence /\
    RawCodedPALocalProofOf M baseContext currentLocal currentLocalRoot.
Proof.
  intros M hPA translation tail level predecessorLevel
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal witnessList baseContext helperRoots
    [hcurrent hhelpers] hlevel.
  destruct hcurrent as [hgraphs _].
  unfold RawSixFieldMasterGraphWitnessesAt in hgraphs.
  destruct hgraphs as [hcurrentLocalGraph _].
  destruct hhelpers as
    (currentLocalRoot & currentCrossLevelRoot & currentShiftRoot &
      currentSubstitutionRoot & currentAxiomSoundnessRoot &
      currentFinalRoot & hwitness & hcurrentLocal & _).
  rewrite hlevel in hcurrentLocalGraph.
  unfold dynamicTruthNativeSplicedLocalFieldGraph,
    dynamicTruthSplicedLocalFieldGraph in hcurrentLocalGraph.
  apply (proj1
    (raw_dynamicLocalFieldGraph_succ_iff M hPA
      dynamicTruthLocalDecisionExclusiveBaseFormulaCodeGraph
      dynamicTruthNativeLocalPositiveGraph tail predecessorLevel
      currentLocal)) in hcurrentLocalGraph.
  apply (proj1
    (raw_sat_dynamicTruthNativeLocalPositiveGraph_iff M tail
      predecessorLevel currentLocal)) in hcurrentLocalGraph.
  destruct
    (raw_dynamicTruthNativeLocalPositiveAt_exact M hPA tail
      predecessorLevel currentLocal hcurrentLocalGraph) as
    (inputGlobalSigma & inputGlobalPi & hadequateOrbit & htransform).
  destruct
    (raw_dynamicTruthNativeLocalProofTraceAt_of_transform M tail
      predecessorLevel inputGlobalSigma inputGlobalPi currentLocal
      hadequateOrbit htransform) as
    (sigmaDomain & piDomain & sigmaEvidence & piEvidence &
      hfield & htrace).
  exists inputGlobalSigma, inputGlobalPi,
    sigmaDomain, piDomain, sigmaEvidence, piEvidence, currentLocalRoot.
  split; [exact hfield |].
  split; assumption.
Qed.

(** The zero/successor decomposition is internal to PA and therefore covers
    nonstandard carrier levels as well.  This theorem is the exact current
    local coordinate retained by the callback: at zero it is the quoted
    fixed base theorem; at a successor it carries an adequate orbit trace for
    the preceding level.  Both alternatives retain a proof of the literal
    [currentLocal] target in the unchanged helper context. *)
Theorem raw_dynamicTruthNativeLocalCurrentHelperContextAt_exact_cases :
    forall (M : RawPAModel), RawPASatisfies M ->
  forall (translation : RawCodedTemplateTranslation M)
      (tail : nat -> M) level
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      witnessList baseContext helperRoots,
  RawDynamicTruthNativeLocalCurrentHelperContextAt M translation
    tail level currentLocal currentCrossLevel currentShift
    currentSubstitution currentAxiomSoundness currentFinal
    witnessList baseContext helperRoots ->
  (exists currentLocalRoot : M,
      level = raw_zero M /\
      currentLocal = rawQuotedFormulaCode M
        dynamicTruthLocalDecisionExclusiveBaseFormula /\
      RawCodedPALocalProofOf M baseContext currentLocal currentLocalRoot) \/
  (exists predecessorLevel inputGlobalSigma inputGlobalPi
      sigmaDomain piDomain sigmaEvidence piEvidence currentLocalRoot : M,
      level = raw_succ M predecessorLevel /\
      currentLocal = rawDynamicTruthLocalDecisionExclusiveFieldCode M
        sigmaDomain piDomain sigmaEvidence piEvidence /\
      RawDynamicTruthNativeLocalProofTraceAt M tail predecessorLevel
        inputGlobalSigma inputGlobalPi sigmaDomain piDomain
        sigmaEvidence piEvidence /\
      RawCodedPALocalProofOf M baseContext currentLocal currentLocalRoot).
Proof.
  intros M hPA translation tail level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal witnessList baseContext helperRoots
    hcontext.
  destruct (raw_assignment_zero_or_successor M hPA level) as
    [hzero | [predecessorLevel hsuccessor]].
  - left.
    destruct hcontext as [[hgraphs _] hhelpers].
    unfold RawSixFieldMasterGraphWitnessesAt in hgraphs.
    destruct hgraphs as [hcurrentLocalGraph _].
    destruct hhelpers as
      (currentLocalRoot & currentCrossLevelRoot & currentShiftRoot &
        currentSubstitutionRoot & currentAxiomSoundnessRoot &
        currentFinalRoot & hwitness & hcurrentLocal & _).
    rewrite hzero in hcurrentLocalGraph.
    unfold dynamicTruthNativeSplicedLocalFieldGraph,
      dynamicTruthSplicedLocalFieldGraph in hcurrentLocalGraph.
    apply (proj1
      (raw_dynamicLocalFieldGraph_zero_iff M hPA
        dynamicTruthLocalDecisionExclusiveBaseFormulaCodeGraph
        dynamicTruthNativeLocalPositiveGraph tail currentLocal))
      in hcurrentLocalGraph.
    apply (proj1
      (dynamicTruthLocalDecisionExclusiveBaseFormulaCodeGraph_representation
        M hPA tail (raw_zero M) currentLocal)) in hcurrentLocalGraph.
    exists currentLocalRoot.
    split; [exact hzero |].
    split; assumption.
  - right.
    destruct
      (raw_dynamicTruthNativeLocalCurrentHelperContextAt_successor_trace
        M hPA translation tail level predecessorLevel
        currentLocal currentCrossLevel currentShift currentSubstitution
        currentAxiomSoundness currentFinal witnessList baseContext
        helperRoots hcontext hsuccessor) as
      (inputGlobalSigma & inputGlobalPi & sigmaDomain & piDomain &
        sigmaEvidence & piEvidence & currentLocalRoot & hfield & htrace &
        hcurrentLocal).
    exists predecessorLevel, inputGlobalSigma, inputGlobalPi,
      sigmaDomain, piDomain, sigmaEvidence, piEvidence, currentLocalRoot.
    split; [exact hsuccessor |].
    split; [exact hfield |].
    split; assumption.
Qed.

(** Information shared by a positive current local field and the next local
    trace.  This is the exact predecessor package needed by the remaining
    collision compilers: it contains the carried local proof, its own exact
    trace, and the equations identifying its successor globals with the
    next trace's input pair. *)
Record RawDynamicTruthNativeLocalAlignedPredecessorAt
    (M : RawPAModel) (tail : nat -> M) (predecessorLevel baseContext
      currentLocal nextInputGlobalSigma nextInputGlobalPi : M) : Type := {
  rawDynamicTruthNativeLocalAligned_currentInputGlobalSigma : M;
  rawDynamicTruthNativeLocalAligned_currentInputGlobalPi : M;
  rawDynamicTruthNativeLocalAligned_currentSigmaDomain : M;
  rawDynamicTruthNativeLocalAligned_currentPiDomain : M;
  rawDynamicTruthNativeLocalAligned_currentSigmaEvidence : M;
  rawDynamicTruthNativeLocalAligned_currentPiEvidence : M;
  rawDynamicTruthNativeLocalAligned_currentLocalRoot : M;
  rawDynamicTruthNativeLocalAligned_currentField :
    currentLocal = rawDynamicTruthLocalDecisionExclusiveFieldCode M
      rawDynamicTruthNativeLocalAligned_currentSigmaDomain
      rawDynamicTruthNativeLocalAligned_currentPiDomain
      rawDynamicTruthNativeLocalAligned_currentSigmaEvidence
      rawDynamicTruthNativeLocalAligned_currentPiEvidence;
  rawDynamicTruthNativeLocalAligned_currentTrace :
    RawDynamicTruthNativeLocalProofTraceAt M tail predecessorLevel
      rawDynamicTruthNativeLocalAligned_currentInputGlobalSigma
      rawDynamicTruthNativeLocalAligned_currentInputGlobalPi
      rawDynamicTruthNativeLocalAligned_currentSigmaDomain
      rawDynamicTruthNativeLocalAligned_currentPiDomain
      rawDynamicTruthNativeLocalAligned_currentSigmaEvidence
      rawDynamicTruthNativeLocalAligned_currentPiEvidence;
  rawDynamicTruthNativeLocalAligned_currentProof :
    RawCodedPALocalProofOf M baseContext currentLocal
      rawDynamicTruthNativeLocalAligned_currentLocalRoot;
  rawDynamicTruthNativeLocalAligned_decisionProjection :
    RawCodedPALocalProofOf M baseContext
      (rawDynamicTruthLocalFormulaAll3Code M
        (rawDynamicTruthLocalDecisionCode M
          rawDynamicTruthNativeLocalAligned_currentSigmaDomain
          rawDynamicTruthNativeLocalAligned_currentPiDomain
          rawDynamicTruthNativeLocalAligned_currentSigmaEvidence
          rawDynamicTruthNativeLocalAligned_currentPiEvidence))
      (rawDynamicTruthLocalDecisionProjectionRoot M baseContext
        rawDynamicTruthNativeLocalAligned_currentSigmaDomain
        rawDynamicTruthNativeLocalAligned_currentPiDomain
        rawDynamicTruthNativeLocalAligned_currentSigmaEvidence
        rawDynamicTruthNativeLocalAligned_currentPiEvidence
        rawDynamicTruthNativeLocalAligned_currentLocalRoot);
  rawDynamicTruthNativeLocalAligned_exclusiveProjection :
    RawCodedPALocalProofOf M baseContext
      (rawDynamicTruthLocalFormulaAll3Code M
        (rawDynamicTruthLocalExclusiveCode M
          rawDynamicTruthNativeLocalAligned_currentSigmaDomain
          rawDynamicTruthNativeLocalAligned_currentPiDomain
          rawDynamicTruthNativeLocalAligned_currentSigmaEvidence
          rawDynamicTruthNativeLocalAligned_currentPiEvidence))
      (rawDynamicTruthLocalExclusiveProjectionRoot M baseContext
        rawDynamicTruthNativeLocalAligned_currentSigmaDomain
        rawDynamicTruthNativeLocalAligned_currentPiDomain
        rawDynamicTruthNativeLocalAligned_currentSigmaEvidence
        rawDynamicTruthNativeLocalAligned_currentPiEvidence
        rawDynamicTruthNativeLocalAligned_currentLocalRoot);
  rawDynamicTruthNativeLocalAligned_successor :
    RawDynamicTruthPairedGlobalSuccessorAt M
      rawDynamicTruthNativeLocalAligned_currentInputGlobalSigma
      rawDynamicTruthNativeLocalAligned_currentInputGlobalPi
      (raw_succ M predecessorLevel)
      nextInputGlobalSigma nextInputGlobalPi;
  rawDynamicTruthNativeLocalAligned_sigmaApplication :
    RawDynamicTruthLocalTernaryApplication M nextInputGlobalSigma
      rawDynamicTruthNativeLocalAligned_currentSigmaEvidence;
  rawDynamicTruthNativeLocalAligned_piApplication :
    RawDynamicTruthLocalTernaryApplication M nextInputGlobalPi
      rawDynamicTruthNativeLocalAligned_currentPiEvidence
}.

Arguments RawDynamicTruthNativeLocalAlignedPredecessorAt
  M tail predecessorLevel baseContext currentLocal
  nextInputGlobalSigma nextInputGlobalPi : clear implicits.

(** The aligned package already contains the source exclusivity proof.  A
    table/application bridge can therefore be consumed immediately, with no
    re-projection of the current conjunction and no independently selected
    predecessor root. *)
Theorem raw_dynamicTruthNativeLocalAligned_predecessorRoot_of_bridge :
    forall (M : RawPAModel), RawPASatisfies M ->
  forall (tail : nat -> M) predecessorLevel baseContext currentLocal
      nextInputGlobalSigma nextInputGlobalPi
      (aligned : RawDynamicTruthNativeLocalAlignedPredecessorAt M tail
        predecessorLevel baseContext currentLocal
        nextInputGlobalSigma nextInputGlobalPi),
  RawContextListRealizable M baseContext ->
  RawContextShift M baseContext baseContext ->
  RawDynamicTruthPredecessorStateApplicationBridgeAt M baseContext
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
      nextInputGlobalSigma nextInputGlobalPi aligned) ->
  exists predecessorRoot,
    RawCodedPALocalProofOf M baseContext
      (rawDynamicTruthImpPredecessorStateExclusivityCode M)
      predecessorRoot.
Proof.
  intros M hPA tail predecessorLevel baseContext currentLocal
    nextInputGlobalSigma nextInputGlobalPi aligned hcontext hshift hbridge.
  exact
    (raw_dynamicTruthImpPredecessorStateExclusivityRoot_of_local_exclusive
      M hPA baseContext
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
        nextInputGlobalSigma nextInputGlobalPi aligned)
      (rawDynamicTruthLocalExclusiveProjectionRoot M baseContext
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
          nextInputGlobalSigma nextInputGlobalPi aligned)
        (rawDynamicTruthNativeLocalAligned_currentLocalRoot M tail
          predecessorLevel baseContext currentLocal
          nextInputGlobalSigma nextInputGlobalPi aligned))
      hcontext hshift
      (rawDynamicTruthNativeLocalAligned_exclusiveProjection M tail
        predecessorLevel baseContext currentLocal
        nextInputGlobalSigma nextInputGlobalPi aligned)
      hbridge).
Qed.

(** Enrich the exhaustive current-field cases with the next trace.  The zero
    alternative is unchanged; in the successor alternative all orbit and
    application alignment is performed once and stored in the record above. *)
Theorem
    raw_dynamicTruthNativeLocalCurrentHelperContextAt_exact_cases_aligned_with_next :
    forall (M : RawPAModel), RawPASatisfies M ->
  forall (translation : RawCodedTemplateTranslation M)
      (tail : nat -> M) level
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      witnessList baseContext helperRoots
      nextInputGlobalSigma nextInputGlobalPi
      nextSigmaDomain nextPiDomain nextSigmaEvidence nextPiEvidence,
  RawDynamicTruthNativeLocalCurrentHelperContextAt M translation
    tail level currentLocal currentCrossLevel currentShift
    currentSubstitution currentAxiomSoundness currentFinal
    witnessList baseContext helperRoots ->
  RawDynamicTruthNativeLocalProofTraceAt M tail level
    nextInputGlobalSigma nextInputGlobalPi
    nextSigmaDomain nextPiDomain nextSigmaEvidence nextPiEvidence ->
  (exists currentLocalRoot : M,
      level = raw_zero M /\
      currentLocal = rawQuotedFormulaCode M
        dynamicTruthLocalDecisionExclusiveBaseFormula /\
      RawCodedPALocalProofOf M baseContext currentLocal currentLocalRoot) \/
  (exists predecessorLevel : M,
      level = raw_succ M predecessorLevel /\
      exists aligned :
          RawDynamicTruthNativeLocalAlignedPredecessorAt M tail
            predecessorLevel baseContext currentLocal
            nextInputGlobalSigma nextInputGlobalPi,
        True).
Proof.
  intros M hPA translation tail level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal witnessList baseContext helperRoots
    nextInputGlobalSigma nextInputGlobalPi
    nextSigmaDomain nextPiDomain nextSigmaEvidence nextPiEvidence
    hcontext hnextTrace.
  destruct
    (raw_dynamicTruthNativeLocalCurrentHelperContextAt_exact_cases
      M hPA translation tail level currentLocal currentCrossLevel
      currentShift currentSubstitution currentAxiomSoundness currentFinal
      witnessList baseContext helperRoots hcontext) as
    [(currentLocalRoot & hzero & hfield & hcurrentProof) |
      (predecessorLevel & currentInputGlobalSigma & currentInputGlobalPi &
        currentSigmaDomain & currentPiDomain & currentSigmaEvidence &
        currentPiEvidence & currentLocalRoot & hlevel & hfield &
        hcurrentTrace & hcurrentProof)].
  - left. exists currentLocalRoot.
    split; [exact hzero |].
    split; assumption.
  - right.
    assert (hnextTraceAtSuccessor :
        RawDynamicTruthNativeLocalProofTraceAt M tail
          (raw_succ M predecessorLevel)
          nextInputGlobalSigma nextInputGlobalPi
          nextSigmaDomain nextPiDomain nextSigmaEvidence nextPiEvidence).
    { rewrite <- hlevel. exact hnextTrace. }
    destruct
      (raw_dynamicTruthNativeLocalProofTraceAt_consecutive_alignment
        M hPA tail predecessorLevel
        currentInputGlobalSigma currentInputGlobalPi
        currentSigmaDomain currentPiDomain currentSigmaEvidence
        currentPiEvidence nextInputGlobalSigma nextInputGlobalPi
        nextSigmaDomain nextPiDomain nextSigmaEvidence nextPiEvidence
        hcurrentTrace hnextTraceAtSuccessor) as
      (hsuccessor & hsigmaApplication & hpiApplication).
    assert (hcurrentFieldProof :
        RawCodedPALocalProofOf M baseContext
          (rawDynamicTruthLocalDecisionExclusiveFieldCode M
            currentSigmaDomain currentPiDomain currentSigmaEvidence
            currentPiEvidence) currentLocalRoot).
    { rewrite <- hfield. exact hcurrentProof. }
    pose proof
      (raw_dynamicTruthLocalDecisionExclusiveProjectedRootsAt_of_local
        M hPA baseContext currentSigmaDomain currentPiDomain
        currentSigmaEvidence currentPiEvidence currentLocalRoot
        hcurrentFieldProof) as hprojected.
    destruct hprojected as [hdecisionProjection hexclusiveProjection].
    exists predecessorLevel.
    split; [exact hlevel |].
    exists
      {| rawDynamicTruthNativeLocalAligned_currentInputGlobalSigma :=
           currentInputGlobalSigma;
         rawDynamicTruthNativeLocalAligned_currentInputGlobalPi :=
           currentInputGlobalPi;
         rawDynamicTruthNativeLocalAligned_currentSigmaDomain :=
           currentSigmaDomain;
         rawDynamicTruthNativeLocalAligned_currentPiDomain :=
           currentPiDomain;
         rawDynamicTruthNativeLocalAligned_currentSigmaEvidence :=
           currentSigmaEvidence;
         rawDynamicTruthNativeLocalAligned_currentPiEvidence :=
           currentPiEvidence;
         rawDynamicTruthNativeLocalAligned_currentLocalRoot :=
           currentLocalRoot;
         rawDynamicTruthNativeLocalAligned_currentField := hfield;
         rawDynamicTruthNativeLocalAligned_currentTrace := hcurrentTrace;
         rawDynamicTruthNativeLocalAligned_currentProof := hcurrentProof;
         rawDynamicTruthNativeLocalAligned_decisionProjection :=
           hdecisionProjection;
         rawDynamicTruthNativeLocalAligned_exclusiveProjection :=
           hexclusiveProjection;
         rawDynamicTruthNativeLocalAligned_successor := hsuccessor;
         rawDynamicTruthNativeLocalAligned_sigmaApplication :=
           hsigmaApplication;
         rawDynamicTruthNativeLocalAligned_piApplication :=
           hpiApplication |}.
    exact I.
Qed.

(** The helper extension is not part of the residual.  It follows uniformly
    from the proof half of the actual current package and preserves all six
    current targets while installing the ordered forty-helper family. *)
Theorem raw_dynamicTruthNativeLocalCurrentHelperContextAt_exists :
    forall (M : RawPAModel), RawPASatisfies M ->
  forall (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall (tail : nat -> M) level
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal,
  RawDynamicTruthNativeStagedPositiveCurrentAt M tail level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal ->
  exists witnessList baseContext : M, exists helperRoots : list M,
    RawDynamicTruthNativeLocalCurrentHelperContextAt M translation
      tail level currentLocal currentCrossLevel currentShift
      currentSubstitution currentAxiomSoundness currentFinal
      witnessList baseContext helperRoots.
Proof.
  intros M hPA translation hagreement tail level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal hcurrent.
  pose proof
    (raw_sixFieldMasterCommonContextProofsWithAllMixedQFHelpers
      M hPA translation hagreement
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal (proj2 hcurrent))
    as hhelpersPackage.
  unfold RawSixFieldMasterCommonContextProofsWithFixedPAHelperBatchOf
    in hhelpersPackage.
  destruct hhelpersPackage as
    (witnessList & baseContext & currentLocalRoot &
      currentCrossLevelRoot & currentShiftRoot &
      currentSubstitutionRoot & currentAxiomSoundnessRoot &
      currentFinalRoot & helperRoots & hwitness & hcurrentLocal &
      hcurrentCrossLevel & hcurrentShift & hcurrentSubstitution &
      hcurrentAxiomSoundness & hcurrentFinal & hhelpers).
  exists witnessList, baseContext, helperRoots.
  split; [exact hcurrent |].
  exists currentLocalRoot, currentCrossLevelRoot, currentShiftRoot,
    currentSubstitutionRoot, currentAxiomSoundnessRoot, currentFinalRoot.
  split; [exact hwitness |].
  split; [exact hcurrentLocal |].
  split; [exact hcurrentCrossLevel |].
  split; [exact hcurrentShift |].
  split; [exact hcurrentSubstitution |].
  split; [exact hcurrentAxiomSoundness |].
  split; [exact hcurrentFinal | exact hhelpers].
Qed.

(** The only proof-producing residual.  The exact row witnesses are supplied
    by the same local transform trace, and the returned staged package is
    indexed by the base context linked above to the actual current package.
    All helper compilation, adequacy, row extraction, collision resources,
    and final certificate packaging remain outside this interface. *)
Definition RawDynamicTruthNativeLocalCurrentStagedRootBuilder
    (M : RawPAModel)
    (translation : RawCodedTemplateTranslation M) : Prop :=
  forall (tail : nat -> M) level
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      witnessList baseContext (helperRoots : list M)
      inputGlobalSigma inputGlobalPi
      sigmaDomain piDomain sigmaEvidence piEvidence,
    RawDynamicTruthNativeLocalCurrentHelperContextAt M translation
      tail level currentLocal currentCrossLevel currentShift
      currentSubstitution currentAxiomSoundness currentFinal
      witnessList baseContext helperRoots ->
    RawDynamicTruthNativeLocalProofTraceAt M tail level
      inputGlobalSigma inputGlobalPi sigmaDomain piDomain
      sigmaEvidence piEvidence ->
    forall sigmaRowDomain piRowDomain
        lowerPiApplication lowerSigmaApplication,
      RawDynamicTruthNativeLocalExactRowParametersAt M level
        inputGlobalSigma inputGlobalPi sigmaEvidence piEvidence
        sigmaRowDomain piRowDomain
        lowerPiApplication lowerSigmaApplication ->
      RawDynamicTruthNativeLocalStagedRootsAt M baseContext
        sigmaDomain piDomain sigmaEvidence piEvidence
        sigmaRowDomain piRowDomain
        lowerPiApplication lowerSigmaApplication.

Arguments RawDynamicTruthNativeLocalCurrentStagedRootBuilder
  M translation : clear implicits.

(** The preferred residual builder uses the reduced staged package.  The two
    row projections are no longer callback inputs: they are reconstructed
    from the exact trace and the two literal row roots by the context-safe
    compiler imported above. *)
Definition RawDynamicTruthNativeLocalCurrentReducedStagedRootBuilder
    (M : RawPAModel)
    (translation : RawCodedTemplateTranslation M) : Prop :=
  forall (tail : nat -> M) level
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      witnessList baseContext (helperRoots : list M)
      inputGlobalSigma inputGlobalPi
      sigmaDomain piDomain sigmaEvidence piEvidence,
    RawDynamicTruthNativeLocalCurrentHelperContextAt M translation
      tail level currentLocal currentCrossLevel currentShift
      currentSubstitution currentAxiomSoundness currentFinal
      witnessList baseContext helperRoots ->
    RawDynamicTruthNativeLocalProofTraceAt M tail level
      inputGlobalSigma inputGlobalPi sigmaDomain piDomain
      sigmaEvidence piEvidence ->
    forall sigmaRowDomain piRowDomain
        lowerPiApplication lowerSigmaApplication,
      RawDynamicTruthNativeLocalExactRowParametersAt M level
        inputGlobalSigma inputGlobalPi sigmaEvidence piEvidence
        sigmaRowDomain piRowDomain
        lowerPiApplication lowerSigmaApplication ->
      RawDynamicTruthNativeLocalReducedStagedRootsAt M baseContext
        sigmaDomain piDomain sigmaEvidence piEvidence
        sigmaRowDomain piRowDomain
        lowerPiApplication lowerSigmaApplication.

Arguments RawDynamicTruthNativeLocalCurrentReducedStagedRootBuilder
  M translation : clear implicits.

(** A pointwise version of the existing decision/exclusivity compiler.  The
    staged callback presents one current package at one [tail, level], so a
    global compiler would be needlessly stronger and could not honestly be
    derived from that pointwise input. *)
Definition RawDynamicTruthNativeLocalDecisionExclusiveProofCompilerAt
    (M : RawPAModel) (tail : nat -> M) (level : M) : Prop :=
  forall inputGlobalSigma inputGlobalPi fieldCode,
    RawDynamicTruthPairedGlobalFormulaCodeAdequateOrbitAt M
      tail (raw_succ M level) inputGlobalSigma inputGlobalPi ->
    RawDynamicTruthNativeLocalFieldTransformAt M
      inputGlobalSigma inputGlobalPi level fieldCode ->
    exists certificate : M,
      RawCodedPAProofOf M fieldCode certificate.

Arguments RawDynamicTruthNativeLocalDecisionExclusiveProofCompilerAt
  M tail level : clear implicits.

(** Reduce the current-linked residual to the pointwise compiler.  The
    transform is unpacked exactly once.  Its field equation is retained
    until the carried local root has been packaged as an ordinary proof of
    precisely that selected target. *)
Theorem
    raw_dynamicTruthNativeLocalDecisionExclusiveProofCompilerAt_of_current_builder :
    forall (M : RawPAModel), RawPASatisfies M ->
  forall (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  RawDynamicTruthNativeLocalCurrentStagedRootBuilder M translation ->
  forall (tail : nat -> M) level
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal,
  RawDynamicTruthNativeStagedPositiveCurrentAt M tail level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal ->
  RawDynamicTruthNativeLocalDecisionExclusiveProofCompilerAt
    M tail level.
Proof.
  intros M hPA translation hagreement hbuilder tail level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal hcurrent.
  destruct
    (raw_dynamicTruthNativeLocalCurrentHelperContextAt_exists
      M hPA translation hagreement tail level
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal hcurrent)
    as (witnessList & baseContext & helperRoots & hcurrentHelpers).
  intros inputGlobalSigma inputGlobalPi fieldCode
    hadequateOrbit htransform.
  destruct (raw_dynamicTruthNativeLocalProofTraceAt_of_transform
    M tail level inputGlobalSigma inputGlobalPi fieldCode
    hadequateOrbit htransform) as
    (sigmaDomain & piDomain & sigmaEvidence & piEvidence &
      hfieldCode & htrace).
  destruct (raw_dynamicTruthNativeLocalProofTraceAt_exposes_exact_rows
    M tail level inputGlobalSigma inputGlobalPi
    sigmaDomain piDomain sigmaEvidence piEvidence htrace) as
    (sigmaRowDomain & piRowDomain & lowerPiApplication &
      lowerSigmaApplication & hlinked).
  pose proof (hbuilder tail level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal
    witnessList baseContext helperRoots
    inputGlobalSigma inputGlobalPi
    sigmaDomain piDomain sigmaEvidence piEvidence
    hcurrentHelpers htrace
    sigmaRowDomain piRowDomain lowerPiApplication lowerSigmaApplication
    hlinked) as hstaged.
  pose proof hcurrentHelpers as hcontextFields.
  destruct hcontextFields as
    [_ (currentLocalRoot & currentCrossLevelRoot & currentShiftRoot &
      currentSubstitutionRoot & currentAxiomSoundnessRoot &
      currentFinalRoot & hwitness & hcurrentLocal &
      hcurrentCrossLevel & hcurrentShift & hcurrentSubstitution &
      hcurrentAxiomSoundness & hcurrentFinal & hhelpers)].
  pose proof
    (raw_dynamicTruthNativeLocalFieldRootOn_of_staged_roots_and_40_helpers
      M hPA translation witnessList baseContext helperRoots
      tail level inputGlobalSigma inputGlobalPi
      sigmaDomain piDomain sigmaEvidence piEvidence
      sigmaRowDomain piRowDomain lowerPiApplication lowerSigmaApplication
      hagreement hwitness hhelpers htrace hlinked hstaged)
    as hfieldRoot.
  rewrite hfieldCode.
  exact
    (raw_codedPAProofOf_dynamicTruthNativeLocalFieldRootOn
      M witnessList baseContext
      sigmaDomain piDomain sigmaEvidence piEvidence
      hwitness hfieldRoot).
Qed.

(** Reduced-builder counterpart of the pointwise callback compiler.  This is
    intentionally a separate theorem so existing clients of the historical
    staged package remain source-compatible while dependency-ordered clients
    can adopt the smaller residual immediately. *)
Theorem
    raw_dynamicTruthNativeLocalDecisionExclusiveProofCompilerAt_of_reduced_current_builder :
    forall (M : RawPAModel), RawPASatisfies M ->
  forall (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  RawDynamicTruthNativeLocalCurrentReducedStagedRootBuilder M translation ->
  forall (tail : nat -> M) level
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal,
  RawDynamicTruthNativeStagedPositiveCurrentAt M tail level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal ->
  RawDynamicTruthNativeLocalDecisionExclusiveProofCompilerAt
    M tail level.
Proof.
  intros M hPA translation hagreement hbuilder tail level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal hcurrent.
  destruct
    (raw_dynamicTruthNativeLocalCurrentHelperContextAt_exists
      M hPA translation hagreement tail level
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal hcurrent)
    as (witnessList & baseContext & helperRoots & hcurrentHelpers).
  intros inputGlobalSigma inputGlobalPi fieldCode
    hadequateOrbit htransform.
  destruct (raw_dynamicTruthNativeLocalProofTraceAt_of_transform
    M tail level inputGlobalSigma inputGlobalPi fieldCode
    hadequateOrbit htransform) as
    (sigmaDomain & piDomain & sigmaEvidence & piEvidence &
      hfieldCode & htrace).
  destruct (raw_dynamicTruthNativeLocalProofTraceAt_exposes_exact_rows
    M tail level inputGlobalSigma inputGlobalPi
    sigmaDomain piDomain sigmaEvidence piEvidence htrace) as
    (sigmaRowDomain & piRowDomain & lowerPiApplication &
      lowerSigmaApplication & hlinked).
  pose proof (hbuilder tail level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal
    witnessList baseContext helperRoots
    inputGlobalSigma inputGlobalPi
    sigmaDomain piDomain sigmaEvidence piEvidence
    hcurrentHelpers htrace
    sigmaRowDomain piRowDomain lowerPiApplication lowerSigmaApplication
    hlinked) as hstaged.
  pose proof hcurrentHelpers as hcontextFields.
  destruct hcontextFields as
    [_ (currentLocalRoot & currentCrossLevelRoot & currentShiftRoot &
      currentSubstitutionRoot & currentAxiomSoundnessRoot &
      currentFinalRoot & hwitness & hcurrentLocal &
      hcurrentCrossLevel & hcurrentShift & hcurrentSubstitution &
      hcurrentAxiomSoundness & hcurrentFinal & hhelpers)].
  pose proof
    (raw_dynamicTruthNativeLocalFieldRootOn_of_reduced_staged_roots_and_40_helpers
      M hPA translation witnessList baseContext helperRoots
      tail level inputGlobalSigma inputGlobalPi
      sigmaDomain piDomain sigmaEvidence piEvidence
      sigmaRowDomain piRowDomain lowerPiApplication lowerSigmaApplication
      hagreement hwitness hhelpers htrace hlinked hstaged)
    as hfieldRoot.
  rewrite hfieldCode.
  exact
    (raw_codedPAProofOf_dynamicTruthNativeLocalFieldRootOn
      M witnessList baseContext
      sigmaDomain piDomain sigmaEvidence piEvidence
      hwitness hfieldRoot).
Qed.

(** Exact positive selection for one callback invocation.  This is the
    pointwise body of native positive-graph proof totality.  The adequate
    orbit and its generated transform stay synchronized until [hcompiler]
    returns a proof; the public result then forgets adequacy, as required by
    the graph's exact law-free semantics. *)
Theorem raw_dynamicTruthNativeLocalPositiveProof_exists_of_compilerAt :
    forall (M : RawPAModel), RawPASatisfies M ->
  forall (tail : nat -> M) level,
  RawDynamicTruthNativeLocalDecisionExclusiveProofCompilerAt M tail level ->
  exists fieldCode certificate : M,
    raw_formula_sat M
      (scons M fieldCode (scons M level tail))
      dynamicTruthNativeLocalPositiveGraph /\
    RawCodedPAProofOf M fieldCode certificate.
Proof.
  intros M hPA tail level hcompiler.
  destruct
    (dynamicTruthPairedGlobalFormulaCodeOrbitGraph_raw_adequate_total
      M hPA tail (raw_succ M level)) as
    (inputGlobalSigma & inputGlobalPi & horbit &
      hinputSigma & hinputPi).
  assert (hadequateOrbit :
      RawDynamicTruthPairedGlobalFormulaCodeAdequateOrbitAt M
        tail (raw_succ M level) inputGlobalSigma inputGlobalPi).
  {
    apply (proj2
      (raw_dynamicTruthPairedGlobalFormulaCodeAdequateOrbitAt_iff M
        tail (raw_succ M level) inputGlobalSigma inputGlobalPi)).
    split.
    - apply (proj1
        (raw_sat_dynamicTruthPairedGlobalFormulaCodeOrbitGraph_iff M
          tail (raw_succ M level) inputGlobalSigma inputGlobalPi)).
      exact horbit.
    - split; assumption.
  }
  destruct
    (dynamicTruthNativeLocalFieldTransformGraph_raw_total_on_adequate
      M hPA tail inputGlobalSigma inputGlobalPi level
      hinputSigma hinputPi) as [fieldCode htransformSat].
  pose proof (proj1
    (raw_sat_dynamicTruthNativeLocalFieldTransformGraph_iff M tail
      inputGlobalSigma inputGlobalPi level fieldCode)
    htransformSat) as htransform.
  destruct (hcompiler inputGlobalSigma inputGlobalPi fieldCode
    hadequateOrbit htransform) as [certificate hcertificate].
  exists fieldCode, certificate. split; [|exact hcertificate].
  apply (proj2 (raw_sat_dynamicTruthNativeLocalPositiveGraph_iff
    M tail level fieldCode)).
  exists inputGlobalSigma, inputGlobalPi. split.
  - apply (proj1
      (raw_dynamicTruthPairedGlobalFormulaCodeAdequateOrbitAt_iff M
        tail (raw_succ M level) inputGlobalSigma inputGlobalPi)).
    exact hadequateOrbit.
  - exact htransform.
Qed.

(** Callback endpoint.  All context construction and graph selection are
    discharged above; only the current-package-linked staged root builder is
    assumed. *)
Theorem raw_dynamicTruthNativeStagedNextLocalCompiler_of_current_builder :
    forall (M : RawPAModel), RawPASatisfies M ->
  forall (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  RawDynamicTruthNativeLocalCurrentStagedRootBuilder M translation ->
  RawDynamicTruthNativeStagedNextLocalCompiler M.
Proof.
  intros M hPA translation hagreement hbuilder
    tail level currentLocal currentCrossLevel currentShift
    currentSubstitution currentAxiomSoundness currentFinal hcurrent.
  pose proof
    (raw_dynamicTruthNativeLocalDecisionExclusiveProofCompilerAt_of_current_builder
      M hPA translation hagreement hbuilder tail level
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal hcurrent) as hcompiler.
  destruct
    (raw_dynamicTruthNativeLocalPositiveProof_exists_of_compilerAt
      M hPA tail level hcompiler) as
    (nextLocal & localCertificate & hgraph & hcertificate).
  exists nextLocal, localCertificate.
  unfold RawDynamicTruthNativeStagedNextLocalProofAt,
    RawDynamicTruthNativePositiveFieldOrdinaryProofAt.
  split; assumption.
Qed.

(** Preferred callback endpoint with the two projection packages eliminated
    from the current-package-linked residual. *)
Theorem
    raw_dynamicTruthNativeStagedNextLocalCompiler_of_reduced_current_builder :
    forall (M : RawPAModel), RawPASatisfies M ->
  forall (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  RawDynamicTruthNativeLocalCurrentReducedStagedRootBuilder M translation ->
  RawDynamicTruthNativeStagedNextLocalCompiler M.
Proof.
  intros M hPA translation hagreement hbuilder
    tail level currentLocal currentCrossLevel currentShift
    currentSubstitution currentAxiomSoundness currentFinal hcurrent.
  pose proof
    (raw_dynamicTruthNativeLocalDecisionExclusiveProofCompilerAt_of_reduced_current_builder
      M hPA translation hagreement hbuilder tail level
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal hcurrent) as hcompiler.
  destruct
    (raw_dynamicTruthNativeLocalPositiveProof_exists_of_compilerAt
      M hPA tail level hcompiler) as
    (nextLocal & localCertificate & hgraph & hcertificate).
  exists nextLocal, localCertificate.
  unfold RawDynamicTruthNativeStagedNextLocalProofAt,
    RawDynamicTruthNativePositiveFieldOrdinaryProofAt.
  split; assumption.
Qed.

End PABoundedRawCodedDynamicTruthNativeLocalStagedCallbackCompilation.
