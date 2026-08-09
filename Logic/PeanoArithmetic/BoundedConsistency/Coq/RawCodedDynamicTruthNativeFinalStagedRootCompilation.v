(**
  Dependency-aware compilation of the sixth native successor field.

  The first five positive fields have already been selected and proved in
  the witnessed PA-axiom context which carries the current six-field master.
  This file extends their literal conjunction by the selected axiom-
  soundness field and follows the compact restricted-consistency graph all
  the way to its transparent successor target.

  Two traces are deliberately kept together.  The compact graph supplies a
  numeral code and the exact closed consistency target made from that code;
  substitution in the fixed dynamic-soundness source supplies the exact
  six-premise implication made from the *same* numeral code.  The one
  residual compiler below is therefore neither an arbitrary successor nor a
  semantic truth-to-proof principle.  It produces only a represented local
  proof of that source-linked implication in the canonical context after the
  three restricted-proof witnesses have been opened.

  Everything following that implication root is structural.  Existing
  theorems realize all three context shifts, project the six checker fields,
  apply six implication eliminations, descend through the three existential
  binders, and close the temporary assumption and outer binders over the
  original nonempty witnessed context.  Both a carried local root and an
  ordinary proof of the exact graph-selected target are exposed.
*)

From Stdlib Require Import List.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors
  RawCodedFormulaOperations
  RawCodedNumeralTermCode
  RawCodedContextLists
  RawCodedContextShift
  RawCodedRestrictedPAProof
  RawCodedProofEndpoints
  RawCodedProofRuleCoverage
  RawCodedProofImpIConstructor
  RawCodedProofAllIConstructor
  RawCodedProofAndIConstructor
  RawCodedPAProvability
  RawCodedPALocalProofExistential
  RawCodedPALocalProofAndIntroduction
  RawCodedPAOpenProofComposition
  RawCodedPAProofAllNCarriedCertificates
  RawCodedPAAxiomContextSelfShift
  RawCodedRestrictedPAConsistencyFormulaCode
  CompactRestrictedPAConsistencyFormulaCodeGraph
  RawCodedRestrictedPAConsistencyOpenCompiler
  RawCodedRestrictedPAConsistencyTripleExDescent
  RawCodedRestrictedPAConsistencyShiftRealization
  RawCodedRestrictedPAFieldProjections
  RawCodedRestrictedPADynamicSoundnessComposition
  RawCodedRestrictedPADynamicSoundnessSource
  RawCodedRestrictedPADynamicSoundnessSubstitution
  RawCodedRestrictedPAProjectedFieldRefutation
  RawCodedTruthCertificateMasterBaseBridge
  RawCodedTruthCertificateMasterSuccessorBridge
  RawCodedDynamicTruthNativeLocalPositiveGraph
  RawCodedDynamicTruthNativeCrossLevelPositiveGraph
  RawCodedDynamicTruthNativeShiftPositiveGraph
  RawCodedDynamicTruthNativeSubstitutionPositiveGraph
  RawCodedDynamicTruthNativeAxiomSoundnessPositiveGraph
  RawCodedDynamicTruthNativeMasterEndpoint
  RawCodedDynamicTruthNativeStagedPositiveSuccessor
  RawCodedDynamicTruthNativeAxiomStagedRootCompilation.

Module PABoundedRawCodedDynamicTruthNativeFinalStagedRootCompilation.

Import ListNotations.
Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedNumeralTermCode.
Import PABoundedRawCodedContextLists.
Import PABoundedRawCodedContextShift.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedProofEndpoints.
Import PABoundedRawCodedProofRuleCoverage.
Import PABoundedRawCodedProofImpIConstructor.
Import PABoundedRawCodedProofAllIConstructor.
Import PABoundedRawCodedProofAndIConstructor.
Import PABoundedRawCodedPAProvability.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPALocalProofAndIntroduction.
Import PABoundedRawCodedPAOpenProofComposition.
Import PABoundedRawCodedPAProofAllNCarriedCertificates.
Import PABoundedRawCodedPAAxiomContextSelfShift.
Import PABoundedRawCodedRestrictedPAConsistencyFormulaCode.
Import PABoundedCompactRestrictedPAConsistencyFormulaCodeGraph.
Import PABoundedRawCodedRestrictedPAConsistencyOpenCompiler.
Import PABoundedRawCodedRestrictedPAConsistencyTripleExDescent.
Import PABoundedRawCodedRestrictedPAConsistencyShiftRealization.
Import PABoundedRawCodedRestrictedPAFieldProjections.
Import PABoundedRawCodedRestrictedPADynamicSoundnessComposition.
Import PABoundedRawCodedRestrictedPADynamicSoundnessSource.
Import PABoundedRawCodedRestrictedPADynamicSoundnessSubstitution.
Import PABoundedRawCodedRestrictedPAProjectedFieldRefutation.
Import PABoundedRawCodedTruthCertificateMasterBaseBridge.
Import PABoundedRawCodedTruthCertificateMasterSuccessorBridge.
Import PABoundedRawCodedDynamicTruthNativeLocalPositiveGraph.
Import PABoundedRawCodedDynamicTruthNativeCrossLevelPositiveGraph.
Import PABoundedRawCodedDynamicTruthNativeShiftPositiveGraph.
Import PABoundedRawCodedDynamicTruthNativeSubstitutionPositiveGraph.
Import PABoundedRawCodedDynamicTruthNativeAxiomSoundnessPositiveGraph.
Import PABoundedRawCodedDynamicTruthNativeMasterEndpoint.
Import PABoundedRawCodedDynamicTruthNativeStagedPositiveSuccessor.
Import PABoundedRawCodedDynamicTruthNativeAxiomStagedRootCompilation.

(** ------------------------------------------------------------------
    The literal final dependency prefix in one witnessed context. *)

Definition rawDynamicTruthNativeFinalStagedAntecedentCode
    (M : RawPAModel)
    (currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift nextSubstitution
      nextAxiomSoundness : M) : M :=
  rawFormulaAndCode M
    (rawDynamicTruthNativeAxiomStagedAntecedentCode M
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift nextSubstitution)
    nextAxiomSoundness.

Arguments rawDynamicTruthNativeFinalStagedAntecedentCode
  M currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal
    nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
  : clear implicits.

(** Extend the preceding ten-root record by exactly the fifth selected
    successor root.  The shared [witnessList] and [baseContext] parameters
    make context preservation definitional rather than an after-the-fact
    transport claim. *)
Record RawDynamicTruthNativeFinalStagedPrerequisitesAt
    (M : RawPAModel)
    (witnessList baseContext
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
      currentLocalRoot currentCrossLevelRoot currentShiftRoot
      currentSubstitutionRoot currentAxiomSoundnessRoot currentFinalRoot
      nextLocalRoot nextCrossLevelRoot nextShiftRoot nextSubstitutionRoot
      nextAxiomSoundnessRoot : M) : Prop := {
  rawDynamicTruthNativeFinal_staged_axiomPrefix :
    RawDynamicTruthNativeAxiomStagedPrerequisitesAt M
      witnessList baseContext
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift nextSubstitution
      currentLocalRoot currentCrossLevelRoot currentShiftRoot
      currentSubstitutionRoot currentAxiomSoundnessRoot currentFinalRoot
      nextLocalRoot nextCrossLevelRoot nextShiftRoot nextSubstitutionRoot;
  rawDynamicTruthNativeFinal_staged_nextAxiomSoundness :
    RawCodedPALocalProofOf M baseContext
      nextAxiomSoundness nextAxiomSoundnessRoot
}.

Arguments RawDynamicTruthNativeFinalStagedPrerequisitesAt
  M witnessList baseContext
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal
    nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
    currentLocalRoot currentCrossLevelRoot currentShiftRoot
    currentSubstitutionRoot currentAxiomSoundnessRoot currentFinalRoot
    nextLocalRoot nextCrossLevelRoot nextShiftRoot nextSubstitutionRoot
    nextAxiomSoundnessRoot : clear implicits.

(** Hide only the concrete root numbers, not the shared witness or context.
    This is the compact prerequisite consumed by the remaining compiler. *)
Definition RawDynamicTruthNativeFinalStagedPrerequisitesOn
    (M : RawPAModel)
    (witnessList baseContext
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift nextSubstitution
      nextAxiomSoundness : M) : Prop :=
  exists currentLocalRoot currentCrossLevelRoot currentShiftRoot
      currentSubstitutionRoot currentAxiomSoundnessRoot currentFinalRoot
      nextLocalRoot nextCrossLevelRoot nextShiftRoot nextSubstitutionRoot
      nextAxiomSoundnessRoot : M,
    RawDynamicTruthNativeFinalStagedPrerequisitesAt M
      witnessList baseContext
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift nextSubstitution
      nextAxiomSoundness
      currentLocalRoot currentCrossLevelRoot currentShiftRoot
      currentSubstitutionRoot currentAxiomSoundnessRoot currentFinalRoot
      nextLocalRoot nextCrossLevelRoot nextShiftRoot nextSubstitutionRoot
      nextAxiomSoundnessRoot.

Arguments RawDynamicTruthNativeFinalStagedPrerequisitesOn
  M witnessList baseContext
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal
    nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
  : clear implicits.

Definition rawDynamicTruthNativeFinalStagedAntecedentRoot
    (M : RawPAModel) (baseContext
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
      currentLocalRoot currentCrossLevelRoot currentShiftRoot
      currentSubstitutionRoot currentAxiomSoundnessRoot currentFinalRoot
      nextLocalRoot nextCrossLevelRoot nextShiftRoot nextSubstitutionRoot
      nextAxiomSoundnessRoot : M) : M :=
  rawProofAndIRoot M baseContext
    (rawDynamicTruthNativeAxiomStagedAntecedentCode M
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift nextSubstitution)
    nextAxiomSoundness
    (rawDynamicTruthNativeAxiomStagedAntecedentRoot M baseContext
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift nextSubstitution
      currentLocalRoot currentCrossLevelRoot currentShiftRoot
      currentSubstitutionRoot currentAxiomSoundnessRoot currentFinalRoot
      nextLocalRoot nextCrossLevelRoot nextShiftRoot nextSubstitutionRoot)
    nextAxiomSoundnessRoot.

Arguments rawDynamicTruthNativeFinalStagedAntecedentRoot
  M baseContext
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal
    nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
    currentLocalRoot currentCrossLevelRoot currentShiftRoot
    currentSubstitutionRoot currentAxiomSoundnessRoot currentFinalRoot
    nextLocalRoot nextCrossLevelRoot nextShiftRoot nextSubstitutionRoot
    nextAxiomSoundnessRoot : clear implicits.

Theorem raw_dynamicTruthNativeFinalStagedAntecedentRoot_of_prerequisites :
    forall (M : RawPAModel), RawPASatisfies M -> forall
      witnessList baseContext
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
      currentLocalRoot currentCrossLevelRoot currentShiftRoot
      currentSubstitutionRoot currentAxiomSoundnessRoot currentFinalRoot
      nextLocalRoot nextCrossLevelRoot nextShiftRoot nextSubstitutionRoot
      nextAxiomSoundnessRoot,
  RawDynamicTruthNativeFinalStagedPrerequisitesAt M
      witnessList baseContext
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
      currentLocalRoot currentCrossLevelRoot currentShiftRoot
      currentSubstitutionRoot currentAxiomSoundnessRoot currentFinalRoot
      nextLocalRoot nextCrossLevelRoot nextShiftRoot nextSubstitutionRoot
      nextAxiomSoundnessRoot ->
  RawCodedPALocalProofOf M baseContext
    (rawDynamicTruthNativeFinalStagedAntecedentCode M
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift nextSubstitution
      nextAxiomSoundness)
    (rawDynamicTruthNativeFinalStagedAntecedentRoot M baseContext
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift nextSubstitution
      nextAxiomSoundness
      currentLocalRoot currentCrossLevelRoot currentShiftRoot
      currentSubstitutionRoot currentAxiomSoundnessRoot currentFinalRoot
      nextLocalRoot nextCrossLevelRoot nextShiftRoot nextSubstitutionRoot
      nextAxiomSoundnessRoot).
Proof.
  intros M hPA witnessList baseContext
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal
    nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
    currentLocalRoot currentCrossLevelRoot currentShiftRoot
    currentSubstitutionRoot currentAxiomSoundnessRoot currentFinalRoot
    nextLocalRoot nextCrossLevelRoot nextShiftRoot nextSubstitutionRoot
    nextAxiomSoundnessRoot [hprefix hnextAxiom].
  pose proof
    (raw_dynamicTruthNativeAxiomStagedAntecedentRoot_of_prerequisites
      M hPA witnessList baseContext
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift nextSubstitution
      currentLocalRoot currentCrossLevelRoot currentShiftRoot
      currentSubstitutionRoot currentAxiomSoundnessRoot currentFinalRoot
      nextLocalRoot nextCrossLevelRoot nextShiftRoot nextSubstitutionRoot
      hprefix) as hprefixRoot.
  unfold rawDynamicTruthNativeFinalStagedAntecedentCode,
    rawDynamicTruthNativeFinalStagedAntecedentRoot.
  exact (raw_codedPALocalProofOf_andI M hPA baseContext
    (rawDynamicTruthNativeAxiomStagedAntecedentCode M
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift nextSubstitution)
    nextAxiomSoundness
    (rawDynamicTruthNativeAxiomStagedAntecedentRoot M baseContext
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift nextSubstitution
      currentLocalRoot currentCrossLevelRoot currentShiftRoot
      currentSubstitutionRoot currentAxiomSoundnessRoot currentFinalRoot
      nextLocalRoot nextCrossLevelRoot nextShiftRoot nextSubstitutionRoot)
    nextAxiomSoundnessRoot hprefixRoot hnextAxiom).
Qed.

(** The prerequisites recover the literal current six-field common-context
    package.  This small projection prevents the final wrapper from hiding a
    stronger or differently contextualized current hypothesis. *)
Theorem raw_dynamicTruthNativeFinal_currentCommonContext_of_prerequisites :
    forall (M : RawPAModel)
      witnessList baseContext
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness,
  RawDynamicTruthNativeFinalStagedPrerequisitesOn M
      witnessList baseContext
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift nextSubstitution
      nextAxiomSoundness ->
  RawSixFieldMasterCommonContextProofsOf M
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal.
Proof.
  intros M witnessList baseContext
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal
    nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
    (currentLocalRoot & currentCrossLevelRoot & currentShiftRoot &
      currentSubstitutionRoot & currentAxiomSoundnessRoot & currentFinalRoot &
      nextLocalRoot & nextCrossLevelRoot & nextShiftRoot &
      nextSubstitutionRoot & nextAxiomSoundnessRoot &
      [hprefix hnextAxiom]).
  destruct hprefix as
    [hwitness hcurrentLocal hcurrentCross hcurrentShift
      hcurrentSubstitution hcurrentAxiom hcurrentFinal
      hnextLocal hnextCross hnextShift hnextSubstitution].
  exists witnessList, baseContext,
    currentLocalRoot, currentCrossLevelRoot, currentShiftRoot,
    currentSubstitutionRoot, currentAxiomSoundnessRoot, currentFinalRoot.
  split; [exact hwitness |].
  split; [exact hcurrentLocal |].
  split; [exact hcurrentCross |].
  split; [exact hcurrentShift |].
  split; [exact hcurrentSubstitution |].
  split; [exact hcurrentAxiom | exact hcurrentFinal].
Qed.

(** ------------------------------------------------------------------
    Exact graph and fixed-source linkage. *)

Record RawDynamicTruthNativeFinalSourceTraceAt
    (M : RawPAModel) (level currentFinal nextFinal successorNumeralCode : M)
    : Prop := {
  rawDynamicTruthNativeFinal_source_currentTarget :
    RawRestrictedPAConsistencyFormulaCodeAt M level currentFinal;
  rawDynamicTruthNativeFinal_source_successorNumeral :
    RawNumeralTermCodeAt M (raw_succ M level) successorNumeralCode;
  rawDynamicTruthNativeFinal_source_successorTarget :
    nextFinal =
      rawRestrictedTargetFormulaContextCode M successorNumeralCode
        restrictedPAConsistencyFormulaContext;
  rawDynamicTruthNativeFinal_source_substitution :
    RawCodedFormulaSingleSubstitution M successorNumeralCode
      (rawRestrictedPADynamicSoundnessSourceCode M)
      (rawRestrictedPADynamicSoundnessImplicationCode M
        successorNumeralCode)
}.

Arguments RawDynamicTruthNativeFinalSourceTraceAt
  M level currentFinal nextFinal successorNumeralCode : clear implicits.

(** The compiler sees all graph choices literally.  In particular, the five
    positive fields are indexed by [level], whereas the compact field is
    indexed by [succ level], matching the staged master convention. *)
Record RawDynamicTruthNativeFinalStagedGraphTraceAt
    (M : RawPAModel) (tail : nat -> M) (level
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
      nextFinal successorNumeralCode : M) : Prop := {
  rawDynamicTruthNativeFinal_graph_current :
    RawSixFieldMasterGraphWitnessesAt M
      dynamicTruthNativeSplicedLocalFieldGraph
      dynamicTruthNativeSplicedCrossLevelFieldGraph
      dynamicTruthNativeSplicedShiftFieldGraph
      dynamicTruthNativeSplicedSubstitutionFieldGraph
      dynamicTruthNativeSplicedAxiomSoundnessFieldGraph
      tail level currentLocal currentCrossLevel currentShift
      currentSubstitution currentAxiomSoundness currentFinal;
  rawDynamicTruthNativeFinal_graph_nextLocal :
    raw_formula_sat M
      (scons M nextLocal (scons M level tail))
      dynamicTruthNativeLocalPositiveGraph;
  rawDynamicTruthNativeFinal_graph_nextCrossLevel :
    raw_formula_sat M
      (scons M nextCrossLevel (scons M level tail))
      dynamicTruthNativeCrossLevelPositiveGraph;
  rawDynamicTruthNativeFinal_graph_nextShift :
    raw_formula_sat M
      (scons M nextShift (scons M level tail))
      dynamicTruthNativeShiftPositiveGraph;
  rawDynamicTruthNativeFinal_graph_nextSubstitution :
    raw_formula_sat M
      (scons M nextSubstitution (scons M level tail))
      dynamicTruthNativeSubstitutionPositiveGraph;
  rawDynamicTruthNativeFinal_graph_nextAxiomSoundness :
    raw_formula_sat M
      (scons M nextAxiomSoundness (scons M level tail))
      dynamicTruthNativeAxiomSoundnessPositiveGraph;
  rawDynamicTruthNativeFinal_graph_nextFinal :
    raw_formula_sat M
      (scons M nextFinal (scons M (raw_succ M level) tail))
      compactRestrictedPAConsistencyFormulaCodeGraph;
  rawDynamicTruthNativeFinal_graph_source :
    RawDynamicTruthNativeFinalSourceTraceAt M level
      currentFinal nextFinal successorNumeralCode
}.

Arguments RawDynamicTruthNativeFinalStagedGraphTraceAt
  M tail level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal
    nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
    nextFinal successorNumeralCode : clear implicits.

Theorem raw_dynamicTruthNativeFinalStagedGraphTrace_of_graphs :
    forall (M : RawPAModel), RawPASatisfies M -> forall
      (tail : nat -> M) level
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
      nextFinal,
  RawSixFieldMasterGraphWitnessesAt M
      dynamicTruthNativeSplicedLocalFieldGraph
      dynamicTruthNativeSplicedCrossLevelFieldGraph
      dynamicTruthNativeSplicedShiftFieldGraph
      dynamicTruthNativeSplicedSubstitutionFieldGraph
      dynamicTruthNativeSplicedAxiomSoundnessFieldGraph
      tail level currentLocal currentCrossLevel currentShift
      currentSubstitution currentAxiomSoundness currentFinal ->
  raw_formula_sat M
      (scons M nextLocal (scons M level tail))
      dynamicTruthNativeLocalPositiveGraph ->
  raw_formula_sat M
      (scons M nextCrossLevel (scons M level tail))
      dynamicTruthNativeCrossLevelPositiveGraph ->
  raw_formula_sat M
      (scons M nextShift (scons M level tail))
      dynamicTruthNativeShiftPositiveGraph ->
  raw_formula_sat M
      (scons M nextSubstitution (scons M level tail))
      dynamicTruthNativeSubstitutionPositiveGraph ->
  raw_formula_sat M
      (scons M nextAxiomSoundness (scons M level tail))
      dynamicTruthNativeAxiomSoundnessPositiveGraph ->
  raw_formula_sat M
      (scons M nextFinal (scons M (raw_succ M level) tail))
      compactRestrictedPAConsistencyFormulaCodeGraph ->
  exists successorNumeralCode : M,
    RawDynamicTruthNativeFinalStagedGraphTraceAt M tail level
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
      nextFinal successorNumeralCode.
Proof.
  intros M hPA tail level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal
    nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
    nextFinal hcurrent hnextLocal hnextCross hnextShift
    hnextSubstitution hnextAxiom hnextFinal.
  pose proof hcurrent as hcurrentCopy.
  unfold RawSixFieldMasterGraphWitnessesAt in hcurrentCopy.
  destruct hcurrentCopy as
    (_ & _ & _ & _ & _ & hcurrentFinalGraph).
  pose proof (proj1
    (compactRestrictedPAConsistencyFormulaCodeGraph_representation
      M tail level currentFinal) hcurrentFinalGraph) as hcurrentTarget.
  pose proof (proj1
    (compactRestrictedPAConsistencyFormulaCodeGraph_representation
      M tail (raw_succ M level) nextFinal) hnextFinal) as hnextTarget.
  destruct hnextTarget as
    [successorNumeralCode [hnumeral htarget]].
  exists successorNumeralCode.
  constructor; try assumption.
  constructor.
  - exact hcurrentTarget.
  - exact hnumeral.
  - exact htarget.
  - exact (raw_codedRestrictedPADynamicSoundnessSource_substitution
      M hPA (raw_succ M level) successorNumeralCode hnumeral).
Qed.

(** ------------------------------------------------------------------
    The sole arithmetic residual. *)

Definition
    RawDynamicTruthNativeFinalSourceLinkedImplicationRootCompiler
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
    RawRestrictedPADynamicSoundnessImplicationProof M
      successorNumeralCode
      (rawRestrictedPACanonicalShiftedProofContextCode
        M baseContext successorNumeralCode).

Arguments
  RawDynamicTruthNativeFinalSourceLinkedImplicationRootCompiler M
  : clear implicits.

(** ------------------------------------------------------------------
    Same-context closing root. *)

Definition rawDynamicTruthNativeFinalStagedClosedRoot
    (M : RawPAModel) (baseContext successorNumeralCode
      shiftedRootContext shiftedWitnessContext shiftedProofContext
      fieldChild : M) : M :=
  rawProofCloseNCarriedRoot M baseContext
    (restrictedTargetFormulaContextBound
      restrictedPAConsistencyBodyFormulaContext)
    (rawFormulaAllCode M
      (rawFormulaImpCode M
        (rawRestrictedPAProofAssumptionCode M successorNumeralCode)
        (rawFormulaBotCode M)))
    (rawProofUniversalOpenNegationCarriedRoot M baseContext
      (rawRestrictedPAProofAssumptionCode M successorNumeralCode)
      (rawRestrictedPATripleExERoot M successorNumeralCode baseContext
        shiftedRootContext shiftedWitnessContext shiftedProofContext
        fieldChild)).

Arguments rawDynamicTruthNativeFinalStagedClosedRoot
  M baseContext successorNumeralCode
    shiftedRootContext shiftedWitnessContext shiftedProofContext fieldChild
  : clear implicits.

(** Local form of the carried closing theorem.  It is useful here because
    common-context master assembly needs the root before the ordinary outer
    certificate is formed.  This is exactly the coverage/endpoint portion of
    [raw_codedPAProofOf_sealed_universal_negation_of_carried_open_bottom]. *)
Theorem raw_dynamicTruthNativeFinalStagedClosedRoot_local :
    forall (M : RawPAModel), RawPASatisfies M -> forall
      witnessList baseContext successorNumeralCode
      shiftedRootContext shiftedWitnessContext shiftedProofContext
      fieldChild,
  RawContextShift M baseContext baseContext ->
  RawCodedPAOpenProofOf M witnessList baseContext
    (rawRestrictedPAProofAssumptionCode M successorNumeralCode)
    (rawFormulaBotCode M)
    (rawRestrictedPATripleExERoot M successorNumeralCode baseContext
      shiftedRootContext shiftedWitnessContext shiftedProofContext
      fieldChild) ->
  RawCodedPALocalProofOf M baseContext
    (rawRestrictedTargetCloseNFormulaCode M
      (restrictedTargetFormulaContextBound
        restrictedPAConsistencyBodyFormulaContext)
      (rawFormulaAllCode M
        (rawFormulaImpCode M
          (rawRestrictedPAProofAssumptionCode M successorNumeralCode)
          (rawFormulaBotCode M))))
    (rawDynamicTruthNativeFinalStagedClosedRoot M baseContext
      successorNumeralCode shiftedRootContext shiftedWitnessContext
      shiftedProofContext fieldChild).
Proof.
  intros M hPA witnessList baseContext successorNumeralCode
    shiftedRootContext shiftedWitnessContext shiftedProofContext
    fieldChild hself [_ [hcoverage hendpoint]].
  set (assumption :=
    rawRestrictedPAProofAssumptionCode M successorNumeralCode).
  set (child := rawRestrictedPATripleExERoot M successorNumeralCode
    baseContext shiftedRootContext shiftedWitnessContext
    shiftedProofContext fieldChild).
  set (impRoot := rawProofImpIRoot M baseContext
    assumption (rawFormulaBotCode M) child).
  set (allRoot := rawProofAllIRoot M baseContext
    (rawFormulaImpCode M assumption (rawFormulaBotCode M)) impRoot).
  assert (himpCoverage : RawProofRuleCoverage M impRoot).
  {
    unfold impRoot.
    exact (raw_proofImpI_ruleCoverage M hPA baseContext
      assumption (rawFormulaBotCode M) child hcoverage hendpoint).
  }
  assert (himpEndpoint : RawProofEndpoint M impRoot baseContext
      (rawFormulaImpCode M assumption (rawFormulaBotCode M))).
  {
    unfold impRoot.
    exact (raw_proofImpI_endpoint M baseContext
      assumption (rawFormulaBotCode M) child).
  }
  assert (hallCoverage : RawProofRuleCoverage M allRoot).
  {
    unfold allRoot.
    exact (raw_proofAllI_ruleCoverage M hPA
      baseContext baseContext
      (rawFormulaImpCode M assumption (rawFormulaBotCode M))
      impRoot hself himpCoverage himpEndpoint).
  }
  assert (hallEndpoint : RawProofEndpoint M allRoot baseContext
      (rawFormulaAllCode M
        (rawFormulaImpCode M assumption (rawFormulaBotCode M)))).
  {
    unfold allRoot.
    exact (raw_proofAllI_endpoint M baseContext
      (rawFormulaImpCode M assumption (rawFormulaBotCode M)) impRoot).
  }
  unfold rawDynamicTruthNativeFinalStagedClosedRoot.
  change (RawCodedPALocalProofOf M baseContext
    (rawRestrictedTargetCloseNFormulaCode M
      (restrictedTargetFormulaContextBound
        restrictedPAConsistencyBodyFormulaContext)
      (rawFormulaAllCode M
        (rawFormulaImpCode M assumption (rawFormulaBotCode M))))
    (rawProofCloseNCarriedRoot M baseContext
      (restrictedTargetFormulaContextBound
        restrictedPAConsistencyBodyFormulaContext)
      (rawFormulaAllCode M
        (rawFormulaImpCode M assumption (rawFormulaBotCode M)))
      allRoot)).
  split.
  - exact (raw_proofCloseNCarriedRoot_ruleCoverage M hPA
      baseContext hself
      (restrictedTargetFormulaContextBound
        restrictedPAConsistencyBodyFormulaContext)
      (rawFormulaAllCode M
        (rawFormulaImpCode M assumption (rawFormulaBotCode M)))
      allRoot hallCoverage hallEndpoint).
  - exact (raw_proofCloseNCarriedRoot_endpoint M hPA
      baseContext hself
      (restrictedTargetFormulaContextBound
        restrictedPAConsistencyBodyFormulaContext)
      (rawFormulaAllCode M
        (rawFormulaImpCode M assumption (rawFormulaBotCode M)))
      allRoot hallCoverage hallEndpoint).
Qed.

(** Pair the exact compact graph with a carried local proof in the unchanged
    witnessed base. *)
Definition RawDynamicTruthNativeFinalStagedLocalProofAt
    (M : RawPAModel) (tail : nat -> M)
    (level baseContext target root : M) : Prop :=
  raw_formula_sat M
    (scons M target (scons M (raw_succ M level) tail))
    compactRestrictedPAConsistencyFormulaCodeGraph /\
  RawCodedPALocalProofOf M baseContext target root.

Arguments RawDynamicTruthNativeFinalStagedLocalProofAt
  M tail level baseContext target root : clear implicits.

(** Pointwise form of the main structural closing theorem.  Keeping the
    source-linked implication proof as a premise at the selected trace is
    important for context-growing callers: an ordinary certificate may have
    to be merged into [baseContext] first, so the resulting proof cannot in
    general inhabit the caller's original context. *)
Theorem
    raw_dynamicTruthNativeFinalStagedLocalProof_of_source_linked_implication_at :
    forall (M : RawPAModel), RawPASatisfies M ->
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
    RawRestrictedPADynamicSoundnessImplicationProof M
      successorNumeralCode
      (rawRestrictedPACanonicalShiftedProofContextCode
        M baseContext successorNumeralCode) ->
  exists finalRoot : M,
    RawDynamicTruthNativeFinalStagedLocalProofAt M tail level
      baseContext nextFinal finalRoot.
Proof.
  intros M hPA tail level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal
    nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
    nextFinal successorNumeralCode witnessList baseContext
    hgraphTrace hprerequisites hsoundness.
  pose proof hgraphTrace as hgraphTraceCopy.
  destruct hgraphTraceCopy as
    [hcurrentGraph hnextLocalGraph hnextCrossGraph hnextShiftGraph
      hnextSubstitutionGraph hnextAxiomGraph hnextFinalGraph hsource].
  destruct hsource as
    [hcurrentTarget hnumeral hnextTarget hsourceSubstitution].
  destruct hprerequisites as
    (currentLocalRoot & currentCrossLevelRoot & currentShiftRoot &
      currentSubstitutionRoot & currentAxiomSoundnessRoot & currentFinalRoot &
      nextLocalRoot & nextCrossLevelRoot & nextShiftRoot &
      nextSubstitutionRoot & nextAxiomSoundnessRoot &
      [hprefix hnextAxiomRoot]).
  pose proof hprefix as hprefixCopy.
  destruct hprefixCopy as
    [hwitness hcurrentLocalRoot hcurrentCrossRoot hcurrentShiftRoot
      hcurrentSubstitutionRoot hcurrentAxiomRoot hcurrentFinalRoot
      hnextLocalRoot hnextCrossRoot hnextShiftRootProof
      hnextSubstitutionRoot].
  assert (hbaseShift : RawContextShift M baseContext baseContext).
  {
    exact (raw_codedPAAxiomWitnessContext_selfShift M hPA
      witnessList baseContext hwitness).
  }
  set (shiftedRootContext :=
    rawRestrictedPACanonicalShiftedRootContextCode
      M baseContext successorNumeralCode).
  set (shiftedWitnessContext :=
    rawRestrictedPACanonicalShiftedWitnessContextCode
      M baseContext successorNumeralCode).
  set (shiftedProofContext :=
    rawRestrictedPACanonicalShiftedProofContextCode
      M baseContext successorNumeralCode).
  assert (hcontexts : RawRestrictedPAExistentialDescentContexts M
      successorNumeralCode baseContext shiftedRootContext
      shiftedWitnessContext shiftedProofContext).
  {
    unfold shiftedRootContext, shiftedWitnessContext, shiftedProofContext.
    exact (raw_restrictedPAExistentialDescentContexts_realized
      M hPA (raw_succ M level) successorNumeralCode baseContext
      hnumeral hbaseShift).
  }
  pose proof hcontexts as hcontextsCopy.
  destruct hcontextsCopy as [hrootShift [hwitnessShift hproofShift]].
  assert (hproofContextRealizable :
      RawContextListRealizable M shiftedProofContext).
  {
    exact (raw_contextShift_target_realizable M
      (rawRestrictedPAAfterProofContextCode M successorNumeralCode
        shiftedWitnessContext)
      shiftedProofContext hproofShift).
  }
  assert (hprojections : RawRestrictedPAFieldProjectionPackage M
      successorNumeralCode shiftedProofContext).
  {
    exact (raw_restrictedPAFieldProjectionPackage M hPA
      successorNumeralCode shiftedProofContext hproofContextRealizable).
  }
  destruct (raw_codedPALocalProofOf_bottom_of_dynamicSoundness
    M hPA successorNumeralCode shiftedProofContext
    hsoundness hprojections) as [fieldChild hfieldChild].
  pose proof (raw_codedPAOpenProofOf_bottom_of_restrictedPA_fields
    M hPA witnessList baseContext successorNumeralCode
    shiftedRootContext shiftedWitnessContext shiftedProofContext
    fieldChild hwitness hcontexts hfieldChild) as hopen.
  pose proof (raw_dynamicTruthNativeFinalStagedClosedRoot_local
    M hPA witnessList baseContext successorNumeralCode
    shiftedRootContext shiftedWitnessContext shiftedProofContext
    fieldChild hbaseShift hopen) as hclosed.
  exists (rawDynamicTruthNativeFinalStagedClosedRoot M baseContext
    successorNumeralCode shiftedRootContext shiftedWitnessContext
    shiftedProofContext fieldChild).
  split; [exact hnextFinalGraph |].
  rewrite hnextTarget.
  rewrite raw_restrictedPAConsistencyTargetCode_view.
  exact hclosed.
Qed.

(** Compiler form used by the existing staged callback.  All proof-tree
    work is delegated to the pointwise theorem above; the global compiler is
    invoked exactly once to obtain its final premise. *)
Theorem
    raw_dynamicTruthNativeFinalStagedLocalProof_of_source_linked_implication :
    forall (M : RawPAModel), RawPASatisfies M ->
  RawDynamicTruthNativeFinalSourceLinkedImplicationRootCompiler M ->
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
  exists finalRoot : M,
    RawDynamicTruthNativeFinalStagedLocalProofAt M tail level
      baseContext nextFinal finalRoot.
Proof.
  intros M hPA hcompiler tail level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal
    nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
    nextFinal successorNumeralCode witnessList baseContext
    hgraphTrace hprerequisites.
  exact
    (raw_dynamicTruthNativeFinalStagedLocalProof_of_source_linked_implication_at
      M hPA tail level
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
      nextFinal successorNumeralCode witnessList baseContext
      hgraphTrace hprerequisites
      (hcompiler tail level
        currentLocal currentCrossLevel currentShift currentSubstitution
        currentAxiomSoundness currentFinal
        nextLocal nextCrossLevel nextShift nextSubstitution
        nextAxiomSoundness nextFinal successorNumeralCode witnessList
        baseContext hgraphTrace hprerequisites)).
Qed.

(** Total graph selection adds no proof-theoretic premise: the compact graph
    already has an arbitrary-model totality theorem. *)
Theorem raw_dynamicTruthNativeFinalStagedLocalProof_exists :
    forall (M : RawPAModel), RawPASatisfies M ->
  RawDynamicTruthNativeFinalSourceLinkedImplicationRootCompiler M ->
  forall (tail : nat -> M) level
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
      witnessList baseContext,
  RawSixFieldMasterGraphWitnessesAt M
      dynamicTruthNativeSplicedLocalFieldGraph
      dynamicTruthNativeSplicedCrossLevelFieldGraph
      dynamicTruthNativeSplicedShiftFieldGraph
      dynamicTruthNativeSplicedSubstitutionFieldGraph
      dynamicTruthNativeSplicedAxiomSoundnessFieldGraph
      tail level currentLocal currentCrossLevel currentShift
      currentSubstitution currentAxiomSoundness currentFinal ->
  raw_formula_sat M
      (scons M nextLocal (scons M level tail))
      dynamicTruthNativeLocalPositiveGraph ->
  raw_formula_sat M
      (scons M nextCrossLevel (scons M level tail))
      dynamicTruthNativeCrossLevelPositiveGraph ->
  raw_formula_sat M
      (scons M nextShift (scons M level tail))
      dynamicTruthNativeShiftPositiveGraph ->
  raw_formula_sat M
      (scons M nextSubstitution (scons M level tail))
      dynamicTruthNativeSubstitutionPositiveGraph ->
  raw_formula_sat M
      (scons M nextAxiomSoundness (scons M level tail))
      dynamicTruthNativeAxiomSoundnessPositiveGraph ->
  RawDynamicTruthNativeFinalStagedPrerequisitesOn M
      witnessList baseContext
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift nextSubstitution
      nextAxiomSoundness ->
  exists nextFinal finalRoot : M,
    RawDynamicTruthNativeFinalStagedLocalProofAt M tail level
      baseContext nextFinal finalRoot.
Proof.
  intros M hPA hcompiler tail level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal
    nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
    witnessList baseContext hcurrent hnextLocal hnextCross hnextShift
    hnextSubstitution hnextAxiom hprerequisites.
  destruct (compactRestrictedPAConsistencyFormulaCodeGraph_raw_total
    M hPA tail (raw_succ M level)) as [nextFinal hnextFinal].
  destruct (raw_dynamicTruthNativeFinalStagedGraphTrace_of_graphs
    M hPA tail level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal
    nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
    nextFinal hcurrent hnextLocal hnextCross hnextShift
    hnextSubstitution hnextAxiom hnextFinal) as
    [successorNumeralCode htrace].
  destruct
    (raw_dynamicTruthNativeFinalStagedLocalProof_of_source_linked_implication
      M hPA hcompiler tail level
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
      nextFinal successorNumeralCode witnessList baseContext
      htrace hprerequisites) as [finalRoot hfinal].
  exists nextFinal, finalRoot. exact hfinal.
Qed.

(** Package a carried local root as an ordinary represented proof without
    changing its witness list, proof root, context, or target. *)
Theorem raw_codedPAProofOf_dynamicTruthNativeFinal_of_carried_root :
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

(** Pointwise shape required by the sixth dependency-ordered callback.  The
    result is now an ordinary certificate only because the stronger carried
    local root has already been proved above. *)
Corollary raw_dynamicTruthNativeFinalStagedNextFinalProof_exists :
    forall (M : RawPAModel), RawPASatisfies M ->
  RawDynamicTruthNativeFinalSourceLinkedImplicationRootCompiler M ->
  forall (tail : nat -> M) level
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
      witnessList baseContext,
  RawSixFieldMasterGraphWitnessesAt M
      dynamicTruthNativeSplicedLocalFieldGraph
      dynamicTruthNativeSplicedCrossLevelFieldGraph
      dynamicTruthNativeSplicedShiftFieldGraph
      dynamicTruthNativeSplicedSubstitutionFieldGraph
      dynamicTruthNativeSplicedAxiomSoundnessFieldGraph
      tail level currentLocal currentCrossLevel currentShift
      currentSubstitution currentAxiomSoundness currentFinal ->
  raw_formula_sat M
      (scons M nextLocal (scons M level tail))
      dynamicTruthNativeLocalPositiveGraph ->
  raw_formula_sat M
      (scons M nextCrossLevel (scons M level tail))
      dynamicTruthNativeCrossLevelPositiveGraph ->
  raw_formula_sat M
      (scons M nextShift (scons M level tail))
      dynamicTruthNativeShiftPositiveGraph ->
  raw_formula_sat M
      (scons M nextSubstitution (scons M level tail))
      dynamicTruthNativeSubstitutionPositiveGraph ->
  raw_formula_sat M
      (scons M nextAxiomSoundness (scons M level tail))
      dynamicTruthNativeAxiomSoundnessPositiveGraph ->
  RawDynamicTruthNativeFinalStagedPrerequisitesOn M
      witnessList baseContext
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift nextSubstitution
      nextAxiomSoundness ->
  exists nextFinal finalCertificate : M,
    RawDynamicTruthNativeStagedNextFinalProofAt M
      tail level nextFinal finalCertificate.
Proof.
  intros M hPA hcompiler tail level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal
    nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
    witnessList baseContext hcurrent hnextLocal hnextCross hnextShift
    hnextSubstitution hnextAxiom hprerequisites.
  pose proof hprerequisites as hprerequisitesCopy.
  destruct hprerequisitesCopy as
    (currentLocalRoot & currentCrossLevelRoot & currentShiftRoot &
      currentSubstitutionRoot & currentAxiomSoundnessRoot & currentFinalRoot &
      nextLocalRoot & nextCrossLevelRoot & nextShiftRoot &
      nextSubstitutionRoot & nextAxiomSoundnessRoot &
      [hprefix hnextAxiomRoot]).
  pose proof hprefix as hprefixCopy.
  destruct hprefixCopy as [hwitness].
  destruct (raw_dynamicTruthNativeFinalStagedLocalProof_exists
    M hPA hcompiler tail level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal
    nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
    witnessList baseContext hcurrent hnextLocal hnextCross hnextShift
    hnextSubstitution hnextAxiom hprerequisites) as
    [nextFinal [finalRoot [hnextFinalGraph hfinalRoot]]].
  exists nextFinal,
    (rawCodeList3 M (rawNumeralValue M 0) witnessList finalRoot).
  split; [exact hnextFinalGraph |].
  exact (raw_codedPAProofOf_dynamicTruthNativeFinal_of_carried_root
    M witnessList baseContext nextFinal finalRoot hwitness hfinalRoot).
Qed.

(** The source-linked implication compiler is intentionally not proved here.
    Existing Coq induction data records the syntax and closure measures, but
    does not yet compile the five staged truth fields into this represented
    nonstandard-level implication.  All graph selection and proof-code
    structure after that exact boundary is discharged above. *)

End PABoundedRawCodedDynamicTruthNativeFinalStagedRootCompilation.
