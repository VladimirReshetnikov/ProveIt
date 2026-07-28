(**
  Assemble the native positive master step from the five proof-total fields.

  Each native [PositiveProofTotal] predicate returns a graph-selected target
  together with an ordinary [RawCodedPAProofOf] certificate.  The compact
  consistency successor does the same for the sixth target.  Consequently
  these six premises construct the exact next graph tuple and six ordinary
  proofs without any semantic or target-identification assumption.

  The public staged master successor asks for something strictly stronger:
  all six next proof roots must inhabit one witnessed PA-axiom context.
  Ordinary certificates hide their contexts, and independently produced
  certificates need not use the same one.  No generic context weakening or
  merging theorem is available for arbitrary raw proof trees.  This file
  therefore exposes that single remaining obstruction explicitly.  The
  pointwise lifting predicate below neither changes a target nor discards a
  graph witness; it merely asks that six proofs of the same six targets be
  presented in one common witnessed context.
*)

From Stdlib Require Import List.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors
  RawCodedPALocalProofExistential
  RawCodedPAProvability
  RawCodedRestrictedPAProof
  RawCodedRestrictedPAConsistencyFormulaCode
  CompactRestrictedPAConsistencyFormulaCodeGraph
  CompactPAUniformProvability
  RawCodedTruthCertificateMasterBaseBridge
  RawCodedTruthCertificateMasterSuccessorBridge
  RawCodedDynamicTruthMasterSplicedSuccessorBridge
  RawCodedDynamicTruthNativeLocalPositiveGraph
  RawCodedDynamicTruthNativeCrossLevelPositiveGraph
  RawCodedDynamicTruthNativeShiftPositiveGraph
  RawCodedDynamicTruthNativeSubstitutionPositiveGraph
  RawCodedDynamicTruthNativeAxiomSoundnessPositiveGraph
  RawCodedDynamicTruthNativeLocalProofCompilation
  RawCodedDynamicTruthNativeCrossLevelProofCompilation
  RawCodedDynamicTruthNativeShiftProofCompilation
  RawCodedDynamicTruthNativeSubstitutionProofCompilation
  RawCodedDynamicTruthNativeAxiomSoundnessProofCompilation
  RawCodedDynamicTruthNativePositiveLocalProofTotals
  RawCodedDynamicTruthNativeMasterEndpoint.

Module PABoundedRawCodedDynamicTruthNativeMasterSuccessorFromProofTotals.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPAProvability.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedRestrictedPAConsistencyFormulaCode.
Import PABoundedCompactRestrictedPAConsistencyFormulaCodeGraph.
Import PABoundedCompactPAUniformProvability.
Import PABoundedRawCodedTruthCertificateMasterBaseBridge.
Import PABoundedRawCodedTruthCertificateMasterSuccessorBridge.
Import PABoundedRawCodedDynamicTruthMasterSplicedSuccessorBridge.
Import PABoundedRawCodedDynamicTruthNativeLocalPositiveGraph.
Import PABoundedRawCodedDynamicTruthNativeCrossLevelPositiveGraph.
Import PABoundedRawCodedDynamicTruthNativeShiftPositiveGraph.
Import PABoundedRawCodedDynamicTruthNativeSubstitutionPositiveGraph.
Import PABoundedRawCodedDynamicTruthNativeAxiomSoundnessPositiveGraph.
Import PABoundedRawCodedDynamicTruthNativeLocalProofCompilation.
Import PABoundedRawCodedDynamicTruthNativeCrossLevelProofCompilation.
Import PABoundedRawCodedDynamicTruthNativeShiftProofCompilation.
Import PABoundedRawCodedDynamicTruthNativeSubstitutionProofCompilation.
Import PABoundedRawCodedDynamicTruthNativeAxiomSoundnessProofCompilation.
Import PABoundedRawCodedDynamicTruthNativePositiveLocalProofTotals.
Import PABoundedRawCodedDynamicTruthNativeMasterEndpoint.

(** Six independent ordinary certificates, with every certificate still
    indexed by its exact target.  In particular this definition does not
    replace the six targets by their conjunction code. *)
Definition RawSixFieldMasterOrdinaryProofsOf (M : RawPAModel)
    (field1 field2 field3 field4 field5 finalField : M) : Prop :=
  exists certificate1 certificate2 certificate3 certificate4 certificate5
      finalCertificate : M,
    RawCodedPAProofOf M field1 certificate1 /\
    RawCodedPAProofOf M field2 certificate2 /\
    RawCodedPAProofOf M field3 certificate3 /\
    RawCodedPAProofOf M field4 certificate4 /\
    RawCodedPAProofOf M field5 certificate5 /\
    RawCodedPAProofOf M finalField finalCertificate.

Arguments RawSixFieldMasterOrdinaryProofsOf
  M field1 field2 field3 field4 field5 finalField : clear implicits.

(** This implication is the precise pointwise gap between independent
    certificates and the package required by the master assembler. *)
Definition RawSixFieldMasterOrdinaryProofsCommonContextLiftAt
    (M : RawPAModel)
    (field1 field2 field3 field4 field5 finalField : M) : Prop :=
  RawSixFieldMasterOrdinaryProofsOf M
    field1 field2 field3 field4 field5 finalField ->
  RawSixFieldMasterCommonContextProofsOf M
    field1 field2 field3 field4 field5 finalField.

Arguments RawSixFieldMasterOrdinaryProofsCommonContextLiftAt
  M field1 field2 field3 field4 field5 finalField : clear implicits.

(** Uniform closure of the pointwise lift, suitable for a successor callback
    whose six graph outputs are chosen only after [tail] and [level] arrive. *)
Definition RawSixFieldMasterOrdinaryProofsCommonContextLift
    (M : RawPAModel) : Prop :=
  forall field1 field2 field3 field4 field5 finalField : M,
    RawSixFieldMasterOrdinaryProofsCommonContextLiftAt M
      field1 field2 field3 field4 field5 finalField.

Arguments RawSixFieldMasterOrdinaryProofsCommonContextLift M
  : clear implicits.

(** A common-context package already contains an honest ordinary proof of
    its final target.  We keep the same witnessed axiom list, context, and
    final root and only add the transparent outer certificate code.  This is
    the current proof consumed by the compact consistency successor below. *)
Lemma raw_codedPAProofOf_final_of_sixFieldMaster_common_context : forall
    (M : RawPAModel) field1 field2 field3 field4 field5 finalField,
  RawSixFieldMasterCommonContextProofsOf M
    field1 field2 field3 field4 field5 finalField ->
  exists finalCertificate : M,
    RawCodedPAProofOf M finalField finalCertificate.
Proof.
  intros M field1 field2 field3 field4 field5 finalField hproofs.
  unfold RawSixFieldMasterCommonContextProofsOf in hproofs.
  destruct hproofs as
    (witnessList & context & root1 & root2 & root3 & root4 & root5 &
      finalRoot & hwitness & hroot1 & hroot2 & hroot3 & hroot4 &
      hroot5 & hfinalRoot).
  exists (rawCodeList3 M
    (rawNumeralValue M 0) witnessList finalRoot).
  exists witnessList, finalRoot, context.
  split; [reflexivity |].
  destruct hfinalRoot as [hcoverage hendpoint].
  repeat split; assumption.
Qed.

(** Bundle the five independently established native proof-total premises.
    Keeping the original predicates visible here makes clear that no stronger
    positive-field compiler is being assumed. *)
Definition RawDynamicTruthNativePositiveProofTotals
    (M : RawPAModel) : Prop :=
  RawDynamicTruthNativeLocalPositiveProofTotal M /\
  RawDynamicTruthNativeCrossLevelPositiveProofTotal M /\
  RawDynamicTruthNativeShiftPositiveProofTotal M /\
  RawDynamicTruthNativeSubstitutionPositiveProofTotal M /\
  RawDynamicTruthNativeAxiomSoundnessPositiveProofTotal M.

Arguments RawDynamicTruthNativePositiveProofTotals M : clear implicits.

(** The strongest successor that follows from the six independent proof
    transformers alone.  It is deliberately identical to the native staged
    successor on its current inputs and next graph witnesses; only the final
    proof package records six ordinary certificates instead of asserting an
    unavailable common context. *)
Definition
    RawDynamicTruthNativeSplicedMasterPositiveOrdinaryComponentSuccessor
    (M : RawPAModel) : Prop :=
  forall (tail : nat -> M) level
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal,
    RawSixFieldMasterGraphWitnessesAt M
      dynamicTruthNativeSplicedLocalFieldGraph
      dynamicTruthNativeSplicedCrossLevelFieldGraph
      dynamicTruthNativeSplicedShiftFieldGraph
      dynamicTruthNativeSplicedSubstitutionFieldGraph
      dynamicTruthNativeSplicedAxiomSoundnessFieldGraph
      tail level currentLocal currentCrossLevel currentShift
      currentSubstitution currentAxiomSoundness currentFinal ->
    RawSixFieldMasterCommonContextProofsOf M
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal ->
    exists nextLocal nextCrossLevel nextShift nextSubstitution
        nextAxiomSoundness nextFinal : M,
      RawDynamicTruthSplicedMasterPositiveGraphWitnessesAt M
        dynamicTruthNativeLocalPositiveGraph
        dynamicTruthNativeCrossLevelPositiveGraph
        dynamicTruthNativeShiftPositiveGraph
        dynamicTruthNativeSubstitutionPositiveGraph
        dynamicTruthNativeAxiomSoundnessPositiveGraph
        tail level nextLocal nextCrossLevel nextShift nextSubstitution
        nextAxiomSoundness nextFinal /\
      RawSixFieldMasterOrdinaryProofsOf M
        nextLocal nextCrossLevel nextShift nextSubstitution
        nextAxiomSoundness nextFinal.

Arguments
  RawDynamicTruthNativeSplicedMasterPositiveOrdinaryComponentSuccessor M
  : clear implicits.

(** The proof totals choose the first five targets.  For the sixth target we
    project the current final root, choose the unique next compact target by
    graph totality, and invoke the supplied certificate successor.  Every
    graph witness and every proof below refers to exactly the same target. *)
Theorem
    raw_dynamicTruthNativeSplicedMasterPositiveOrdinaryComponentSuccessor_of_proof_totals
    : forall (M : RawPAModel), RawPASatisfies M ->
  RawDynamicTruthNativePositiveProofTotals M ->
  RawRestrictedPAConsistencyCertificateSuccessor M ->
  RawDynamicTruthNativeSplicedMasterPositiveOrdinaryComponentSuccessor M.
Proof.
  intros M hPA
    (hlocalTotal & hcrossTotal & hshiftTotal & hsubstitutionTotal &
      haxiomSoundnessTotal)
    hconsistencySuccessor.
  intros tail level currentLocal currentCrossLevel currentShift
    currentSubstitution currentAxiomSoundness currentFinal
    hcurrentGraphs hcurrentProofs.
  destruct (hlocalTotal tail level) as
    (nextLocal & localCertificate & hnextLocalGraph & hnextLocalProof).
  destruct (hcrossTotal tail level) as
    (nextCrossLevel & crossCertificate & hnextCrossGraph &
      hnextCrossProof).
  destruct (hshiftTotal tail level) as
    (nextShift & shiftCertificate & hnextShiftGraph &
      hnextShiftAdequate & hnextShiftProof).
  destruct (hsubstitutionTotal tail level) as
    (nextSubstitution & substitutionCertificate &
      hnextSubstitutionGraph & hnextSubstitutionAdequate &
      hnextSubstitutionProof).
  destruct (haxiomSoundnessTotal tail level) as
    (nextAxiomSoundness & axiomSoundnessCertificate &
      hnextAxiomSoundnessGraph & hnextAxiomSoundnessAdequate &
      hnextAxiomSoundnessProof).
  unfold RawSixFieldMasterGraphWitnessesAt in hcurrentGraphs.
  destruct hcurrentGraphs as
    (hcurrentLocalGraph & hcurrentCrossGraph & hcurrentShiftGraph &
      hcurrentSubstitutionGraph & hcurrentAxiomSoundnessGraph &
      hcurrentFinalGraph).
  assert (hcurrentFinalTarget :
      RawRestrictedPAConsistencyFormulaCodeAt M level currentFinal).
  {
    exact (proj1
      (compactRestrictedPAConsistencyFormulaCodeGraph_representation
        M tail level currentFinal) hcurrentFinalGraph).
  }
  destruct
    (raw_codedPAProofOf_final_of_sixFieldMaster_common_context M
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal hcurrentProofs) as
    [currentFinalCertificate hcurrentFinalProof].
  destruct
    (raw_restrictedPAConsistencyFormulaCodeAt_total M hPA
      (raw_succ M level)) as [nextFinal hnextFinalTarget].
  destruct
    (hconsistencySuccessor level currentFinal currentFinalCertificate
      nextFinal hcurrentFinalTarget hcurrentFinalProof hnextFinalTarget) as
    [nextFinalCertificate hnextFinalProof].
  assert (hnextFinalGraph :
      raw_formula_sat M
        (scons M nextFinal (scons M (raw_succ M level) tail))
        compactRestrictedPAConsistencyFormulaCodeGraph).
  {
    exact (proj2
      (compactRestrictedPAConsistencyFormulaCodeGraph_representation
        M tail (raw_succ M level) nextFinal) hnextFinalTarget).
  }
  exists nextLocal, nextCrossLevel, nextShift, nextSubstitution,
    nextAxiomSoundness, nextFinal.
  split.
  - unfold RawDynamicTruthSplicedMasterPositiveGraphWitnessesAt.
    repeat split; assumption.
  - unfold RawSixFieldMasterOrdinaryProofsOf.
    exists localCertificate, crossCertificate, shiftCertificate,
      substitutionCertificate, axiomSoundnessCertificate,
      nextFinalCertificate.
    repeat split; assumption.
Qed.

(** Exact adapter from the independently provable successor to the public
    native successor.  The common-context lift is used once, on the same six
    graph-selected outputs; all current data and all graph witnesses pass
    through unchanged. *)
Theorem
    raw_dynamicTruthNativeSplicedMasterPositiveComponentSuccessor_of_ordinary_and_common_context_lift
    : forall (M : RawPAModel),
  RawDynamicTruthNativeSplicedMasterPositiveOrdinaryComponentSuccessor M ->
  RawSixFieldMasterOrdinaryProofsCommonContextLift M ->
  RawDynamicTruthNativeSplicedMasterPositiveComponentSuccessor M.
Proof.
  intros M hordinarySuccessor hlift.
  intros tail level currentLocal currentCrossLevel currentShift
    currentSubstitution currentAxiomSoundness currentFinal
    hcurrentGraphs hcurrentProofs.
  destruct
    (hordinarySuccessor tail level
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      hcurrentGraphs hcurrentProofs) as
    (nextLocal & nextCrossLevel & nextShift & nextSubstitution &
      nextAxiomSoundness & nextFinal & hnextGraphs & hnextProofs).
  exists nextLocal, nextCrossLevel, nextShift, nextSubstitution,
    nextAxiomSoundness, nextFinal.
  split; [exact hnextGraphs |].
  exact (hlift nextLocal nextCrossLevel nextShift nextSubstitution
    nextAxiomSoundness nextFinal hnextProofs).
Qed.

(** The advertised construction, with the only non-derivable operation named
    as an explicit premise.  Removing that premise would amount precisely to
    deriving a common witnessed context from arbitrary independent ordinary
    certificates. *)
Corollary
    raw_dynamicTruthNativeSplicedMasterPositiveComponentSuccessor_of_proof_totals_and_common_context_lift
    : forall (M : RawPAModel), RawPASatisfies M ->
  RawDynamicTruthNativePositiveProofTotals M ->
  RawRestrictedPAConsistencyCertificateSuccessor M ->
  RawSixFieldMasterOrdinaryProofsCommonContextLift M ->
  RawDynamicTruthNativeSplicedMasterPositiveComponentSuccessor M.
Proof.
  intros M hPA htotals hconsistencySuccessor hlift.
  apply
    raw_dynamicTruthNativeSplicedMasterPositiveComponentSuccessor_of_ordinary_and_common_context_lift.
  - exact
      (raw_dynamicTruthNativeSplicedMasterPositiveOrdinaryComponentSuccessor_of_proof_totals
        M hPA htotals hconsistencySuccessor).
  - exact hlift.
Qed.

(** The five local-proof totals proved by the native local-root compilers are
    sharper than ordinary proof totals: their roots already share the empty
    context.  The sixth proof returned by consistency successor still owns a
    possibly nonstandard witnessed PA context.  The only operation needed to
    join these packages is therefore transport of an empty-context proof into
    that supplied witnessed context.  This one-proof interface states exactly
    that operation and neither changes the conclusion nor chooses a context. *)
Definition RawCodedPAEmptyContextToWitnessedContextTransport
    (M : RawPAModel) : Prop :=
  forall witnessList context target root : M,
    RawCodedPAAxiomWitnessContext M witnessList context ->
    RawCodedPALocalProofOf M (raw_zero M) target root ->
    exists transportedRoot : M,
      RawCodedPALocalProofOf M context target transportedRoot.

Arguments RawCodedPAEmptyContextToWitnessedContextTransport M
  : clear implicits.

(** Sharper assembly using the five empty-context local-proof totals.  The
    final successor certificate is opened once; its own witness list and
    context become the next common context.  Transport is applied only to the
    five closed native roots, while the final root remains untouched. *)
Theorem
    raw_dynamicTruthNativeSplicedMasterPositiveComponentSuccessor_of_local_proof_totals_and_empty_context_transport
    : forall (M : RawPAModel), RawPASatisfies M ->
  RawDynamicTruthNativePositiveLocalProofTotals M ->
  RawRestrictedPAConsistencyCertificateSuccessor M ->
  RawCodedPAEmptyContextToWitnessedContextTransport M ->
  RawDynamicTruthNativeSplicedMasterPositiveComponentSuccessor M.
Proof.
  intros M hPA
    (hlocalTotal & hcrossTotal & hshiftTotal & hsubstitutionTotal &
      haxiomSoundnessTotal)
    hconsistencySuccessor htransport.
  intros tail level currentLocal currentCrossLevel currentShift
    currentSubstitution currentAxiomSoundness currentFinal
    hcurrentGraphs hcurrentProofs.
  destruct (hlocalTotal tail level) as
    (nextLocal & localRoot & hnextLocalGraph & hnextLocalProof).
  destruct (hcrossTotal tail level) as
    (nextCrossLevel & crossRoot & hnextCrossGraph & hnextCrossProof).
  destruct (hshiftTotal tail level) as
    (nextShift & shiftRoot & hnextShiftGraph & hnextShiftProof).
  destruct (hsubstitutionTotal tail level) as
    (nextSubstitution & substitutionRoot & hnextSubstitutionGraph &
      hnextSubstitutionProof).
  destruct (haxiomSoundnessTotal tail level) as
    (nextAxiomSoundness & axiomSoundnessRoot &
      hnextAxiomSoundnessGraph & hnextAxiomSoundnessProof).
  unfold RawSixFieldMasterGraphWitnessesAt in hcurrentGraphs.
  destruct hcurrentGraphs as
    (hcurrentLocalGraph & hcurrentCrossGraph & hcurrentShiftGraph &
      hcurrentSubstitutionGraph & hcurrentAxiomSoundnessGraph &
      hcurrentFinalGraph).
  assert (hcurrentFinalTarget :
      RawRestrictedPAConsistencyFormulaCodeAt M level currentFinal).
  {
    exact (proj1
      (compactRestrictedPAConsistencyFormulaCodeGraph_representation
        M tail level currentFinal) hcurrentFinalGraph).
  }
  destruct
    (raw_codedPAProofOf_final_of_sixFieldMaster_common_context M
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal hcurrentProofs) as
    [currentFinalCertificate hcurrentFinalProof].
  destruct
    (raw_restrictedPAConsistencyFormulaCodeAt_total M hPA
      (raw_succ M level)) as [nextFinal hnextFinalTarget].
  destruct
    (hconsistencySuccessor level currentFinal currentFinalCertificate
      nextFinal hcurrentFinalTarget hcurrentFinalProof hnextFinalTarget) as
    [nextFinalCertificate hnextFinalProof].
  assert (hnextFinalGraph :
      raw_formula_sat M
        (scons M nextFinal (scons M (raw_succ M level) tail))
        compactRestrictedPAConsistencyFormulaCodeGraph).
  {
    exact (proj2
      (compactRestrictedPAConsistencyFormulaCodeGraph_representation
        M tail (raw_succ M level) nextFinal) hnextFinalTarget).
  }
  unfold RawCodedPAProofOf in hnextFinalProof.
  destruct hnextFinalProof as
    (nextWitnessList & nextFinalRoot & nextContext &
      _hnextCertificateCode & hnextWitnessedContext &
      hnextFinalCoverage & hnextFinalEndpoint).
  destruct
    (htransport nextWitnessList nextContext nextLocal localRoot
      hnextWitnessedContext hnextLocalProof) as
    [nextLocalRoot hnextLocalContextProof].
  destruct
    (htransport nextWitnessList nextContext nextCrossLevel crossRoot
      hnextWitnessedContext hnextCrossProof) as
    [nextCrossRoot hnextCrossContextProof].
  destruct
    (htransport nextWitnessList nextContext nextShift shiftRoot
      hnextWitnessedContext hnextShiftProof) as
    [nextShiftRoot hnextShiftContextProof].
  destruct
    (htransport nextWitnessList nextContext nextSubstitution
      substitutionRoot hnextWitnessedContext hnextSubstitutionProof) as
    [nextSubstitutionRoot hnextSubstitutionContextProof].
  destruct
    (htransport nextWitnessList nextContext nextAxiomSoundness
      axiomSoundnessRoot hnextWitnessedContext
      hnextAxiomSoundnessProof) as
    [nextAxiomSoundnessRoot hnextAxiomSoundnessContextProof].
  exists nextLocal, nextCrossLevel, nextShift, nextSubstitution,
    nextAxiomSoundness, nextFinal.
  split.
  - unfold RawDynamicTruthSplicedMasterPositiveGraphWitnessesAt.
    repeat split; assumption.
  - unfold RawSixFieldMasterCommonContextProofsOf.
    exists nextWitnessList, nextContext,
      nextLocalRoot, nextCrossRoot, nextShiftRoot,
      nextSubstitutionRoot, nextAxiomSoundnessRoot, nextFinalRoot.
    split; [exact hnextWitnessedContext |].
    split; [exact hnextLocalContextProof |].
    split; [exact hnextCrossContextProof |].
    split; [exact hnextShiftContextProof |].
    split; [exact hnextSubstitutionContextProof |].
    split; [exact hnextAxiomSoundnessContextProof |].
    unfold RawCodedPALocalProofOf. split; assumption.
Qed.

(** Direct connection to the complementary local-root compilation module.
    This corollary discharges all five local-total premises at once; the
    transparent context-transport primitive remains the sole context gap. *)
Corollary
    raw_dynamicTruthNativeSplicedMasterPositiveComponentSuccessor_of_local_roots_and_empty_context_transport
    : forall (M : RawPAModel), RawPASatisfies M ->
  RawDynamicTruthNativeLocalLeafRootCompiler M ->
  RawDynamicTruthNativeCrossLevelLocalRootCompiler M ->
  RawDynamicTruthNativeShiftLocalRootCompiler M ->
  RawDynamicTruthNativeSubstitutionLocalRootCompiler M ->
  RawDynamicTruthNativeAxiomSoundnessLocalRootCompiler M ->
  RawRestrictedPAConsistencyCertificateSuccessor M ->
  RawCodedPAEmptyContextToWitnessedContextTransport M ->
  RawDynamicTruthNativeSplicedMasterPositiveComponentSuccessor M.
Proof.
  intros M hPA hlocal hcross hshift hsubstitution haxiomSoundness
    hconsistencySuccessor htransport.
  apply
    raw_dynamicTruthNativeSplicedMasterPositiveComponentSuccessor_of_local_proof_totals_and_empty_context_transport;
    try assumption.
  exact (dynamicTruthNativePositiveLocalProofTotals_of_local_roots
    M hPA hlocal hcross hshift hsubstitution haxiomSoundness).
Qed.

End PABoundedRawCodedDynamicTruthNativeMasterSuccessorFromProofTotals.
