(**
  Eliminate the context-transplant side condition for the restricted
  dynamic-soundness producer.

  The legacy producer factorisation asks for an unrestricted one-head
  transplant.  That premise is intentionally too broad: an arbitrary carrier
  value need not be a formula whose bound variables can be shifted.  The four
  heads used by the restricted consistency target are different.  Three are
  represented shifts of the fixed proof-checker contexts, and the fourth is
  the seven-field checker conjunction.  The restricted-target shift tree and
  the target atomic-adequacy theorem certify exactly those four heads.

  We therefore replay the four guarded single-cons steps directly.  This
  keeps the caller's witnessed context throughout and removes the broad
  [RawCodedPALocalProofConsTransplant] premise without claiming a general
  weakening theorem.
*)

From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors
  RawCodedContextLists
  RawCodedContextStructure
  RawCodedNumeralTermCode
  RawCodedFixedLevelTruthTotality
  RawCodedFormulaShiftAtomicAdequacy
  RawCodedRestrictedTargetFormulaShift
  RawCodedFormulaOperationTraceConcatenation
  RawCodedRestrictedPAConsistencyShiftRealization
  RawCodedRestrictedPAConsistencyOpenDescent
  RawCodedRestrictedPADynamicSoundnessProducer
  RawCodedRestrictedPADynamicSoundnessComposition
  CompactPAUniformProvability
  RawCodedPALocalProofConsTransplant
  RawCodedPALocalProofWitnessedContextMerge
  RawCodedPALocalProofContextInsertComplete
  RawCodedDynamicTruthNativeFinalBridgeFieldsHeadAdequacy.

Module
  PABoundedRawCodedRestrictedPADynamicSoundnessProducerFromBaseAndCompositional.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedContextLists.
Import PABoundedRawCodedContextStructure.
Import PABoundedRawCodedNumeralTermCode.
Import PABoundedRawCodedFixedLevelTruthTotality.
Import PABoundedRawCodedFormulaShiftAtomicAdequacy.
Import PABoundedRawCodedRestrictedTargetFormulaShift.
Import PABoundedRawCodedFormulaOperationTraceConcatenation.
Import PABoundedRawCodedRestrictedPAConsistencyShiftRealization.
Import PABoundedRawCodedRestrictedPAConsistencyOpenDescent.
Import PABoundedRawCodedRestrictedPADynamicSoundnessProducer.
Import PABoundedRawCodedRestrictedPADynamicSoundnessComposition.
Import PABoundedCompactPAUniformProvability.
Import PABoundedRawCodedPALocalProofConsTransplant.
Import PABoundedRawCodedPALocalProofWitnessedContextMerge.
Import PABoundedRawCodedPALocalProofContextInsertComplete.
Import PABoundedRawCodedDynamicTruthNativeFinalBridgeFieldsHeadAdequacy.

(** A shift edge certifies atomic adequacy of its target.  The three
    checker-context heads are exactly the targets at prior 1, 2, and 3. *)
Lemma raw_restrictedPAProofAfterProofIteratedShiftCode_atomically_adequate :
    forall (M : RawPAModel), RawPASatisfies M -> forall
    level numeralCode,
  RawNumeralTermCodeAt M level numeralCode ->
  RawCodedFormulaAtomicallyAdequate M
    (rawRestrictedPAProofAfterProofIteratedShiftCode M numeralCode 1).
Proof.
  intros M hPA level numeralCode hnumeral.
  apply (raw_codedFormulaShift_target_atomically_adequate M hPA
    (rawNumeralValue M 0) (rawNumeralValue M 1)
    (rawRestrictedTargetFormulaContextIteratedShiftCode
      M numeralCode 0 0 restrictedPAProofAfterProofFormulaContext)
    (rawRestrictedTargetFormulaContextIteratedShiftCode
      M numeralCode 0 1 restrictedPAProofAfterProofFormulaContext)).
  exact (raw_codedFormulaShift_restrictedTargetContext_iterated
    M hPA level numeralCode 0 0
    restrictedPAProofAfterProofFormulaContext hnumeral
    restrictedPAProofAfterProofFormulaContext_shift_supported).
Qed.

Lemma raw_restrictedPAProofAfterWitnessIteratedShiftCode_atomically_adequate :
    forall (M : RawPAModel), RawPASatisfies M -> forall
    level numeralCode,
  RawNumeralTermCodeAt M level numeralCode ->
  RawCodedFormulaAtomicallyAdequate M
    (rawRestrictedPAProofAfterWitnessIteratedShiftCode M numeralCode 2).
Proof.
  intros M hPA level numeralCode hnumeral.
  apply (raw_codedFormulaShift_target_atomically_adequate M hPA
    (rawNumeralValue M 0) (rawNumeralValue M 1)
    (rawRestrictedTargetFormulaContextIteratedShiftCode
      M numeralCode 0 1 restrictedPAProofAfterWitnessFormulaContext)
    (rawRestrictedTargetFormulaContextIteratedShiftCode
      M numeralCode 0 2 restrictedPAProofAfterWitnessFormulaContext)).
  exact (raw_codedFormulaShift_restrictedTargetContext_iterated
    M hPA level numeralCode 0 1
    restrictedPAProofAfterWitnessFormulaContext hnumeral
    restrictedPAProofAfterWitnessFormulaContext_shift_supported).
Qed.

Lemma raw_restrictedPAProofAssumptionIteratedShiftCode_atomically_adequate :
    forall (M : RawPAModel), RawPASatisfies M -> forall
    level numeralCode,
  RawNumeralTermCodeAt M level numeralCode ->
  RawCodedFormulaAtomicallyAdequate M
    (rawRestrictedPAProofAssumptionIteratedShiftCode M numeralCode 3).
Proof.
  intros M hPA level numeralCode hnumeral.
  apply (raw_codedFormulaShift_target_atomically_adequate M hPA
    (rawNumeralValue M 0) (rawNumeralValue M 1)
    (rawRestrictedTargetFormulaContextIteratedShiftCode
      M numeralCode 0 2 restrictedPAProofAssumptionFormulaContext)
    (rawRestrictedTargetFormulaContextIteratedShiftCode
      M numeralCode 0 3 restrictedPAProofAssumptionFormulaContext)).
  exact (raw_codedFormulaShift_restrictedTargetContext_iterated
    M hPA level numeralCode 0 2
    restrictedPAProofAssumptionFormulaContext hnumeral
    restrictedPAProofAssumptionFormulaContext_shift_supported).
Qed.

(** The four guarded steps are deliberately written out.  Besides making the
    context order auditable, this ensures that every later step uses the
    realizability certificate generated by the previous step. *)
Theorem
    raw_restrictedPADynamicSoundnessProducer_of_baseProof_and_compositional
    : forall (M : RawPAModel), RawPASatisfies M ->
  RawRestrictedPADynamicSoundnessBaseProof M ->
  RawRestrictedPADynamicSoundnessProducer M.
Proof.
  intros M hPA hbase
    value numeralCode baseWitnessList baseContext hnumeral hwitness.
  destruct (hbase value numeralCode baseWitnessList baseContext
    hnumeral hwitness) as [child0 hchild0].
  assert (hrealizable0 : RawContextListRealizable M baseContext).
  {
    exact (raw_codedPAAxiomWitnessContext_context_realizable M
      baseWitnessList baseContext hwitness).
  }
  set (proofFormula := rawRestrictedPADynamicSoundnessImplicationCode
    M numeralCode).
  set (proofShift := rawRestrictedPAProofAfterProofIteratedShiftCode
    M numeralCode 1).
  set (witnessShift := rawRestrictedPAProofAfterWitnessIteratedShiftCode
    M numeralCode 2).
  set (assumptionShift := rawRestrictedPAProofAssumptionIteratedShiftCode
    M numeralCode 3).
  set (fields := rawRestrictedPAProofFieldsCode M numeralCode).
  assert (hproofShift : RawCodedFormulaAtomicallyAdequate M proofShift).
  {
    unfold proofShift.
    exact (raw_restrictedPAProofAfterProofIteratedShiftCode_atomically_adequate
      M hPA value numeralCode hnumeral).
  }
  assert (hwitnessShift : RawCodedFormulaAtomicallyAdequate M witnessShift).
  {
    unfold witnessShift.
    exact (raw_restrictedPAProofAfterWitnessIteratedShiftCode_atomically_adequate
      M hPA value numeralCode hnumeral).
  }
  assert (hassumptionShift : RawCodedFormulaAtomicallyAdequate M
      assumptionShift).
  {
    unfold assumptionShift.
    exact (raw_restrictedPAProofAssumptionIteratedShiftCode_atomically_adequate
      M hPA value numeralCode hnumeral).
  }
  assert (hfields : RawCodedFormulaAtomicallyAdequate M fields).
  {
    unfold fields.
    exact (raw_restrictedPAProofFieldsCode_atomically_adequate
      M hPA value numeralCode hnumeral).
  }
  destruct (raw_codedPALocalProof_adequateConsTransplant_of_compositional
    M hPA (raw_codedFormulaShift_compositional M hPA)
    baseContext assumptionShift proofFormula child0 hassumptionShift
    hrealizable0 hchild0) as [child1 hchild1].
  assert (hrealizable1 : RawContextListRealizable M
      (rawListNode M assumptionShift baseContext)).
  {
    exact (raw_contextList_cons_realizable M hPA baseContext
      assumptionShift hrealizable0).
  }
  destruct (raw_codedPALocalProof_adequateConsTransplant_of_compositional
    M hPA (raw_codedFormulaShift_compositional M hPA)
    (rawListNode M assumptionShift baseContext) witnessShift proofFormula
    child1 hwitnessShift hrealizable1 hchild1) as [child2 hchild2].
  assert (hrealizable2 : RawContextListRealizable M
      (rawListNode M witnessShift
        (rawListNode M assumptionShift baseContext))).
  {
    exact (raw_contextList_cons_realizable M hPA
      (rawListNode M assumptionShift baseContext) witnessShift hrealizable1).
  }
  destruct (raw_codedPALocalProof_adequateConsTransplant_of_compositional
    M hPA (raw_codedFormulaShift_compositional M hPA)
    (rawListNode M witnessShift
      (rawListNode M assumptionShift baseContext)) proofShift proofFormula
    child2 hproofShift hrealizable2 hchild2) as [child3 hchild3].
  assert (hrealizable3 : RawContextListRealizable M
      (rawListNode M proofShift
        (rawListNode M witnessShift
          (rawListNode M assumptionShift baseContext)))).
  {
    exact (raw_contextList_cons_realizable M hPA
      (rawListNode M witnessShift
        (rawListNode M assumptionShift baseContext)) proofShift hrealizable2).
  }
  destruct (raw_codedPALocalProof_adequateConsTransplant_of_compositional
    M hPA (raw_codedFormulaShift_compositional M hPA)
    (rawListNode M proofShift
      (rawListNode M witnessShift
        (rawListNode M assumptionShift baseContext))) fields proofFormula
    child3 hfields hrealizable3 hchild3) as [child4 hchild4].
  exists child4.
  exact hchild4.
Qed.

Corollary
    raw_restrictedPADynamicSoundnessProducerInAllModels_of_baseProof_and_compositional
    : RawRestrictedPADynamicSoundnessBaseProofInAllModels ->
  RawRestrictedPADynamicSoundnessProducerInAllModels.
Proof.
  intros hbase M hPA.
  exact (raw_restrictedPADynamicSoundnessProducer_of_baseProof_and_compositional
    M hPA (hbase M hPA)).
Qed.

(** Consequently the broad transplant premise disappears from the compact
    endpoint as well; the only remaining premise here is the exact
    base-context proof of the dynamic-soundness implication. *)
Corollary
    PA_BProv_compactUniformRestrictedPAConsistencyProvabilityFormula_of_baseProof_and_compositional
    : RawRestrictedPADynamicSoundnessBaseProofInAllModels ->
  Formula.BProv Formula.Ax_s nil
    compactUniformRestrictedPAConsistencyProvabilityFormula.
Proof.
  intro hbase.
  apply
    PA_BProv_compactUniformRestrictedPAConsistencyProvabilityFormula_of_dynamicSoundnessProducer.
  exact
    (raw_restrictedPADynamicSoundnessProducerInAllModels_of_baseProof_and_compositional
      hbase).
Qed.

End
  PABoundedRawCodedRestrictedPADynamicSoundnessProducerFromBaseAndCompositional.
