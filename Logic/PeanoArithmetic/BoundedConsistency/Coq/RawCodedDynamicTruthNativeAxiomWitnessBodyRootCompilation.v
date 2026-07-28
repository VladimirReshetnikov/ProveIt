(**
  Dependency-aware reduction of the native PA-axiom witness-body leaves.

  [RawCodedDynamicTruthNativeAxiomSoundnessLeafRootCompilation] reduces the
  native axiom-soundness field to two local roots.  Their contexts differ
  only in the shifted lower-domain assumption selected by an outer [Or-E].
  The mathematical content needed at a positive orbit stage is better
  isolated before either of those assumptions is installed:

      shifted-base |- shifted-antecedent -> witness-body -> shifted-next-Sigma.

  In Lean this is precisely where the dependency-ordered axiom-soundness
  kernel consumes the previous certificate fields and the newly established
  local, cross-level, shift, and substitution fields.  This file gives the
  corresponding raw-proof boundary in Coq.  From one such staged kernel root
  it constructs both old leaves using only checked context insertion,
  assumption leaves, and two applications of [Imp-E].

  The compiler remains indexed by the actual successor rows exposed by the
  axiom-soundness trace.  In particular the Sigma row, Pi row, their lower
  applications, their shared wrapper, and the next-Sigma application cannot
  be selected independently.  No empty-base instance is asserted: the
  positive staged kernel genuinely needs the proof resources carried by its
  visible base context.  Nor is semantic PA-axiom truth converted into proof
  syntax.  A later fixed-source/template compilation should construct the
  single staged kernel root named below.
*)

From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAListCoding Require Import Representability.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  CodedSyntax
  RawCodedSyntaxConstructors
  RawCodedFormulaOperations
  RawCodedFixedLevelTruthTotality
  RawCodedFormulaShiftAtomicAdequacy
  RawCodedProofAtomicAdequacyStandard
  RawCodedContextLists
  RawCodedContextStructure
  RawCodedContextShift
  RawCodedRestrictedPAProof
  RawCodedProofAssumptionLeaf
  RawCodedProofBinaryConstructors
  RawCodedPALocalProofExistential
  RawCodedPALocalProofComposition
  RawCodedPALocalProofContextInsertUnconditional
  RawCodedDynamicTruthNativeAxiomSoundnessProofCompilation
  RawCodedDynamicTruthNativeAxiomSoundnessLeafRootCompilation.

Module
  PABoundedRawCodedDynamicTruthNativeAxiomWitnessBodyRootCompilation.

Import PA.
Import PAListRepresentability.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedCodedSyntax.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedFixedLevelTruthTotality.
Import PABoundedRawCodedFormulaShiftAtomicAdequacy.
Import PABoundedRawCodedProofAtomicAdequacyStandard.
Import PABoundedRawCodedContextLists.
Import PABoundedRawCodedContextStructure.
Import PABoundedRawCodedContextShift.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedProofAssumptionLeaf.
Import PABoundedRawCodedProofBinaryConstructors.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPALocalProofComposition.
Import PABoundedRawCodedPALocalProofContextInsertUnconditional.
Import PABoundedRawCodedDynamicTruthNativeAxiomSoundnessProofCompilation.
Import
  PABoundedRawCodedDynamicTruthNativeAxiomSoundnessLeafRootCompilation.

(** ------------------------------------------------------------------
    The single dependency-ordered kernel target. *)

(** The two implications are deliberately curried.  This lets the raw proof
    compiler add the shifted soundness antecedent first and the opened axiom
    witness second, exactly matching the context order below [Ex-E]. *)
Definition rawDynamicTruthNativeAxiomWitnessBodyKernelCode
    (M : RawPAModel) (shiftedAntecedent shiftedNextSigma : M) : M :=
  rawFormulaImpCode M shiftedAntecedent
    (rawFormulaImpCode M
      (rawDynamicTruthNativeAxiomWitnessBodyCode M)
      shiftedNextSigma).

Arguments rawDynamicTruthNativeAxiomWitnessBodyKernelCode
  M shiftedAntecedent shiftedNextSigma : clear implicits.

Definition RawDynamicTruthNativeAxiomWitnessBodyKernelRootOn
    (M : RawPAModel)
    (shiftedBaseContext shiftedAntecedent shiftedNextSigma : M) : Prop :=
  exists kernelRoot : M,
    RawCodedPALocalProofOf M shiftedBaseContext
      (rawDynamicTruthNativeAxiomWitnessBodyKernelCode M
        shiftedAntecedent shiftedNextSigma)
      kernelRoot.

Arguments RawDynamicTruthNativeAxiomWitnessBodyKernelRootOn
  M shiftedBaseContext shiftedAntecedent shiftedNextSigma : clear implicits.

(** This is the exact one-root successor interface left for the eventual
    staged fixed-source proof.  It repeats all parameters of the old two-leaf
    callback so the kernel remains attached to one concrete trace.  The four
    shift premises prevent a caller from mixing the target of one binder
    opening with domains or an antecedent selected by another. *)
Definition
    RawDynamicTruthNativeAxiomLinkedWitnessBodyKernelRootCompiler
    (M : RawPAModel) : Prop :=
  forall (tail : nat -> M) predecessorLevel
      currentGlobalSigma currentGlobalPi
      sigmaDomain piDomain nextSigmaEvidence
      sigmaRowDomain piRowDomain
      lowerPiApplication lowerSigmaApplication
      baseContext shiftedBaseContext
      shiftedAntecedent shiftedSigmaDomain shiftedPiDomain
      shiftedNextSigma,
    RawDynamicTruthNativeAxiomSoundnessLinkedRowsAt M tail
      predecessorLevel currentGlobalSigma currentGlobalPi
      sigmaDomain piDomain nextSigmaEvidence
      sigmaRowDomain piRowDomain
      lowerPiApplication lowerSigmaApplication ->
    RawContextShift M baseContext shiftedBaseContext ->
    RawCodedFormulaShift M
      (raw_zero M) (rawNumeralValue M 1)
      (rawDynamicTruthNativeAxiomSoundnessAntecedentCode M
        sigmaDomain piDomain)
      shiftedAntecedent ->
    RawCodedFormulaShift M
      (raw_zero M) (rawNumeralValue M 1)
      sigmaDomain shiftedSigmaDomain ->
    RawCodedFormulaShift M
      (raw_zero M) (rawNumeralValue M 1)
      piDomain shiftedPiDomain ->
    RawCodedFormulaShift M
      (raw_zero M) (rawNumeralValue M 1)
      nextSigmaEvidence shiftedNextSigma ->
    RawDynamicTruthNativeAxiomWitnessBodyKernelRootOn M
      shiftedBaseContext shiftedAntecedent shiftedNextSigma.

Arguments
  RawDynamicTruthNativeAxiomLinkedWitnessBodyKernelRootCompiler M
  : clear implicits.

(** ------------------------------------------------------------------
    Mechanical compilation of one domain-specialized witness leaf. *)

Lemma raw_dynamicTruthNativeAxiomWitnessBodyCode_atomically_adequate :
    forall (M : RawPAModel), RawPASatisfies M ->
  RawCodedFormulaAtomicallyAdequate M
    (rawDynamicTruthNativeAxiomWitnessBodyCode M).
Proof.
  intros M hPA.
  unfold rawDynamicTruthNativeAxiomWitnessBodyCode.
  rewrite <- (rawQuotedFormulaCode_standard M hPA
    dynamicTruthNativeAxiomWitnessBodyFormula).
  exact (raw_quotedFormula_atomically_adequate M hPA
    dynamicTruthNativeAxiomWitnessBodyFormula).
Qed.

(** A single staged kernel gives one leaf after a selected shifted domain is
    supplied.  Every context extension is adequacy guarded.  Notice that the
    source base is used only through its represented shift: this obtains an
    honest traversal of the shifted base and does not erase its contents. *)
Theorem raw_dynamicTruthNativeAxiomWitnessBodyLeaf_of_kernel_root : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      baseContext shiftedBaseContext
      antecedent shiftedAntecedent
      domain shiftedDomain shiftedNextSigma kernelRoot,
  RawContextShift M baseContext shiftedBaseContext ->
  RawCodedFormulaShift M
    (raw_zero M) (rawNumeralValue M 1)
    antecedent shiftedAntecedent ->
  RawCodedFormulaShift M
    (raw_zero M) (rawNumeralValue M 1)
    domain shiftedDomain ->
  RawCodedPALocalProofOf M shiftedBaseContext
    (rawDynamicTruthNativeAxiomWitnessBodyKernelCode M
      shiftedAntecedent shiftedNextSigma)
    kernelRoot ->
  exists leaf : M,
    RawCodedPALocalProofOf M
      (rawDynamicTruthNativeAxiomWitnessContext M
        shiftedBaseContext shiftedAntecedent shiftedDomain)
      shiftedNextSigma leaf.
Proof.
  intros M hPA baseContext shiftedBaseContext
    antecedent shiftedAntecedent domain shiftedDomain
    shiftedNextSigma kernelRoot hbaseShift hantecedentShift
    hdomainShift hkernel.
  set (witnessBody := rawDynamicTruthNativeAxiomWitnessBodyCode M).
  set (antecedentContext :=
    rawListNode M shiftedAntecedent shiftedBaseContext).
  set (domainContext :=
    rawListNode M shiftedDomain antecedentContext).
  set (witnessContext := rawListNode M witnessBody domainContext).

  assert (hbaseRealizable :
      RawContextListRealizable M shiftedBaseContext).
  { exact (raw_contextShift_target_realizable M
      baseContext shiftedBaseContext hbaseShift). }
  assert (hantecedentAdequate :
      RawCodedFormulaAtomicallyAdequate M shiftedAntecedent).
  { exact (raw_codedFormulaShift_target_atomically_adequate M hPA
      (raw_zero M) (rawNumeralValue M 1)
      antecedent shiftedAntecedent hantecedentShift). }
  assert (hdomainAdequate :
      RawCodedFormulaAtomicallyAdequate M shiftedDomain).
  { exact (raw_codedFormulaShift_target_atomically_adequate M hPA
      (raw_zero M) (rawNumeralValue M 1)
      domain shiftedDomain hdomainShift). }
  assert (hwitnessAdequate :
      RawCodedFormulaAtomicallyAdequate M witnessBody).
  { unfold witnessBody.
    exact
      (raw_dynamicTruthNativeAxiomWitnessBodyCode_atomically_adequate
        M hPA). }

  (** Install the shifted outer antecedent and apply the first implication. *)
  destruct (raw_codedPALocalProof_adequateConsTransplant
    M hPA shiftedBaseContext shiftedAntecedent
    (rawDynamicTruthNativeAxiomWitnessBodyKernelCode M
      shiftedAntecedent shiftedNextSigma)
    kernelRoot hantecedentAdequate hbaseRealizable hkernel) as
    [kernelAtAntecedent hkernelAtAntecedent].
  pose proof (raw_codedPALocalProofOf_assumption M hPA
    shiftedBaseContext shiftedAntecedent hbaseRealizable)
    as hantecedentRoot.
  pose proof (raw_codedPALocalProofOf_impE M hPA
    antecedentContext shiftedAntecedent
    (rawFormulaImpCode M witnessBody shiftedNextSigma)
    kernelAtAntecedent
    (rawProofAssumptionRoot M antecedentContext shiftedAntecedent)
    hkernelAtAntecedent hantecedentRoot) as hwitnessImpAtAntecedent.

  assert (hantecedentContextRealizable :
      RawContextListRealizable M antecedentContext).
  { unfold antecedentContext.
    exact (raw_contextList_cons_realizable M hPA
      shiftedBaseContext shiftedAntecedent hbaseRealizable). }

  (** Install the selected domain.  This step is the only difference between
      the Sigma and Pi leaves.  The kernel theorem itself is shared. *)
  destruct (raw_codedPALocalProof_adequateConsTransplant
    M hPA antecedentContext shiftedDomain
    (rawFormulaImpCode M witnessBody shiftedNextSigma)
    (rawProofImpERoot M antecedentContext shiftedAntecedent
      (rawFormulaImpCode M witnessBody shiftedNextSigma)
      kernelAtAntecedent
      (rawProofAssumptionRoot M antecedentContext shiftedAntecedent))
    hdomainAdequate hantecedentContextRealizable
    hwitnessImpAtAntecedent) as
    [witnessImpAtDomain hwitnessImpAtDomain].
  assert (hdomainContextRealizable :
      RawContextListRealizable M domainContext).
  { unfold domainContext.
    exact (raw_contextList_cons_realizable M hPA
      antecedentContext shiftedDomain hantecedentContextRealizable). }

  (** Finally open the transparent witness body and apply the second
      implication.  This produces the literal context required by Ex-E. *)
  destruct (raw_codedPALocalProof_adequateConsTransplant
    M hPA domainContext witnessBody
    (rawFormulaImpCode M witnessBody shiftedNextSigma)
    witnessImpAtDomain hwitnessAdequate hdomainContextRealizable
    hwitnessImpAtDomain) as
    [witnessImpAtWitness hwitnessImpAtWitness].
  pose proof (raw_codedPALocalProofOf_assumption M hPA
    domainContext witnessBody hdomainContextRealizable) as hwitnessRoot.
  exists (rawProofImpERoot M witnessContext witnessBody shiftedNextSigma
    witnessImpAtWitness
    (rawProofAssumptionRoot M witnessContext witnessBody)).
  change (RawCodedPALocalProofOf M witnessContext shiftedNextSigma
    (rawProofImpERoot M witnessContext witnessBody shiftedNextSigma
      witnessImpAtWitness
      (rawProofAssumptionRoot M witnessContext witnessBody))).
  exact (raw_codedPALocalProofOf_impE M hPA
    witnessContext witnessBody shiftedNextSigma
    witnessImpAtWitness
    (rawProofAssumptionRoot M witnessContext witnessBody)
    hwitnessImpAtWitness hwitnessRoot).
Qed.

(** ------------------------------------------------------------------
    Reduction of the old two-leaf callback to the staged kernel. *)

Theorem
    raw_dynamicTruthNativeAxiomLinkedWitnessBodyLeafRootCompiler_of_kernel :
    forall (M : RawPAModel), RawPASatisfies M ->
  RawDynamicTruthNativeAxiomLinkedWitnessBodyKernelRootCompiler M ->
  RawDynamicTruthNativeAxiomLinkedWitnessBodyLeafRootCompiler M.
Proof.
  intros M hPA hkernelCompiler tail predecessorLevel
    currentGlobalSigma currentGlobalPi sigmaDomain piDomain
    nextSigmaEvidence sigmaRowDomain piRowDomain
    lowerPiApplication lowerSigmaApplication
    baseContext shiftedBaseContext
    shiftedAntecedent shiftedSigmaDomain shiftedPiDomain
    shiftedNextSigma hlinked hbaseShift hantecedentShift
    hsigmaShift hpiShift hnextShift.
  destruct (hkernelCompiler tail predecessorLevel
    currentGlobalSigma currentGlobalPi sigmaDomain piDomain
    nextSigmaEvidence sigmaRowDomain piRowDomain
    lowerPiApplication lowerSigmaApplication
    baseContext shiftedBaseContext shiftedAntecedent
    shiftedSigmaDomain shiftedPiDomain shiftedNextSigma
    hlinked hbaseShift hantecedentShift hsigmaShift hpiShift hnextShift) as
    [kernelRoot hkernelRoot].
  destruct (raw_dynamicTruthNativeAxiomWitnessBodyLeaf_of_kernel_root
    M hPA baseContext shiftedBaseContext
    (rawDynamicTruthNativeAxiomSoundnessAntecedentCode M
      sigmaDomain piDomain)
    shiftedAntecedent sigmaDomain shiftedSigmaDomain
    shiftedNextSigma kernelRoot hbaseShift hantecedentShift
    hsigmaShift hkernelRoot) as [sigmaLeaf hsigmaLeaf].
  destruct (raw_dynamicTruthNativeAxiomWitnessBodyLeaf_of_kernel_root
    M hPA baseContext shiftedBaseContext
    (rawDynamicTruthNativeAxiomSoundnessAntecedentCode M
      sigmaDomain piDomain)
    shiftedAntecedent piDomain shiftedPiDomain
    shiftedNextSigma kernelRoot hbaseShift hantecedentShift
    hpiShift hkernelRoot) as [piLeaf hpiLeaf].
  exists sigmaLeaf, piLeaf. split; assumption.
Qed.

(** The following endpoint composes the one-root reduction with the complete
    structural shell from the preceding module.  It is intentionally
    conditional: proving the staged kernel is the remaining fixed-source
    axiom-soundness task, and no semantic validity shortcut is hidden here. *)
Corollary
    raw_dynamicTruthNativeAxiomSoundnessLocalRootCompiler_of_linked_witness_body_kernel :
    forall (M : RawPAModel), RawPASatisfies M ->
  RawDynamicTruthNativeAxiomLinkedWitnessBodyKernelRootCompiler M ->
  RawDynamicTruthNativeAxiomSoundnessLocalRootCompiler M.
Proof.
  intros M hPA hkernel.
  exact
    (raw_dynamicTruthNativeAxiomSoundnessLocalRootCompiler_of_linked_witness_body_leaves
      M hPA
      (raw_dynamicTruthNativeAxiomLinkedWitnessBodyLeafRootCompiler_of_kernel
        M hPA hkernel)).
Qed.

End
  PABoundedRawCodedDynamicTruthNativeAxiomWitnessBodyRootCompilation.
