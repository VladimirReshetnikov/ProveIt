(**
  Growing-context discharge of the strong-prefix finalizer.

  The fixed-context finalizer cannot manufacture [d < S d] when its
  witnessed base is allowed to be empty: raw PA proofs carry every PA axiom
  they use as an explicit context assumption.  The honest remedy is to let
  the arithmetic proof choose its finite standard PA-axiom prefix first.

  This module performs that construction without changing the final target:

  - quote the ordinary PA proof of [d < S d] over the caller's base;
  - adjoin the already selected induction axiom above the enlarged base;
  - weaken both the arithmetic root and the incoming strong-step root into
    that one common witnessed context;
  - insert the closed [forall d, K(d)] assumption with an explicit
    binder-readiness proof;
  - invoke the checked logical finalizer and the existing case compiler.

  The resulting ordinary certificate exposes the selected finite prefix in
  its witness/context code.  No fixed-context compiler, semantic soundness
  principle, or unregistered axiom is assumed.
*)

From Stdlib Require Import List.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  CodedProof
  RawCodedSyntaxConstructors
  RawCodedFormulaOperations
  RawCodedContextLists
  RawCodedContextStructure
  RawCodedContextShift
  RawCodedRestrictedPAProof
  RawCodedPALocalProofExistential
  RawCodedPAProvability
  RawCodedPAAxiomWitnessPrefix
  RawCodedPAInductionAxiomCertificate
  RawCodedTemplateSyntax
  RawCodedTemplateStructuralTranslation
  RawCodedTemplateStructuralPAAgreement
  RawCodedTemplatePAEmbeddingSelfShiftTail
  RawCodedPALocalProofWitnessedContextMerge
  RawCodedPALocalProofWitnessedContextMergeTransportComplete
  RawCodedRestrictedPAConsistencyFromUniversalSoundness
  RawCodedRestrictedPADerivationSoundnessCarrierStrongPrefixInductionShell
  RawCodedRestrictedPADerivationSoundnessCarrierStrongPrefixFinalizerCompilation.

Import ListNotations.

Module
  PABoundedRawCodedRestrictedPADerivationSoundnessCarrierStrongPrefixGrowingFinalizer.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedCodedProof.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedContextLists.
Import PABoundedRawCodedContextStructure.
Import PABoundedRawCodedContextShift.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPAProvability.
Import PABoundedRawCodedPAAxiomWitnessPrefix.
Import PABoundedRawCodedPAInductionAxiomCertificate.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateStructuralTranslation.
Import PABoundedRawCodedTemplateStructuralPAAgreement.
Import PABoundedRawCodedTemplatePAEmbeddingSelfShiftTail.
Import PABoundedRawCodedPALocalProofWitnessedContextMerge.
Import PABoundedRawCodedPALocalProofWitnessedContextMergeTransportComplete.
Import PABoundedRawCodedRestrictedPAConsistencyFromUniversalSoundness.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessCarrierStrongPrefixInductionShell.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessCarrierStrongPrefixFinalizerCompilation.

(** ------------------------------------------------------------------
    Prefix inclusion and the closed-head binder square. *)

(** A standard PA prefix only prepends rows, so every member of the old
    carrier-coded context remains a member of the enlarged context. *)
Lemma raw_contextListIncluded_standardPAAxiomWitnessPrefix_base : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    (prefix : StandardPAAxiomWitnessPrefix) baseContext,
  RawContextListIncluded M baseContext
    (rawStandardPAAxiomWitnessPrefixContextCode M prefix baseContext).
Proof.
  intros M hPA prefix.
  induction prefix as [| witness tail ih]; intro baseContext.
  - exact (raw_contextListIncluded_refl M baseContext).
  - cbn [rawStandardPAAxiomWitnessPrefixContextCode].
    exact (raw_contextListIncluded_cons_target M hPA
      baseContext
      (rawStandardPAAxiomWitnessPrefixContextCode M tail baseContext)
      (rawQuotedFormulaCode M (witnessedAxiom witness))
      (ih baseContext)).
Qed.

(** [forall d, K(d)] is a closed structural template.  This exported shift
    certificate is the head edge needed for every binder encountered while
    weakening an arithmetic proof beneath that temporary assumption. *)
Lemma
    raw_coqRestrictedPADerivationSoundnessCarrierStrongPrefixAll_selfShift
    : forall (M : RawPAModel), RawPASatisfies M -> forall
      (inputs : RawCodedTemplateStructuralInputs M),
  RawCodedFormulaShift M
    (raw_zero M) (rawNumeralValue M 1)
    (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixAllCode M inputs)
    (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixAllCode M inputs).
Proof.
  intros M hPA inputs.
  change (RawCodedFormulaShift M
    (raw_zero M) (rawNumeralValue M 1)
    (rawStructuralTemplateFormula inputs
      coqRestrictedPADerivationSoundnessCarrierStrongPrefixAllTemplate)
    (rawStructuralTemplateFormula inputs
      coqRestrictedPADerivationSoundnessCarrierStrongPrefixAllTemplate)).
  pose proof (raw_coqCarrierStrongPrefix_templateFormula_shiftAt
    M hPA inputs 0
    coqRestrictedPADerivationSoundnessCarrierStrongPrefixAllTemplate)
    as hshift.
  rewrite
    coqRestrictedPADerivationSoundnessCarrierStrongPrefixAllTemplate_shift_closed
    in hshift.
  exact hshift.
Qed.

(** Binder readiness is stronger than a one-time source/target shift: it
    must respond to every shifted source chosen by a proof rule.  For a cons
    with a known head shift, the response is explicit—reuse that head image
    above the supplied shifted tail, then use tail membership inclusion. *)
Lemma raw_contextBinderReady_cons_target_of_head_shift : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    source head shiftedHead,
  RawCodedFormulaShift M
    (raw_zero M) (rawNumeralValue M 1) head shiftedHead ->
  RawContextBinderReady M source (rawListNode M head source).
Proof.
  intros M hPA source head shiftedHead hheadShift
    shiftedSource hsourceShift.
  exists (rawListNode M shiftedHead shiftedSource).
  split.
  - exact (raw_contextShift_cons M hPA
      source shiftedSource head shiftedHead hsourceShift hheadShift).
  - exact (raw_contextListIncluded_cons_target M hPA
      shiftedSource shiftedSource shiftedHead
      (raw_contextListIncluded_refl M shiftedSource)).
Qed.

Corollary
    raw_coqRestrictedPADerivationSoundnessCarrierStrongPrefixAll_cons_binderReady
    : forall (M : RawPAModel), RawPASatisfies M -> forall
      (inputs : RawCodedTemplateStructuralInputs M) context,
  RawContextBinderReady M context
    (rawListNode M
      (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixAllCode
        M inputs)
      context).
Proof.
  intros M hPA inputs context.
  exact (raw_contextBinderReady_cons_target_of_head_shift M hPA
    context
    (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixAllCode
      M inputs)
    (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixAllCode
      M inputs)
    (raw_coqRestrictedPADerivationSoundnessCarrierStrongPrefixAll_selfShift
      M hPA inputs)).
Qed.

(** ------------------------------------------------------------------
    Transparent names for the selected growing base. *)

Definition
    rawCoqRestrictedPADerivationSoundnessCarrierGrowingBaseWitnessList
    (M : RawPAModel) (prefix : StandardPAAxiomWitnessPrefix)
    (baseWitnessList : M) : M :=
  rawStandardPAAxiomWitnessPrefixWitnessListCode
    M prefix baseWitnessList.

Definition rawCoqRestrictedPADerivationSoundnessCarrierGrowingBaseContext
    (M : RawPAModel) (prefix : StandardPAAxiomWitnessPrefix)
    (baseContext : M) : M :=
  rawStandardPAAxiomWitnessPrefixContextCode M prefix baseContext.

Arguments
  rawCoqRestrictedPADerivationSoundnessCarrierGrowingBaseWitnessList
  M prefix baseWitnessList : clear implicits.
Arguments rawCoqRestrictedPADerivationSoundnessCarrierGrowingBaseContext
  M prefix baseContext : clear implicits.

(** The full growing result keeps every context-sensitive intermediate root
    visible.  In particular, a later growing case compiler can inspect or
    replace [prefixedStrongStepRoot], [zeroChild], and [stepChild] without
    reverse-engineering them from the final certificate. *)
Definition
    RawCoqRestrictedPADerivationSoundnessCarrierGrowingFinalizationPackageOf
    (M : RawPAModel) (inputs : RawCodedTemplateStructuralInputs M)
    (baseWitnessList baseContext axiom : M)
    (prefix : StandardPAAxiomWitnessPrefix)
    (prefixedStrongStepRoot zeroChild stepChild arithmeticBaseRoot
      arithmeticExtendedRoot arithmeticOpenRoot bodyChild : M) : Prop :=
  let growingWitnessList :=
    rawCoqRestrictedPADerivationSoundnessCarrierGrowingBaseWitnessList
      M prefix baseWitnessList in
  let growingContext :=
    rawCoqRestrictedPADerivationSoundnessCarrierGrowingBaseContext
      M prefix baseContext in
  let extendedWitnessList :=
    rawPAInductionExtendedWitnessList M growingWitnessList
      (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixCode
        M inputs) in
  let extendedContext :=
    rawPAInductionExtendedContext M growingContext axiom in
  let openContext :=
    rawCoqRestrictedPADerivationSoundnessCarrierFinalizerOpenContext
      M inputs growingContext axiom in
  let finalizerRoot :=
    rawCoqRestrictedPADerivationSoundnessCarrierFinalizerRoot
      M inputs growingContext axiom arithmeticOpenRoot in
  RawCodedPAAxiomWitnessContext M growingWitnessList growingContext /\
  RawCodedPALocalProofOf M growingContext
    (rawCoqRestrictedPADerivationSoundnessCarrierFinalizerLtSelfSuccCode
      M inputs)
    arithmeticBaseRoot /\
  RawCodedPAAxiomWitnessContext M extendedWitnessList extendedContext /\
  RawCodedPALocalProofOf M extendedContext
    (rawCoqRestrictedPADerivationSoundnessCarrierStrongStepCode M inputs)
    prefixedStrongStepRoot /\
  RawCodedPALocalProofOf M extendedContext
    (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixZeroCode
      M inputs)
    zeroChild /\
  RawCodedPALocalProofOf M extendedContext
    (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixStepAllCode
      M inputs)
    stepChild /\
  RawCodedPALocalProofOf M extendedContext
    (rawCoqRestrictedPADerivationSoundnessCarrierFinalizerLtSelfSuccCode
      M inputs)
    arithmeticExtendedRoot /\
  RawCodedPALocalProofOf M openContext
    (rawCoqRestrictedPADerivationSoundnessCarrierFinalizerLtSelfSuccCode
      M inputs)
    arithmeticOpenRoot /\
  RawCodedPALocalProofOf M extendedContext
    (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixFinalizerCode
      M inputs)
    finalizerRoot /\
  RawCodedPAProofOf M
    (rawCoqRestrictedPADerivationSoundnessUniversalCode M inputs)
    (rawCoqRestrictedPADerivationSoundnessStrongPrefixFinalizedCertificate
      M inputs growingWitnessList growingContext axiom bodyChild
      zeroChild stepChild finalizerRoot).

Arguments
  RawCoqRestrictedPADerivationSoundnessCarrierGrowingFinalizationPackageOf
  M inputs baseWitnessList baseContext axiom prefix
  prefixedStrongStepRoot zeroChild stepChild arithmeticBaseRoot
  arithmeticExtendedRoot arithmeticOpenRoot bodyChild : clear implicits.

(** ------------------------------------------------------------------
    Final ordinary certificate over the enlarged witnessed base. *)

Theorem
    raw_coqRestrictedPADerivationSoundnessCarrierGrowingFinalizationPackage_of_strongPrefix_cases
    : forall (M : RawPAModel), RawPASatisfies M -> forall
      (inputs : RawCodedTemplateStructuralInputs M),
  RawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixCaseRootCompiler
    M inputs ->
  forall replacement axiom closureCount baseWitnessList baseContext
      strongStepRoot,
  RawCodedPAAxiomWitnessContext M baseWitnessList baseContext ->
  RawCoqRestrictedPADerivationSoundnessStrongPrefixClosureRemainder
    M inputs replacement axiom closureCount ->
  RawCodedPALocalProofOf M
    (rawPAInductionExtendedContext M baseContext axiom)
    (rawCoqRestrictedPADerivationSoundnessCarrierStrongStepCode M inputs)
    strongStepRoot ->
  exists (prefix : StandardPAAxiomWitnessPrefix)
      (prefixedStrongStepRoot zeroChild stepChild arithmeticBaseRoot
        arithmeticExtendedRoot arithmeticOpenRoot bodyChild : M),
    RawCoqRestrictedPADerivationSoundnessCarrierGrowingFinalizationPackageOf
      M inputs baseWitnessList baseContext axiom prefix
      prefixedStrongStepRoot zeroChild stepChild arithmeticBaseRoot
      arithmeticExtendedRoot arithmeticOpenRoot bodyChild.
Proof.
  intros M hPA inputs hcases
    replacement axiom closureCount baseWitnessList baseContext
    strongStepRoot hbase hremainder hstrongStep.

  (* The fixed PA theorem chooses one finite witness prefix.  Structural PA
     agreement makes its target literally the same [d < S d] code consumed
     by the checked finalizer. *)
  destruct
    (raw_codedTemplatePALocalProofOf_of_BProv_on_witnessed_tail
      M hPA (rawStructuralTemplateTranslation M hPA inputs)
      (rawStructuralTemplatePAAgreement M hPA inputs)
      baseWitnessList baseContext
      (Formula.ltTermAt (tVar 0) (tSucc (tVar 0)))
      hbase
      coqRestrictedPADerivationSoundnessCarrierFinalizer_ltSelfSucc_bprov)
    as (prefix & arithmeticBaseRoot & hprefixedBase & harithmeticBase).
  change (RawCodedPALocalProofOf M
    (rawCoqRestrictedPADerivationSoundnessCarrierGrowingBaseContext
      M prefix baseContext)
    (rawCoqRestrictedPADerivationSoundnessCarrierFinalizerLtSelfSuccCode
      M inputs)
    arithmeticBaseRoot) in harithmeticBase.

  (* The same induction axiom is now adjoined above the enlarged base. *)
  pose proof
    (raw_coqRestrictedPADerivationSoundnessCarrierFinalizer_extendedContext_witnessed
      M hPA inputs replacement axiom closureCount
      (rawCoqRestrictedPADerivationSoundnessCarrierGrowingBaseWitnessList
        M prefix baseWitnessList)
      (rawCoqRestrictedPADerivationSoundnessCarrierGrowingBaseContext
        M prefix baseContext)
      hprefixedBase hremainder) as hprefixedExtended.

  (* The arithmetic root moves from the prefixed base to the witnessed
     induction extension.  This is ordinary inclusion weakening, not a
     context equality: the new induction axiom is a genuine extra row. *)
  assert (harithmeticExtendedInclusion : RawContextListIncluded M
      (rawCoqRestrictedPADerivationSoundnessCarrierGrowingBaseContext
        M prefix baseContext)
      (rawPAInductionExtendedContext M
        (rawCoqRestrictedPADerivationSoundnessCarrierGrowingBaseContext
          M prefix baseContext)
        axiom)).
  {
    unfold rawPAInductionExtendedContext.
    exact (raw_contextListIncluded_cons_target M hPA
      (rawCoqRestrictedPADerivationSoundnessCarrierGrowingBaseContext
        M prefix baseContext)
      (rawCoqRestrictedPADerivationSoundnessCarrierGrowingBaseContext
        M prefix baseContext)
      axiom
      (raw_contextListIncluded_refl M
        (rawCoqRestrictedPADerivationSoundnessCarrierGrowingBaseContext
          M prefix baseContext))).
  }
  destruct
    (raw_codedPALocalProofWitnessedContextInclusionWeakening_complete
      M hPA
      (rawCoqRestrictedPADerivationSoundnessCarrierGrowingBaseWitnessList
        M prefix baseWitnessList)
      (rawCoqRestrictedPADerivationSoundnessCarrierGrowingBaseContext
        M prefix baseContext)
      (rawPAInductionExtendedWitnessList M
        (rawCoqRestrictedPADerivationSoundnessCarrierGrowingBaseWitnessList
          M prefix baseWitnessList)
        (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixCode
          M inputs))
      (rawPAInductionExtendedContext M
        (rawCoqRestrictedPADerivationSoundnessCarrierGrowingBaseContext
          M prefix baseContext)
        axiom)
      (rawCoqRestrictedPADerivationSoundnessCarrierFinalizerLtSelfSuccCode
        M inputs)
      arithmeticBaseRoot
      hprefixedBase hprefixedExtended harithmeticExtendedInclusion
      harithmeticBase)
    as [arithmeticExtendedRoot harithmeticExtended].

  (* Insert the closed [forall K] assumption.  The target is no longer a
     witnessed PA context, so this step uses the explicitly proved binder
     square above rather than pretending that [forall K] is a PA axiom. *)
  pose proof
    (raw_codedPAAxiomWitnessPrefix_context_realizable_of_witnessed M
      (rawPAInductionExtendedWitnessList M
        (rawCoqRestrictedPADerivationSoundnessCarrierGrowingBaseWitnessList
          M prefix baseWitnessList)
        (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixCode
          M inputs))
      (rawPAInductionExtendedContext M
        (rawCoqRestrictedPADerivationSoundnessCarrierGrowingBaseContext
          M prefix baseContext)
        axiom)
      hprefixedExtended) as hprefixedExtendedRealizable.
  assert (hopenInclusion : RawContextListIncluded M
      (rawPAInductionExtendedContext M
        (rawCoqRestrictedPADerivationSoundnessCarrierGrowingBaseContext
          M prefix baseContext)
        axiom)
      (rawCoqRestrictedPADerivationSoundnessCarrierFinalizerOpenContext
        M inputs
        (rawCoqRestrictedPADerivationSoundnessCarrierGrowingBaseContext
          M prefix baseContext)
        axiom)).
  {
    unfold
      rawCoqRestrictedPADerivationSoundnessCarrierFinalizerOpenContext.
    exact (raw_contextListIncluded_cons_target M hPA
      (rawPAInductionExtendedContext M
        (rawCoqRestrictedPADerivationSoundnessCarrierGrowingBaseContext
          M prefix baseContext)
        axiom)
      (rawPAInductionExtendedContext M
        (rawCoqRestrictedPADerivationSoundnessCarrierGrowingBaseContext
          M prefix baseContext)
        axiom)
      (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixAllCode
        M inputs)
      (raw_contextListIncluded_refl M
        (rawPAInductionExtendedContext M
          (rawCoqRestrictedPADerivationSoundnessCarrierGrowingBaseContext
            M prefix baseContext)
          axiom))).
  }
  assert (hopenRealizable : RawContextListRealizable M
      (rawCoqRestrictedPADerivationSoundnessCarrierFinalizerOpenContext
        M inputs
        (rawCoqRestrictedPADerivationSoundnessCarrierGrowingBaseContext
          M prefix baseContext)
        axiom)).
  {
    unfold
      rawCoqRestrictedPADerivationSoundnessCarrierFinalizerOpenContext.
    exact (raw_contextList_cons_realizable M hPA
      (rawPAInductionExtendedContext M
        (rawCoqRestrictedPADerivationSoundnessCarrierGrowingBaseContext
          M prefix baseContext)
        axiom)
      (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixAllCode
        M inputs)
      hprefixedExtendedRealizable).
  }
  destruct (raw_codedPALocalProof_contextInclusionWeakening_of_binderReady
    M hPA
    (rawPAInductionExtendedContext M
      (rawCoqRestrictedPADerivationSoundnessCarrierGrowingBaseContext
        M prefix baseContext)
      axiom)
    (rawCoqRestrictedPADerivationSoundnessCarrierFinalizerOpenContext
      M inputs
      (rawCoqRestrictedPADerivationSoundnessCarrierGrowingBaseContext
        M prefix baseContext)
      axiom)
    (rawCoqRestrictedPADerivationSoundnessCarrierFinalizerLtSelfSuccCode
      M inputs)
    arithmeticExtendedRoot
    hprefixedExtendedRealizable hopenRealizable hopenInclusion
    (raw_coqRestrictedPADerivationSoundnessCarrierStrongPrefixAll_cons_binderReady
      M hPA inputs
      (rawPAInductionExtendedContext M
        (rawCoqRestrictedPADerivationSoundnessCarrierGrowingBaseContext
          M prefix baseContext)
        axiom))
    harithmeticExtended) as
    [arithmeticOpenRoot harithmeticOpen].

  (* The incoming strong step is rebuilt over the same enlarged induction
     context.  Inclusion is lifted under the identical induction-axiom head;
     hence no context permutation or decoded carrier comparison occurs. *)
  pose proof
    (raw_coqRestrictedPADerivationSoundnessCarrierFinalizer_extendedContext_witnessed
      M hPA inputs replacement axiom closureCount
      baseWitnessList baseContext hbase hremainder) as hbaseExtended.
  pose proof
    (raw_codedPAAxiomWitnessPrefix_context_realizable_of_witnessed
      M baseWitnessList baseContext hbase) as hbaseRealizable.
  pose proof
    (raw_codedPAAxiomWitnessPrefix_context_realizable_of_witnessed M
      (rawCoqRestrictedPADerivationSoundnessCarrierGrowingBaseWitnessList
        M prefix baseWitnessList)
      (rawCoqRestrictedPADerivationSoundnessCarrierGrowingBaseContext
        M prefix baseContext)
      hprefixedBase) as hprefixedBaseRealizable.
  assert (hstrongStepInclusion : RawContextListIncluded M
      (rawPAInductionExtendedContext M baseContext axiom)
      (rawPAInductionExtendedContext M
        (rawCoqRestrictedPADerivationSoundnessCarrierGrowingBaseContext
          M prefix baseContext)
        axiom)).
  {
    unfold rawPAInductionExtendedContext.
    exact (raw_contextListIncluded_cons M hPA
      baseContext
      (rawCoqRestrictedPADerivationSoundnessCarrierGrowingBaseContext
        M prefix baseContext)
      axiom axiom hbaseRealizable hprefixedBaseRealizable eq_refl
      (raw_contextListIncluded_standardPAAxiomWitnessPrefix_base
        M hPA prefix baseContext)).
  }
  destruct
    (raw_codedPALocalProofWitnessedContextInclusionWeakening_complete
      M hPA
      (rawPAInductionExtendedWitnessList M baseWitnessList
        (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixCode
          M inputs))
      (rawPAInductionExtendedContext M baseContext axiom)
      (rawPAInductionExtendedWitnessList M
        (rawCoqRestrictedPADerivationSoundnessCarrierGrowingBaseWitnessList
          M prefix baseWitnessList)
        (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixCode
          M inputs))
      (rawPAInductionExtendedContext M
        (rawCoqRestrictedPADerivationSoundnessCarrierGrowingBaseContext
          M prefix baseContext)
        axiom)
      (rawCoqRestrictedPADerivationSoundnessCarrierStrongStepCode M inputs)
      strongStepRoot hbaseExtended hprefixedExtended hstrongStepInclusion
      hstrongStep) as [prefixedStrongStepRoot hprefixedStrongStep].

  destruct (hcases replacement axiom closureCount
    (rawCoqRestrictedPADerivationSoundnessCarrierGrowingBaseWitnessList
      M prefix baseWitnessList)
    (rawCoqRestrictedPADerivationSoundnessCarrierGrowingBaseContext
      M prefix baseContext)
    prefixedStrongStepRoot hprefixedBase hremainder hprefixedStrongStep)
    as (zeroChild & stepChild & hzero & hstep).

  pose proof
    (raw_codedPALocalProofOf_coqRestrictedPADerivationSoundnessCarrierFinalizer_from_exact_arithmetic_leaf
      M hPA inputs replacement axiom closureCount
      (rawCoqRestrictedPADerivationSoundnessCarrierGrowingBaseWitnessList
        M prefix baseWitnessList)
      (rawCoqRestrictedPADerivationSoundnessCarrierGrowingBaseContext
        M prefix baseContext)
      arithmeticOpenRoot hprefixedBase hremainder harithmeticOpen)
    as hfinalizer.

  destruct
    (raw_codedPAProofOf_coqRestrictedPADerivationSoundnessUniversal_of_strongPrefix_cases_and_finalizer
      M hPA inputs replacement axiom closureCount
      (rawCoqRestrictedPADerivationSoundnessCarrierGrowingBaseWitnessList
        M prefix baseWitnessList)
      (rawCoqRestrictedPADerivationSoundnessCarrierGrowingBaseContext
        M prefix baseContext)
      zeroChild stepChild
      (rawCoqRestrictedPADerivationSoundnessCarrierFinalizerRoot
        M inputs
        (rawCoqRestrictedPADerivationSoundnessCarrierGrowingBaseContext
          M prefix baseContext)
        axiom arithmeticOpenRoot)
      hprefixedBase hremainder hzero hstep hfinalizer)
    as [bodyChild hproof].
  exists prefix, prefixedStrongStepRoot, zeroChild, stepChild,
    arithmeticBaseRoot, arithmeticExtendedRoot, arithmeticOpenRoot,
    bodyChild.
  unfold
    RawCoqRestrictedPADerivationSoundnessCarrierGrowingFinalizationPackageOf.
  split; [exact hprefixedBase |].
  split; [exact harithmeticBase |].
  split; [exact hprefixedExtended |].
  split; [exact hprefixedStrongStep |].
  split; [exact hzero |].
  split; [exact hstep |].
  split; [exact harithmeticExtended |].
  split; [exact harithmeticOpen |].
  split; [exact hfinalizer |].
  exact hproof.
Qed.

(** Compact endpoint for callers that only need the ordinary certificate.
    The stronger package theorem above remains the primary audit surface. *)
Corollary
    raw_codedPAProofOf_coqRestrictedPADerivationSoundnessUniversal_of_growing_strongPrefix_cases
    : forall (M : RawPAModel), RawPASatisfies M -> forall
      (inputs : RawCodedTemplateStructuralInputs M),
  RawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixCaseRootCompiler
    M inputs ->
  forall replacement axiom closureCount baseWitnessList baseContext
      strongStepRoot,
  RawCodedPAAxiomWitnessContext M baseWitnessList baseContext ->
  RawCoqRestrictedPADerivationSoundnessStrongPrefixClosureRemainder
    M inputs replacement axiom closureCount ->
  RawCodedPALocalProofOf M
    (rawPAInductionExtendedContext M baseContext axiom)
    (rawCoqRestrictedPADerivationSoundnessCarrierStrongStepCode M inputs)
    strongStepRoot ->
  exists (prefix : StandardPAAxiomWitnessPrefix)
      (zeroChild stepChild arithmeticOpenRoot bodyChild : M),
    RawCodedPAProofOf M
      (rawCoqRestrictedPADerivationSoundnessUniversalCode M inputs)
      (rawCoqRestrictedPADerivationSoundnessStrongPrefixFinalizedCertificate
        M inputs
        (rawCoqRestrictedPADerivationSoundnessCarrierGrowingBaseWitnessList
          M prefix baseWitnessList)
        (rawCoqRestrictedPADerivationSoundnessCarrierGrowingBaseContext
          M prefix baseContext)
        axiom bodyChild zeroChild stepChild
        (rawCoqRestrictedPADerivationSoundnessCarrierFinalizerRoot
          M inputs
          (rawCoqRestrictedPADerivationSoundnessCarrierGrowingBaseContext
            M prefix baseContext)
          axiom arithmeticOpenRoot)).
Proof.
  intros M hPA inputs hcases replacement axiom closureCount
    baseWitnessList baseContext strongStepRoot hbase hremainder hstrongStep.
  destruct
    (raw_coqRestrictedPADerivationSoundnessCarrierGrowingFinalizationPackage_of_strongPrefix_cases
      M hPA inputs hcases replacement axiom closureCount
      baseWitnessList baseContext strongStepRoot
      hbase hremainder hstrongStep)
    as (prefix & prefixedStrongStepRoot & zeroChild & stepChild &
      arithmeticBaseRoot & arithmeticExtendedRoot & arithmeticOpenRoot &
      bodyChild & hpackage).
  exists prefix, zeroChild, stepChild, arithmeticOpenRoot, bodyChild.
  unfold
    RawCoqRestrictedPADerivationSoundnessCarrierGrowingFinalizationPackageOf
    in hpackage.
  destruct hpackage as
    [_ [_ [_ [_ [_ [_ [_ [_ [_ hproof]]]]]]]]].
  exact hproof.
Qed.

End
  PABoundedRawCodedRestrictedPADerivationSoundnessCarrierStrongPrefixGrowingFinalizer.
