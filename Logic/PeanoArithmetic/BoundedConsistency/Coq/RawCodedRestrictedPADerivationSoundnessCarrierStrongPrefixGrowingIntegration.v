(**
  Join the growing strong-prefix cases to the growing finalizer.

  The case compiler and the finalizer compiler each honestly select a finite
  prefix of standard PA axioms.  Consequently, the growing case package
  cannot inhabit the older fixed-context case-compiler interface: its two
  roots live over a genuinely enlarged witnessed base.

  This module composes the two growing interfaces directly.  Starting from a
  completed case package, it lets the finalizer choose a second prefix,
  transports the strong-step, zero, and successor roots through that prefix,
  and then invokes the already checked finalizer and closure-induction shell.
  Prefix concatenation flattens the two nested finite extensions into the
  single prefix exposed by the existing finalization package.
*)

From Stdlib Require Import List.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors
  RawCodedContextLists
  RawCodedContextStructure
  RawCodedContextShift
  RawCodedRestrictedPAProof
  RawCodedPALocalProofExistential
  RawCodedPAProvability
  RawCodedPAAxiomWitnessPrefix
  RawCodedPAInductionAxiomCertificate
  RawCodedTemplateStructuralTranslation
  RawCodedTemplateStructuralPAAgreement
  RawCodedTemplatePAEmbeddingSelfShiftTail
  RawCodedPALocalProofWitnessedContextMerge
  RawCodedPALocalProofWitnessedContextMergeTransportComplete
  RawCodedRestrictedPAConsistencyFromUniversalSoundness
  RawCodedRestrictedPADerivationSoundnessCarrierStrongPrefixInductionShell
  RawCodedRestrictedPADerivationSoundnessCarrierStrongPrefixFinalizerCompilation
  RawCodedRestrictedPADerivationSoundnessCarrierStrongPrefixGrowingFinalizer
  RawCodedRestrictedPADerivationSoundnessCarrierStrongPrefixGrowingCaseCompilation.

Import ListNotations.

Module
  PABoundedRawCodedRestrictedPADerivationSoundnessCarrierStrongPrefixGrowingIntegration.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedContextLists.
Import PABoundedRawCodedContextStructure.
Import PABoundedRawCodedContextShift.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPAProvability.
Import PABoundedRawCodedPAAxiomWitnessPrefix.
Import PABoundedRawCodedPAInductionAxiomCertificate.
Import PABoundedRawCodedTemplateStructuralTranslation.
Import PABoundedRawCodedTemplateStructuralPAAgreement.
Import PABoundedRawCodedTemplatePAEmbeddingSelfShiftTail.
Import PABoundedRawCodedPALocalProofWitnessedContextMerge.
Import
  PABoundedRawCodedPALocalProofWitnessedContextMergeTransportComplete.
Import PABoundedRawCodedRestrictedPAConsistencyFromUniversalSoundness.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessCarrierStrongPrefixInductionShell.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessCarrierStrongPrefixFinalizerCompilation.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessCarrierStrongPrefixGrowingFinalizer.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessCarrierStrongPrefixGrowingCaseCompilation.

(** A completed growing case package already contains everything needed at
    its selected induction context.  The only additional mathematical datum
    needed by the finalizer is the same closure remainder that identifies the
    induction axiom. *)
Theorem
    raw_coqRestrictedPADerivationSoundnessCarrierGrowingFinalizationPackage_of_growing_case_package
    : forall (M : RawPAModel), RawPASatisfies M -> forall
      (inputs : RawCodedTemplateStructuralInputs M)
      replacement axiom closureCount baseWitnessList baseContext
      (casePrefix : StandardPAAxiomWitnessPrefix)
      noLtZeroBaseRoot ltKernelBaseRoot caseStrongStepRoot
      noLtZeroExtendedRoot ltKernelExtendedRoot zeroChild stepChild,
  RawCoqCarrierStrongPrefixGrowingCasePackageOf
    M inputs baseWitnessList baseContext axiom casePrefix
    noLtZeroBaseRoot ltKernelBaseRoot caseStrongStepRoot
    noLtZeroExtendedRoot ltKernelExtendedRoot zeroChild stepChild ->
  RawCoqRestrictedPADerivationSoundnessStrongPrefixClosureRemainder
    M inputs replacement axiom closureCount ->
  exists (combinedPrefix : StandardPAAxiomWitnessPrefix)
      (finalStrongStepRoot finalZeroChild finalStepChild
        arithmeticBaseRoot arithmeticExtendedRoot arithmeticOpenRoot
        bodyChild : M),
    RawCoqRestrictedPADerivationSoundnessCarrierGrowingFinalizationPackageOf
      M inputs baseWitnessList baseContext axiom
      combinedPrefix
      finalStrongStepRoot finalZeroChild finalStepChild
      arithmeticBaseRoot arithmeticExtendedRoot arithmeticOpenRoot
      bodyChild.
Proof.
  intros M hPA inputs replacement axiom closureCount
    baseWitnessList baseContext casePrefix
    noLtZeroBaseRoot ltKernelBaseRoot caseStrongStepRoot
    noLtZeroExtendedRoot ltKernelExtendedRoot zeroChild stepChild
    hcasePackage hremainder.
  unfold RawCoqCarrierStrongPrefixGrowingCasePackageOf in hcasePackage.
  destruct hcasePackage as
    [hcaseBase
      [hnoLtZeroBase
        [hltKernelBase
          [hcaseExtended
            [hcaseStrongStep
              [hnoLtZeroExtended
                [hltKernelExtended [hzero hstep]]]]]]]].

  (* Regard the case compiler's selected base as the caller's base for the
     finalizer arithmetic theorem.  This second compilation contributes a
     new prefix above, rather than replacing, the case prefix. *)
  destruct
    (raw_codedTemplatePALocalProofOf_of_BProv_on_witnessed_tail
      M hPA (rawStructuralTemplateTranslation M hPA inputs)
      (rawStructuralTemplatePAAgreement M hPA inputs)
      (rawCoqCarrierStrongPrefixGrowingCaseWitnessList
        M casePrefix baseWitnessList)
      (rawCoqCarrierStrongPrefixGrowingCaseContext
        M casePrefix baseContext)
      (Formula.ltTermAt (tVar 0) (tSucc (tVar 0)))
      hcaseBase
      coqRestrictedPADerivationSoundnessCarrierFinalizer_ltSelfSucc_bprov)
    as (finalizerPrefix & arithmeticBaseRoot & hfinalBase & harithmeticBase).
  change (RawCodedPALocalProofOf M
    (rawCoqRestrictedPADerivationSoundnessCarrierGrowingBaseContext
      M finalizerPrefix
      (rawCoqCarrierStrongPrefixGrowingCaseContext
        M casePrefix baseContext))
    (rawCoqRestrictedPADerivationSoundnessCarrierFinalizerLtSelfSuccCode
      M inputs)
    arithmeticBaseRoot) in harithmeticBase.

  (* Adjoin the same represented induction axiom above the twice-enlarged
     base.  The case package already certifies the source induction context. *)
  pose proof
    (raw_coqRestrictedPADerivationSoundnessCarrierFinalizer_extendedContext_witnessed
      M hPA inputs replacement axiom closureCount
      (rawCoqRestrictedPADerivationSoundnessCarrierGrowingBaseWitnessList
        M finalizerPrefix
        (rawCoqCarrierStrongPrefixGrowingCaseWitnessList
          M casePrefix baseWitnessList))
      (rawCoqRestrictedPADerivationSoundnessCarrierGrowingBaseContext
        M finalizerPrefix
        (rawCoqCarrierStrongPrefixGrowingCaseContext
          M casePrefix baseContext))
      hfinalBase hremainder) as hfinalExtended.

  pose proof
    (raw_codedPAAxiomWitnessPrefix_context_realizable_of_witnessed M
      (rawCoqCarrierStrongPrefixGrowingCaseWitnessList
        M casePrefix baseWitnessList)
      (rawCoqCarrierStrongPrefixGrowingCaseContext
        M casePrefix baseContext)
      hcaseBase) as hcaseBaseRealizable.
  pose proof
    (raw_codedPAAxiomWitnessPrefix_context_realizable_of_witnessed M
      (rawCoqRestrictedPADerivationSoundnessCarrierGrowingBaseWitnessList
        M finalizerPrefix
        (rawCoqCarrierStrongPrefixGrowingCaseWitnessList
          M casePrefix baseWitnessList))
      (rawCoqRestrictedPADerivationSoundnessCarrierGrowingBaseContext
        M finalizerPrefix
        (rawCoqCarrierStrongPrefixGrowingCaseContext
          M casePrefix baseContext))
      hfinalBase) as hfinalBaseRealizable.
  assert (hextendedInclusion : RawContextListIncluded M
      (rawPAInductionExtendedContext M
        (rawCoqCarrierStrongPrefixGrowingCaseContext
          M casePrefix baseContext)
        axiom)
      (rawPAInductionExtendedContext M
        (rawCoqRestrictedPADerivationSoundnessCarrierGrowingBaseContext
          M finalizerPrefix
          (rawCoqCarrierStrongPrefixGrowingCaseContext
            M casePrefix baseContext))
        axiom)).
  {
    unfold rawPAInductionExtendedContext.
    exact (raw_contextListIncluded_cons M hPA
      (rawCoqCarrierStrongPrefixGrowingCaseContext
        M casePrefix baseContext)
      (rawCoqRestrictedPADerivationSoundnessCarrierGrowingBaseContext
        M finalizerPrefix
        (rawCoqCarrierStrongPrefixGrowingCaseContext
          M casePrefix baseContext))
      axiom axiom hcaseBaseRealizable hfinalBaseRealizable eq_refl
      (raw_contextListIncluded_standardPAAxiomWitnessPrefix_base
        M hPA finalizerPrefix
        (rawCoqCarrierStrongPrefixGrowingCaseContext
          M casePrefix baseContext))).
  }

  (* The strong step and both compiled cases must move together.  Reusing one
     literal inclusion proof here prevents the three targets from drifting
     to independently selected contexts. *)
  destruct
    (raw_codedPALocalProofWitnessedContextInclusionWeakening_complete
      M hPA
      (rawPAInductionExtendedWitnessList M
        (rawCoqCarrierStrongPrefixGrowingCaseWitnessList
          M casePrefix baseWitnessList)
        (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixCode
          M inputs))
      (rawPAInductionExtendedContext M
        (rawCoqCarrierStrongPrefixGrowingCaseContext
          M casePrefix baseContext)
        axiom)
      (rawPAInductionExtendedWitnessList M
        (rawCoqRestrictedPADerivationSoundnessCarrierGrowingBaseWitnessList
          M finalizerPrefix
          (rawCoqCarrierStrongPrefixGrowingCaseWitnessList
            M casePrefix baseWitnessList))
        (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixCode
          M inputs))
      (rawPAInductionExtendedContext M
        (rawCoqRestrictedPADerivationSoundnessCarrierGrowingBaseContext
          M finalizerPrefix
          (rawCoqCarrierStrongPrefixGrowingCaseContext
            M casePrefix baseContext))
        axiom)
      (rawCoqRestrictedPADerivationSoundnessCarrierStrongStepCode M inputs)
      caseStrongStepRoot hcaseExtended hfinalExtended hextendedInclusion
      hcaseStrongStep) as [finalStrongStepRoot hfinalStrongStep].
  destruct
    (raw_codedPALocalProofWitnessedContextInclusionWeakening_complete
      M hPA
      (rawPAInductionExtendedWitnessList M
        (rawCoqCarrierStrongPrefixGrowingCaseWitnessList
          M casePrefix baseWitnessList)
        (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixCode
          M inputs))
      (rawPAInductionExtendedContext M
        (rawCoqCarrierStrongPrefixGrowingCaseContext
          M casePrefix baseContext)
        axiom)
      (rawPAInductionExtendedWitnessList M
        (rawCoqRestrictedPADerivationSoundnessCarrierGrowingBaseWitnessList
          M finalizerPrefix
          (rawCoqCarrierStrongPrefixGrowingCaseWitnessList
            M casePrefix baseWitnessList))
        (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixCode
          M inputs))
      (rawPAInductionExtendedContext M
        (rawCoqRestrictedPADerivationSoundnessCarrierGrowingBaseContext
          M finalizerPrefix
          (rawCoqCarrierStrongPrefixGrowingCaseContext
            M casePrefix baseContext))
        axiom)
      (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixZeroCode
        M inputs)
      zeroChild hcaseExtended hfinalExtended hextendedInclusion hzero)
    as [finalZeroChild hfinalZero].
  destruct
    (raw_codedPALocalProofWitnessedContextInclusionWeakening_complete
      M hPA
      (rawPAInductionExtendedWitnessList M
        (rawCoqCarrierStrongPrefixGrowingCaseWitnessList
          M casePrefix baseWitnessList)
        (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixCode
          M inputs))
      (rawPAInductionExtendedContext M
        (rawCoqCarrierStrongPrefixGrowingCaseContext
          M casePrefix baseContext)
        axiom)
      (rawPAInductionExtendedWitnessList M
        (rawCoqRestrictedPADerivationSoundnessCarrierGrowingBaseWitnessList
          M finalizerPrefix
          (rawCoqCarrierStrongPrefixGrowingCaseWitnessList
            M casePrefix baseWitnessList))
        (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixCode
          M inputs))
      (rawPAInductionExtendedContext M
        (rawCoqRestrictedPADerivationSoundnessCarrierGrowingBaseContext
          M finalizerPrefix
          (rawCoqCarrierStrongPrefixGrowingCaseContext
            M casePrefix baseContext))
        axiom)
      (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixStepAllCode
        M inputs)
      stepChild hcaseExtended hfinalExtended hextendedInclusion hstep)
    as [finalStepChild hfinalStep].

  (* Move d < S d first beneath the induction axiom and then beneath the
     temporary closed forall-K assumption used by the finalizer proof tree. *)
  assert (harithmeticExtendedInclusion : RawContextListIncluded M
      (rawCoqRestrictedPADerivationSoundnessCarrierGrowingBaseContext
        M finalizerPrefix
        (rawCoqCarrierStrongPrefixGrowingCaseContext
          M casePrefix baseContext))
      (rawPAInductionExtendedContext M
        (rawCoqRestrictedPADerivationSoundnessCarrierGrowingBaseContext
          M finalizerPrefix
          (rawCoqCarrierStrongPrefixGrowingCaseContext
            M casePrefix baseContext))
        axiom)).
  {
    unfold rawPAInductionExtendedContext.
    exact (raw_contextListIncluded_cons_target M hPA
      (rawCoqRestrictedPADerivationSoundnessCarrierGrowingBaseContext
        M finalizerPrefix
        (rawCoqCarrierStrongPrefixGrowingCaseContext
          M casePrefix baseContext))
      (rawCoqRestrictedPADerivationSoundnessCarrierGrowingBaseContext
        M finalizerPrefix
        (rawCoqCarrierStrongPrefixGrowingCaseContext
          M casePrefix baseContext))
      axiom
      (raw_contextListIncluded_refl M
        (rawCoqRestrictedPADerivationSoundnessCarrierGrowingBaseContext
          M finalizerPrefix
          (rawCoqCarrierStrongPrefixGrowingCaseContext
            M casePrefix baseContext)))).
  }
  destruct
    (raw_codedPALocalProofWitnessedContextInclusionWeakening_complete
      M hPA
      (rawCoqRestrictedPADerivationSoundnessCarrierGrowingBaseWitnessList
        M finalizerPrefix
        (rawCoqCarrierStrongPrefixGrowingCaseWitnessList
          M casePrefix baseWitnessList))
      (rawCoqRestrictedPADerivationSoundnessCarrierGrowingBaseContext
        M finalizerPrefix
        (rawCoqCarrierStrongPrefixGrowingCaseContext
          M casePrefix baseContext))
      (rawPAInductionExtendedWitnessList M
        (rawCoqRestrictedPADerivationSoundnessCarrierGrowingBaseWitnessList
          M finalizerPrefix
          (rawCoqCarrierStrongPrefixGrowingCaseWitnessList
            M casePrefix baseWitnessList))
        (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixCode
          M inputs))
      (rawPAInductionExtendedContext M
        (rawCoqRestrictedPADerivationSoundnessCarrierGrowingBaseContext
          M finalizerPrefix
          (rawCoqCarrierStrongPrefixGrowingCaseContext
            M casePrefix baseContext))
        axiom)
      (rawCoqRestrictedPADerivationSoundnessCarrierFinalizerLtSelfSuccCode
        M inputs)
      arithmeticBaseRoot hfinalBase hfinalExtended
      harithmeticExtendedInclusion harithmeticBase)
    as [arithmeticExtendedRoot harithmeticExtended].

  pose proof
    (raw_codedPAAxiomWitnessPrefix_context_realizable_of_witnessed M
      (rawPAInductionExtendedWitnessList M
        (rawCoqRestrictedPADerivationSoundnessCarrierGrowingBaseWitnessList
          M finalizerPrefix
          (rawCoqCarrierStrongPrefixGrowingCaseWitnessList
            M casePrefix baseWitnessList))
        (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixCode
          M inputs))
      (rawPAInductionExtendedContext M
        (rawCoqRestrictedPADerivationSoundnessCarrierGrowingBaseContext
          M finalizerPrefix
          (rawCoqCarrierStrongPrefixGrowingCaseContext
            M casePrefix baseContext))
        axiom)
      hfinalExtended) as hfinalExtendedRealizable.
  assert (hopenInclusion : RawContextListIncluded M
      (rawPAInductionExtendedContext M
        (rawCoqRestrictedPADerivationSoundnessCarrierGrowingBaseContext
          M finalizerPrefix
          (rawCoqCarrierStrongPrefixGrowingCaseContext
            M casePrefix baseContext))
        axiom)
      (rawCoqRestrictedPADerivationSoundnessCarrierFinalizerOpenContext
        M inputs
        (rawCoqRestrictedPADerivationSoundnessCarrierGrowingBaseContext
          M finalizerPrefix
          (rawCoqCarrierStrongPrefixGrowingCaseContext
            M casePrefix baseContext))
        axiom)).
  {
    unfold
      rawCoqRestrictedPADerivationSoundnessCarrierFinalizerOpenContext.
    exact (raw_contextListIncluded_cons_target M hPA
      (rawPAInductionExtendedContext M
        (rawCoqRestrictedPADerivationSoundnessCarrierGrowingBaseContext
          M finalizerPrefix
          (rawCoqCarrierStrongPrefixGrowingCaseContext
            M casePrefix baseContext))
        axiom)
      (rawPAInductionExtendedContext M
        (rawCoqRestrictedPADerivationSoundnessCarrierGrowingBaseContext
          M finalizerPrefix
          (rawCoqCarrierStrongPrefixGrowingCaseContext
            M casePrefix baseContext))
        axiom)
      (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixAllCode
        M inputs)
      (raw_contextListIncluded_refl M
        (rawPAInductionExtendedContext M
          (rawCoqRestrictedPADerivationSoundnessCarrierGrowingBaseContext
            M finalizerPrefix
            (rawCoqCarrierStrongPrefixGrowingCaseContext
              M casePrefix baseContext))
          axiom))).
  }
  assert (hopenRealizable : RawContextListRealizable M
      (rawCoqRestrictedPADerivationSoundnessCarrierFinalizerOpenContext
        M inputs
        (rawCoqRestrictedPADerivationSoundnessCarrierGrowingBaseContext
          M finalizerPrefix
          (rawCoqCarrierStrongPrefixGrowingCaseContext
            M casePrefix baseContext))
        axiom)).
  {
    unfold
      rawCoqRestrictedPADerivationSoundnessCarrierFinalizerOpenContext.
    exact (raw_contextList_cons_realizable M hPA
      (rawPAInductionExtendedContext M
        (rawCoqRestrictedPADerivationSoundnessCarrierGrowingBaseContext
          M finalizerPrefix
          (rawCoqCarrierStrongPrefixGrowingCaseContext
            M casePrefix baseContext))
        axiom)
      (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixAllCode
        M inputs)
      hfinalExtendedRealizable).
  }
  destruct (raw_codedPALocalProof_contextInclusionWeakening_of_binderReady
    M hPA
    (rawPAInductionExtendedContext M
      (rawCoqRestrictedPADerivationSoundnessCarrierGrowingBaseContext
        M finalizerPrefix
        (rawCoqCarrierStrongPrefixGrowingCaseContext
          M casePrefix baseContext))
      axiom)
    (rawCoqRestrictedPADerivationSoundnessCarrierFinalizerOpenContext
      M inputs
      (rawCoqRestrictedPADerivationSoundnessCarrierGrowingBaseContext
        M finalizerPrefix
        (rawCoqCarrierStrongPrefixGrowingCaseContext
          M casePrefix baseContext))
      axiom)
    (rawCoqRestrictedPADerivationSoundnessCarrierFinalizerLtSelfSuccCode
      M inputs)
    arithmeticExtendedRoot hfinalExtendedRealizable hopenRealizable
    hopenInclusion
    (raw_coqRestrictedPADerivationSoundnessCarrierStrongPrefixAll_cons_binderReady
      M hPA inputs
      (rawPAInductionExtendedContext M
        (rawCoqRestrictedPADerivationSoundnessCarrierGrowingBaseContext
          M finalizerPrefix
          (rawCoqCarrierStrongPrefixGrowingCaseContext
            M casePrefix baseContext))
        axiom))
    harithmeticExtended) as [arithmeticOpenRoot harithmeticOpen].

  pose proof
    (raw_codedPALocalProofOf_coqRestrictedPADerivationSoundnessCarrierFinalizer_from_exact_arithmetic_leaf
      M hPA inputs replacement axiom closureCount
      (rawCoqRestrictedPADerivationSoundnessCarrierGrowingBaseWitnessList
        M finalizerPrefix
        (rawCoqCarrierStrongPrefixGrowingCaseWitnessList
          M casePrefix baseWitnessList))
      (rawCoqRestrictedPADerivationSoundnessCarrierGrowingBaseContext
        M finalizerPrefix
        (rawCoqCarrierStrongPrefixGrowingCaseContext
          M casePrefix baseContext))
      arithmeticOpenRoot hfinalBase hremainder harithmeticOpen)
    as hfinalizer.
  destruct
    (raw_codedPAProofOf_coqRestrictedPADerivationSoundnessUniversal_of_strongPrefix_cases_and_finalizer
      M hPA inputs replacement axiom closureCount
      (rawCoqRestrictedPADerivationSoundnessCarrierGrowingBaseWitnessList
        M finalizerPrefix
        (rawCoqCarrierStrongPrefixGrowingCaseWitnessList
          M casePrefix baseWitnessList))
      (rawCoqRestrictedPADerivationSoundnessCarrierGrowingBaseContext
        M finalizerPrefix
        (rawCoqCarrierStrongPrefixGrowingCaseContext
          M casePrefix baseContext))
      finalZeroChild finalStepChild
      (rawCoqRestrictedPADerivationSoundnessCarrierFinalizerRoot
        M inputs
        (rawCoqRestrictedPADerivationSoundnessCarrierGrowingBaseContext
          M finalizerPrefix
          (rawCoqCarrierStrongPrefixGrowingCaseContext
            M casePrefix baseContext))
        axiom arithmeticOpenRoot)
      hfinalBase hremainder hfinalZero hfinalStep hfinalizer)
    as [bodyChild hproof].

  exists (finalizerPrefix ++ casePrefix), finalStrongStepRoot,
    finalZeroChild, finalStepChild, arithmeticBaseRoot,
    arithmeticExtendedRoot, arithmeticOpenRoot, bodyChild.
  unfold
    RawCoqRestrictedPADerivationSoundnessCarrierGrowingFinalizationPackageOf,
    rawCoqRestrictedPADerivationSoundnessCarrierGrowingBaseWitnessList,
    rawCoqRestrictedPADerivationSoundnessCarrierGrowingBaseContext,
    rawCoqCarrierStrongPrefixGrowingCaseWitnessList,
    rawCoqCarrierStrongPrefixGrowingCaseContext in *.
  rewrite rawStandardPAAxiomWitnessPrefixWitnessListCode_app.
  rewrite rawStandardPAAxiomWitnessPrefixContextCode_app.
  split; [exact hfinalBase |].
  split; [exact harithmeticBase |].
  split; [exact hfinalExtended |].
  split; [exact hfinalStrongStep |].
  split; [exact hfinalZero |].
  split; [exact hfinalStep |].
  split; [exact harithmeticExtended |].
  split; [exact harithmeticOpen |].
  split; [exact hfinalizer |].
  exact hproof.
Qed.

(** Compact public endpoint: the unconditional growing case compiler is
    invoked first, and the package theorem above then supplies the final
    ordinary universal-soundness certificate.  The only remaining inputs are
    the genuine recursive strong step and the nonstandard closure data. *)
Corollary
    raw_codedPAProofOf_coqRestrictedPADerivationSoundnessUniversal_of_growing_case_and_finalizer
    : forall (M : RawPAModel), RawPASatisfies M -> forall
      (inputs : RawCodedTemplateStructuralInputs M)
      replacement axiom closureCount baseWitnessList baseContext
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
  intros M hPA inputs replacement axiom closureCount
    baseWitnessList baseContext strongStepRoot hbase hremainder hstrongStep.
  destruct
    (raw_coqCarrierStrongPrefixGrowingCasePackage
      M hPA inputs replacement axiom closureCount
      baseWitnessList baseContext strongStepRoot
      hbase hremainder hstrongStep)
    as (casePrefix & noLtZeroBaseRoot & ltKernelBaseRoot &
      caseStrongStepRoot & noLtZeroExtendedRoot & ltKernelExtendedRoot &
      caseZeroChild & caseStepChild & hcasePackage).
  destruct
    (raw_coqRestrictedPADerivationSoundnessCarrierGrowingFinalizationPackage_of_growing_case_package
      M hPA inputs replacement axiom closureCount
      baseWitnessList baseContext casePrefix
      noLtZeroBaseRoot ltKernelBaseRoot caseStrongStepRoot
      noLtZeroExtendedRoot ltKernelExtendedRoot
      caseZeroChild caseStepChild hcasePackage hremainder)
    as (prefix & finalStrongStepRoot & zeroChild & stepChild &
      arithmeticBaseRoot & arithmeticExtendedRoot & arithmeticOpenRoot &
      bodyChild & hfinalPackage).
  exists prefix, zeroChild, stepChild, arithmeticOpenRoot, bodyChild.
  unfold
    RawCoqRestrictedPADerivationSoundnessCarrierGrowingFinalizationPackageOf
    in hfinalPackage.
  destruct hfinalPackage as
    [_ [_ [_ [_ [_ [_ [_ [_ [_ hproof]]]]]]]]].
  exact hproof.
Qed.

End
  PABoundedRawCodedRestrictedPADerivationSoundnessCarrierStrongPrefixGrowingIntegration.
