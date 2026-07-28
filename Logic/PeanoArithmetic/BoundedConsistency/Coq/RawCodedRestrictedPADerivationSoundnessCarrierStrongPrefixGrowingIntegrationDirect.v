(**
  Join the direct growing strong-prefix cases to the direct finalizer.

  Both arithmetic compilers choose honest finite prefixes of standard PA.
  The case prefix is selected first.  The finalizer then works over that
  enlarged base and may select a second prefix.  The public package exposes
  their literal concatenation, [finalizerPrefix ++ casePrefix], rather than
  hiding either context extension behind an existential certificate.

  This is the direct-code counterpart of the structural growing integration.
  Opaque truth atoms are never decoded: their shift and opening behavior is
  supplied by [RawCodedTemplateDirectStructuralInputs].
*)

From Stdlib Require Import List.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
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
  RawCodedTemplateStructuralTranslation
  RawCodedTemplateDirectStructuralTranslation
  RawCodedTemplateDirectStructuralPAAgreement
  RawCodedTemplatePAEmbeddingSelfShiftTail
  RawCodedPALocalProofWitnessedContextMerge
  RawCodedPALocalProofWitnessedContextMergeTransportComplete
  RawCodedRestrictedPAConsistencyFromUniversalSoundness
  RawCodedRestrictedPADerivationSoundnessCarrierStrongPrefixInductionShell
  RawCodedRestrictedPADerivationSoundnessCarrierStrongPrefixFinalizerCompilation
  RawCodedRestrictedPADerivationSoundnessCarrierStrongPrefixGrowingFinalizer
  RawCodedRestrictedPADerivationSoundnessCarrierStrongPrefixDirectInductionShell
  RawCodedRestrictedPADerivationSoundnessCarrierStrongPrefixFinalizerCompilationDirect
  RawCodedRestrictedPADerivationSoundnessCarrierStrongPrefixGrowingCaseCompilation
  RawCodedRestrictedPADerivationSoundnessCarrierStrongPrefixGrowingCaseCompilationDirect.

Import ListNotations.

Module
  PABoundedRawCodedRestrictedPADerivationSoundnessCarrierStrongPrefixGrowingIntegrationDirect.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
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
Import PABoundedRawCodedTemplateStructuralTranslation.
Import PABoundedRawCodedTemplateDirectStructuralTranslation.
Import PABoundedRawCodedTemplateDirectStructuralPAAgreement.
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
  PABoundedRawCodedRestrictedPADerivationSoundnessCarrierStrongPrefixDirectInductionShell.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessCarrierStrongPrefixFinalizerCompilationDirect.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessCarrierStrongPrefixGrowingCaseCompilation.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessCarrierStrongPrefixGrowingCaseCompilationDirect.

(** A direct finalization package records all context-sensitive roots.  Its
    prefix is the complete prefix above the caller's original PA base. *)
Definition
    RawCoqRestrictedPADerivationSoundnessCarrierGrowingFinalizationPackageOfDirect
    (M : RawPAModel)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
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
      (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixDirectCode
        M inputs) in
  let extendedContext :=
    rawPAInductionExtendedContext M growingContext axiom in
  let openContext :=
    rawCoqRestrictedPADerivationSoundnessCarrierFinalizerDirectOpenContext
      M inputs growingContext axiom in
  let finalizerRoot :=
    rawCoqRestrictedPADerivationSoundnessCarrierFinalizerDirectRoot
      M inputs growingContext axiom arithmeticOpenRoot in
  RawCodedPAAxiomWitnessContext M growingWitnessList growingContext /\
  RawCodedPALocalProofOf M growingContext
    (rawCoqRestrictedPADerivationSoundnessCarrierFinalizerLtSelfSuccDirectCode
      M inputs)
    arithmeticBaseRoot /\
  RawCodedPAAxiomWitnessContext M extendedWitnessList extendedContext /\
  RawCodedPALocalProofOf M extendedContext
    (rawCoqRestrictedPADerivationSoundnessCarrierStrongStepDirectCode
      M inputs)
    prefixedStrongStepRoot /\
  RawCodedPALocalProofOf M extendedContext
    (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixZeroDirectCode
      M inputs)
    zeroChild /\
  RawCodedPALocalProofOf M extendedContext
    (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixStepAllDirectCode
      M inputs)
    stepChild /\
  RawCodedPALocalProofOf M extendedContext
    (rawCoqRestrictedPADerivationSoundnessCarrierFinalizerLtSelfSuccDirectCode
      M inputs)
    arithmeticExtendedRoot /\
  RawCodedPALocalProofOf M openContext
    (rawCoqRestrictedPADerivationSoundnessCarrierFinalizerLtSelfSuccDirectCode
      M inputs)
    arithmeticOpenRoot /\
  RawCodedPALocalProofOf M extendedContext
    (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixFinalizerDirectCode
      M inputs)
    finalizerRoot /\
  RawCodedPAProofOf M
    (rawCoqRestrictedPADerivationSoundnessUniversalDirectCode M inputs)
    (rawCoqRestrictedPADerivationSoundnessStrongPrefixDirectFinalizedCertificate
      M inputs growingWitnessList growingContext axiom bodyChild
      zeroChild stepChild finalizerRoot).

Arguments
  RawCoqRestrictedPADerivationSoundnessCarrierGrowingFinalizationPackageOfDirect
  M inputs baseWitnessList baseContext axiom prefix
  prefixedStrongStepRoot zeroChild stepChild arithmeticBaseRoot
  arithmeticExtendedRoot arithmeticOpenRoot bodyChild : clear implicits.

(** The temporary [forall d, K(d)] assumption is closed.  This direct shift
    proof is the sole opaque-sensitive ingredient needed to reuse the generic
    cons-target binder-readiness lemma. *)
Lemma
    raw_coqRestrictedPADerivationSoundnessCarrierStrongPrefixAllDirect_selfShift
    : forall (M : RawPAModel), RawPASatisfies M -> forall
      (inputs : RawCodedTemplateDirectStructuralInputs M),
  RawCodedFormulaShift M
    (raw_zero M) (rawNumeralValue M 1)
    (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixAllDirectCode
      M inputs)
    (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixAllDirectCode
      M inputs).
Proof.
  intros M hPA inputs.
  change (RawCodedFormulaShift M
    (raw_zero M) (rawNumeralValue M 1)
    (rawDirectTemplateFormula inputs
      coqRestrictedPADerivationSoundnessCarrierStrongPrefixAllTemplate)
    (rawDirectTemplateFormula inputs
      coqRestrictedPADerivationSoundnessCarrierStrongPrefixAllTemplate)).
  pose proof (rawDirectTemplateFormula_shiftAt M hPA inputs 0
    coqRestrictedPADerivationSoundnessCarrierStrongPrefixAllTemplate)
    as hshift.
  rewrite
    coqRestrictedPADerivationSoundnessCarrierStrongPrefixAllTemplate_shift_closed
    in hshift.
  exact hshift.
Qed.

Corollary
    raw_coqRestrictedPADerivationSoundnessCarrierStrongPrefixAllDirect_cons_binderReady
    : forall (M : RawPAModel), RawPASatisfies M -> forall
      (inputs : RawCodedTemplateDirectStructuralInputs M) context,
  RawContextBinderReady M context
    (rawListNode M
      (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixAllDirectCode
        M inputs)
      context).
Proof.
  intros M hPA inputs context.
  exact (raw_contextBinderReady_cons_target_of_head_shift M hPA
    context
    (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixAllDirectCode
      M inputs)
    (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixAllDirectCode
      M inputs)
    (raw_coqRestrictedPADerivationSoundnessCarrierStrongPrefixAllDirect_selfShift
      M hPA inputs)).
Qed.

(** Complete a direct growing case package by selecting the finalizer's
    arithmetic prefix above it.  The closure and strong-step hypotheses are
    deliberately unchanged: neither finite arithmetic compilation claims
    to discharge the genuinely nonstandard recursive argument. *)
Theorem
    raw_coqRestrictedPADerivationSoundnessCarrierGrowingFinalizationPackageDirect_of_growing_case_package
    : forall (M : RawPAModel), RawPASatisfies M -> forall
      (inputs : RawCodedTemplateDirectStructuralInputs M)
      replacement axiom closureCount baseWitnessList baseContext
      (casePrefix : StandardPAAxiomWitnessPrefix)
      noLtZeroBaseRoot ltKernelBaseRoot caseStrongStepRoot
      noLtZeroExtendedRoot ltKernelExtendedRoot zeroChild stepChild,
  RawCoqCarrierStrongPrefixGrowingCasePackageOfDirect
    M inputs baseWitnessList baseContext axiom casePrefix
    noLtZeroBaseRoot ltKernelBaseRoot caseStrongStepRoot
    noLtZeroExtendedRoot ltKernelExtendedRoot zeroChild stepChild ->
  RawCoqRestrictedPADerivationSoundnessStrongPrefixDirectClosureRemainder
    M inputs replacement axiom closureCount ->
  exists (combinedPrefix : StandardPAAxiomWitnessPrefix)
      (finalStrongStepRoot finalZeroChild finalStepChild
        arithmeticBaseRoot arithmeticExtendedRoot arithmeticOpenRoot
        bodyChild : M),
    RawCoqRestrictedPADerivationSoundnessCarrierGrowingFinalizationPackageOfDirect
      M inputs baseWitnessList baseContext axiom combinedPrefix
      finalStrongStepRoot finalZeroChild finalStepChild
      arithmeticBaseRoot arithmeticExtendedRoot arithmeticOpenRoot
      bodyChild.
Proof.
  intros M hPA inputs replacement axiom closureCount
    baseWitnessList baseContext casePrefix
    noLtZeroBaseRoot ltKernelBaseRoot caseStrongStepRoot
    noLtZeroExtendedRoot ltKernelExtendedRoot zeroChild stepChild
    hcasePackage hremainder.
  unfold RawCoqCarrierStrongPrefixGrowingCasePackageOfDirect in hcasePackage.
  destruct hcasePackage as
    [hcaseBase
      [hnoLtZeroBase
        [hltKernelBase
          [hcaseExtended
            [hcaseStrongStep
              [hnoLtZeroExtended
                [hltKernelExtended [hzero hstep]]]]]]]].

  (* Compile [d < S d] over the already-prefixed case base. *)
  destruct
    (raw_codedTemplatePALocalProofOf_of_BProv_on_witnessed_tail
      M hPA (rawDirectStructuralTemplateTranslation M hPA inputs)
      (rawDirectStructuralTemplatePAAgreement M hPA inputs)
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
    (rawCoqRestrictedPADerivationSoundnessCarrierFinalizerLtSelfSuccDirectCode
      M inputs)
    arithmeticBaseRoot) in harithmeticBase.

  pose proof
    (raw_coqRestrictedPADerivationSoundnessCarrierFinalizerDirect_extendedContext_witnessed
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

  (* Transport all three case roots through one literal context inclusion. *)
  destruct
    (raw_codedPALocalProofWitnessedContextInclusionWeakening_complete
      M hPA
      (rawPAInductionExtendedWitnessList M
        (rawCoqCarrierStrongPrefixGrowingCaseWitnessList
          M casePrefix baseWitnessList)
        (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixDirectCode
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
        (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixDirectCode
          M inputs))
      (rawPAInductionExtendedContext M
        (rawCoqRestrictedPADerivationSoundnessCarrierGrowingBaseContext
          M finalizerPrefix
          (rawCoqCarrierStrongPrefixGrowingCaseContext
            M casePrefix baseContext))
        axiom)
      (rawCoqRestrictedPADerivationSoundnessCarrierStrongStepDirectCode
        M inputs)
      caseStrongStepRoot hcaseExtended hfinalExtended hextendedInclusion
      hcaseStrongStep) as [finalStrongStepRoot hfinalStrongStep].
  destruct
    (raw_codedPALocalProofWitnessedContextInclusionWeakening_complete
      M hPA
      (rawPAInductionExtendedWitnessList M
        (rawCoqCarrierStrongPrefixGrowingCaseWitnessList
          M casePrefix baseWitnessList)
        (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixDirectCode
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
        (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixDirectCode
          M inputs))
      (rawPAInductionExtendedContext M
        (rawCoqRestrictedPADerivationSoundnessCarrierGrowingBaseContext
          M finalizerPrefix
          (rawCoqCarrierStrongPrefixGrowingCaseContext
            M casePrefix baseContext))
        axiom)
      (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixZeroDirectCode
        M inputs)
      zeroChild hcaseExtended hfinalExtended hextendedInclusion hzero)
    as [finalZeroChild hfinalZero].
  destruct
    (raw_codedPALocalProofWitnessedContextInclusionWeakening_complete
      M hPA
      (rawPAInductionExtendedWitnessList M
        (rawCoqCarrierStrongPrefixGrowingCaseWitnessList
          M casePrefix baseWitnessList)
        (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixDirectCode
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
        (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixDirectCode
          M inputs))
      (rawPAInductionExtendedContext M
        (rawCoqRestrictedPADerivationSoundnessCarrierGrowingBaseContext
          M finalizerPrefix
          (rawCoqCarrierStrongPrefixGrowingCaseContext
            M casePrefix baseContext))
        axiom)
      (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixStepAllDirectCode
        M inputs)
      stepChild hcaseExtended hfinalExtended hextendedInclusion hstep)
    as [finalStepChild hfinalStep].

  (* Move the arithmetic guard beneath the induction axiom. *)
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
        (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixDirectCode
          M inputs))
      (rawPAInductionExtendedContext M
        (rawCoqRestrictedPADerivationSoundnessCarrierGrowingBaseContext
          M finalizerPrefix
          (rawCoqCarrierStrongPrefixGrowingCaseContext
            M casePrefix baseContext))
        axiom)
      (rawCoqRestrictedPADerivationSoundnessCarrierFinalizerLtSelfSuccDirectCode
        M inputs)
      arithmeticBaseRoot hfinalBase hfinalExtended
      harithmeticExtendedInclusion harithmeticBase)
    as [arithmeticExtendedRoot harithmeticExtended].

  (* The finalizer discharges an implication from the closed [forall K]
     assumption, so the arithmetic guard must also be weakened under that
     assumption.  Binder readiness, not mere list inclusion, justifies this
     quantifier-sensitive transport. *)
  pose proof
    (raw_codedPAAxiomWitnessPrefix_context_realizable_of_witnessed M
      (rawPAInductionExtendedWitnessList M
        (rawCoqRestrictedPADerivationSoundnessCarrierGrowingBaseWitnessList
          M finalizerPrefix
          (rawCoqCarrierStrongPrefixGrowingCaseWitnessList
            M casePrefix baseWitnessList))
        (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixDirectCode
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
      (rawCoqRestrictedPADerivationSoundnessCarrierFinalizerDirectOpenContext
        M inputs
        (rawCoqRestrictedPADerivationSoundnessCarrierGrowingBaseContext
          M finalizerPrefix
          (rawCoqCarrierStrongPrefixGrowingCaseContext
            M casePrefix baseContext))
        axiom)).
  {
    unfold
      rawCoqRestrictedPADerivationSoundnessCarrierFinalizerDirectOpenContext.
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
      (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixAllDirectCode
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
      (rawCoqRestrictedPADerivationSoundnessCarrierFinalizerDirectOpenContext
        M inputs
        (rawCoqRestrictedPADerivationSoundnessCarrierGrowingBaseContext
          M finalizerPrefix
          (rawCoqCarrierStrongPrefixGrowingCaseContext
            M casePrefix baseContext))
        axiom)).
  {
    unfold
      rawCoqRestrictedPADerivationSoundnessCarrierFinalizerDirectOpenContext.
    exact (raw_contextList_cons_realizable M hPA
      (rawPAInductionExtendedContext M
        (rawCoqRestrictedPADerivationSoundnessCarrierGrowingBaseContext
          M finalizerPrefix
          (rawCoqCarrierStrongPrefixGrowingCaseContext
            M casePrefix baseContext))
        axiom)
      (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixAllDirectCode
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
    (rawCoqRestrictedPADerivationSoundnessCarrierFinalizerDirectOpenContext
      M inputs
      (rawCoqRestrictedPADerivationSoundnessCarrierGrowingBaseContext
        M finalizerPrefix
        (rawCoqCarrierStrongPrefixGrowingCaseContext
          M casePrefix baseContext))
      axiom)
    (rawCoqRestrictedPADerivationSoundnessCarrierFinalizerLtSelfSuccDirectCode
      M inputs)
    arithmeticExtendedRoot hfinalExtendedRealizable hopenRealizable
    hopenInclusion
    (raw_coqRestrictedPADerivationSoundnessCarrierStrongPrefixAllDirect_cons_binderReady
      M hPA inputs
      (rawPAInductionExtendedContext M
        (rawCoqRestrictedPADerivationSoundnessCarrierGrowingBaseContext
          M finalizerPrefix
          (rawCoqCarrierStrongPrefixGrowingCaseContext
            M casePrefix baseContext))
        axiom))
    harithmeticExtended) as [arithmeticOpenRoot harithmeticOpen].

  pose proof
    (raw_codedPALocalProofOf_coqRestrictedPADerivationSoundnessCarrierFinalizerDirect_from_exact_arithmetic_leaf
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
    (raw_codedPAProofOf_coqRestrictedPADerivationSoundnessUniversalDirect_of_strongPrefix_cases_and_finalizer
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
      (rawCoqRestrictedPADerivationSoundnessCarrierFinalizerDirectRoot
        M inputs
        (rawCoqRestrictedPADerivationSoundnessCarrierGrowingBaseContext
          M finalizerPrefix
          (rawCoqCarrierStrongPrefixGrowingCaseContext
            M casePrefix baseContext))
        axiom arithmeticOpenRoot)
      hfinalBase hremainder hfinalZero hfinalStep hfinalizer)
    as [bodyChild hproof].

  (* Prefix folds cons each list from right to left.  Therefore adding the
     finalizer prefix above the case prefix is represented by this precise
     order of append. *)
  exists (finalizerPrefix ++ casePrefix), finalStrongStepRoot,
    finalZeroChild, finalStepChild, arithmeticBaseRoot,
    arithmeticExtendedRoot, arithmeticOpenRoot, bodyChild.
  unfold
    RawCoqRestrictedPADerivationSoundnessCarrierGrowingFinalizationPackageOfDirect,
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

(** Compact endpoint: run the direct growing case compiler, add the direct
    finalizer prefix, and return the ordinary PA proof certificate. *)
Corollary
    raw_codedPAProofOf_coqRestrictedPADerivationSoundnessUniversalDirect_of_growing_case_and_finalizer
    : forall (M : RawPAModel), RawPASatisfies M -> forall
      (inputs : RawCodedTemplateDirectStructuralInputs M)
      replacement axiom closureCount baseWitnessList baseContext
      strongStepRoot,
  RawCodedPAAxiomWitnessContext M baseWitnessList baseContext ->
  RawCoqRestrictedPADerivationSoundnessStrongPrefixDirectClosureRemainder
    M inputs replacement axiom closureCount ->
  RawCodedPALocalProofOf M
    (rawPAInductionExtendedContext M baseContext axiom)
    (rawCoqRestrictedPADerivationSoundnessCarrierStrongStepDirectCode
      M inputs)
    strongStepRoot ->
  exists (prefix : StandardPAAxiomWitnessPrefix)
      (zeroChild stepChild arithmeticOpenRoot bodyChild : M),
    RawCodedPAProofOf M
      (rawCoqRestrictedPADerivationSoundnessUniversalDirectCode M inputs)
      (rawCoqRestrictedPADerivationSoundnessStrongPrefixDirectFinalizedCertificate
        M inputs
        (rawCoqRestrictedPADerivationSoundnessCarrierGrowingBaseWitnessList
          M prefix baseWitnessList)
        (rawCoqRestrictedPADerivationSoundnessCarrierGrowingBaseContext
          M prefix baseContext)
        axiom bodyChild zeroChild stepChild
        (rawCoqRestrictedPADerivationSoundnessCarrierFinalizerDirectRoot
          M inputs
          (rawCoqRestrictedPADerivationSoundnessCarrierGrowingBaseContext
            M prefix baseContext)
          axiom arithmeticOpenRoot)).
Proof.
  intros M hPA inputs replacement axiom closureCount
    baseWitnessList baseContext strongStepRoot hbase hremainder hstrongStep.
  destruct
    (raw_coqCarrierStrongPrefixGrowingCasePackageDirect
      M hPA inputs replacement axiom closureCount
      baseWitnessList baseContext strongStepRoot
      hbase hremainder hstrongStep)
    as (casePrefix & noLtZeroBaseRoot & ltKernelBaseRoot &
      caseStrongStepRoot & noLtZeroExtendedRoot & ltKernelExtendedRoot &
      caseZeroChild & caseStepChild & hcasePackage).
  destruct
    (raw_coqRestrictedPADerivationSoundnessCarrierGrowingFinalizationPackageDirect_of_growing_case_package
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
    RawCoqRestrictedPADerivationSoundnessCarrierGrowingFinalizationPackageOfDirect
    in hfinalPackage.
  destruct hfinalPackage as
    [_ [_ [_ [_ [_ [_ [_ [_ [_ hproof]]]]]]]]].
  exact hproof.
Qed.

End
  PABoundedRawCodedRestrictedPADerivationSoundnessCarrierStrongPrefixGrowingIntegrationDirect.
