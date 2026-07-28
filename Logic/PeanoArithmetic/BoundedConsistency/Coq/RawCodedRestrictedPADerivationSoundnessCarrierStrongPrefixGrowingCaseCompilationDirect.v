(**
  Direct-code specialization of the growing strong-prefix case compiler.

  The arithmetic case analysis and its finite proof template were already
  checked in
  [RawCodedRestrictedPADerivationSoundnessCarrierStrongPrefixGrowingCaseCompilation].
  In particular, this file does not duplicate the roughly 1,630-line
  metaproof establishing
  [coqCarrierStrongPrefixCaseCompilationRoot_valid].  It specializes that
  same checked tree through the direct translation used for genuinely
  nonstandard opaque formula codes.

  This distinction is essential: direct inputs expose represented shift and
  opening traces at opaque leaves.  No finite structural formula tree is
  inferred from those traces, and no carrier formula code is decoded.
*)

From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors
  RawCodedContextStructure
  RawCodedPAAxiomWitness
  RawCodedRestrictedPAProof
  RawCodedProofBinaryConstructors
  RawCodedProofAndEConstructors
  RawCodedPALocalProofExistential
  RawCodedPALocalProofComposition
  RawCodedPALocalProofConjunction
  RawCodedPALocalProofPropositionalRules
  RawCodedPALocalProofWitnessedContextMerge
  RawCodedPALocalProofWitnessedContextMergeTransportComplete
  RawCodedPAAxiomContextSelfShift
  RawCodedPAInductionAxiomCertificate
  RawCodedPAClosureInductionCompiler
  RawCodedPAAxiomWitnessPrefix
  RawCodedTemplateSyntax
  RawCodedTemplateProofCompiler
  RawCodedTemplateProofCompilerSelfShiftTail
  RawCodedTemplatePAEmbeddingSelfShiftTail
  RawCodedTemplateStructuralTranslation
  RawCodedTemplateDirectStructuralTranslation
  RawCodedTemplateDirectStructuralPAAgreement
  RawCodedRestrictedPADerivationSoundnessCarrierStrongPrefixGrowingCaseCompilation
  RawCodedRestrictedPADerivationSoundnessCarrierStrongPrefixDirectInductionShell.

Module
  PABoundedRawCodedRestrictedPADerivationSoundnessCarrierStrongPrefixGrowingCaseCompilationDirect.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedContextStructure.
Import PABoundedRawCodedPAAxiomWitness.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedProofBinaryConstructors.
Import PABoundedRawCodedProofAndEConstructors.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPALocalProofComposition.
Import PABoundedRawCodedPALocalProofConjunction.
Import PABoundedRawCodedPALocalProofPropositionalRules.
Import PABoundedRawCodedPALocalProofWitnessedContextMerge.
Import
  PABoundedRawCodedPALocalProofWitnessedContextMergeTransportComplete.
Import PABoundedRawCodedPAAxiomContextSelfShift.
Import PABoundedRawCodedPAInductionAxiomCertificate.
Import PABoundedRawCodedPAClosureInductionCompiler.
Import PABoundedRawCodedPAAxiomWitnessPrefix.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedTemplateProofCompilerSelfShiftTail.
Import PABoundedRawCodedTemplatePAEmbeddingSelfShiftTail.
Import PABoundedRawCodedTemplateStructuralTranslation.
Import PABoundedRawCodedTemplateDirectStructuralTranslation.
Import PABoundedRawCodedTemplateDirectStructuralPAAgreement.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessCarrierStrongPrefixGrowingCaseCompilation.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessCarrierStrongPrefixDirectInductionShell.

(** Exact direct translations of the two arithmetic assumptions and of the
    case compiler's conjunction. *)
Definition rawCoqCarrierStrongPrefixNoLtZeroDirectCode
    (M : RawPAModel)
    (inputs : RawCodedTemplateDirectStructuralInputs M) : M :=
  rawDirectTemplateFormula inputs
    coqCarrierStrongPrefixNoLtZeroTemplate.

Definition rawCoqCarrierStrongPrefixLtKernelDirectCode
    (M : RawPAModel)
    (inputs : RawCodedTemplateDirectStructuralInputs M) : M :=
  rawDirectTemplateFormula inputs
    coqCarrierStrongPrefixLtKernelTemplate.

Definition rawCoqCarrierStrongPrefixOrdinaryStepDirectCode
    (M : RawPAModel)
    (inputs : RawCodedTemplateDirectStructuralInputs M) : M :=
  rawDirectTemplateFormula inputs
    coqCarrierStrongPrefixOrdinaryStepTemplate.

Definition rawCoqCarrierStrongPrefixCasePairDirectCode
    (M : RawPAModel)
    (inputs : RawCodedTemplateDirectStructuralInputs M) : M :=
  rawFormulaAndCode M
    (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixZeroDirectCode
      M inputs)
    (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixStepAllDirectCode
      M inputs).

Arguments rawCoqCarrierStrongPrefixNoLtZeroDirectCode M inputs
  : clear implicits.
Arguments rawCoqCarrierStrongPrefixLtKernelDirectCode M inputs
  : clear implicits.
Arguments rawCoqCarrierStrongPrefixOrdinaryStepDirectCode M inputs
  : clear implicits.
Arguments rawCoqCarrierStrongPrefixCasePairDirectCode M inputs
  : clear implicits.

Lemma raw_coqCarrierStrongPrefixOrdinaryStepDirectCode_view : forall
    (M : RawPAModel)
    (inputs : RawCodedTemplateDirectStructuralInputs M),
  rawCoqCarrierStrongPrefixOrdinaryStepDirectCode M inputs =
  rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixStepAllDirectCode
    M inputs.
Proof. reflexivity. Qed.

(** Compile the already-validated finite proof tree on an arbitrary witnessed
    PA tail.  The direct translation is accepted by the generic compiler
    precisely because its opaque leaves carry the represented operation
    traces required by the quantifier rules. *)
Definition rawCoqCarrierStrongPrefixCaseCompilationDirectRoot
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    (context : M) : M :=
  rawTemplateProofCodeOnTail
    (rawDirectStructuralTemplateTranslation M hPA inputs)
    context coqCarrierStrongPrefixCaseCompilationRoot.

Arguments rawCoqCarrierStrongPrefixCaseCompilationDirectRoot
  M hPA inputs context : clear implicits.

Theorem
    raw_codedPALocalProofOf_coqCarrierStrongPrefixCaseCompilationDirect
    : forall (M : RawPAModel) (hPA : RawPASatisfies M)
      (inputs : RawCodedTemplateDirectStructuralInputs M)
      witnessList context,
  RawCodedPAAxiomWitnessContext M witnessList context ->
  RawCodedPALocalProofOf M context
    (rawDirectTemplateFormula inputs
      coqCarrierStrongPrefixCaseCompilationTemplate)
    (rawCoqCarrierStrongPrefixCaseCompilationDirectRoot
      M hPA inputs context).
Proof.
  intros M hPA inputs witnessList context hwitnessed.
  unfold rawCoqCarrierStrongPrefixCaseCompilationDirectRoot.
  apply (raw_templateProofOnPAAxiomContext_localProof M hPA
    (rawDirectStructuralTemplateTranslation M hPA inputs)
    witnessList context coqCarrierStrongPrefixCaseCompilationRoot).
  - exact hwitnessed.
  - exact (proj1 coqCarrierStrongPrefixCaseCompilationRoot_valid).
Qed.

(** Consume the direct compiled implication using three genuine local proof
    roots in one witnessed context.  All formula identities here are finite
    constructor computations around the opaque leaves; none asks for a
    structural description of an opaque carrier formula. *)
Theorem
    raw_codedPALocalProofOf_coqCarrierStrongPrefixCasesDirect_from_roots
    : forall (M : RawPAModel) (hPA : RawPASatisfies M)
      (inputs : RawCodedTemplateDirectStructuralInputs M)
      witnessList context noLtZeroRoot ltKernelRoot strongStepRoot,
  RawCodedPAAxiomWitnessContext M witnessList context ->
  RawCodedPALocalProofOf M context
    (rawCoqCarrierStrongPrefixNoLtZeroDirectCode M inputs) noLtZeroRoot ->
  RawCodedPALocalProofOf M context
    (rawCoqCarrierStrongPrefixLtKernelDirectCode M inputs) ltKernelRoot ->
  RawCodedPALocalProofOf M context
    (rawCoqRestrictedPADerivationSoundnessCarrierStrongStepDirectCode
      M inputs) strongStepRoot ->
  exists zeroChild stepChild : M,
    RawCodedPALocalProofOf M context
      (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixZeroDirectCode
        M inputs) zeroChild /\
    RawCodedPALocalProofOf M context
      (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixStepAllDirectCode
        M inputs) stepChild.
Proof.
  intros M hPA inputs witnessList context
    noLtZeroRoot ltKernelRoot strongStepRoot
    hwitnessed hnoZero hkernel hstrong.
  pose proof
    (raw_codedPALocalProofOf_coqCarrierStrongPrefixCaseCompilationDirect
      M hPA inputs witnessList context hwitnessed) as hcompiled.
  unfold coqCarrierStrongPrefixCaseCompilationTemplate in hcompiled.
  cbn [rawDirectTemplateFormula
    rawStructuralTemplateFormulaWith] in hcompiled.
  set (afterNoZero := rawProofImpERoot M context
    (rawCoqCarrierStrongPrefixNoLtZeroDirectCode M inputs)
    (rawFormulaImpCode M
      (rawCoqCarrierStrongPrefixLtKernelDirectCode M inputs)
      (rawFormulaImpCode M
        (rawCoqRestrictedPADerivationSoundnessCarrierStrongStepDirectCode
          M inputs)
        (rawCoqCarrierStrongPrefixCasePairDirectCode M inputs)))
    (rawCoqCarrierStrongPrefixCaseCompilationDirectRoot
      M hPA inputs context) noLtZeroRoot).
  assert (hafterNoZero : RawCodedPALocalProofOf M context
      (rawFormulaImpCode M
        (rawCoqCarrierStrongPrefixLtKernelDirectCode M inputs)
        (rawFormulaImpCode M
          (rawCoqRestrictedPADerivationSoundnessCarrierStrongStepDirectCode
            M inputs)
          (rawCoqCarrierStrongPrefixCasePairDirectCode M inputs)))
      afterNoZero).
  {
    apply (raw_codedPALocalProofOf_impE M hPA context
      (rawCoqCarrierStrongPrefixNoLtZeroDirectCode M inputs)
      (rawFormulaImpCode M
        (rawCoqCarrierStrongPrefixLtKernelDirectCode M inputs)
        (rawFormulaImpCode M
          (rawCoqRestrictedPADerivationSoundnessCarrierStrongStepDirectCode
            M inputs)
          (rawCoqCarrierStrongPrefixCasePairDirectCode M inputs)))
      (rawCoqCarrierStrongPrefixCaseCompilationDirectRoot
        M hPA inputs context) noLtZeroRoot).
    - exact hcompiled.
    - exact hnoZero.
  }
  set (afterKernel := rawProofImpERoot M context
    (rawCoqCarrierStrongPrefixLtKernelDirectCode M inputs)
    (rawFormulaImpCode M
      (rawCoqRestrictedPADerivationSoundnessCarrierStrongStepDirectCode
        M inputs)
      (rawCoqCarrierStrongPrefixCasePairDirectCode M inputs))
    afterNoZero ltKernelRoot).
  assert (hafterKernel : RawCodedPALocalProofOf M context
      (rawFormulaImpCode M
        (rawCoqRestrictedPADerivationSoundnessCarrierStrongStepDirectCode
          M inputs)
        (rawCoqCarrierStrongPrefixCasePairDirectCode M inputs))
      afterKernel).
  {
    exact (raw_codedPALocalProofOf_impE M hPA context
      (rawCoqCarrierStrongPrefixLtKernelDirectCode M inputs)
      (rawFormulaImpCode M
        (rawCoqRestrictedPADerivationSoundnessCarrierStrongStepDirectCode
          M inputs)
        (rawCoqCarrierStrongPrefixCasePairDirectCode M inputs))
      afterNoZero ltKernelRoot hafterNoZero hkernel).
  }
  set (pairRoot := rawProofImpERoot M context
    (rawCoqRestrictedPADerivationSoundnessCarrierStrongStepDirectCode
      M inputs)
    (rawCoqCarrierStrongPrefixCasePairDirectCode M inputs)
    afterKernel strongStepRoot).
  assert (hpair : RawCodedPALocalProofOf M context
      (rawCoqCarrierStrongPrefixCasePairDirectCode M inputs) pairRoot).
  {
    exact (raw_codedPALocalProofOf_impE M hPA context
      (rawCoqRestrictedPADerivationSoundnessCarrierStrongStepDirectCode
        M inputs)
      (rawCoqCarrierStrongPrefixCasePairDirectCode M inputs)
      afterKernel strongStepRoot hafterKernel hstrong).
  }
  exists
    (rawProofAndERoot M RawAndLeft context
      (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixZeroDirectCode
        M inputs)
      (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixStepAllDirectCode
        M inputs) pairRoot),
    (rawProofAndERoot M RawAndRight context
      (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixZeroDirectCode
        M inputs)
      (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixStepAllDirectCode
        M inputs) pairRoot).
  split.
  - exact (raw_codedPALocalProofOf_andE1 M hPA context
      (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixZeroDirectCode
        M inputs)
      (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixStepAllDirectCode
        M inputs) pairRoot hpair).
  - exact (raw_codedPALocalProofOf_andE2 M hPA context
      (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixZeroDirectCode
        M inputs)
      (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixStepAllDirectCode
        M inputs) pairRoot hpair).
Qed.

(** ------------------------------------------------------------------
    Honest growth of the witnessed arithmetic base.

    The witness-list and context folds are independent of the template
    translation, so this direct package deliberately reuses the literal
    prefix operations from the checked structural package. *)

Definition RawCoqCarrierStrongPrefixGrowingCasePackageOfDirect
    (M : RawPAModel)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    (baseWitnessList baseContext axiom : M)
    (prefix : StandardPAAxiomWitnessPrefix)
    (noLtZeroBaseRoot ltKernelBaseRoot prefixedStrongStepRoot
      noLtZeroExtendedRoot ltKernelExtendedRoot zeroChild stepChild : M)
    : Prop :=
  let growingWitnessList :=
    rawCoqCarrierStrongPrefixGrowingCaseWitnessList
      M prefix baseWitnessList in
  let growingContext :=
    rawCoqCarrierStrongPrefixGrowingCaseContext
      M prefix baseContext in
  let extendedWitnessList :=
    rawPAInductionExtendedWitnessList M growingWitnessList
      (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixDirectCode
        M inputs) in
  let extendedContext :=
    rawPAInductionExtendedContext M growingContext axiom in
  RawCodedPAAxiomWitnessContext M growingWitnessList growingContext /\
  RawCodedPALocalProofOf M growingContext
    (rawCoqCarrierStrongPrefixNoLtZeroDirectCode M inputs)
    noLtZeroBaseRoot /\
  RawCodedPALocalProofOf M growingContext
    (rawCoqCarrierStrongPrefixLtKernelDirectCode M inputs)
    ltKernelBaseRoot /\
  RawCodedPAAxiomWitnessContext M extendedWitnessList extendedContext /\
  RawCodedPALocalProofOf M extendedContext
    (rawCoqRestrictedPADerivationSoundnessCarrierStrongStepDirectCode
      M inputs) prefixedStrongStepRoot /\
  RawCodedPALocalProofOf M extendedContext
    (rawCoqCarrierStrongPrefixNoLtZeroDirectCode M inputs)
    noLtZeroExtendedRoot /\
  RawCodedPALocalProofOf M extendedContext
    (rawCoqCarrierStrongPrefixLtKernelDirectCode M inputs)
    ltKernelExtendedRoot /\
  RawCodedPALocalProofOf M extendedContext
    (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixZeroDirectCode
      M inputs) zeroChild /\
  RawCodedPALocalProofOf M extendedContext
    (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixStepAllDirectCode
      M inputs) stepChild.

Arguments RawCoqCarrierStrongPrefixGrowingCasePackageOfDirect
  M inputs baseWitnessList baseContext axiom prefix
  noLtZeroBaseRoot ltKernelBaseRoot prefixedStrongStepRoot
  noLtZeroExtendedRoot ltKernelExtendedRoot zeroChild stepChild
  : clear implicits.

(** Select one finite prefix for the two ordinary arithmetic kernels,
    transport the supplied direct strong-step root into that enlarged base,
    and run the direct case compiler there.  The selected prefix is exposed
    in the result; no hidden certificate or context extension is assumed. *)
Theorem raw_coqCarrierStrongPrefixGrowingCasePackageDirect : forall
    (M : RawPAModel), RawPASatisfies M -> forall
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
      (noLtZeroBaseRoot ltKernelBaseRoot prefixedStrongStepRoot
        noLtZeroExtendedRoot ltKernelExtendedRoot zeroChild stepChild : M),
    RawCoqCarrierStrongPrefixGrowingCasePackageOfDirect
      M inputs baseWitnessList baseContext axiom prefix
      noLtZeroBaseRoot ltKernelBaseRoot prefixedStrongStepRoot
      noLtZeroExtendedRoot ltKernelExtendedRoot zeroChild stepChild.
Proof.
  intros M hPA inputs replacement axiom closureCount
    baseWitnessList baseContext strongStepRoot
    hbase hremainder hstrongStep.

  (* Compile the conjunction of the two closed PA kernels through the direct
     translation.  Embedded ordinary PA syntax never touches an opaque leaf,
     so direct PA agreement is sufficient. *)
  destruct
    (raw_codedTemplatePALocalProofOf_of_BProv_on_witnessed_tail
      M hPA (rawDirectStructuralTemplateTranslation M hPA inputs)
      (rawDirectStructuralTemplatePAAgreement M hPA inputs)
      baseWitnessList baseContext
      coqCarrierStrongPrefixCaseArithmeticFormula
      hbase coqCarrierStrongPrefixCaseArithmetic_bprov)
    as (prefix & arithmeticPairRoot & hprefixed & harithmeticPair).
  change (RawCodedPALocalProofOf M
    (rawCoqCarrierStrongPrefixGrowingCaseContext M prefix baseContext)
    (rawFormulaAndCode M
      (rawCoqCarrierStrongPrefixNoLtZeroDirectCode M inputs)
      (rawCoqCarrierStrongPrefixLtKernelDirectCode M inputs))
    arithmeticPairRoot) in harithmeticPair.
  pose proof (raw_codedPALocalProofOf_andE1 M hPA
    (rawCoqCarrierStrongPrefixGrowingCaseContext M prefix baseContext)
    (rawCoqCarrierStrongPrefixNoLtZeroDirectCode M inputs)
    (rawCoqCarrierStrongPrefixLtKernelDirectCode M inputs)
    arithmeticPairRoot harithmeticPair) as hnoLtZeroBase.
  pose proof (raw_codedPALocalProofOf_andE2 M hPA
    (rawCoqCarrierStrongPrefixGrowingCaseContext M prefix baseContext)
    (rawCoqCarrierStrongPrefixNoLtZeroDirectCode M inputs)
    (rawCoqCarrierStrongPrefixLtKernelDirectCode M inputs)
    arithmeticPairRoot harithmeticPair) as hltKernelBase.
  set (noLtZeroBaseRoot := rawProofAndERoot M RawAndLeft
    (rawCoqCarrierStrongPrefixGrowingCaseContext M prefix baseContext)
    (rawCoqCarrierStrongPrefixNoLtZeroDirectCode M inputs)
    (rawCoqCarrierStrongPrefixLtKernelDirectCode M inputs)
    arithmeticPairRoot) in hnoLtZeroBase |- *.
  set (ltKernelBaseRoot := rawProofAndERoot M RawAndRight
    (rawCoqCarrierStrongPrefixGrowingCaseContext M prefix baseContext)
    (rawCoqCarrierStrongPrefixNoLtZeroDirectCode M inputs)
    (rawCoqCarrierStrongPrefixLtKernelDirectCode M inputs)
    arithmeticPairRoot) in hltKernelBase |- *.

  (* The direct closure remainder identifies the same genuine induction
     axiom for both bases. *)
  pose proof
    (raw_coqRestrictedPADerivationSoundnessCarrierStrongPrefixDirectClosureInductionData
      M hPA inputs replacement axiom closureCount hremainder) as hdata.
  pose proof (raw_codedPAClosureInductionData_axiom M
    replacement
    (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixDirectCode
      M inputs)
    axiom
    (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixShiftedDirectCode
      M inputs)
    (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixSuccessorDirectCode
      M inputs)
    (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixZeroDirectCode
      M inputs)
    (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixAllDirectCode
      M inputs)
    (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixStepImpDirectCode
      M inputs)
    (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixStepAllDirectCode
      M inputs)
    (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixPremiseDirectCode
      M inputs)
    (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixBodyDirectCode
      M inputs)
    closureCount hdata) as hinduction.
  pose proof (raw_codedPAAxiomWitnessContext_add_induction M hPA
    baseWitnessList baseContext
    (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixDirectCode
      M inputs)
    axiom hbase hinduction) as hbaseExtended.
  pose proof (raw_codedPAAxiomWitnessContext_add_induction M hPA
    (rawCoqCarrierStrongPrefixGrowingCaseWitnessList
      M prefix baseWitnessList)
    (rawCoqCarrierStrongPrefixGrowingCaseContext M prefix baseContext)
    (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixDirectCode
      M inputs)
    axiom hprefixed hinduction) as hprefixedExtended.

  pose proof (raw_codedPAAxiomWitnessContext_context_realizable M
    baseWitnessList baseContext hbase) as hbaseRealizable.
  pose proof (raw_codedPAAxiomWitnessContext_context_realizable M
    (rawCoqCarrierStrongPrefixGrowingCaseWitnessList
      M prefix baseWitnessList)
    (rawCoqCarrierStrongPrefixGrowingCaseContext M prefix baseContext)
    hprefixed) as hprefixedRealizable.
  assert (hextendedInclusion : RawContextListIncluded M
      (rawPAInductionExtendedContext M baseContext axiom)
      (rawPAInductionExtendedContext M
        (rawCoqCarrierStrongPrefixGrowingCaseContext M prefix baseContext)
        axiom)).
  {
    unfold rawPAInductionExtendedContext.
    exact (raw_contextListIncluded_cons M hPA
      baseContext
      (rawCoqCarrierStrongPrefixGrowingCaseContext M prefix baseContext)
      axiom axiom hbaseRealizable hprefixedRealizable eq_refl
      (raw_contextListIncluded_coqCarrierStrongPrefixGrowingCase_base
        M hPA prefix baseContext)).
  }
  destruct
    (raw_codedPALocalProofWitnessedContextInclusionWeakening_complete
      M hPA
      (rawPAInductionExtendedWitnessList M baseWitnessList
        (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixDirectCode
          M inputs))
      (rawPAInductionExtendedContext M baseContext axiom)
      (rawPAInductionExtendedWitnessList M
        (rawCoqCarrierStrongPrefixGrowingCaseWitnessList
          M prefix baseWitnessList)
        (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixDirectCode
          M inputs))
      (rawPAInductionExtendedContext M
        (rawCoqCarrierStrongPrefixGrowingCaseContext M prefix baseContext)
        axiom)
      (rawCoqRestrictedPADerivationSoundnessCarrierStrongStepDirectCode
        M inputs)
      strongStepRoot hbaseExtended hprefixedExtended
      hextendedInclusion hstrongStep) as
    [prefixedStrongStepRoot hprefixedStrongStep].

  assert (harithmeticExtendedInclusion : RawContextListIncluded M
      (rawCoqCarrierStrongPrefixGrowingCaseContext M prefix baseContext)
      (rawPAInductionExtendedContext M
        (rawCoqCarrierStrongPrefixGrowingCaseContext M prefix baseContext)
        axiom)).
  {
    unfold rawPAInductionExtendedContext.
    exact (raw_contextListIncluded_cons_target M hPA
      (rawCoqCarrierStrongPrefixGrowingCaseContext M prefix baseContext)
      (rawCoqCarrierStrongPrefixGrowingCaseContext M prefix baseContext)
      axiom
      (raw_contextListIncluded_refl M
        (rawCoqCarrierStrongPrefixGrowingCaseContext
          M prefix baseContext))).
  }
  destruct
    (raw_codedPALocalProofWitnessedContextInclusionWeakening_complete
      M hPA
      (rawCoqCarrierStrongPrefixGrowingCaseWitnessList
        M prefix baseWitnessList)
      (rawCoqCarrierStrongPrefixGrowingCaseContext M prefix baseContext)
      (rawPAInductionExtendedWitnessList M
        (rawCoqCarrierStrongPrefixGrowingCaseWitnessList
          M prefix baseWitnessList)
        (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixDirectCode
          M inputs))
      (rawPAInductionExtendedContext M
        (rawCoqCarrierStrongPrefixGrowingCaseContext M prefix baseContext)
        axiom)
      (rawCoqCarrierStrongPrefixNoLtZeroDirectCode M inputs)
      noLtZeroBaseRoot hprefixed hprefixedExtended
      harithmeticExtendedInclusion hnoLtZeroBase) as
    [noLtZeroExtendedRoot hnoLtZeroExtended].
  destruct
    (raw_codedPALocalProofWitnessedContextInclusionWeakening_complete
      M hPA
      (rawCoqCarrierStrongPrefixGrowingCaseWitnessList
        M prefix baseWitnessList)
      (rawCoqCarrierStrongPrefixGrowingCaseContext M prefix baseContext)
      (rawPAInductionExtendedWitnessList M
        (rawCoqCarrierStrongPrefixGrowingCaseWitnessList
          M prefix baseWitnessList)
        (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixDirectCode
          M inputs))
      (rawPAInductionExtendedContext M
        (rawCoqCarrierStrongPrefixGrowingCaseContext M prefix baseContext)
        axiom)
      (rawCoqCarrierStrongPrefixLtKernelDirectCode M inputs)
      ltKernelBaseRoot hprefixed hprefixedExtended
      harithmeticExtendedInclusion hltKernelBase) as
    [ltKernelExtendedRoot hltKernelExtended].

  destruct
    (raw_codedPALocalProofOf_coqCarrierStrongPrefixCasesDirect_from_roots
      M hPA inputs
      (rawPAInductionExtendedWitnessList M
        (rawCoqCarrierStrongPrefixGrowingCaseWitnessList
          M prefix baseWitnessList)
        (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixDirectCode
          M inputs))
      (rawPAInductionExtendedContext M
        (rawCoqCarrierStrongPrefixGrowingCaseContext M prefix baseContext)
        axiom)
      noLtZeroExtendedRoot ltKernelExtendedRoot prefixedStrongStepRoot
      hprefixedExtended hnoLtZeroExtended hltKernelExtended
      hprefixedStrongStep) as
    (zeroChild & stepChild & hzero & hstep).
  exists prefix, noLtZeroBaseRoot, ltKernelBaseRoot,
    prefixedStrongStepRoot, noLtZeroExtendedRoot,
    ltKernelExtendedRoot, zeroChild, stepChild.
  unfold RawCoqCarrierStrongPrefixGrowingCasePackageOfDirect.
  split.
  - exact hprefixed.
  - split.
    + exact hnoLtZeroBase.
    + split.
      * exact hltKernelBase.
      * split.
        -- exact hprefixedExtended.
        -- split.
           ++ exact hprefixedStrongStep.
           ++ split.
              ** exact hnoLtZeroExtended.
              ** split.
                 --- exact hltKernelExtended.
                 --- split.
                     +++ exact hzero.
                     +++ exact hstep.
Qed.

End
  PABoundedRawCodedRestrictedPADerivationSoundnessCarrierStrongPrefixGrowingCaseCompilationDirect.
