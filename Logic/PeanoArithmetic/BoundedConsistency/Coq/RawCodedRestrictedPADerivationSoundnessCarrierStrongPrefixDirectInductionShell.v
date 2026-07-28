(**
  Direct-code strong-prefix induction data for derivation soundness.

  The original carrier shell is specialized to finite structural inputs.
  That is appropriate when every opaque atom has a metatheoretic formula
  tree, but the selected truth formula in a nonstandard PA model need not
  have such a tree.  Direct structural inputs instead carry the represented
  shift and opening relations at opaque leaves.

  This module reuses the very same finite templates and exposes their exact
  direct codes.  It then assembles the generic closure-induction data from
  the direct shift/open relations.  The genuinely nonstandard operations—
  formula-bound discovery, carrier-length universal closure, and the full
  self-instantiation orbit—remain one explicit remainder, exactly as in the
  finite structural shell.
*)

From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors
  RawCodedFormulaOperations
  RawCodedPAAxiomWitness
  RawCodedRestrictedPAProof
  RawCodedPAProvability
  RawCodedProofBinaryConstructors
  RawCodedPALocalProofExistential
  RawCodedPALocalProofComposition
  RawCodedTemplateSyntax
  RawCodedTemplatePAEmbedding
  RawCodedTemplateDirectStructuralTranslation
  RawCodedTemplateDirectStructuralPAAgreement
  RawCodedPAInductionAxiomCertificate
  RawCodedPAUniversalClosureProofReduction
  RawCodedPAClosureInductionCompiler
  RawCodedRestrictedPAConsistencyFromUniversalSoundness
  RawCodedRestrictedPADerivationSoundnessCarrierStrongPrefixInductionShell.

Module
  PABoundedRawCodedRestrictedPADerivationSoundnessCarrierStrongPrefixDirectInductionShell.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedPAAxiomWitness.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedPAProvability.
Import PABoundedRawCodedProofBinaryConstructors.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPALocalProofComposition.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplatePAEmbedding.
Import PABoundedRawCodedTemplateDirectStructuralTranslation.
Import PABoundedRawCodedTemplateDirectStructuralPAAgreement.
Import PABoundedRawCodedPAInductionAxiomCertificate.
Import PABoundedRawCodedPAUniversalClosureProofReduction.
Import PABoundedRawCodedPAClosureInductionCompiler.
Import PABoundedRawCodedRestrictedPAConsistencyFromUniversalSoundness.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessCarrierStrongPrefixInductionShell.

(** ------------------------------------------------------------------
    Exact direct codes.

    Large soundness templates are kept behind named definitions.  Composite
    codes are built explicitly from their children so later proofs never ask
    the kernel to normalize both branches of the full predicate at once. *)

Definition rawCoqRestrictedPADerivationSoundnessPredicateDirectCode
    (M : RawPAModel) (inputs : RawCodedTemplateDirectStructuralInputs M) : M :=
  rawDirectTemplateFormula inputs
    coqRestrictedPADerivationSoundnessPredicateTemplate.

Definition rawCoqRestrictedPADerivationSoundnessUniversalDirectCode
    (M : RawPAModel) (inputs : RawCodedTemplateDirectStructuralInputs M) : M :=
  rawFormulaAllCode M
    (rawCoqRestrictedPADerivationSoundnessPredicateDirectCode M inputs).

Definition
    rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixDirectCode
    (M : RawPAModel) (inputs : RawCodedTemplateDirectStructuralInputs M) : M :=
  rawDirectTemplateFormula inputs
    coqRestrictedPADerivationSoundnessCarrierStrongPrefixTemplate.

Definition
    rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixShiftedDirectCode
    (M : RawPAModel) (inputs : RawCodedTemplateDirectStructuralInputs M) : M :=
  rawDirectTemplateFormula inputs
    coqRestrictedPADerivationSoundnessCarrierStrongPrefixShiftedTemplate.

Definition
    rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixSuccessorDirectCode
    (M : RawPAModel) (inputs : RawCodedTemplateDirectStructuralInputs M) : M :=
  rawDirectTemplateFormula inputs
    coqRestrictedPADerivationSoundnessCarrierStrongPrefixSuccessorTemplate.

Definition
    rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixZeroDirectCode
    (M : RawPAModel) (inputs : RawCodedTemplateDirectStructuralInputs M) : M :=
  rawDirectTemplateFormula inputs
    coqRestrictedPADerivationSoundnessCarrierStrongPrefixZeroTemplate.

Definition
    rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixAllDirectCode
    (M : RawPAModel) (inputs : RawCodedTemplateDirectStructuralInputs M) : M :=
  rawFormulaAllCode M
    (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixDirectCode
      M inputs).

Definition
    rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixStepImpDirectCode
    (M : RawPAModel) (inputs : RawCodedTemplateDirectStructuralInputs M) : M :=
  rawFormulaImpCode M
    (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixDirectCode
      M inputs)
    (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixSuccessorDirectCode
      M inputs).

Definition
    rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixStepAllDirectCode
    (M : RawPAModel) (inputs : RawCodedTemplateDirectStructuralInputs M) : M :=
  rawFormulaAllCode M
    (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixStepImpDirectCode
      M inputs).

Definition rawCoqRestrictedPADerivationSoundnessCarrierStrongStepDirectCode
    (M : RawPAModel) (inputs : RawCodedTemplateDirectStructuralInputs M) : M :=
  rawFormulaAllCode M
    (rawFormulaImpCode M
      (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixDirectCode
        M inputs)
      (rawCoqRestrictedPADerivationSoundnessPredicateDirectCode M inputs)).

Definition
    rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixPremiseDirectCode
    (M : RawPAModel) (inputs : RawCodedTemplateDirectStructuralInputs M) : M :=
  rawFormulaAndCode M
    (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixZeroDirectCode
      M inputs)
    (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixStepAllDirectCode
      M inputs).

Definition
    rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixBodyDirectCode
    (M : RawPAModel) (inputs : RawCodedTemplateDirectStructuralInputs M) : M :=
  rawFormulaImpCode M
    (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixPremiseDirectCode
      M inputs)
    (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixAllDirectCode
      M inputs).

Definition
    rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixFinalizerDirectCode
    (M : RawPAModel) (inputs : RawCodedTemplateDirectStructuralInputs M) : M :=
  rawFormulaImpCode M
    (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixAllDirectCode
      M inputs)
    (rawCoqRestrictedPADerivationSoundnessUniversalDirectCode M inputs).

Arguments rawCoqRestrictedPADerivationSoundnessPredicateDirectCode
  M inputs : clear implicits.
Arguments rawCoqRestrictedPADerivationSoundnessUniversalDirectCode
  M inputs : clear implicits.
Arguments
  rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixDirectCode
  M inputs : clear implicits.
Arguments
  rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixShiftedDirectCode
  M inputs : clear implicits.
Arguments
  rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixSuccessorDirectCode
  M inputs : clear implicits.
Arguments
  rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixZeroDirectCode
  M inputs : clear implicits.
Arguments
  rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixAllDirectCode
  M inputs : clear implicits.
Arguments
  rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixStepImpDirectCode
  M inputs : clear implicits.
Arguments
  rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixStepAllDirectCode
  M inputs : clear implicits.
Arguments rawCoqRestrictedPADerivationSoundnessCarrierStrongStepDirectCode
  M inputs : clear implicits.
Arguments
  rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixPremiseDirectCode
  M inputs : clear implicits.
Arguments
  rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixBodyDirectCode
  M inputs : clear implicits.
Arguments
  rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixFinalizerDirectCode
  M inputs : clear implicits.

(** Small constructor equations stay polymorphic in their children. *)
Lemma rawDirectTemplateFormula_imp_code : forall
    (M : RawPAModel) (inputs : RawCodedTemplateDirectStructuralInputs M)
    left right,
  rawDirectTemplateFormula inputs (tfImp left right) =
  rawFormulaImpCode M
    (rawDirectTemplateFormula inputs left)
    (rawDirectTemplateFormula inputs right).
Proof. reflexivity. Qed.

Lemma rawDirectTemplateFormula_all_code : forall
    (M : RawPAModel) (inputs : RawCodedTemplateDirectStructuralInputs M)
    body,
  rawDirectTemplateFormula inputs (tfAll body) =
  rawFormulaAllCode M (rawDirectTemplateFormula inputs body).
Proof. reflexivity. Qed.

Lemma raw_coqRestrictedPADerivationSoundnessUniversalDirectCode_view : forall
    (M : RawPAModel) (inputs : RawCodedTemplateDirectStructuralInputs M),
  rawCoqRestrictedPADerivationSoundnessUniversalDirectCode M inputs =
  rawDirectTemplateFormula inputs
    coqRestrictedPADerivationSoundnessUniversalTemplate.
Proof.
  intros M inputs.
  unfold rawCoqRestrictedPADerivationSoundnessUniversalDirectCode,
    coqRestrictedPADerivationSoundnessUniversalTemplate.
  rewrite rawDirectTemplateFormula_all_code.
  reflexivity.
Qed.

Lemma
    raw_coqRestrictedPADerivationSoundnessCarrierStrongStepDirectCode_view
    : forall (M : RawPAModel)
      (inputs : RawCodedTemplateDirectStructuralInputs M),
  rawCoqRestrictedPADerivationSoundnessCarrierStrongStepDirectCode M inputs =
  rawDirectTemplateFormula inputs
    coqRestrictedPADerivationSoundnessCarrierStrongStepTemplate.
Proof.
  intros M inputs.
  unfold rawCoqRestrictedPADerivationSoundnessCarrierStrongStepDirectCode,
    coqRestrictedPADerivationSoundnessCarrierStrongStepTemplate.
  rewrite rawDirectTemplateFormula_all_code.
  rewrite rawDirectTemplateFormula_imp_code.
  reflexivity.
Qed.

Lemma
    raw_coqRestrictedPADerivationSoundnessCarrierStrongPrefixFinalizerDirectCode_view
    : forall (M : RawPAModel)
      (inputs : RawCodedTemplateDirectStructuralInputs M),
  rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixFinalizerDirectCode
    M inputs =
  rawDirectTemplateFormula inputs
    coqRestrictedPADerivationSoundnessCarrierStrongPrefixFinalizerTemplate.
Proof.
  intros M inputs.
  unfold
    rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixFinalizerDirectCode,
    coqRestrictedPADerivationSoundnessCarrierStrongPrefixFinalizerTemplate,
    coqRestrictedPADerivationSoundnessCarrierStrongPrefixAllTemplate.
  rewrite rawDirectTemplateFormula_imp_code.
  rewrite rawDirectTemplateFormula_all_code.
  rewrite <-
    raw_coqRestrictedPADerivationSoundnessUniversalDirectCode_view.
  reflexivity.
Qed.

(** ------------------------------------------------------------------
    Honest direct closure boundary and induction graph. *)

Definition
    RawCoqRestrictedPADerivationSoundnessStrongPrefixDirectClosureRemainder
    (M : RawPAModel) (inputs : RawCodedTemplateDirectStructuralInputs M)
    (replacement axiom closureCount : M) : Prop :=
  RawCodedFormulaBound M
    (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixBodyDirectCode
      M inputs)
    closureCount /\
  RawCodedUniversalClosure M closureCount
    (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixBodyDirectCode
      M inputs)
    axiom /\
  RawCodedUniversalClosureSelfInstantiationThrough M replacement
    (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixBodyDirectCode
      M inputs)
    closureCount.

Arguments
  RawCoqRestrictedPADerivationSoundnessStrongPrefixDirectClosureRemainder
  M inputs replacement axiom closureCount : clear implicits.

(** Every finite operation edge is provided by the direct translation.
    Only the three arbitrary-carrier closure fields are projected from the
    explicit remainder. *)
Theorem
    raw_coqRestrictedPADerivationSoundnessCarrierStrongPrefixDirectClosureInductionData
    : forall (M : RawPAModel), RawPASatisfies M -> forall
      (inputs : RawCodedTemplateDirectStructuralInputs M)
      replacement axiom closureCount,
  RawCoqRestrictedPADerivationSoundnessStrongPrefixDirectClosureRemainder
    M inputs replacement axiom closureCount ->
  RawCodedPAClosureInductionData M replacement
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
    closureCount.
Proof.
  intros M hPA inputs replacement axiom closureCount
    [hbound [hclosure hself]].
  unfold RawCodedPAClosureInductionData.
  repeat apply conj.
  - unfold
      rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixDirectCode,
      rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixShiftedDirectCode,
      coqRestrictedPADerivationSoundnessCarrierStrongPrefixShiftedTemplate.
    exact (rawDirectTemplateFormula_shiftAt M hPA inputs 1
      coqRestrictedPADerivationSoundnessCarrierStrongPrefixTemplate).
  - rewrite <- (rawQuotedTermCode_standard M hPA
      (tSucc (tVar 0))).
    rewrite <- (rawTemplateTerm_embedPA
      (rawDirectStructuralTemplatePAAgreement M hPA inputs)
      (tSucc (tVar 0))).
    unfold
      rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixShiftedDirectCode,
      rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixSuccessorDirectCode,
      coqRestrictedPADerivationSoundnessCarrierStrongPrefixSuccessorTemplate.
    exact (rawDirectTemplateFormula_open M hPA inputs
      coqRestrictedPADerivationSoundnessCarrierStrongPrefixShiftedTemplate
      (embedPATerm (tSucc (tVar 0)))).
  - rewrite <- (rawQuotedTermCode_standard M hPA tZero).
    rewrite <- (rawTemplateTerm_embedPA
      (rawDirectStructuralTemplatePAAgreement M hPA inputs) tZero).
    unfold
      rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixDirectCode,
      rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixZeroDirectCode,
      coqRestrictedPADerivationSoundnessCarrierStrongPrefixZeroTemplate.
    exact (rawDirectTemplateFormula_open M hPA inputs
      coqRestrictedPADerivationSoundnessCarrierStrongPrefixTemplate
      (embedPATerm tZero)).
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - exact hbound.
  - exact hclosure.
  - exact hself.
Qed.

(** ------------------------------------------------------------------
    Generic induction and final packaging over the direct codes. *)

(** Once callers provide the ordinary zero and successor roots, the generic
    closure-induction compiler proves [forall d, K(d)].  This theorem does
    no truth-specific work and therefore needs no decoded opaque formula. *)
Theorem
    raw_codedPAProofOf_coqRestrictedPADerivationSoundnessStrongPrefixAllDirect_of_cases
    : forall (M : RawPAModel), RawPASatisfies M -> forall
      (inputs : RawCodedTemplateDirectStructuralInputs M)
      replacement axiom closureCount baseWitnessList baseContext
      zeroChild stepChild,
  RawCodedPAAxiomWitnessContext M baseWitnessList baseContext ->
  RawCoqRestrictedPADerivationSoundnessStrongPrefixDirectClosureRemainder
    M inputs replacement axiom closureCount ->
  RawCodedPALocalProofOf M
    (rawPAInductionExtendedContext M baseContext axiom)
    (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixZeroDirectCode
      M inputs)
    zeroChild ->
  RawCodedPALocalProofOf M
    (rawPAInductionExtendedContext M baseContext axiom)
    (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixStepAllDirectCode
      M inputs)
    stepChild ->
  exists bodyChild : M,
    RawCodedPAProofOf M
      (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixAllDirectCode
        M inputs)
      (rawPAClosureInductionCertificate M
        baseWitnessList baseContext
        (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixDirectCode
          M inputs)
        axiom
        (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixPremiseDirectCode
          M inputs)
        (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixAllDirectCode
          M inputs)
        (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixZeroDirectCode
          M inputs)
        (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixStepAllDirectCode
          M inputs)
        bodyChild zeroChild stepChild).
Proof.
  intros M hPA inputs replacement axiom closureCount
    baseWitnessList baseContext zeroChild stepChild
    hbase hremainder hzero hstep.
  exact (raw_codedPAProofOf_closure_induction M hPA
    baseWitnessList baseContext replacement
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
    closureCount zeroChild stepChild hbase
    (raw_coqRestrictedPADerivationSoundnessCarrierStrongPrefixDirectClosureInductionData
      M hPA inputs replacement axiom closureCount hremainder)
    hzero hstep).
Qed.

(** The last implication-elimination root and its ordinary PA certificate
    remain transparent so audits can inspect every context and child. *)
Definition
    rawCoqRestrictedPADerivationSoundnessStrongPrefixDirectFinalizedRoot
    (M : RawPAModel) (inputs : RawCodedTemplateDirectStructuralInputs M)
    (baseContext axiom bodyChild zeroChild stepChild finalizerChild : M) : M :=
  rawProofImpERoot M
    (rawPAInductionExtendedContext M baseContext axiom)
    (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixAllDirectCode
      M inputs)
    (rawCoqRestrictedPADerivationSoundnessUniversalDirectCode M inputs)
    finalizerChild
    (rawPAClosureInductionProofRoot M
      baseContext axiom
      (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixPremiseDirectCode
        M inputs)
      (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixAllDirectCode
        M inputs)
      (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixZeroDirectCode
        M inputs)
      (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixStepAllDirectCode
        M inputs)
      bodyChild zeroChild stepChild).

Definition
    rawCoqRestrictedPADerivationSoundnessStrongPrefixDirectFinalizedCertificate
    (M : RawPAModel) (inputs : RawCodedTemplateDirectStructuralInputs M)
    (baseWitnessList baseContext axiom bodyChild zeroChild stepChild
      finalizerChild : M) : M :=
  rawCodeList3 M (rawNumeralValue M 0)
    (rawPAInductionExtendedWitnessList M baseWitnessList
      (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixDirectCode
        M inputs))
    (rawCoqRestrictedPADerivationSoundnessStrongPrefixDirectFinalizedRoot
      M inputs baseContext axiom bodyChild zeroChild stepChild
      finalizerChild).

Arguments
  rawCoqRestrictedPADerivationSoundnessStrongPrefixDirectFinalizedRoot
  M inputs baseContext axiom bodyChild zeroChild stepChild finalizerChild
  : clear implicits.
Arguments
  rawCoqRestrictedPADerivationSoundnessStrongPrefixDirectFinalizedCertificate
  M inputs baseWitnessList baseContext axiom bodyChild zeroChild stepChild
    finalizerChild : clear implicits.

(** Exact direct analogue of the old structural endpoint.  Its hypotheses
    are only the three roots actually consumed by the generic induction and
    implication-elimination compilers. *)
Theorem
    raw_codedPAProofOf_coqRestrictedPADerivationSoundnessUniversalDirect_of_strongPrefix_cases_and_finalizer
    : forall (M : RawPAModel), RawPASatisfies M -> forall
      (inputs : RawCodedTemplateDirectStructuralInputs M)
      replacement axiom closureCount baseWitnessList baseContext
      zeroChild stepChild finalizerChild,
  RawCodedPAAxiomWitnessContext M baseWitnessList baseContext ->
  RawCoqRestrictedPADerivationSoundnessStrongPrefixDirectClosureRemainder
    M inputs replacement axiom closureCount ->
  RawCodedPALocalProofOf M
    (rawPAInductionExtendedContext M baseContext axiom)
    (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixZeroDirectCode
      M inputs)
    zeroChild ->
  RawCodedPALocalProofOf M
    (rawPAInductionExtendedContext M baseContext axiom)
    (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixStepAllDirectCode
      M inputs)
    stepChild ->
  RawCodedPALocalProofOf M
    (rawPAInductionExtendedContext M baseContext axiom)
    (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixFinalizerDirectCode
      M inputs)
    finalizerChild ->
  exists bodyChild : M,
    RawCodedPAProofOf M
      (rawCoqRestrictedPADerivationSoundnessUniversalDirectCode M inputs)
      (rawCoqRestrictedPADerivationSoundnessStrongPrefixDirectFinalizedCertificate
        M inputs baseWitnessList baseContext axiom bodyChild
        zeroChild stepChild finalizerChild).
Proof.
  intros M hPA inputs replacement axiom closureCount
    baseWitnessList baseContext zeroChild stepChild finalizerChild
    hbase hremainder hzero hstep hfinalizer.
  pose proof
    (raw_coqRestrictedPADerivationSoundnessCarrierStrongPrefixDirectClosureInductionData
      M hPA inputs replacement axiom closureCount hremainder) as hdata.
  destruct (raw_codedPALocalProofOf_closure_induction M hPA
    baseWitnessList baseContext replacement
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
    closureCount zeroChild stepChild hbase hdata hzero hstep)
    as [bodyChild hprefixAll].
  assert (hfinalized : RawCodedPALocalProofOf M
      (rawPAInductionExtendedContext M baseContext axiom)
      (rawCoqRestrictedPADerivationSoundnessUniversalDirectCode M inputs)
      (rawCoqRestrictedPADerivationSoundnessStrongPrefixDirectFinalizedRoot
        M inputs baseContext axiom bodyChild zeroChild stepChild
        finalizerChild)).
  {
    unfold
      rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixFinalizerDirectCode,
      rawCoqRestrictedPADerivationSoundnessStrongPrefixDirectFinalizedRoot.
    exact (raw_codedPALocalProofOf_impE M hPA
      (rawPAInductionExtendedContext M baseContext axiom)
      (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixAllDirectCode
        M inputs)
      (rawCoqRestrictedPADerivationSoundnessUniversalDirectCode M inputs)
      finalizerChild
      (rawPAClosureInductionProofRoot M
        baseContext axiom
        (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixPremiseDirectCode
          M inputs)
        (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixAllDirectCode
          M inputs)
        (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixZeroDirectCode
          M inputs)
        (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixStepAllDirectCode
          M inputs)
        bodyChild zeroChild stepChild)
      hfinalizer hprefixAll).
  }
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
  exists bodyChild.
  exists
    (rawPAInductionExtendedWitnessList M baseWitnessList
      (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixDirectCode
        M inputs)),
    (rawCoqRestrictedPADerivationSoundnessStrongPrefixDirectFinalizedRoot
      M inputs baseContext axiom bodyChild zeroChild stepChild
      finalizerChild),
    (rawPAInductionExtendedContext M baseContext axiom).
  split.
  - unfold
      rawCoqRestrictedPADerivationSoundnessStrongPrefixDirectFinalizedCertificate.
    reflexivity.
  - split.
    + exact (raw_codedPAAxiomWitnessContext_add_induction M hPA
        baseWitnessList baseContext
        (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixDirectCode
          M inputs)
        axiom hbase hinduction).
    + exact hfinalized.
Qed.

End
  PABoundedRawCodedRestrictedPADerivationSoundnessCarrierStrongPrefixDirectInductionShell.
