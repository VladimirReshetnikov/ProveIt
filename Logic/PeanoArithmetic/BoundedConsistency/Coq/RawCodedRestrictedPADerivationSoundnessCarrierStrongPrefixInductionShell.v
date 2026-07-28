(**
  Arbitrary-carrier strong-prefix induction for derivation soundness.

  The bridge predicate

      P(d) := coqRestrictedPADerivationSoundnessPredicateTemplate(d)

  is the exact finite template used by the nonstandard consistency bridge.
  Recursive proof soundness does not supply [P(d) -> P(S d)].  Its natural
  induction hypothesis is instead the strict prefix

      K(d) := forall e, e < d -> P(e),

  and its constructor-local step has the shape [K(d) -> P(d)].  Ordinary PA
  induction is therefore applied to [K], never directly to [P].

  This module performs all deterministic finite-template work for that
  induction: it represents [K], its zero and successor instances, its
  ordinary induction step, and its universal closure; it also assembles the
  generic induction certificate from supplied zero and successor proof
  roots.  Formula-bound discovery, nonstandard universal closure, and its
  bounded self-instantiation orbit remain one explicit closure remainder.

  Two mathematical proof compilers remain deliberately open:

  - the case compiler must turn the genuine strong step [K(d) -> P(d)] and
    the arithmetic split [e < S d] into the ordinary step
    [K(d) -> K(S d)], as well as prove the vacuous zero case;
  - the finalizer must derive [forall d, P(d)] from [forall d, K(d)], using
    [d < S d] and the instance [K(S d)].

  Both are named local-root interfaces below.  No implication
  [P(d) -> P(S d)] is assumed or manufactured.
*)

From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors
  RawCodedFormulaOperations
  RawCodedFormulaShiftTreeRealization
  RawCodedPAAxiomWitness
  RawCodedRestrictedPAProof
  RawCodedPAProvability
  RawCodedProofBinaryConstructors
  RawCodedPALocalProofExistential
  RawCodedPALocalProofComposition
  RawCodedTemplateSyntax
  RawCodedTemplateStructuralTranslation
  RawCodedTemplateStructuralPAAgreement
  RawCodedPAInductionAxiomCertificate
  RawCodedPAUniversalClosureProofReduction
  RawCodedPAClosureInductionCompiler
  RawCodedRestrictedPAConsistencyFromUniversalSoundness.

Module
  PABoundedRawCodedRestrictedPADerivationSoundnessCarrierStrongPrefixInductionShell.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedFormulaShiftTreeRealization.
Import PABoundedRawCodedPAAxiomWitness.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedPAProvability.
Import PABoundedRawCodedProofBinaryConstructors.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPALocalProofComposition.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateStructuralTranslation.
Import PABoundedRawCodedTemplateStructuralPAAgreement.
Import PABoundedRawCodedPAInductionAxiomCertificate.
Import PABoundedRawCodedPAUniversalClosureProofReduction.
Import PABoundedRawCodedPAClosureInductionCompiler.
Import PABoundedRawCodedRestrictedPAConsistencyFromUniversalSoundness.

(** The structural translation already contains a valid shift tree at every
    finite external depth.  Induction shifts free variables above the
    induction variable, hence uses depth one rather than the public
    depth-zero specialization. *)
Theorem raw_coqCarrierStrongPrefix_templateFormula_shiftAt : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    (inputs : RawCodedTemplateStructuralInputs M) depth formula,
  RawCodedFormulaShift M
    (rawNumeralValue M depth) (rawNumeralValue M 1)
    (rawStructuralTemplateFormula inputs formula)
    (rawStructuralTemplateFormula inputs
      (templateFormulaRename
        (templateShiftRenamingAt depth) formula)).
Proof.
  intros M hPA inputs depth formula.
  pose proof (raw_codedFormulaShift_of_valid_tree M hPA
    (rawNumeralValue M 1)
    (rawStructuralTemplateShiftTree inputs depth formula)
    (rawStructuralTemplateShiftTree_valid
      M inputs depth formula)) as hshift.
  rewrite rawStructuralTemplateShiftTree_depth in hshift.
  rewrite rawStructuralTemplateShiftTree_source in hshift.
  rewrite rawStructuralTemplateShiftTree_target in hshift.
  exact hshift.
Qed.

(** ------------------------------------------------------------------
    Exact finite templates [P], [K], and the genuine recursive step. *)

Definition coqRestrictedPADerivationSoundnessCarrierPredicateTemplate
    : TemplateFormula :=
  coqRestrictedPADerivationSoundnessPredicateTemplate.

(** Inside the new universal binder, [#0] is [e] and [#1] is the free
    induction variable [d].  The predicate template is inserted unchanged:
    its free root variable is intentionally captured by the [e] binder. *)
Definition coqRestrictedPADerivationSoundnessCarrierStrongPrefixTemplate
    : TemplateFormula :=
  tfAll
    (tfImp
      (embedPAFormula
        (Formula.ltTermAt (tVar 0) (tVar 1)))
      coqRestrictedPADerivationSoundnessCarrierPredicateTemplate).

Definition coqRestrictedPADerivationSoundnessCarrierStrongStepTemplate
    : TemplateFormula :=
  tfAll
    (tfImp
      coqRestrictedPADerivationSoundnessCarrierStrongPrefixTemplate
      coqRestrictedPADerivationSoundnessCarrierPredicateTemplate).

Definition coqRestrictedPADerivationSoundnessCarrierStrongPrefixAllTemplate
    : TemplateFormula :=
  tfAll coqRestrictedPADerivationSoundnessCarrierStrongPrefixTemplate.

Definition coqRestrictedPADerivationSoundnessCarrierStrongPrefixFinalizerTemplate
    : TemplateFormula :=
  tfImp
    coqRestrictedPADerivationSoundnessCarrierStrongPrefixAllTemplate
    coqRestrictedPADerivationSoundnessUniversalTemplate.

(** ------------------------------------------------------------------
    Ordinary-induction templates for [K]. *)

Definition coqRestrictedPADerivationSoundnessCarrierStrongPrefixShiftedTemplate
    : TemplateFormula :=
  templateFormulaRename (templateShiftRenamingAt 1)
    coqRestrictedPADerivationSoundnessCarrierStrongPrefixTemplate.

Definition
    coqRestrictedPADerivationSoundnessCarrierStrongPrefixSuccessorTemplate
    : TemplateFormula :=
  templateFormulaOpen (embedPATerm (tSucc (tVar 0)))
    coqRestrictedPADerivationSoundnessCarrierStrongPrefixShiftedTemplate.

Definition coqRestrictedPADerivationSoundnessCarrierStrongPrefixZeroTemplate
    : TemplateFormula :=
  templateFormulaOpen (embedPATerm tZero)
    coqRestrictedPADerivationSoundnessCarrierStrongPrefixTemplate.

(** ------------------------------------------------------------------
    Exact raw carrier codes. *)

Definition rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixCode
    (M : RawPAModel) (inputs : RawCodedTemplateStructuralInputs M) : M :=
  rawStructuralTemplateFormula inputs
    coqRestrictedPADerivationSoundnessCarrierStrongPrefixTemplate.

Definition rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixShiftedCode
    (M : RawPAModel) (inputs : RawCodedTemplateStructuralInputs M) : M :=
  rawStructuralTemplateFormula inputs
    coqRestrictedPADerivationSoundnessCarrierStrongPrefixShiftedTemplate.

Definition
    rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixSuccessorCode
    (M : RawPAModel) (inputs : RawCodedTemplateStructuralInputs M) : M :=
  rawStructuralTemplateFormula inputs
    coqRestrictedPADerivationSoundnessCarrierStrongPrefixSuccessorTemplate.

Definition rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixZeroCode
    (M : RawPAModel) (inputs : RawCodedTemplateStructuralInputs M) : M :=
  rawStructuralTemplateFormula inputs
    coqRestrictedPADerivationSoundnessCarrierStrongPrefixZeroTemplate.

Definition rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixAllCode
    (M : RawPAModel) (inputs : RawCodedTemplateStructuralInputs M) : M :=
  rawFormulaAllCode M
    (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixCode M inputs).

Definition rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixStepImpCode
    (M : RawPAModel) (inputs : RawCodedTemplateStructuralInputs M) : M :=
  rawFormulaImpCode M
    (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixCode M inputs)
    (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixSuccessorCode
      M inputs).

Definition rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixStepAllCode
    (M : RawPAModel) (inputs : RawCodedTemplateStructuralInputs M) : M :=
  rawFormulaAllCode M
    (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixStepImpCode
      M inputs).

Definition rawCoqRestrictedPADerivationSoundnessCarrierStrongStepCode
    (M : RawPAModel) (inputs : RawCodedTemplateStructuralInputs M) : M :=
  rawFormulaAllCode M
    (rawFormulaImpCode M
      (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixCode M inputs)
      (rawCoqRestrictedPADerivationSoundnessPredicateCode M inputs)).

Definition rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixPremiseCode
    (M : RawPAModel) (inputs : RawCodedTemplateStructuralInputs M) : M :=
  rawFormulaAndCode M
    (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixZeroCode
      M inputs)
    (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixStepAllCode
      M inputs).

Definition rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixBodyCode
    (M : RawPAModel) (inputs : RawCodedTemplateStructuralInputs M) : M :=
  rawFormulaImpCode M
    (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixPremiseCode
      M inputs)
    (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixAllCode
      M inputs).

Definition rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixFinalizerCode
    (M : RawPAModel) (inputs : RawCodedTemplateStructuralInputs M) : M :=
  rawFormulaImpCode M
    (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixAllCode M inputs)
    (rawCoqRestrictedPADerivationSoundnessUniversalCode M inputs).

Arguments rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixCode
  M inputs : clear implicits.
Arguments rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixShiftedCode
  M inputs : clear implicits.
Arguments
  rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixSuccessorCode
  M inputs : clear implicits.
Arguments rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixZeroCode
  M inputs : clear implicits.
Arguments rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixAllCode
  M inputs : clear implicits.
Arguments rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixStepImpCode
  M inputs : clear implicits.
Arguments rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixStepAllCode
  M inputs : clear implicits.
Arguments rawCoqRestrictedPADerivationSoundnessCarrierStrongStepCode
  M inputs : clear implicits.
Arguments rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixPremiseCode
  M inputs : clear implicits.
Arguments rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixBodyCode
  M inputs : clear implicits.
Arguments rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixFinalizerCode
  M inputs : clear implicits.

(** The raw codes above are the literal translations of the advertised
    strong-step and finalizer templates.  These equations are syntax views,
    not proof-producing claims. *)
Lemma raw_coqRestrictedPADerivationSoundnessCarrierStrongStepCode_structural :
    forall (M : RawPAModel)
      (inputs : RawCodedTemplateStructuralInputs M),
  rawCoqRestrictedPADerivationSoundnessCarrierStrongStepCode M inputs =
  rawStructuralTemplateFormula inputs
    coqRestrictedPADerivationSoundnessCarrierStrongStepTemplate.
Proof.
  intros M inputs.
  unfold rawCoqRestrictedPADerivationSoundnessCarrierStrongStepCode,
    coqRestrictedPADerivationSoundnessCarrierStrongStepTemplate.
  rewrite rawStructuralTemplateFormula_all_code.
  rewrite rawStructuralTemplateFormula_imp_code.
  rewrite <- raw_coqRestrictedPADerivationSoundnessPredicateCode_structural.
  reflexivity.
Qed.

Lemma
    raw_coqRestrictedPADerivationSoundnessCarrierStrongPrefixFinalizerCode_structural
    : forall (M : RawPAModel)
      (inputs : RawCodedTemplateStructuralInputs M),
  rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixFinalizerCode
    M inputs =
  rawStructuralTemplateFormula inputs
    coqRestrictedPADerivationSoundnessCarrierStrongPrefixFinalizerTemplate.
Proof.
  intros M inputs.
  unfold rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixFinalizerCode,
    coqRestrictedPADerivationSoundnessCarrierStrongPrefixFinalizerTemplate,
    coqRestrictedPADerivationSoundnessCarrierStrongPrefixAllTemplate.
  rewrite rawStructuralTemplateFormula_imp_code.
  rewrite rawStructuralTemplateFormula_all_code.
  rewrite <- raw_coqRestrictedPADerivationSoundnessUniversalCode_structural.
  reflexivity.
Qed.

(** ------------------------------------------------------------------
    Honest nonstandard closure boundary. *)

Definition RawCoqRestrictedPADerivationSoundnessStrongPrefixClosureRemainder
    (M : RawPAModel) (inputs : RawCodedTemplateStructuralInputs M)
    (replacement axiom closureCount : M) : Prop :=
  RawCodedFormulaBound M
    (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixBodyCode
      M inputs)
    closureCount /\
  RawCodedUniversalClosure M closureCount
    (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixBodyCode
      M inputs)
    axiom /\
  RawCodedUniversalClosureSelfInstantiationThrough M replacement
    (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixBodyCode
      M inputs)
    closureCount.

Arguments
  RawCoqRestrictedPADerivationSoundnessStrongPrefixClosureRemainder
  M inputs replacement axiom closureCount : clear implicits.

(** All finite fields of the generic closure-induction graph are structural.
    Only the bound, arbitrary carrier-length closure, and its opening orbit
    are copied from the explicit remainder. *)
Theorem
    raw_coqRestrictedPADerivationSoundnessCarrierStrongPrefixClosureInductionData
    : forall (M : RawPAModel), RawPASatisfies M -> forall
    (inputs : RawCodedTemplateStructuralInputs M)
    replacement axiom closureCount,
  RawCoqRestrictedPADerivationSoundnessStrongPrefixClosureRemainder
    M inputs replacement axiom closureCount ->
  RawCodedPAClosureInductionData M replacement
    (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixCode M inputs)
    axiom
    (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixShiftedCode
      M inputs)
    (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixSuccessorCode
      M inputs)
    (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixZeroCode
      M inputs)
    (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixAllCode
      M inputs)
    (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixStepImpCode
      M inputs)
    (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixStepAllCode
      M inputs)
    (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixPremiseCode
      M inputs)
    (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixBodyCode
      M inputs)
    closureCount.
Proof.
  intros M hPA inputs replacement axiom closureCount
    [hbound [hclosure hself]].
  unfold RawCodedPAClosureInductionData.
  repeat apply conj.
  - unfold rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixCode,
      rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixShiftedCode,
      coqRestrictedPADerivationSoundnessCarrierStrongPrefixShiftedTemplate.
    exact (raw_coqCarrierStrongPrefix_templateFormula_shiftAt
      M hPA inputs 1
      coqRestrictedPADerivationSoundnessCarrierStrongPrefixTemplate).
  - rewrite <- (rawQuotedTermCode_standard M hPA
      (tSucc (tVar 0))).
    rewrite <- (rawStructuralTemplateTerm_embedPA M inputs
      (tSucc (tVar 0))).
    unfold
      rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixShiftedCode,
      rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixSuccessorCode,
      coqRestrictedPADerivationSoundnessCarrierStrongPrefixSuccessorTemplate.
    exact (rawStructuralTemplateFormula_open M hPA inputs
      coqRestrictedPADerivationSoundnessCarrierStrongPrefixShiftedTemplate
      (embedPATerm (tSucc (tVar 0)))).
  - rewrite <- (rawQuotedTermCode_standard M hPA tZero).
    rewrite <- (rawStructuralTemplateTerm_embedPA M inputs tZero).
    unfold rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixCode,
      rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixZeroCode,
      coqRestrictedPADerivationSoundnessCarrierStrongPrefixZeroTemplate.
    exact (rawStructuralTemplateFormula_open M hPA inputs
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
    Ordinary PA induction certificate for [forall d, K(d)]. *)

Theorem
    raw_codedPAProofOf_coqRestrictedPADerivationSoundnessStrongPrefixAll_of_cases
    : forall (M : RawPAModel), RawPASatisfies M -> forall
    (inputs : RawCodedTemplateStructuralInputs M)
    replacement axiom closureCount baseWitnessList baseContext
    zeroChild stepChild,
  RawCodedPAAxiomWitnessContext M baseWitnessList baseContext ->
  RawCoqRestrictedPADerivationSoundnessStrongPrefixClosureRemainder
    M inputs replacement axiom closureCount ->
  RawCodedPALocalProofOf M
    (rawPAInductionExtendedContext M baseContext axiom)
    (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixZeroCode
      M inputs)
    zeroChild ->
  RawCodedPALocalProofOf M
    (rawPAInductionExtendedContext M baseContext axiom)
    (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixStepAllCode
      M inputs)
    stepChild ->
  exists bodyChild : M,
    RawCodedPAProofOf M
      (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixAllCode
        M inputs)
      (rawPAClosureInductionCertificate M
        baseWitnessList baseContext
        (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixCode
          M inputs)
        axiom
        (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixPremiseCode
          M inputs)
        (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixAllCode
          M inputs)
        (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixZeroCode
          M inputs)
        (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixStepAllCode
          M inputs)
        bodyChild zeroChild stepChild).
Proof.
  intros M hPA inputs replacement axiom closureCount
    baseWitnessList baseContext zeroChild stepChild
    hbase hremainder hzero hstep.
  exact (raw_codedPAProofOf_closure_induction M hPA
    baseWitnessList baseContext replacement
    (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixCode M inputs)
    axiom
    (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixShiftedCode
      M inputs)
    (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixSuccessorCode
      M inputs)
    (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixZeroCode
      M inputs)
    (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixAllCode
      M inputs)
    (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixStepImpCode
      M inputs)
    (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixStepAllCode
      M inputs)
    (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixPremiseCode
      M inputs)
    (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixBodyCode
      M inputs)
    closureCount zeroChild stepChild hbase
    (raw_coqRestrictedPADerivationSoundnessCarrierStrongPrefixClosureInductionData
      M hPA inputs replacement axiom closureCount hremainder)
    hzero hstep).
Qed.

(** ------------------------------------------------------------------
    Explicit case and finalizer boundaries. *)

(** A future case compiler must consume the correct recursive strong-step
    root.  Its result is the vacuous [K(0)] proof and the ordinary induction
    step [forall d, K(d) -> K(S d)].  This definition asserts no inhabitant. *)
Definition
    RawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixCaseRootCompiler
    (M : RawPAModel) (inputs : RawCodedTemplateStructuralInputs M) : Prop :=
  forall replacement axiom closureCount baseWitnessList baseContext
      strongStepRoot,
    RawCodedPAAxiomWitnessContext M baseWitnessList baseContext ->
    RawCoqRestrictedPADerivationSoundnessStrongPrefixClosureRemainder
      M inputs replacement axiom closureCount ->
    RawCodedPALocalProofOf M
      (rawPAInductionExtendedContext M baseContext axiom)
      (rawCoqRestrictedPADerivationSoundnessCarrierStrongStepCode M inputs)
      strongStepRoot ->
    exists zeroChild stepChild : M,
      RawCodedPALocalProofOf M
        (rawPAInductionExtendedContext M baseContext axiom)
        (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixZeroCode
          M inputs)
        zeroChild /\
      RawCodedPALocalProofOf M
        (rawPAInductionExtendedContext M baseContext axiom)
        (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixStepAllCode
          M inputs)
        stepChild.

Arguments
  RawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixCaseRootCompiler
  M inputs : clear implicits.

(** The exact remaining [forall K -> forall P] proof compiler.  Existing
    universal-elimination and arithmetic libraries suggest how to implement
    it—instantiate [K] at [S d], then use [d < S d]—but no current API
    combines those operations under an arbitrary shifted local context.
    Keeping the local root explicit is strictly weaker and honest. *)
Definition
    RawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixFinalizerRootCompiler
    (M : RawPAModel) (inputs : RawCodedTemplateStructuralInputs M) : Prop :=
  forall replacement axiom closureCount baseWitnessList baseContext,
    RawCodedPAAxiomWitnessContext M baseWitnessList baseContext ->
    RawCoqRestrictedPADerivationSoundnessStrongPrefixClosureRemainder
      M inputs replacement axiom closureCount ->
    exists finalizerChild : M,
      RawCodedPALocalProofOf M
        (rawPAInductionExtendedContext M baseContext axiom)
        (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixFinalizerCode
          M inputs)
        finalizerChild.

Arguments
  RawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixFinalizerRootCompiler
  M inputs : clear implicits.

(** ------------------------------------------------------------------
    Conditional exact finalization to [forall d, P(d)]. *)

Definition rawCoqRestrictedPADerivationSoundnessStrongPrefixFinalizedRoot
    (M : RawPAModel) (inputs : RawCodedTemplateStructuralInputs M)
    (baseContext axiom bodyChild zeroChild stepChild finalizerChild : M) : M :=
  rawProofImpERoot M
    (rawPAInductionExtendedContext M baseContext axiom)
    (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixAllCode M inputs)
    (rawCoqRestrictedPADerivationSoundnessUniversalCode M inputs)
    finalizerChild
    (rawPAClosureInductionProofRoot M
      baseContext axiom
      (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixPremiseCode
        M inputs)
      (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixAllCode
        M inputs)
      (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixZeroCode
        M inputs)
      (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixStepAllCode
        M inputs)
      bodyChild zeroChild stepChild).

Definition
    rawCoqRestrictedPADerivationSoundnessStrongPrefixFinalizedCertificate
    (M : RawPAModel) (inputs : RawCodedTemplateStructuralInputs M)
    (baseWitnessList baseContext axiom bodyChild zeroChild stepChild
      finalizerChild : M) : M :=
  rawCodeList3 M (rawNumeralValue M 0)
    (rawPAInductionExtendedWitnessList M baseWitnessList
      (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixCode M inputs))
    (rawCoqRestrictedPADerivationSoundnessStrongPrefixFinalizedRoot
      M inputs baseContext axiom bodyChild zeroChild stepChild
      finalizerChild).

Arguments rawCoqRestrictedPADerivationSoundnessStrongPrefixFinalizedRoot
  M inputs baseContext axiom bodyChild zeroChild stepChild finalizerChild
  : clear implicits.
Arguments
  rawCoqRestrictedPADerivationSoundnessStrongPrefixFinalizedCertificate
  M inputs baseWitnessList baseContext axiom bodyChild zeroChild stepChild
    finalizerChild : clear implicits.

Theorem
    raw_codedPAProofOf_coqRestrictedPADerivationSoundnessUniversal_of_strongPrefix_cases_and_finalizer
    : forall (M : RawPAModel), RawPASatisfies M -> forall
    (inputs : RawCodedTemplateStructuralInputs M)
    replacement axiom closureCount baseWitnessList baseContext
    zeroChild stepChild finalizerChild,
  RawCodedPAAxiomWitnessContext M baseWitnessList baseContext ->
  RawCoqRestrictedPADerivationSoundnessStrongPrefixClosureRemainder
    M inputs replacement axiom closureCount ->
  RawCodedPALocalProofOf M
    (rawPAInductionExtendedContext M baseContext axiom)
    (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixZeroCode
      M inputs)
    zeroChild ->
  RawCodedPALocalProofOf M
    (rawPAInductionExtendedContext M baseContext axiom)
    (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixStepAllCode
      M inputs)
    stepChild ->
  RawCodedPALocalProofOf M
    (rawPAInductionExtendedContext M baseContext axiom)
    (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixFinalizerCode
      M inputs)
    finalizerChild ->
  exists bodyChild : M,
    RawCodedPAProofOf M
      (rawCoqRestrictedPADerivationSoundnessUniversalCode M inputs)
      (rawCoqRestrictedPADerivationSoundnessStrongPrefixFinalizedCertificate
        M inputs baseWitnessList baseContext axiom bodyChild
        zeroChild stepChild finalizerChild).
Proof.
  intros M hPA inputs replacement axiom closureCount
    baseWitnessList baseContext zeroChild stepChild finalizerChild
    hbase hremainder hzero hstep hfinalizer.
  pose proof
    (raw_coqRestrictedPADerivationSoundnessCarrierStrongPrefixClosureInductionData
      M hPA inputs replacement axiom closureCount hremainder) as hdata.
  destruct (raw_codedPALocalProofOf_closure_induction M hPA
    baseWitnessList baseContext replacement
    (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixCode M inputs)
    axiom
    (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixShiftedCode
      M inputs)
    (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixSuccessorCode
      M inputs)
    (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixZeroCode
      M inputs)
    (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixAllCode
      M inputs)
    (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixStepImpCode
      M inputs)
    (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixStepAllCode
      M inputs)
    (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixPremiseCode
      M inputs)
    (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixBodyCode
      M inputs)
    closureCount zeroChild stepChild hbase hdata hzero hstep)
    as [bodyChild hprefixAll].
  assert (hfinalized : RawCodedPALocalProofOf M
      (rawPAInductionExtendedContext M baseContext axiom)
      (rawCoqRestrictedPADerivationSoundnessUniversalCode M inputs)
      (rawCoqRestrictedPADerivationSoundnessStrongPrefixFinalizedRoot
        M inputs baseContext axiom bodyChild zeroChild stepChild
        finalizerChild)).
  {
    unfold
      rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixFinalizerCode,
      rawCoqRestrictedPADerivationSoundnessStrongPrefixFinalizedRoot.
    exact (raw_codedPALocalProofOf_impE M hPA
      (rawPAInductionExtendedContext M baseContext axiom)
      (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixAllCode
        M inputs)
      (rawCoqRestrictedPADerivationSoundnessUniversalCode M inputs)
      finalizerChild
      (rawPAClosureInductionProofRoot M
        baseContext axiom
        (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixPremiseCode
          M inputs)
        (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixAllCode
          M inputs)
        (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixZeroCode
          M inputs)
        (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixStepAllCode
          M inputs)
        bodyChild zeroChild stepChild)
      hfinalizer hprefixAll).
  }
  pose proof (raw_codedPAClosureInductionData_axiom M
    replacement
    (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixCode M inputs)
    axiom
    (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixShiftedCode
      M inputs)
    (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixSuccessorCode
      M inputs)
    (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixZeroCode
      M inputs)
    (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixAllCode
      M inputs)
    (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixStepImpCode
      M inputs)
    (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixStepAllCode
      M inputs)
    (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixPremiseCode
      M inputs)
    (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixBodyCode
      M inputs)
    closureCount hdata) as hinduction.
  exists bodyChild.
  exists
    (rawPAInductionExtendedWitnessList M baseWitnessList
      (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixCode M inputs)),
    (rawCoqRestrictedPADerivationSoundnessStrongPrefixFinalizedRoot
      M inputs baseContext axiom bodyChild zeroChild stepChild
      finalizerChild),
    (rawPAInductionExtendedContext M baseContext axiom).
  split.
  - unfold
      rawCoqRestrictedPADerivationSoundnessStrongPrefixFinalizedCertificate.
    reflexivity.
  - split.
    + exact (raw_codedPAAxiomWitnessContext_add_induction M hPA
        baseWitnessList baseContext
        (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixCode
          M inputs)
        axiom hbase hinduction).
    + exact hfinalized.
Qed.

(** If future modules implement the two named compilers, this endpoint
    packages their roots without adding another proof-theoretic premise. *)
Theorem
    raw_codedPAProofOf_coqRestrictedPADerivationSoundnessUniversal_of_strongPrefix_compilers
    : forall (M : RawPAModel), RawPASatisfies M -> forall
    (inputs : RawCodedTemplateStructuralInputs M),
  RawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixCaseRootCompiler
    M inputs ->
  RawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixFinalizerRootCompiler
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
    exists zeroChild stepChild finalizerChild bodyChild : M,
      RawCodedPAProofOf M
        (rawCoqRestrictedPADerivationSoundnessUniversalCode M inputs)
        (rawCoqRestrictedPADerivationSoundnessStrongPrefixFinalizedCertificate
          M inputs baseWitnessList baseContext axiom bodyChild
          zeroChild stepChild finalizerChild).
Proof.
  intros M hPA inputs hcases hfinalizer
    replacement axiom closureCount baseWitnessList baseContext
    strongStepRoot hbase hremainder hstrongStep.
  destruct (hcases replacement axiom closureCount
    baseWitnessList baseContext strongStepRoot
    hbase hremainder hstrongStep) as
    (zeroChild & stepChild & hzero & hstep).
  destruct (hfinalizer replacement axiom closureCount
    baseWitnessList baseContext hbase hremainder) as
    [finalizerChild hfinalizerRoot].
  destruct
    (raw_codedPAProofOf_coqRestrictedPADerivationSoundnessUniversal_of_strongPrefix_cases_and_finalizer
      M hPA inputs replacement axiom closureCount
      baseWitnessList baseContext zeroChild stepChild finalizerChild
      hbase hremainder hzero hstep hfinalizerRoot) as
    [bodyChild hproof].
  exists zeroChild, stepChild, finalizerChild, bodyChild.
  exact hproof.
Qed.

End
  PABoundedRawCodedRestrictedPADerivationSoundnessCarrierStrongPrefixInductionShell.
