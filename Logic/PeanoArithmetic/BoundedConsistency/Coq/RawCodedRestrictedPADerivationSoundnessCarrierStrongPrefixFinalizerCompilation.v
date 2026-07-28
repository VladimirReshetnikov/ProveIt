(**
  Checked compilation of the strong-prefix finalizer.

  The strong-prefix induction shell leaves the implication

      (forall d, K(d)) -> forall d, P(d)

  as a named compiler boundary.  Its logical part is completely finite:
  under a fresh [d], instantiate the premise at [S d], instantiate the
  resulting prefix at [d], and apply the guarded conclusion to [d < S d].

  This file implements that exact proof tree with the raw All-E, Imp-E,
  All-I, and Imp-I constructors.  The sole remaining input is deliberately
  the exact arithmetic leaf [d < S d] in the shifted open context.  It is
  not replaced by semantic truth and the finalizer itself is never assumed.
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
  RawCodedContextShift
  RawCodedPAAxiomWitness
  RawCodedRestrictedPAProof
  RawCodedPAAxiomContextSelfShift
  RawCodedProofBinaryConstructors
  RawCodedProofAssumptionLeaf
  RawCodedProofImpIConstructor
  RawCodedProofAllEConstructor
  RawCodedProofAllIConstructor
  RawCodedPALocalProofExistential
  RawCodedPALocalProofComposition
  RawCodedPALocalProofPropositionalRules
  RawCodedPALocalProofUniversalElimination
  RawCodedPAProofImpICertificates
  RawCodedPAProvability
  RawCodedPAInductionAxiomCertificate
  RawCodedPAClosureInductionCompiler
  RawCodedTemplateSyntax
  RawCodedTemplateStructuralTranslation
  RawCodedTemplateStructuralPAAgreement
  RawCodedRestrictedPAConsistencyFromUniversalSoundness
  RawCodedRestrictedPADerivationSoundnessCarrierStrongPrefixInductionShell.

Module
  PABoundedRawCodedRestrictedPADerivationSoundnessCarrierStrongPrefixFinalizerCompilation.

Import ListNotations.
Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedContextLists.
Import PABoundedRawCodedContextShift.
Import PABoundedRawCodedPAAxiomWitness.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedPAAxiomContextSelfShift.
Import PABoundedRawCodedProofBinaryConstructors.
Import PABoundedRawCodedProofAssumptionLeaf.
Import PABoundedRawCodedProofImpIConstructor.
Import PABoundedRawCodedProofAllEConstructor.
Import PABoundedRawCodedProofAllIConstructor.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPALocalProofComposition.
Import PABoundedRawCodedPALocalProofPropositionalRules.
Import PABoundedRawCodedPALocalProofUniversalElimination.
Import PABoundedRawCodedPAProofImpICertificates.
Import PABoundedRawCodedPAProvability.
Import PABoundedRawCodedPAInductionAxiomCertificate.
Import PABoundedRawCodedPAClosureInductionCompiler.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateStructuralTranslation.
Import PABoundedRawCodedTemplateStructuralPAAgreement.
Import PABoundedRawCodedRestrictedPAConsistencyFromUniversalSoundness.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessCarrierStrongPrefixInductionShell.

(** ------------------------------------------------------------------
    The two concrete universal instances used by the finalizer. *)

Definition
    coqRestrictedPADerivationSoundnessCarrierFinalizerSuccessorPrefixTemplate
    : TemplateFormula :=
  templateFormulaOpen (embedPATerm (tSucc (tVar 0)))
    coqRestrictedPADerivationSoundnessCarrierStrongPrefixTemplate.

Definition
    coqRestrictedPADerivationSoundnessCarrierFinalizerSuccessorPrefixBodyTemplate
    : TemplateFormula :=
  tfImp
    (embedPAFormula
      (Formula.ltTermAt (tVar 0) (tSucc (tVar 1))))
    coqRestrictedPADerivationSoundnessCarrierPredicateTemplate.

Definition
    coqRestrictedPADerivationSoundnessCarrierFinalizerGuardedPredicateTemplate
    : TemplateFormula :=
  templateFormulaOpen (embedPATerm (tVar 0))
    coqRestrictedPADerivationSoundnessCarrierFinalizerSuccessorPrefixBodyTemplate.

Definition
    coqRestrictedPADerivationSoundnessCarrierFinalizerLtSelfSuccTemplate
    : TemplateFormula :=
  embedPAFormula
    (Formula.ltTermAt (tVar 0) (tSucc (tVar 0))).

Lemma
    coqRestrictedPADerivationSoundnessCarrierFinalizerSuccessorPrefixTemplate_shape
    :
  coqRestrictedPADerivationSoundnessCarrierFinalizerSuccessorPrefixTemplate =
  tfAll
    coqRestrictedPADerivationSoundnessCarrierFinalizerSuccessorPrefixBodyTemplate.
Proof.
  reflexivity.
Qed.

Lemma
    coqRestrictedPADerivationSoundnessCarrierFinalizerGuardedPredicateTemplate_shape
    :
  coqRestrictedPADerivationSoundnessCarrierFinalizerGuardedPredicateTemplate =
  tfImp
    coqRestrictedPADerivationSoundnessCarrierFinalizerLtSelfSuccTemplate
    coqRestrictedPADerivationSoundnessCarrierPredicateTemplate.
Proof.
  reflexivity.
Qed.

(** [forall d, K(d)] is closed.  Consequently the eigenvariable shift used
    by All-I leaves the freshly assumed premise literally unchanged.  This
    is a syntactic computation over the finite template, not a semantic
    closed-formula shortcut. *)
Lemma
    coqRestrictedPADerivationSoundnessCarrierStrongPrefixAllTemplate_shift_closed
    :
  templateFormulaRename (templateShiftRenamingAt 0)
    coqRestrictedPADerivationSoundnessCarrierStrongPrefixAllTemplate =
  coqRestrictedPADerivationSoundnessCarrierStrongPrefixAllTemplate.
Proof.
  reflexivity.
Qed.

(** ------------------------------------------------------------------
    Raw codes and their constructor views. *)

Definition
    rawCoqRestrictedPADerivationSoundnessCarrierFinalizerSuccessorTermCode
    (M : RawPAModel) (inputs : RawCodedTemplateStructuralInputs M) : M :=
  rawStructuralTemplateTerm inputs (embedPATerm (tSucc (tVar 0))).

Definition
    rawCoqRestrictedPADerivationSoundnessCarrierFinalizerVariableTermCode
    (M : RawPAModel) (inputs : RawCodedTemplateStructuralInputs M) : M :=
  rawStructuralTemplateTerm inputs (embedPATerm (tVar 0)).

Definition
    rawCoqRestrictedPADerivationSoundnessCarrierFinalizerSuccessorPrefixCode
    (M : RawPAModel) (inputs : RawCodedTemplateStructuralInputs M) : M :=
  rawStructuralTemplateFormula inputs
    coqRestrictedPADerivationSoundnessCarrierFinalizerSuccessorPrefixTemplate.

Definition
    rawCoqRestrictedPADerivationSoundnessCarrierFinalizerSuccessorPrefixBodyCode
    (M : RawPAModel) (inputs : RawCodedTemplateStructuralInputs M) : M :=
  rawStructuralTemplateFormula inputs
    coqRestrictedPADerivationSoundnessCarrierFinalizerSuccessorPrefixBodyTemplate.

Definition
    rawCoqRestrictedPADerivationSoundnessCarrierFinalizerGuardedPredicateCode
    (M : RawPAModel) (inputs : RawCodedTemplateStructuralInputs M) : M :=
  rawStructuralTemplateFormula inputs
    coqRestrictedPADerivationSoundnessCarrierFinalizerGuardedPredicateTemplate.

Definition
    rawCoqRestrictedPADerivationSoundnessCarrierFinalizerLtSelfSuccCode
    (M : RawPAModel) (inputs : RawCodedTemplateStructuralInputs M) : M :=
  rawStructuralTemplateFormula inputs
    coqRestrictedPADerivationSoundnessCarrierFinalizerLtSelfSuccTemplate.

Arguments
  rawCoqRestrictedPADerivationSoundnessCarrierFinalizerSuccessorTermCode
  M inputs : clear implicits.
Arguments
  rawCoqRestrictedPADerivationSoundnessCarrierFinalizerVariableTermCode
  M inputs : clear implicits.
Arguments
  rawCoqRestrictedPADerivationSoundnessCarrierFinalizerSuccessorPrefixCode
  M inputs : clear implicits.
Arguments
  rawCoqRestrictedPADerivationSoundnessCarrierFinalizerSuccessorPrefixBodyCode
  M inputs : clear implicits.
Arguments
  rawCoqRestrictedPADerivationSoundnessCarrierFinalizerGuardedPredicateCode
  M inputs : clear implicits.
Arguments
  rawCoqRestrictedPADerivationSoundnessCarrierFinalizerLtSelfSuccCode
  M inputs : clear implicits.

Lemma
    raw_coqRestrictedPADerivationSoundnessCarrierFinalizerLtSelfSuccCode_quoted
    : forall (M : RawPAModel)
      (inputs : RawCodedTemplateStructuralInputs M),
  rawCoqRestrictedPADerivationSoundnessCarrierFinalizerLtSelfSuccCode
    M inputs =
  rawQuotedFormulaCode M
    (Formula.ltTermAt (tVar 0) (tSucc (tVar 0))).
Proof.
  intros M inputs.
  unfold
    rawCoqRestrictedPADerivationSoundnessCarrierFinalizerLtSelfSuccCode,
    coqRestrictedPADerivationSoundnessCarrierFinalizerLtSelfSuccTemplate.
  apply rawStructuralTemplateFormula_embedPA.
Qed.

Lemma
    raw_coqRestrictedPADerivationSoundnessCarrierFinalizerSuccessorPrefixCode_as_all
    : forall (M : RawPAModel)
      (inputs : RawCodedTemplateStructuralInputs M),
  rawCoqRestrictedPADerivationSoundnessCarrierFinalizerSuccessorPrefixCode
    M inputs =
  rawFormulaAllCode M
    (rawCoqRestrictedPADerivationSoundnessCarrierFinalizerSuccessorPrefixBodyCode
      M inputs).
Proof.
  intros M inputs.
  unfold
    rawCoqRestrictedPADerivationSoundnessCarrierFinalizerSuccessorPrefixCode,
    rawCoqRestrictedPADerivationSoundnessCarrierFinalizerSuccessorPrefixBodyCode.
  rewrite
    coqRestrictedPADerivationSoundnessCarrierFinalizerSuccessorPrefixTemplate_shape.
  apply rawStructuralTemplateFormula_all_code.
Qed.

Lemma
    raw_coqRestrictedPADerivationSoundnessCarrierFinalizerGuardedPredicateCode_as_imp
    : forall (M : RawPAModel)
      (inputs : RawCodedTemplateStructuralInputs M),
  rawCoqRestrictedPADerivationSoundnessCarrierFinalizerGuardedPredicateCode
    M inputs =
  rawFormulaImpCode M
    (rawCoqRestrictedPADerivationSoundnessCarrierFinalizerLtSelfSuccCode
      M inputs)
    (rawCoqRestrictedPADerivationSoundnessPredicateCode M inputs).
Proof.
  intros M inputs.
  unfold
    rawCoqRestrictedPADerivationSoundnessCarrierFinalizerGuardedPredicateCode,
    rawCoqRestrictedPADerivationSoundnessCarrierFinalizerLtSelfSuccCode.
  rewrite
    coqRestrictedPADerivationSoundnessCarrierFinalizerGuardedPredicateTemplate_shape.
  rewrite rawStructuralTemplateFormula_imp_code.
  rewrite
    <- raw_coqRestrictedPADerivationSoundnessPredicateCode_structural.
  reflexivity.
Qed.

(** Each All-E endpoint is backed by the actual represented substitution
    tree generated by structural translation. *)
Theorem
    raw_coqRestrictedPADerivationSoundnessCarrierFinalizer_prefix_successor_substitution
    : forall (M : RawPAModel), RawPASatisfies M -> forall
      (inputs : RawCodedTemplateStructuralInputs M),
  RawCodedFormulaSingleSubstitution M
    (rawCoqRestrictedPADerivationSoundnessCarrierFinalizerSuccessorTermCode
      M inputs)
    (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixCode M inputs)
    (rawCoqRestrictedPADerivationSoundnessCarrierFinalizerSuccessorPrefixCode
      M inputs).
Proof.
  intros M hPA inputs.
  unfold
    rawCoqRestrictedPADerivationSoundnessCarrierFinalizerSuccessorTermCode,
    rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixCode,
    rawCoqRestrictedPADerivationSoundnessCarrierFinalizerSuccessorPrefixCode,
    coqRestrictedPADerivationSoundnessCarrierFinalizerSuccessorPrefixTemplate.
  exact (rawStructuralTemplateFormula_open M hPA inputs
    coqRestrictedPADerivationSoundnessCarrierStrongPrefixTemplate
    (embedPATerm (tSucc (tVar 0)))).
Qed.

Theorem
    raw_coqRestrictedPADerivationSoundnessCarrierFinalizer_prefix_member_substitution
    : forall (M : RawPAModel), RawPASatisfies M -> forall
      (inputs : RawCodedTemplateStructuralInputs M),
  RawCodedFormulaSingleSubstitution M
    (rawCoqRestrictedPADerivationSoundnessCarrierFinalizerVariableTermCode
      M inputs)
    (rawCoqRestrictedPADerivationSoundnessCarrierFinalizerSuccessorPrefixBodyCode
      M inputs)
    (rawCoqRestrictedPADerivationSoundnessCarrierFinalizerGuardedPredicateCode
      M inputs).
Proof.
  intros M hPA inputs.
  unfold
    rawCoqRestrictedPADerivationSoundnessCarrierFinalizerVariableTermCode,
    rawCoqRestrictedPADerivationSoundnessCarrierFinalizerSuccessorPrefixBodyCode,
    rawCoqRestrictedPADerivationSoundnessCarrierFinalizerGuardedPredicateCode,
    coqRestrictedPADerivationSoundnessCarrierFinalizerGuardedPredicateTemplate.
  exact (rawStructuralTemplateFormula_open M hPA inputs
    coqRestrictedPADerivationSoundnessCarrierFinalizerSuccessorPrefixBodyTemplate
    (embedPATerm (tVar 0))).
Qed.

(** ------------------------------------------------------------------
    The exact open context and its eigenvariable shift. *)

Definition rawCoqRestrictedPADerivationSoundnessCarrierFinalizerOpenContext
    (M : RawPAModel) (inputs : RawCodedTemplateStructuralInputs M)
    (baseContext axiom : M) : M :=
  rawListNode M
    (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixAllCode M inputs)
    (rawPAInductionExtendedContext M baseContext axiom).

Arguments rawCoqRestrictedPADerivationSoundnessCarrierFinalizerOpenContext
  M inputs baseContext axiom : clear implicits.

(** The induction closure data witnesses the newly adjoined induction axiom;
    hence its extended PA context self-shifts.  The head [forall d, K(d)] is
    closed by the finite syntactic computation above, so cons preserves the
    pointwise shift without changing either side. *)
Theorem
    raw_coqRestrictedPADerivationSoundnessCarrierFinalizerOpenContext_selfShift
    : forall (M : RawPAModel), RawPASatisfies M -> forall
      (inputs : RawCodedTemplateStructuralInputs M)
      replacement axiom closureCount baseWitnessList baseContext,
  RawCodedPAAxiomWitnessContext M baseWitnessList baseContext ->
  RawCoqRestrictedPADerivationSoundnessStrongPrefixClosureRemainder
    M inputs replacement axiom closureCount ->
  RawContextShift M
    (rawCoqRestrictedPADerivationSoundnessCarrierFinalizerOpenContext
      M inputs baseContext axiom)
    (rawCoqRestrictedPADerivationSoundnessCarrierFinalizerOpenContext
      M inputs baseContext axiom).
Proof.
  intros M hPA inputs replacement axiom closureCount
    baseWitnessList baseContext hbase hremainder.
  pose proof
    (raw_coqRestrictedPADerivationSoundnessCarrierStrongPrefixClosureInductionData
      M hPA inputs replacement axiom closureCount hremainder) as hdata.
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
  pose proof (raw_codedPAAxiomWitnessContext_add_induction M hPA
    baseWitnessList baseContext
    (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixCode M inputs)
    axiom hbase hinduction) as hextended.
  assert (htailShift : RawContextShift M
      (rawPAInductionExtendedContext M baseContext axiom)
      (rawPAInductionExtendedContext M baseContext axiom)).
  {
    exact (raw_codedPAAxiomWitnessContext_selfShift M hPA
      (rawPAInductionExtendedWitnessList M baseWitnessList
        (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixCode
          M inputs))
      (rawPAInductionExtendedContext M baseContext axiom)
      hextended).
  }
  assert (hheadShift : RawCodedFormulaShift M
      (raw_zero M) (rawNumeralValue M 1)
      (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixAllCode
        M inputs)
      (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixAllCode
        M inputs)).
  {
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
  }
  unfold rawCoqRestrictedPADerivationSoundnessCarrierFinalizerOpenContext.
  exact (raw_contextShift_cons M hPA
    (rawPAInductionExtendedContext M baseContext axiom)
    (rawPAInductionExtendedContext M baseContext axiom)
    (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixAllCode
      M inputs)
    (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixAllCode
      M inputs)
    htailShift hheadShift).
Qed.

(** ------------------------------------------------------------------
    Transparent proof-root graph. *)

Definition
    rawCoqRestrictedPADerivationSoundnessCarrierFinalizerPremiseRoot
    (M : RawPAModel) (inputs : RawCodedTemplateStructuralInputs M)
    (baseContext axiom : M) : M :=
  rawProofAssumptionRoot M
    (rawCoqRestrictedPADerivationSoundnessCarrierFinalizerOpenContext
      M inputs baseContext axiom)
    (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixAllCode
      M inputs).

Definition
    rawCoqRestrictedPADerivationSoundnessCarrierFinalizerSuccessorPrefixRoot
    (M : RawPAModel) (inputs : RawCodedTemplateStructuralInputs M)
    (baseContext axiom : M) : M :=
  rawProofAllERoot M
    (rawCoqRestrictedPADerivationSoundnessCarrierFinalizerOpenContext
      M inputs baseContext axiom)
    (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixCode M inputs)
    (rawCoqRestrictedPADerivationSoundnessCarrierFinalizerSuccessorTermCode
      M inputs)
    (rawCoqRestrictedPADerivationSoundnessCarrierFinalizerPremiseRoot
      M inputs baseContext axiom).

Definition
    rawCoqRestrictedPADerivationSoundnessCarrierFinalizerGuardedPredicateRoot
    (M : RawPAModel) (inputs : RawCodedTemplateStructuralInputs M)
    (baseContext axiom : M) : M :=
  rawProofAllERoot M
    (rawCoqRestrictedPADerivationSoundnessCarrierFinalizerOpenContext
      M inputs baseContext axiom)
    (rawCoqRestrictedPADerivationSoundnessCarrierFinalizerSuccessorPrefixBodyCode
      M inputs)
    (rawCoqRestrictedPADerivationSoundnessCarrierFinalizerVariableTermCode
      M inputs)
    (rawCoqRestrictedPADerivationSoundnessCarrierFinalizerSuccessorPrefixRoot
      M inputs baseContext axiom).

Definition
    rawCoqRestrictedPADerivationSoundnessCarrierFinalizerPredicateRoot
    (M : RawPAModel) (inputs : RawCodedTemplateStructuralInputs M)
    (baseContext axiom arithmeticRoot : M) : M :=
  rawProofImpERoot M
    (rawCoqRestrictedPADerivationSoundnessCarrierFinalizerOpenContext
      M inputs baseContext axiom)
    (rawCoqRestrictedPADerivationSoundnessCarrierFinalizerLtSelfSuccCode
      M inputs)
    (rawCoqRestrictedPADerivationSoundnessPredicateCode M inputs)
    (rawCoqRestrictedPADerivationSoundnessCarrierFinalizerGuardedPredicateRoot
      M inputs baseContext axiom)
    arithmeticRoot.

Definition rawCoqRestrictedPADerivationSoundnessCarrierFinalizerRoot
    (M : RawPAModel) (inputs : RawCodedTemplateStructuralInputs M)
    (baseContext axiom arithmeticRoot : M) : M :=
  rawProofImpIRoot M
    (rawPAInductionExtendedContext M baseContext axiom)
    (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixAllCode M inputs)
    (rawCoqRestrictedPADerivationSoundnessUniversalCode M inputs)
    (rawProofAllIRoot M
      (rawCoqRestrictedPADerivationSoundnessCarrierFinalizerOpenContext
        M inputs baseContext axiom)
      (rawCoqRestrictedPADerivationSoundnessPredicateCode M inputs)
      (rawCoqRestrictedPADerivationSoundnessCarrierFinalizerPredicateRoot
        M inputs baseContext axiom arithmeticRoot)).

Arguments
  rawCoqRestrictedPADerivationSoundnessCarrierFinalizerPremiseRoot
  M inputs baseContext axiom : clear implicits.
Arguments
  rawCoqRestrictedPADerivationSoundnessCarrierFinalizerSuccessorPrefixRoot
  M inputs baseContext axiom : clear implicits.
Arguments
  rawCoqRestrictedPADerivationSoundnessCarrierFinalizerGuardedPredicateRoot
  M inputs baseContext axiom : clear implicits.
Arguments
  rawCoqRestrictedPADerivationSoundnessCarrierFinalizerPredicateRoot
  M inputs baseContext axiom arithmeticRoot : clear implicits.
Arguments rawCoqRestrictedPADerivationSoundnessCarrierFinalizerRoot
  M inputs baseContext axiom arithmeticRoot : clear implicits.

(** All logical edges of the finalizer are now checked.  Notice that the
    arithmetic root is used only as the antecedent child of the final Imp-E;
    it does not stand in for any universal or propositional constructor. *)
Theorem
    raw_codedPALocalProofOf_coqRestrictedPADerivationSoundnessCarrierFinalizer_of_ltSelfSucc
    : forall (M : RawPAModel), RawPASatisfies M -> forall
      (inputs : RawCodedTemplateStructuralInputs M)
      baseContext axiom arithmeticRoot,
  RawContextListRealizable M
    (rawPAInductionExtendedContext M baseContext axiom) ->
  RawContextShift M
    (rawCoqRestrictedPADerivationSoundnessCarrierFinalizerOpenContext
      M inputs baseContext axiom)
    (rawCoqRestrictedPADerivationSoundnessCarrierFinalizerOpenContext
      M inputs baseContext axiom) ->
  RawCodedPALocalProofOf M
    (rawCoqRestrictedPADerivationSoundnessCarrierFinalizerOpenContext
      M inputs baseContext axiom)
    (rawCoqRestrictedPADerivationSoundnessCarrierFinalizerLtSelfSuccCode
      M inputs)
    arithmeticRoot ->
  RawCodedPALocalProofOf M
    (rawPAInductionExtendedContext M baseContext axiom)
    (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixFinalizerCode
      M inputs)
    (rawCoqRestrictedPADerivationSoundnessCarrierFinalizerRoot
      M inputs baseContext axiom arithmeticRoot).
Proof.
  intros M hPA inputs baseContext axiom arithmeticRoot
    htailRealizable hopenShift harithmetic.
  assert (hpremise : RawCodedPALocalProofOf M
      (rawCoqRestrictedPADerivationSoundnessCarrierFinalizerOpenContext
        M inputs baseContext axiom)
      (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixAllCode
        M inputs)
      (rawCoqRestrictedPADerivationSoundnessCarrierFinalizerPremiseRoot
        M inputs baseContext axiom)).
  {
    unfold
      rawCoqRestrictedPADerivationSoundnessCarrierFinalizerOpenContext,
      rawCoqRestrictedPADerivationSoundnessCarrierFinalizerPremiseRoot.
    exact (raw_codedPALocalProofOf_assumption M hPA
      (rawPAInductionExtendedContext M baseContext axiom)
      (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixAllCode
        M inputs)
      htailRealizable).
  }
  assert (hsuccessorPrefix : RawCodedPALocalProofOf M
      (rawCoqRestrictedPADerivationSoundnessCarrierFinalizerOpenContext
        M inputs baseContext axiom)
      (rawCoqRestrictedPADerivationSoundnessCarrierFinalizerSuccessorPrefixCode
        M inputs)
      (rawCoqRestrictedPADerivationSoundnessCarrierFinalizerSuccessorPrefixRoot
        M inputs baseContext axiom)).
  {
    unfold
      rawCoqRestrictedPADerivationSoundnessCarrierFinalizerSuccessorPrefixRoot.
    apply (raw_codedPALocalProofOf_allE M hPA
      (rawCoqRestrictedPADerivationSoundnessCarrierFinalizerOpenContext
        M inputs baseContext axiom)
      (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixCode M inputs)
      (rawCoqRestrictedPADerivationSoundnessCarrierFinalizerSuccessorTermCode
        M inputs)
      (rawCoqRestrictedPADerivationSoundnessCarrierFinalizerSuccessorPrefixCode
        M inputs)
      (rawCoqRestrictedPADerivationSoundnessCarrierFinalizerPremiseRoot
        M inputs baseContext axiom)).
    - exact hpremise.
    - exact
        (raw_coqRestrictedPADerivationSoundnessCarrierFinalizer_prefix_successor_substitution
          M hPA inputs).
  }
  assert (hguarded : RawCodedPALocalProofOf M
      (rawCoqRestrictedPADerivationSoundnessCarrierFinalizerOpenContext
        M inputs baseContext axiom)
      (rawCoqRestrictedPADerivationSoundnessCarrierFinalizerGuardedPredicateCode
        M inputs)
      (rawCoqRestrictedPADerivationSoundnessCarrierFinalizerGuardedPredicateRoot
        M inputs baseContext axiom)).
  {
    unfold
      rawCoqRestrictedPADerivationSoundnessCarrierFinalizerGuardedPredicateRoot.
    apply (raw_codedPALocalProofOf_allE M hPA
      (rawCoqRestrictedPADerivationSoundnessCarrierFinalizerOpenContext
        M inputs baseContext axiom)
      (rawCoqRestrictedPADerivationSoundnessCarrierFinalizerSuccessorPrefixBodyCode
        M inputs)
      (rawCoqRestrictedPADerivationSoundnessCarrierFinalizerVariableTermCode
        M inputs)
      (rawCoqRestrictedPADerivationSoundnessCarrierFinalizerGuardedPredicateCode
        M inputs)
      (rawCoqRestrictedPADerivationSoundnessCarrierFinalizerSuccessorPrefixRoot
        M inputs baseContext axiom)).
    - rewrite
        <- raw_coqRestrictedPADerivationSoundnessCarrierFinalizerSuccessorPrefixCode_as_all.
      exact hsuccessorPrefix.
    - exact
        (raw_coqRestrictedPADerivationSoundnessCarrierFinalizer_prefix_member_substitution
          M hPA inputs).
  }
  assert (hpredicate : RawCodedPALocalProofOf M
      (rawCoqRestrictedPADerivationSoundnessCarrierFinalizerOpenContext
        M inputs baseContext axiom)
      (rawCoqRestrictedPADerivationSoundnessPredicateCode M inputs)
      (rawCoqRestrictedPADerivationSoundnessCarrierFinalizerPredicateRoot
        M inputs baseContext axiom arithmeticRoot)).
  {
    unfold
      rawCoqRestrictedPADerivationSoundnessCarrierFinalizerPredicateRoot.
    apply (raw_codedPALocalProofOf_impE M hPA
      (rawCoqRestrictedPADerivationSoundnessCarrierFinalizerOpenContext
        M inputs baseContext axiom)
      (rawCoqRestrictedPADerivationSoundnessCarrierFinalizerLtSelfSuccCode
        M inputs)
      (rawCoqRestrictedPADerivationSoundnessPredicateCode M inputs)
      (rawCoqRestrictedPADerivationSoundnessCarrierFinalizerGuardedPredicateRoot
        M inputs baseContext axiom)
      arithmeticRoot).
    - rewrite
        <- raw_coqRestrictedPADerivationSoundnessCarrierFinalizerGuardedPredicateCode_as_imp.
      exact hguarded.
    - exact harithmetic.
  }
  destruct hpredicate as [hpredicateCoverage hpredicateEndpoint].
  assert (huniversal : RawCodedPALocalProofOf M
      (rawCoqRestrictedPADerivationSoundnessCarrierFinalizerOpenContext
        M inputs baseContext axiom)
      (rawCoqRestrictedPADerivationSoundnessUniversalCode M inputs)
      (rawProofAllIRoot M
        (rawCoqRestrictedPADerivationSoundnessCarrierFinalizerOpenContext
          M inputs baseContext axiom)
        (rawCoqRestrictedPADerivationSoundnessPredicateCode M inputs)
        (rawCoqRestrictedPADerivationSoundnessCarrierFinalizerPredicateRoot
          M inputs baseContext axiom arithmeticRoot))).
  {
    rewrite raw_coqRestrictedPADerivationSoundnessUniversalCode_view.
    split.
    - exact (raw_proofAllI_ruleCoverage M hPA
        (rawCoqRestrictedPADerivationSoundnessCarrierFinalizerOpenContext
          M inputs baseContext axiom)
        (rawCoqRestrictedPADerivationSoundnessCarrierFinalizerOpenContext
          M inputs baseContext axiom)
        (rawCoqRestrictedPADerivationSoundnessPredicateCode M inputs)
        (rawCoqRestrictedPADerivationSoundnessCarrierFinalizerPredicateRoot
          M inputs baseContext axiom arithmeticRoot)
        hopenShift hpredicateCoverage hpredicateEndpoint).
    - exact (raw_proofAllI_endpoint M
        (rawCoqRestrictedPADerivationSoundnessCarrierFinalizerOpenContext
          M inputs baseContext axiom)
        (rawCoqRestrictedPADerivationSoundnessPredicateCode M inputs)
        (rawCoqRestrictedPADerivationSoundnessCarrierFinalizerPredicateRoot
          M inputs baseContext axiom arithmeticRoot)).
  }
  unfold
    rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixFinalizerCode,
    rawCoqRestrictedPADerivationSoundnessCarrierFinalizerRoot.
  exact (raw_codedPALocalProofOf_impI M hPA
    (rawPAInductionExtendedContext M baseContext axiom)
    (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixAllCode M inputs)
    (rawCoqRestrictedPADerivationSoundnessUniversalCode M inputs)
    (rawProofAllIRoot M
      (rawCoqRestrictedPADerivationSoundnessCarrierFinalizerOpenContext
        M inputs baseContext axiom)
      (rawCoqRestrictedPADerivationSoundnessPredicateCode M inputs)
      (rawCoqRestrictedPADerivationSoundnessCarrierFinalizerPredicateRoot
        M inputs baseContext axiom arithmeticRoot))
    huniversal).
Qed.

(** Repackage the closure data as the witnessed extended context needed by
    the local assumption and All-I constructors. *)
Theorem
    raw_coqRestrictedPADerivationSoundnessCarrierFinalizer_extendedContext_witnessed
    : forall (M : RawPAModel), RawPASatisfies M -> forall
      (inputs : RawCodedTemplateStructuralInputs M)
      replacement axiom closureCount baseWitnessList baseContext,
  RawCodedPAAxiomWitnessContext M baseWitnessList baseContext ->
  RawCoqRestrictedPADerivationSoundnessStrongPrefixClosureRemainder
    M inputs replacement axiom closureCount ->
  RawCodedPAAxiomWitnessContext M
    (rawPAInductionExtendedWitnessList M baseWitnessList
      (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixCode M inputs))
    (rawPAInductionExtendedContext M baseContext axiom).
Proof.
  intros M hPA inputs replacement axiom closureCount
    baseWitnessList baseContext hbase hremainder.
  pose proof
    (raw_coqRestrictedPADerivationSoundnessCarrierStrongPrefixClosureInductionData
      M hPA inputs replacement axiom closureCount hremainder) as hdata.
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
  exact (raw_codedPAAxiomWitnessContext_add_induction M hPA
    baseWitnessList baseContext
    (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixCode M inputs)
    axiom hbase hinduction).
Qed.

(** PA itself proves the missing arithmetic formula.  Quotation therefore
    supplies an ordinary raw PA certificate with its own finite witnessed
    axiom context.  This theorem records that the obstruction below is not
    arithmetic provability: it is the stronger demand that the proof root
    inhabit the shell's already fixed, potentially empty base context. *)
Theorem
    coqRestrictedPADerivationSoundnessCarrierFinalizer_ltSelfSucc_bprov :
  Formula.BProv Formula.Ax_s []
    (Formula.ltTermAt (tVar 0) (tSucc (tVar 0))).
Proof.
  apply Formula.BProv_Ax_s_ltTermAt_succ_right_of_leTermAt.
  apply Formula.BProv_Ax_s_leTermAt_refl.
Qed.

Theorem
    raw_codedPAProofOf_coqRestrictedPADerivationSoundnessCarrierFinalizer_ltSelfSucc
    : forall (M : RawPAModel), RawPASatisfies M -> forall
      (inputs : RawCodedTemplateStructuralInputs M),
  exists certificate : M,
    RawCodedPAProofOf M
      (rawCoqRestrictedPADerivationSoundnessCarrierFinalizerLtSelfSuccCode
        M inputs)
      certificate.
Proof.
  intros M hPA inputs.
  destruct (raw_codedPAProofOf_of_BProv M hPA
    (Formula.ltTermAt (tVar 0) (tSucc (tVar 0)))
    coqRestrictedPADerivationSoundnessCarrierFinalizer_ltSelfSucc_bprov)
    as [certificate hcertificate].
  exists certificate.
  rewrite
    raw_coqRestrictedPADerivationSoundnessCarrierFinalizerLtSelfSuccCode_quoted.
  rewrite rawQuotedFormulaCode_standard by exact hPA.
  exact hcertificate.
Qed.

(** The literal arithmetic residual.  The root must prove [d < S d] after
    [forall K] has been assumed and after All-I has introduced [d].  Stating
    the leaf at precisely this context prevents accidental weakening to a
    semantic assertion or to a proof in an enlarged PA-axiom context. *)
Definition
    RawCoqRestrictedPADerivationSoundnessCarrierFinalizerLtSelfSuccRootCompiler
    (M : RawPAModel) (inputs : RawCodedTemplateStructuralInputs M) : Prop :=
  forall replacement axiom closureCount baseWitnessList baseContext,
    RawCodedPAAxiomWitnessContext M baseWitnessList baseContext ->
    RawCoqRestrictedPADerivationSoundnessStrongPrefixClosureRemainder
      M inputs replacement axiom closureCount ->
    exists arithmeticRoot : M,
      RawCodedPALocalProofOf M
        (rawCoqRestrictedPADerivationSoundnessCarrierFinalizerOpenContext
          M inputs baseContext axiom)
        (rawCoqRestrictedPADerivationSoundnessCarrierFinalizerLtSelfSuccCode
          M inputs)
        arithmeticRoot.

Arguments
  RawCoqRestrictedPADerivationSoundnessCarrierFinalizerLtSelfSuccRootCompiler
  M inputs : clear implicits.

(** Pointwise specialization: once the exact arithmetic leaf is present,
    every other premise of the original finalizer compiler follows from the
    already checked closure and witnessed-context data. *)
Theorem
    raw_codedPALocalProofOf_coqRestrictedPADerivationSoundnessCarrierFinalizer_from_exact_arithmetic_leaf
    : forall (M : RawPAModel), RawPASatisfies M -> forall
      (inputs : RawCodedTemplateStructuralInputs M)
      replacement axiom closureCount baseWitnessList baseContext
      arithmeticRoot,
  RawCodedPAAxiomWitnessContext M baseWitnessList baseContext ->
  RawCoqRestrictedPADerivationSoundnessStrongPrefixClosureRemainder
    M inputs replacement axiom closureCount ->
  RawCodedPALocalProofOf M
    (rawCoqRestrictedPADerivationSoundnessCarrierFinalizerOpenContext
      M inputs baseContext axiom)
    (rawCoqRestrictedPADerivationSoundnessCarrierFinalizerLtSelfSuccCode
      M inputs)
    arithmeticRoot ->
  RawCodedPALocalProofOf M
    (rawPAInductionExtendedContext M baseContext axiom)
    (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixFinalizerCode
      M inputs)
    (rawCoqRestrictedPADerivationSoundnessCarrierFinalizerRoot
      M inputs baseContext axiom arithmeticRoot).
Proof.
  intros M hPA inputs replacement axiom closureCount
    baseWitnessList baseContext arithmeticRoot hbase hremainder harithmetic.
  pose proof
    (raw_coqRestrictedPADerivationSoundnessCarrierFinalizer_extendedContext_witnessed
      M hPA inputs replacement axiom closureCount
      baseWitnessList baseContext hbase hremainder) as hextended.
  apply
    (raw_codedPALocalProofOf_coqRestrictedPADerivationSoundnessCarrierFinalizer_of_ltSelfSucc
      M hPA inputs baseContext axiom arithmeticRoot).
  - exact (raw_codedPAAxiomWitnessContext_context_realizable M
      (rawPAInductionExtendedWitnessList M baseWitnessList
        (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixCode
          M inputs))
      (rawPAInductionExtendedContext M baseContext axiom)
      hextended).
  - exact
      (raw_coqRestrictedPADerivationSoundnessCarrierFinalizerOpenContext_selfShift
        M hPA inputs replacement axiom closureCount
        baseWitnessList baseContext hbase hremainder).
  - exact harithmetic.
Qed.

(** Therefore the shell's whole finalizer boundary is discharged from the
    strictly smaller arithmetic compiler—never from a hypothesis asserting
    the finalizer itself. *)
Theorem
    raw_coqRestrictedPADerivationSoundnessCarrierStrongPrefixFinalizerRootCompiler_of_ltSelfSucc
    : forall (M : RawPAModel), RawPASatisfies M -> forall
      (inputs : RawCodedTemplateStructuralInputs M),
  RawCoqRestrictedPADerivationSoundnessCarrierFinalizerLtSelfSuccRootCompiler
    M inputs ->
  RawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixFinalizerRootCompiler
    M inputs.
Proof.
  intros M hPA inputs harithmeticCompiler.
  unfold
    RawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixFinalizerRootCompiler.
  intros replacement axiom closureCount baseWitnessList baseContext
    hbase hremainder.
  destruct (harithmeticCompiler replacement axiom closureCount
    baseWitnessList baseContext hbase hremainder) as
    [arithmeticRoot harithmetic].
  exists (rawCoqRestrictedPADerivationSoundnessCarrierFinalizerRoot
    M inputs baseContext axiom arithmeticRoot).
  exact
    (raw_codedPALocalProofOf_coqRestrictedPADerivationSoundnessCarrierFinalizer_from_exact_arithmetic_leaf
      M hPA inputs replacement axiom closureCount
      baseWitnessList baseContext arithmeticRoot
      hbase hremainder harithmetic).
Qed.

End
  PABoundedRawCodedRestrictedPADerivationSoundnessCarrierStrongPrefixFinalizerCompilation.
