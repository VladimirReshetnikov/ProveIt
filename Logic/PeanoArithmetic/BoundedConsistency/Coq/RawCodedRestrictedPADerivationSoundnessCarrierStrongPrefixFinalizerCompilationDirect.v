(**
  Direct-code compilation of the strong-prefix finalizer.

  The finite finalizer proof is independent of how opaque truth atoms are
  represented.  This module therefore reuses the checked templates from the
  structural compiler, but translates them with direct structural inputs.
  In particular, the two All-E edges below use the represented opening
  traces carried by those inputs; no opaque formula code is decoded into a
  metatheoretic syntax tree.

  The logical graph proves

      (forall d, K(d)) -> forall d, P(d)

  by instantiating the prefix at [S d], then its member at [d], and finally
  applying the resulting guard [d < S d].  The only residual premise is an
  exact local proof of that arithmetic guard in the shifted open context.
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
  RawCodedTemplateProofCompiler
  RawCodedTemplatePAEmbedding
  RawCodedTemplateDirectStructuralTranslation
  RawCodedTemplateDirectStructuralPAAgreement
  RawCodedRestrictedPAConsistencyFromUniversalSoundness
  RawCodedRestrictedPADerivationSoundnessCarrierStrongPrefixInductionShell
  RawCodedRestrictedPADerivationSoundnessCarrierStrongPrefixFinalizerCompilation
  RawCodedRestrictedPADerivationSoundnessCarrierStrongPrefixDirectInductionShell.

Module
  PABoundedRawCodedRestrictedPADerivationSoundnessCarrierStrongPrefixFinalizerCompilationDirect.

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
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedTemplatePAEmbedding.
Import PABoundedRawCodedTemplateDirectStructuralTranslation.
Import PABoundedRawCodedTemplateDirectStructuralPAAgreement.
Import PABoundedRawCodedRestrictedPAConsistencyFromUniversalSoundness.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessCarrierStrongPrefixInductionShell.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessCarrierStrongPrefixFinalizerCompilation.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessCarrierStrongPrefixDirectInductionShell.

(** ------------------------------------------------------------------
    Direct codes of the two universal instances and the arithmetic guard. *)

Definition
    rawCoqRestrictedPADerivationSoundnessCarrierFinalizerSuccessorTermDirectCode
    (M : RawPAModel)
    (inputs : RawCodedTemplateDirectStructuralInputs M) : M :=
  rawDirectTemplateTerm inputs (embedPATerm (tSucc (tVar 0))).

Definition
    rawCoqRestrictedPADerivationSoundnessCarrierFinalizerVariableTermDirectCode
    (M : RawPAModel)
    (inputs : RawCodedTemplateDirectStructuralInputs M) : M :=
  rawDirectTemplateTerm inputs (embedPATerm (tVar 0)).

Definition
    rawCoqRestrictedPADerivationSoundnessCarrierFinalizerSuccessorPrefixDirectCode
    (M : RawPAModel)
    (inputs : RawCodedTemplateDirectStructuralInputs M) : M :=
  rawDirectTemplateFormula inputs
    coqRestrictedPADerivationSoundnessCarrierFinalizerSuccessorPrefixTemplate.

Definition
    rawCoqRestrictedPADerivationSoundnessCarrierFinalizerSuccessorPrefixBodyDirectCode
    (M : RawPAModel)
    (inputs : RawCodedTemplateDirectStructuralInputs M) : M :=
  rawDirectTemplateFormula inputs
    coqRestrictedPADerivationSoundnessCarrierFinalizerSuccessorPrefixBodyTemplate.

Definition
    rawCoqRestrictedPADerivationSoundnessCarrierFinalizerGuardedPredicateDirectCode
    (M : RawPAModel)
    (inputs : RawCodedTemplateDirectStructuralInputs M) : M :=
  rawDirectTemplateFormula inputs
    coqRestrictedPADerivationSoundnessCarrierFinalizerGuardedPredicateTemplate.

Definition
    rawCoqRestrictedPADerivationSoundnessCarrierFinalizerLtSelfSuccDirectCode
    (M : RawPAModel)
    (inputs : RawCodedTemplateDirectStructuralInputs M) : M :=
  rawDirectTemplateFormula inputs
    coqRestrictedPADerivationSoundnessCarrierFinalizerLtSelfSuccTemplate.

Arguments
  rawCoqRestrictedPADerivationSoundnessCarrierFinalizerSuccessorTermDirectCode
  M inputs : clear implicits.
Arguments
  rawCoqRestrictedPADerivationSoundnessCarrierFinalizerVariableTermDirectCode
  M inputs : clear implicits.
Arguments
  rawCoqRestrictedPADerivationSoundnessCarrierFinalizerSuccessorPrefixDirectCode
  M inputs : clear implicits.
Arguments
  rawCoqRestrictedPADerivationSoundnessCarrierFinalizerSuccessorPrefixBodyDirectCode
  M inputs : clear implicits.
Arguments
  rawCoqRestrictedPADerivationSoundnessCarrierFinalizerGuardedPredicateDirectCode
  M inputs : clear implicits.
Arguments
  rawCoqRestrictedPADerivationSoundnessCarrierFinalizerLtSelfSuccDirectCode
  M inputs : clear implicits.

(** Agreement is invoked through the generic translation interface, so this
    equality does not depend on implementation details of direct symbols. *)
Lemma
    raw_coqRestrictedPADerivationSoundnessCarrierFinalizerLtSelfSuccDirectCode_quoted
    : forall (M : RawPAModel), RawPASatisfies M -> forall
      (inputs : RawCodedTemplateDirectStructuralInputs M),
  rawCoqRestrictedPADerivationSoundnessCarrierFinalizerLtSelfSuccDirectCode
    M inputs =
  rawQuotedFormulaCode M
    (Formula.ltTermAt (tVar 0) (tSucc (tVar 0))).
Proof.
  intros M hPA inputs.
  unfold
    rawCoqRestrictedPADerivationSoundnessCarrierFinalizerLtSelfSuccDirectCode,
    coqRestrictedPADerivationSoundnessCarrierFinalizerLtSelfSuccTemplate.
  change
    (rawTemplateFormula
      (rawDirectStructuralTemplateTranslation M hPA inputs)
      (embedPAFormula
        (Formula.ltTermAt (tVar 0) (tSucc (tVar 0)))) =
     rawQuotedFormulaCode M
       (Formula.ltTermAt (tVar 0) (tSucc (tVar 0)))).
  exact (rawTemplateFormula_embedPA
    (rawDirectStructuralTemplatePAAgreement M hPA inputs)
    (Formula.ltTermAt (tVar 0) (tSucc (tVar 0)))).
Qed.

Lemma
    raw_coqRestrictedPADerivationSoundnessCarrierFinalizerSuccessorPrefixDirectCode_as_all
    : forall (M : RawPAModel)
      (inputs : RawCodedTemplateDirectStructuralInputs M),
  rawCoqRestrictedPADerivationSoundnessCarrierFinalizerSuccessorPrefixDirectCode
    M inputs =
  rawFormulaAllCode M
    (rawCoqRestrictedPADerivationSoundnessCarrierFinalizerSuccessorPrefixBodyDirectCode
      M inputs).
Proof.
  intros M inputs.
  unfold
    rawCoqRestrictedPADerivationSoundnessCarrierFinalizerSuccessorPrefixDirectCode,
    rawCoqRestrictedPADerivationSoundnessCarrierFinalizerSuccessorPrefixBodyDirectCode.
  rewrite
    coqRestrictedPADerivationSoundnessCarrierFinalizerSuccessorPrefixTemplate_shape.
  apply rawDirectTemplateFormula_all_code.
Qed.

Lemma
    raw_coqRestrictedPADerivationSoundnessCarrierFinalizerGuardedPredicateDirectCode_as_imp
    : forall (M : RawPAModel)
      (inputs : RawCodedTemplateDirectStructuralInputs M),
  rawCoqRestrictedPADerivationSoundnessCarrierFinalizerGuardedPredicateDirectCode
    M inputs =
  rawFormulaImpCode M
    (rawCoqRestrictedPADerivationSoundnessCarrierFinalizerLtSelfSuccDirectCode
      M inputs)
    (rawCoqRestrictedPADerivationSoundnessPredicateDirectCode M inputs).
Proof.
  intros M inputs.
  unfold
    rawCoqRestrictedPADerivationSoundnessCarrierFinalizerGuardedPredicateDirectCode,
    rawCoqRestrictedPADerivationSoundnessCarrierFinalizerLtSelfSuccDirectCode,
    rawCoqRestrictedPADerivationSoundnessPredicateDirectCode.
  rewrite
    coqRestrictedPADerivationSoundnessCarrierFinalizerGuardedPredicateTemplate_shape.
  apply rawDirectTemplateFormula_imp_code.
Qed.

(** These are the actual represented substitutions consumed by All-E.  The
    second opening happens under the outer prefix binder: after instantiating
    that binder at [S d], the remaining member binder is opened at [d]. *)
Theorem
    raw_coqRestrictedPADerivationSoundnessCarrierFinalizer_prefix_successor_direct_substitution
    : forall (M : RawPAModel), RawPASatisfies M -> forall
      (inputs : RawCodedTemplateDirectStructuralInputs M),
  RawCodedFormulaSingleSubstitution M
    (rawCoqRestrictedPADerivationSoundnessCarrierFinalizerSuccessorTermDirectCode
      M inputs)
    (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixDirectCode
      M inputs)
    (rawCoqRestrictedPADerivationSoundnessCarrierFinalizerSuccessorPrefixDirectCode
      M inputs).
Proof.
  intros M hPA inputs.
  unfold
    rawCoqRestrictedPADerivationSoundnessCarrierFinalizerSuccessorTermDirectCode,
    rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixDirectCode,
    rawCoqRestrictedPADerivationSoundnessCarrierFinalizerSuccessorPrefixDirectCode,
    coqRestrictedPADerivationSoundnessCarrierFinalizerSuccessorPrefixTemplate.
  exact (rawDirectTemplateFormula_open M hPA inputs
    coqRestrictedPADerivationSoundnessCarrierStrongPrefixTemplate
    (embedPATerm (tSucc (tVar 0)))).
Qed.

Theorem
    raw_coqRestrictedPADerivationSoundnessCarrierFinalizer_prefix_member_direct_substitution
    : forall (M : RawPAModel), RawPASatisfies M -> forall
      (inputs : RawCodedTemplateDirectStructuralInputs M),
  RawCodedFormulaSingleSubstitution M
    (rawCoqRestrictedPADerivationSoundnessCarrierFinalizerVariableTermDirectCode
      M inputs)
    (rawCoqRestrictedPADerivationSoundnessCarrierFinalizerSuccessorPrefixBodyDirectCode
      M inputs)
    (rawCoqRestrictedPADerivationSoundnessCarrierFinalizerGuardedPredicateDirectCode
      M inputs).
Proof.
  intros M hPA inputs.
  unfold
    rawCoqRestrictedPADerivationSoundnessCarrierFinalizerVariableTermDirectCode,
    rawCoqRestrictedPADerivationSoundnessCarrierFinalizerSuccessorPrefixBodyDirectCode,
    rawCoqRestrictedPADerivationSoundnessCarrierFinalizerGuardedPredicateDirectCode,
    coqRestrictedPADerivationSoundnessCarrierFinalizerGuardedPredicateTemplate.
  exact (rawDirectTemplateFormula_open M hPA inputs
    coqRestrictedPADerivationSoundnessCarrierFinalizerSuccessorPrefixBodyTemplate
    (embedPATerm (tVar 0))).
Qed.

(** ------------------------------------------------------------------
    The temporary premise context and its eigenvariable shift. *)

Definition
    rawCoqRestrictedPADerivationSoundnessCarrierFinalizerDirectOpenContext
    (M : RawPAModel)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    (baseContext axiom : M) : M :=
  rawListNode M
    (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixAllDirectCode
      M inputs)
    (rawPAInductionExtendedContext M baseContext axiom).

Arguments
  rawCoqRestrictedPADerivationSoundnessCarrierFinalizerDirectOpenContext
  M inputs baseContext axiom : clear implicits.

Theorem
    raw_coqRestrictedPADerivationSoundnessCarrierFinalizerDirectOpenContext_selfShift
    : forall (M : RawPAModel), RawPASatisfies M -> forall
      (inputs : RawCodedTemplateDirectStructuralInputs M)
      replacement axiom closureCount baseWitnessList baseContext,
  RawCodedPAAxiomWitnessContext M baseWitnessList baseContext ->
  RawCoqRestrictedPADerivationSoundnessStrongPrefixDirectClosureRemainder
    M inputs replacement axiom closureCount ->
  RawContextShift M
    (rawCoqRestrictedPADerivationSoundnessCarrierFinalizerDirectOpenContext
      M inputs baseContext axiom)
    (rawCoqRestrictedPADerivationSoundnessCarrierFinalizerDirectOpenContext
      M inputs baseContext axiom).
Proof.
  intros M hPA inputs replacement axiom closureCount
    baseWitnessList baseContext hbase hremainder.
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
    axiom hbase hinduction) as hextended.
  assert (htailShift : RawContextShift M
      (rawPAInductionExtendedContext M baseContext axiom)
      (rawPAInductionExtendedContext M baseContext axiom)).
  {
    exact (raw_codedPAAxiomWitnessContext_selfShift M hPA
      (rawPAInductionExtendedWitnessList M baseWitnessList
        (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixDirectCode
          M inputs))
      (rawPAInductionExtendedContext M baseContext axiom)
      hextended).
  }
  assert (hheadShift : RawCodedFormulaShift M
      (raw_zero M) (rawNumeralValue M 1)
      (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixAllDirectCode
        M inputs)
      (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixAllDirectCode
        M inputs)).
  {
    (* The head is closed, so opening an eigenvariable beneath it leaves the
       exact same direct code.  Only the finite template is normalized. *)
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
  }
  unfold
    rawCoqRestrictedPADerivationSoundnessCarrierFinalizerDirectOpenContext.
  exact (raw_contextShift_cons M hPA
    (rawPAInductionExtendedContext M baseContext axiom)
    (rawPAInductionExtendedContext M baseContext axiom)
    (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixAllDirectCode
      M inputs)
    (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixAllDirectCode
      M inputs)
    htailShift hheadShift).
Qed.

(** ------------------------------------------------------------------
    Transparent direct proof-root graph. *)

Definition
    rawCoqRestrictedPADerivationSoundnessCarrierFinalizerDirectPremiseRoot
    (M : RawPAModel)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    (baseContext axiom : M) : M :=
  rawProofAssumptionRoot M
    (rawCoqRestrictedPADerivationSoundnessCarrierFinalizerDirectOpenContext
      M inputs baseContext axiom)
    (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixAllDirectCode
      M inputs).

Definition
    rawCoqRestrictedPADerivationSoundnessCarrierFinalizerDirectSuccessorPrefixRoot
    (M : RawPAModel)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    (baseContext axiom : M) : M :=
  rawProofAllERoot M
    (rawCoqRestrictedPADerivationSoundnessCarrierFinalizerDirectOpenContext
      M inputs baseContext axiom)
    (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixDirectCode
      M inputs)
    (rawCoqRestrictedPADerivationSoundnessCarrierFinalizerSuccessorTermDirectCode
      M inputs)
    (rawCoqRestrictedPADerivationSoundnessCarrierFinalizerDirectPremiseRoot
      M inputs baseContext axiom).

Definition
    rawCoqRestrictedPADerivationSoundnessCarrierFinalizerDirectGuardedPredicateRoot
    (M : RawPAModel)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    (baseContext axiom : M) : M :=
  rawProofAllERoot M
    (rawCoqRestrictedPADerivationSoundnessCarrierFinalizerDirectOpenContext
      M inputs baseContext axiom)
    (rawCoqRestrictedPADerivationSoundnessCarrierFinalizerSuccessorPrefixBodyDirectCode
      M inputs)
    (rawCoqRestrictedPADerivationSoundnessCarrierFinalizerVariableTermDirectCode
      M inputs)
    (rawCoqRestrictedPADerivationSoundnessCarrierFinalizerDirectSuccessorPrefixRoot
      M inputs baseContext axiom).

Definition
    rawCoqRestrictedPADerivationSoundnessCarrierFinalizerDirectPredicateRoot
    (M : RawPAModel)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    (baseContext axiom arithmeticRoot : M) : M :=
  rawProofImpERoot M
    (rawCoqRestrictedPADerivationSoundnessCarrierFinalizerDirectOpenContext
      M inputs baseContext axiom)
    (rawCoqRestrictedPADerivationSoundnessCarrierFinalizerLtSelfSuccDirectCode
      M inputs)
    (rawCoqRestrictedPADerivationSoundnessPredicateDirectCode M inputs)
    (rawCoqRestrictedPADerivationSoundnessCarrierFinalizerDirectGuardedPredicateRoot
      M inputs baseContext axiom)
    arithmeticRoot.

Definition
    rawCoqRestrictedPADerivationSoundnessCarrierFinalizerDirectRoot
    (M : RawPAModel)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    (baseContext axiom arithmeticRoot : M) : M :=
  rawProofImpIRoot M
    (rawPAInductionExtendedContext M baseContext axiom)
    (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixAllDirectCode
      M inputs)
    (rawCoqRestrictedPADerivationSoundnessUniversalDirectCode M inputs)
    (rawProofAllIRoot M
      (rawCoqRestrictedPADerivationSoundnessCarrierFinalizerDirectOpenContext
        M inputs baseContext axiom)
      (rawCoqRestrictedPADerivationSoundnessPredicateDirectCode M inputs)
      (rawCoqRestrictedPADerivationSoundnessCarrierFinalizerDirectPredicateRoot
        M inputs baseContext axiom arithmeticRoot)).

Arguments
  rawCoqRestrictedPADerivationSoundnessCarrierFinalizerDirectPremiseRoot
  M inputs baseContext axiom : clear implicits.
Arguments
  rawCoqRestrictedPADerivationSoundnessCarrierFinalizerDirectSuccessorPrefixRoot
  M inputs baseContext axiom : clear implicits.
Arguments
  rawCoqRestrictedPADerivationSoundnessCarrierFinalizerDirectGuardedPredicateRoot
  M inputs baseContext axiom : clear implicits.
Arguments
  rawCoqRestrictedPADerivationSoundnessCarrierFinalizerDirectPredicateRoot
  M inputs baseContext axiom arithmeticRoot : clear implicits.
Arguments
  rawCoqRestrictedPADerivationSoundnessCarrierFinalizerDirectRoot
  M inputs baseContext axiom arithmeticRoot : clear implicits.

(** The arithmetic root occurs only at the final Imp-E edge.  Every All-E,
    All-I, and Imp-I node is constructed and checked independently. *)
Theorem
    raw_codedPALocalProofOf_coqRestrictedPADerivationSoundnessCarrierFinalizerDirect_of_ltSelfSucc
    : forall (M : RawPAModel), RawPASatisfies M -> forall
      (inputs : RawCodedTemplateDirectStructuralInputs M)
      baseContext axiom arithmeticRoot,
  RawContextListRealizable M
    (rawPAInductionExtendedContext M baseContext axiom) ->
  RawContextShift M
    (rawCoqRestrictedPADerivationSoundnessCarrierFinalizerDirectOpenContext
      M inputs baseContext axiom)
    (rawCoqRestrictedPADerivationSoundnessCarrierFinalizerDirectOpenContext
      M inputs baseContext axiom) ->
  RawCodedPALocalProofOf M
    (rawCoqRestrictedPADerivationSoundnessCarrierFinalizerDirectOpenContext
      M inputs baseContext axiom)
    (rawCoqRestrictedPADerivationSoundnessCarrierFinalizerLtSelfSuccDirectCode
      M inputs)
    arithmeticRoot ->
  RawCodedPALocalProofOf M
    (rawPAInductionExtendedContext M baseContext axiom)
    (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixFinalizerDirectCode
      M inputs)
    (rawCoqRestrictedPADerivationSoundnessCarrierFinalizerDirectRoot
      M inputs baseContext axiom arithmeticRoot).
Proof.
  intros M hPA inputs baseContext axiom arithmeticRoot
    htailRealizable hopenShift harithmetic.
  assert (hpremise : RawCodedPALocalProofOf M
      (rawCoqRestrictedPADerivationSoundnessCarrierFinalizerDirectOpenContext
        M inputs baseContext axiom)
      (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixAllDirectCode
        M inputs)
      (rawCoqRestrictedPADerivationSoundnessCarrierFinalizerDirectPremiseRoot
        M inputs baseContext axiom)).
  {
    unfold
      rawCoqRestrictedPADerivationSoundnessCarrierFinalizerDirectOpenContext,
      rawCoqRestrictedPADerivationSoundnessCarrierFinalizerDirectPremiseRoot.
    exact (raw_codedPALocalProofOf_assumption M hPA
      (rawPAInductionExtendedContext M baseContext axiom)
      (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixAllDirectCode
        M inputs)
      htailRealizable).
  }
  assert (hsuccessorPrefix : RawCodedPALocalProofOf M
      (rawCoqRestrictedPADerivationSoundnessCarrierFinalizerDirectOpenContext
        M inputs baseContext axiom)
      (rawCoqRestrictedPADerivationSoundnessCarrierFinalizerSuccessorPrefixDirectCode
        M inputs)
      (rawCoqRestrictedPADerivationSoundnessCarrierFinalizerDirectSuccessorPrefixRoot
        M inputs baseContext axiom)).
  {
    unfold
      rawCoqRestrictedPADerivationSoundnessCarrierFinalizerDirectSuccessorPrefixRoot.
    apply (raw_codedPALocalProofOf_allE M hPA
      (rawCoqRestrictedPADerivationSoundnessCarrierFinalizerDirectOpenContext
        M inputs baseContext axiom)
      (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixDirectCode
        M inputs)
      (rawCoqRestrictedPADerivationSoundnessCarrierFinalizerSuccessorTermDirectCode
        M inputs)
      (rawCoqRestrictedPADerivationSoundnessCarrierFinalizerSuccessorPrefixDirectCode
        M inputs)
      (rawCoqRestrictedPADerivationSoundnessCarrierFinalizerDirectPremiseRoot
        M inputs baseContext axiom)).
    - exact hpremise.
    - exact
        (raw_coqRestrictedPADerivationSoundnessCarrierFinalizer_prefix_successor_direct_substitution
          M hPA inputs).
  }
  assert (hguarded : RawCodedPALocalProofOf M
      (rawCoqRestrictedPADerivationSoundnessCarrierFinalizerDirectOpenContext
        M inputs baseContext axiom)
      (rawCoqRestrictedPADerivationSoundnessCarrierFinalizerGuardedPredicateDirectCode
        M inputs)
      (rawCoqRestrictedPADerivationSoundnessCarrierFinalizerDirectGuardedPredicateRoot
        M inputs baseContext axiom)).
  {
    unfold
      rawCoqRestrictedPADerivationSoundnessCarrierFinalizerDirectGuardedPredicateRoot.
    apply (raw_codedPALocalProofOf_allE M hPA
      (rawCoqRestrictedPADerivationSoundnessCarrierFinalizerDirectOpenContext
        M inputs baseContext axiom)
      (rawCoqRestrictedPADerivationSoundnessCarrierFinalizerSuccessorPrefixBodyDirectCode
        M inputs)
      (rawCoqRestrictedPADerivationSoundnessCarrierFinalizerVariableTermDirectCode
        M inputs)
      (rawCoqRestrictedPADerivationSoundnessCarrierFinalizerGuardedPredicateDirectCode
        M inputs)
      (rawCoqRestrictedPADerivationSoundnessCarrierFinalizerDirectSuccessorPrefixRoot
        M inputs baseContext axiom)).
    - rewrite
        <- raw_coqRestrictedPADerivationSoundnessCarrierFinalizerSuccessorPrefixDirectCode_as_all.
      exact hsuccessorPrefix.
    - exact
        (raw_coqRestrictedPADerivationSoundnessCarrierFinalizer_prefix_member_direct_substitution
          M hPA inputs).
  }
  assert (hpredicate : RawCodedPALocalProofOf M
      (rawCoqRestrictedPADerivationSoundnessCarrierFinalizerDirectOpenContext
        M inputs baseContext axiom)
      (rawCoqRestrictedPADerivationSoundnessPredicateDirectCode M inputs)
      (rawCoqRestrictedPADerivationSoundnessCarrierFinalizerDirectPredicateRoot
        M inputs baseContext axiom arithmeticRoot)).
  {
    unfold
      rawCoqRestrictedPADerivationSoundnessCarrierFinalizerDirectPredicateRoot.
    apply (raw_codedPALocalProofOf_impE M hPA
      (rawCoqRestrictedPADerivationSoundnessCarrierFinalizerDirectOpenContext
        M inputs baseContext axiom)
      (rawCoqRestrictedPADerivationSoundnessCarrierFinalizerLtSelfSuccDirectCode
        M inputs)
      (rawCoqRestrictedPADerivationSoundnessPredicateDirectCode M inputs)
      (rawCoqRestrictedPADerivationSoundnessCarrierFinalizerDirectGuardedPredicateRoot
        M inputs baseContext axiom)
      arithmeticRoot).
    - rewrite
        <- raw_coqRestrictedPADerivationSoundnessCarrierFinalizerGuardedPredicateDirectCode_as_imp.
      exact hguarded.
    - exact harithmetic.
  }
  destruct hpredicate as [hpredicateCoverage hpredicateEndpoint].
  assert (huniversal : RawCodedPALocalProofOf M
      (rawCoqRestrictedPADerivationSoundnessCarrierFinalizerDirectOpenContext
        M inputs baseContext axiom)
      (rawCoqRestrictedPADerivationSoundnessUniversalDirectCode M inputs)
      (rawProofAllIRoot M
        (rawCoqRestrictedPADerivationSoundnessCarrierFinalizerDirectOpenContext
          M inputs baseContext axiom)
        (rawCoqRestrictedPADerivationSoundnessPredicateDirectCode M inputs)
        (rawCoqRestrictedPADerivationSoundnessCarrierFinalizerDirectPredicateRoot
          M inputs baseContext axiom arithmeticRoot))).
  {
    rewrite raw_coqRestrictedPADerivationSoundnessUniversalDirectCode_view.
    split.
    - exact (raw_proofAllI_ruleCoverage M hPA
        (rawCoqRestrictedPADerivationSoundnessCarrierFinalizerDirectOpenContext
          M inputs baseContext axiom)
        (rawCoqRestrictedPADerivationSoundnessCarrierFinalizerDirectOpenContext
          M inputs baseContext axiom)
        (rawCoqRestrictedPADerivationSoundnessPredicateDirectCode M inputs)
        (rawCoqRestrictedPADerivationSoundnessCarrierFinalizerDirectPredicateRoot
          M inputs baseContext axiom arithmeticRoot)
        hopenShift hpredicateCoverage hpredicateEndpoint).
    - exact (raw_proofAllI_endpoint M
        (rawCoqRestrictedPADerivationSoundnessCarrierFinalizerDirectOpenContext
          M inputs baseContext axiom)
        (rawCoqRestrictedPADerivationSoundnessPredicateDirectCode M inputs)
        (rawCoqRestrictedPADerivationSoundnessCarrierFinalizerDirectPredicateRoot
          M inputs baseContext axiom arithmeticRoot)).
  }
  unfold
    rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixFinalizerDirectCode,
    rawCoqRestrictedPADerivationSoundnessCarrierFinalizerDirectRoot.
  exact (raw_codedPALocalProofOf_impI M hPA
    (rawPAInductionExtendedContext M baseContext axiom)
    (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixAllDirectCode
      M inputs)
    (rawCoqRestrictedPADerivationSoundnessUniversalDirectCode M inputs)
    (rawProofAllIRoot M
      (rawCoqRestrictedPADerivationSoundnessCarrierFinalizerDirectOpenContext
        M inputs baseContext axiom)
      (rawCoqRestrictedPADerivationSoundnessPredicateDirectCode M inputs)
      (rawCoqRestrictedPADerivationSoundnessCarrierFinalizerDirectPredicateRoot
        M inputs baseContext axiom arithmeticRoot))
    huniversal).
Qed.

(** Repackage the direct closure data as the witnessed extended context used
    by the temporary assumption and the eigenvariable rule. *)
Theorem
    raw_coqRestrictedPADerivationSoundnessCarrierFinalizerDirect_extendedContext_witnessed
    : forall (M : RawPAModel), RawPASatisfies M -> forall
      (inputs : RawCodedTemplateDirectStructuralInputs M)
      replacement axiom closureCount baseWitnessList baseContext,
  RawCodedPAAxiomWitnessContext M baseWitnessList baseContext ->
  RawCoqRestrictedPADerivationSoundnessStrongPrefixDirectClosureRemainder
    M inputs replacement axiom closureCount ->
  RawCodedPAAxiomWitnessContext M
    (rawPAInductionExtendedWitnessList M baseWitnessList
      (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixDirectCode
        M inputs))
    (rawPAInductionExtendedContext M baseContext axiom).
Proof.
  intros M hPA inputs replacement axiom closureCount
    baseWitnessList baseContext hbase hremainder.
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
  exact (raw_codedPAAxiomWitnessContext_add_induction M hPA
    baseWitnessList baseContext
    (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixDirectCode
      M inputs)
    axiom hbase hinduction).
Qed.

(** PA proves the guard independently of the opaque direct atoms.  This is
    useful for growing-context clients; the exact finalizer below still asks
    for a root in its already fixed open context. *)
Theorem
    raw_codedPAProofOf_coqRestrictedPADerivationSoundnessCarrierFinalizerLtSelfSuccDirect
    : forall (M : RawPAModel), RawPASatisfies M -> forall
      (inputs : RawCodedTemplateDirectStructuralInputs M),
  exists certificate : M,
    RawCodedPAProofOf M
      (rawCoqRestrictedPADerivationSoundnessCarrierFinalizerLtSelfSuccDirectCode
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
    raw_coqRestrictedPADerivationSoundnessCarrierFinalizerLtSelfSuccDirectCode_quoted
    by exact hPA.
  rewrite rawQuotedFormulaCode_standard by exact hPA.
  exact hcertificate.
Qed.

(** The literal residual compiler.  Its result is intentionally local to
    the open context, rather than merely an ordinary PA proof in some other
    finite axiom context. *)
Definition
    RawCoqRestrictedPADerivationSoundnessCarrierFinalizerLtSelfSuccDirectRootCompiler
    (M : RawPAModel)
    (inputs : RawCodedTemplateDirectStructuralInputs M) : Prop :=
  forall replacement axiom closureCount baseWitnessList baseContext,
    RawCodedPAAxiomWitnessContext M baseWitnessList baseContext ->
    RawCoqRestrictedPADerivationSoundnessStrongPrefixDirectClosureRemainder
      M inputs replacement axiom closureCount ->
    exists arithmeticRoot : M,
      RawCodedPALocalProofOf M
        (rawCoqRestrictedPADerivationSoundnessCarrierFinalizerDirectOpenContext
          M inputs baseContext axiom)
        (rawCoqRestrictedPADerivationSoundnessCarrierFinalizerLtSelfSuccDirectCode
          M inputs)
        arithmeticRoot.

Arguments
  RawCoqRestrictedPADerivationSoundnessCarrierFinalizerLtSelfSuccDirectRootCompiler
  M inputs : clear implicits.

(** Pointwise endpoint requested by the direct shell: the closure remainder
    supplies both the witnessed induction context and its shift; the caller
    supplies only the exact arithmetic leaf used by the proof graph. *)
Theorem
    raw_codedPALocalProofOf_coqRestrictedPADerivationSoundnessCarrierFinalizerDirect_from_exact_arithmetic_leaf
    : forall (M : RawPAModel), RawPASatisfies M -> forall
      (inputs : RawCodedTemplateDirectStructuralInputs M)
      replacement axiom closureCount baseWitnessList baseContext
      arithmeticRoot,
  RawCodedPAAxiomWitnessContext M baseWitnessList baseContext ->
  RawCoqRestrictedPADerivationSoundnessStrongPrefixDirectClosureRemainder
    M inputs replacement axiom closureCount ->
  RawCodedPALocalProofOf M
    (rawCoqRestrictedPADerivationSoundnessCarrierFinalizerDirectOpenContext
      M inputs baseContext axiom)
    (rawCoqRestrictedPADerivationSoundnessCarrierFinalizerLtSelfSuccDirectCode
      M inputs)
    arithmeticRoot ->
  RawCodedPALocalProofOf M
    (rawPAInductionExtendedContext M baseContext axiom)
    (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixFinalizerDirectCode
      M inputs)
    (rawCoqRestrictedPADerivationSoundnessCarrierFinalizerDirectRoot
      M inputs baseContext axiom arithmeticRoot).
Proof.
  intros M hPA inputs replacement axiom closureCount
    baseWitnessList baseContext arithmeticRoot hbase hremainder harithmetic.
  pose proof
    (raw_coqRestrictedPADerivationSoundnessCarrierFinalizerDirect_extendedContext_witnessed
      M hPA inputs replacement axiom closureCount
      baseWitnessList baseContext hbase hremainder) as hextended.
  apply
    (raw_codedPALocalProofOf_coqRestrictedPADerivationSoundnessCarrierFinalizerDirect_of_ltSelfSucc
      M hPA inputs baseContext axiom arithmeticRoot).
  - exact (raw_codedPAAxiomWitnessContext_context_realizable M
      (rawPAInductionExtendedWitnessList M baseWitnessList
        (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixDirectCode
          M inputs))
      (rawPAInductionExtendedContext M baseContext axiom)
      hextended).
  - exact
      (raw_coqRestrictedPADerivationSoundnessCarrierFinalizerDirectOpenContext_selfShift
        M hPA inputs replacement axiom closureCount
        baseWitnessList baseContext hbase hremainder).
  - exact harithmetic.
Qed.

(** Direct counterpart of the shell-level finalizer boundary.  Defining it
    here keeps clients independent of the concrete root graph above. *)
Definition
    RawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixFinalizerDirectRootCompiler
    (M : RawPAModel)
    (inputs : RawCodedTemplateDirectStructuralInputs M) : Prop :=
  forall replacement axiom closureCount baseWitnessList baseContext,
    RawCodedPAAxiomWitnessContext M baseWitnessList baseContext ->
    RawCoqRestrictedPADerivationSoundnessStrongPrefixDirectClosureRemainder
      M inputs replacement axiom closureCount ->
    exists finalizerRoot : M,
      RawCodedPALocalProofOf M
        (rawPAInductionExtendedContext M baseContext axiom)
        (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixFinalizerDirectCode
          M inputs)
        finalizerRoot.

Arguments
  RawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixFinalizerDirectRootCompiler
  M inputs : clear implicits.

Theorem
    raw_coqRestrictedPADerivationSoundnessCarrierStrongPrefixFinalizerDirectRootCompiler_of_ltSelfSucc
    : forall (M : RawPAModel), RawPASatisfies M -> forall
      (inputs : RawCodedTemplateDirectStructuralInputs M),
  RawCoqRestrictedPADerivationSoundnessCarrierFinalizerLtSelfSuccDirectRootCompiler
    M inputs ->
  RawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixFinalizerDirectRootCompiler
    M inputs.
Proof.
  intros M hPA inputs harithmeticCompiler.
  unfold
    RawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixFinalizerDirectRootCompiler.
  intros replacement axiom closureCount baseWitnessList baseContext
    hbase hremainder.
  destruct (harithmeticCompiler replacement axiom closureCount
    baseWitnessList baseContext hbase hremainder) as
    [arithmeticRoot harithmetic].
  exists (rawCoqRestrictedPADerivationSoundnessCarrierFinalizerDirectRoot
    M inputs baseContext axiom arithmeticRoot).
  exact
    (raw_codedPALocalProofOf_coqRestrictedPADerivationSoundnessCarrierFinalizerDirect_from_exact_arithmetic_leaf
      M hPA inputs replacement axiom closureCount
      baseWitnessList baseContext arithmeticRoot
      hbase hremainder harithmetic).
Qed.

End
  PABoundedRawCodedRestrictedPADerivationSoundnessCarrierStrongPrefixFinalizerCompilationDirect.
