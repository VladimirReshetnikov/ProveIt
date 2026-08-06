(**
  Retain the direct strong-step premises below guarded truth binders.

  The direct endpoint shell opens eight existential witnesses before rule
  dispatch.  Its restricted-proof and rule-validity assumptions therefore
  occur in the endpoint tail after eight shifts.  The implication and
  Boolean guarded truth constructors then open five more witnesses.  This
  module records that composition literally: the guarded assumption leaves
  prove the fivefold shift of the already eightfold-renamed premises.

  We deliberately compile fresh represented assumption leaves from context
  membership.  Renaming an existing represented proof would require a much
  stronger proof-code naturality theorem and would obscure the only fact
  used here: shifted caller assumptions remain members of the shifted caller
  suffix.
*)

From Stdlib Require Import List.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA.
From BoundedPAConsistency Require Import
  RawCodedRestrictedPAProof
  RawCodedLtSuccCasesProofCompilation
  RawCodedPALocalProofExistentialEliminationChain
  RawCodedPALocalProofUniversalIntroductionChain
  RawCodedTemplateSyntax
  RawCodedTemplateProofCompiler
  RawCodedTemplateProofCompilerSelfShiftTail
  RawCodedTemplateDirectStructuralTranslation
  RawCodedRestrictedPAConsistencyFromUniversalSoundness
  RawCodedStrongStepProofEndpointAtomicAdequacyProofCompilation
  RawCodedRestrictedPADerivationSoundnessDirectRuleDispatchFrontier
  RawCodedRestrictedPADerivationSoundnessDirectStrongStepShell
  RawCodedDynamicTruthImpGuardedPredecessorExclusivityCompilation
  RawCodedDynamicTruthBooleanGuardedBranchExclusivity
  RawCodedDynamicTruthBooleanGuardedDiagonalCompilation
  RawCodedDynamicTruthNativeZeroGuardedPredecessorCompilation
  RawCodedDynamicTruthNativeZeroBooleanGuardedParentCompilation.

Module
  PABoundedRawCodedDynamicTruthNativeDirectStrongStepGuardedPremiseIntegration.

Import ListNotations.
Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedLtSuccCasesProofCompilation.
Import PABoundedRawCodedPALocalProofExistentialEliminationChain.
Import PABoundedRawCodedPALocalProofUniversalIntroductionChain.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedTemplateProofCompilerSelfShiftTail.
Import PABoundedRawCodedTemplateDirectStructuralTranslation.
Import PABoundedRawCodedRestrictedPAConsistencyFromUniversalSoundness.
Import
  PABoundedRawCodedStrongStepProofEndpointAtomicAdequacyProofCompilation.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectRuleDispatchFrontier.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectStrongStepShell.
Import
  PABoundedRawCodedDynamicTruthImpGuardedPredecessorExclusivityCompilation.
Import PABoundedRawCodedDynamicTruthBooleanGuardedBranchExclusivity.
Import PABoundedRawCodedDynamicTruthBooleanGuardedDiagonalCompilation.
Import
  PABoundedRawCodedDynamicTruthNativeZeroGuardedPredecessorCompilation.
Import
  PABoundedRawCodedDynamicTruthNativeZeroBooleanGuardedParentCompilation.

(** A caller assumption remains directly compilable after any finite binder
    block and below any fixed constructor-local prefix.  The output is put in
    the standard growing-proof interface even though this canonical
    assumption leaf does not enlarge the witnessed PA tail. *)
Theorem
    raw_codedPAGrowingTemplateLocalProofAt_of_shifted_assumption_under_fixed_prefix :
    forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
      (translation : RawCodedTemplateTranslation M)
      binderCount witnessList baseContext fixedPrefix callerPrefix formula,
  RawCodedPAAxiomWitnessContext M witnessList baseContext ->
  In formula callerPrefix ->
  RawCodedPAGrowingTemplateLocalProofAt M translation
    witnessList baseContext
    (fixedPrefix ++ templateContextShiftMany binderCount callerPrefix)
    (rawTemplateFormula translation
      (templateFormulaShiftMany binderCount formula)).
Proof.
  intros M hPA translation binderCount witnessList baseContext
    fixedPrefix callerPrefix formula hbase hmember.
  exists witnessList, baseContext.
  exists (rawTemplateProofCodeOnTail translation baseContext
    (trpAss
      (fixedPrefix ++ templateContextShiftMany binderCount callerPrefix)
      (templateFormulaShiftMany binderCount formula))).
  split; [exact hbase |].
  split.
  - intros member hmember'. exact hmember'.
  - apply (raw_templateAssumptionOnPAAxiomContext_localProof
      M hPA translation witnessList baseContext
      (fixedPrefix ++ templateContextShiftMany binderCount callerPrefix)
      (templateFormulaShiftMany binderCount formula) hbase).
    apply in_or_app. right.
    exact (templateContextShiftMany_member
      binderCount callerPrefix formula hmember).
Qed.

(** The caller prefix present at the deepest direct strong-step endpoint.
    Giving it a name keeps the 8+5 shift accounting visible in all six
    guarded specializations below. *)
Definition rawCoqRestrictedPADirectStrongStepDeepEndpointTail
    (tail : TemplateContext) : TemplateContext :=
  rawCoqRestrictedPADirectEndpointDeepTail
    (rawCoqRestrictedPADirectStrongStepEndpointTail tail).

Arguments rawCoqRestrictedPADirectStrongStepDeepEndpointTail
  tail : clear implicits.

(** All premise roots needed by the guarded collision constructor.  Each
    field uses the literal constructor-specific prefix, because implication,
    conjunction, and disjunction guards are not interchangeable. *)
Record RawCoqRestrictedPADirectStrongStepGuardedPremiseRootsAt
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    (witnessList baseContext : M) (tail : TemplateContext) : Prop := {
  rawCoqRestrictedPADirectStrongStepGuardedPremise_imp_restricted :
    RawCodedPAGrowingTemplateLocalProofAt M
      (rawDirectStructuralTemplateTranslation M hPA inputs)
      witnessList baseContext
      (coqDynamicTruthImpGuardedDeepPrefix
        (rawCoqRestrictedPADirectStrongStepDeepEndpointTail tail))
      (rawDirectTemplateFormula inputs
        (templateFormulaShiftMany 5
          (rawCoqTemplateRenameN 8
            coqRestrictedPADerivationSoundnessRestrictedProofTemplate)));
  rawCoqRestrictedPADirectStrongStepGuardedPremise_imp_rule :
    RawCodedPAGrowingTemplateLocalProofAt M
      (rawDirectStructuralTemplateTranslation M hPA inputs)
      witnessList baseContext
      (coqDynamicTruthImpGuardedDeepPrefix
        (rawCoqRestrictedPADirectStrongStepDeepEndpointTail tail))
      (rawDirectTemplateFormula inputs
        (templateFormulaShiftMany 5
          (rawCoqTemplateRenameN 8
            coqStrongStepProofEndpointAtomicAdequacyRulePremise)));
  rawCoqRestrictedPADirectStrongStepGuardedPremise_and_restricted :
    RawCodedPAGrowingTemplateLocalProofAt M
      (rawDirectStructuralTemplateTranslation M hPA inputs)
      witnessList baseContext
      (coqDynamicTruthBooleanGuardedDeepPrefix DTBooleanAnd
        (rawCoqRestrictedPADirectStrongStepDeepEndpointTail tail))
      (rawDirectTemplateFormula inputs
        (templateFormulaShiftMany 5
          (rawCoqTemplateRenameN 8
            coqRestrictedPADerivationSoundnessRestrictedProofTemplate)));
  rawCoqRestrictedPADirectStrongStepGuardedPremise_and_rule :
    RawCodedPAGrowingTemplateLocalProofAt M
      (rawDirectStructuralTemplateTranslation M hPA inputs)
      witnessList baseContext
      (coqDynamicTruthBooleanGuardedDeepPrefix DTBooleanAnd
        (rawCoqRestrictedPADirectStrongStepDeepEndpointTail tail))
      (rawDirectTemplateFormula inputs
        (templateFormulaShiftMany 5
          (rawCoqTemplateRenameN 8
            coqStrongStepProofEndpointAtomicAdequacyRulePremise)));
  rawCoqRestrictedPADirectStrongStepGuardedPremise_or_restricted :
    RawCodedPAGrowingTemplateLocalProofAt M
      (rawDirectStructuralTemplateTranslation M hPA inputs)
      witnessList baseContext
      (coqDynamicTruthBooleanGuardedDeepPrefix DTBooleanOr
        (rawCoqRestrictedPADirectStrongStepDeepEndpointTail tail))
      (rawDirectTemplateFormula inputs
        (templateFormulaShiftMany 5
          (rawCoqTemplateRenameN 8
            coqRestrictedPADerivationSoundnessRestrictedProofTemplate)));
  rawCoqRestrictedPADirectStrongStepGuardedPremise_or_rule :
    RawCodedPAGrowingTemplateLocalProofAt M
      (rawDirectStructuralTemplateTranslation M hPA inputs)
      witnessList baseContext
      (coqDynamicTruthBooleanGuardedDeepPrefix DTBooleanOr
        (rawCoqRestrictedPADirectStrongStepDeepEndpointTail tail))
      (rawDirectTemplateFormula inputs
        (templateFormulaShiftMany 5
          (rawCoqTemplateRenameN 8
            coqStrongStepProofEndpointAtomicAdequacyRulePremise)))
}.

Arguments RawCoqRestrictedPADirectStrongStepGuardedPremiseRootsAt
  M hPA inputs witnessList baseContext tail : clear implicits.

(** The two endpoint membership facts are enough to build all six guarded
    roots.  The proof has no semantic or rule-dispatch premise. *)
Theorem raw_coqRestrictedPADirectStrongStep_guardedPremiseRoots :
    forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
      (inputs : RawCodedTemplateDirectStructuralInputs M)
      tail witnessList baseContext,
  RawCodedPAAxiomWitnessContext M witnessList baseContext ->
  RawCoqRestrictedPADirectStrongStepGuardedPremiseRootsAt
    M hPA inputs witnessList baseContext tail.
Proof.
  intros M hPA inputs tail witnessList baseContext hbase.
  constructor.
  - rewrite coqDynamicTruthImpGuardedDeepPrefix_split.
    apply
      (raw_codedPAGrowingTemplateLocalProofAt_of_shifted_assumption_under_fixed_prefix
        M hPA (rawDirectStructuralTemplateTranslation M hPA inputs)
        5 witnessList baseContext coqDynamicTruthImpGuardedFixedDeepPrefix
        (rawCoqRestrictedPADirectStrongStepDeepEndpointTail tail)
        (rawCoqTemplateRenameN 8
          coqRestrictedPADerivationSoundnessRestrictedProofTemplate)
        hbase).
    exact
      (raw_coqRestrictedPADirectStrongStepDeepEndpointTail_restricted_member
        tail).
  - rewrite coqDynamicTruthImpGuardedDeepPrefix_split.
    apply
      (raw_codedPAGrowingTemplateLocalProofAt_of_shifted_assumption_under_fixed_prefix
        M hPA (rawDirectStructuralTemplateTranslation M hPA inputs)
        5 witnessList baseContext coqDynamicTruthImpGuardedFixedDeepPrefix
        (rawCoqRestrictedPADirectStrongStepDeepEndpointTail tail)
        (rawCoqTemplateRenameN 8
          coqStrongStepProofEndpointAtomicAdequacyRulePremise) hbase).
    exact
      (raw_coqRestrictedPADirectStrongStepDeepEndpointTail_rule_member tail).
  - rewrite coqDynamicTruthBooleanGuardedDeepPrefix_split.
    apply
      (raw_codedPAGrowingTemplateLocalProofAt_of_shifted_assumption_under_fixed_prefix
        M hPA (rawDirectStructuralTemplateTranslation M hPA inputs)
        5 witnessList baseContext
        (coqDynamicTruthBooleanGuardedFixedDeepPrefix DTBooleanAnd)
        (rawCoqRestrictedPADirectStrongStepDeepEndpointTail tail)
        (rawCoqTemplateRenameN 8
          coqRestrictedPADerivationSoundnessRestrictedProofTemplate)
        hbase).
    exact
      (raw_coqRestrictedPADirectStrongStepDeepEndpointTail_restricted_member
        tail).
  - rewrite coqDynamicTruthBooleanGuardedDeepPrefix_split.
    apply
      (raw_codedPAGrowingTemplateLocalProofAt_of_shifted_assumption_under_fixed_prefix
        M hPA (rawDirectStructuralTemplateTranslation M hPA inputs)
        5 witnessList baseContext
        (coqDynamicTruthBooleanGuardedFixedDeepPrefix DTBooleanAnd)
        (rawCoqRestrictedPADirectStrongStepDeepEndpointTail tail)
        (rawCoqTemplateRenameN 8
          coqStrongStepProofEndpointAtomicAdequacyRulePremise) hbase).
    exact
      (raw_coqRestrictedPADirectStrongStepDeepEndpointTail_rule_member tail).
  - rewrite coqDynamicTruthBooleanGuardedDeepPrefix_split.
    apply
      (raw_codedPAGrowingTemplateLocalProofAt_of_shifted_assumption_under_fixed_prefix
        M hPA (rawDirectStructuralTemplateTranslation M hPA inputs)
        5 witnessList baseContext
        (coqDynamicTruthBooleanGuardedFixedDeepPrefix DTBooleanOr)
        (rawCoqRestrictedPADirectStrongStepDeepEndpointTail tail)
        (rawCoqTemplateRenameN 8
          coqRestrictedPADerivationSoundnessRestrictedProofTemplate)
        hbase).
    exact
      (raw_coqRestrictedPADirectStrongStepDeepEndpointTail_restricted_member
        tail).
  - rewrite coqDynamicTruthBooleanGuardedDeepPrefix_split.
    apply
      (raw_codedPAGrowingTemplateLocalProofAt_of_shifted_assumption_under_fixed_prefix
        M hPA (rawDirectStructuralTemplateTranslation M hPA inputs)
        5 witnessList baseContext
        (coqDynamicTruthBooleanGuardedFixedDeepPrefix DTBooleanOr)
        (rawCoqRestrictedPADirectStrongStepDeepEndpointTail tail)
        (rawCoqTemplateRenameN 8
          coqStrongStepProofEndpointAtomicAdequacyRulePremise) hbase).
    exact
      (raw_coqRestrictedPADirectStrongStepDeepEndpointTail_rule_member tail).
Qed.

(** For the two fixed binder counts used here, the nested shift is literally
    the thirteenfold shift.  This is an explanatory normalization lemma; the
    guarded root record retains the compositional 5-after-8 form because it
    mirrors the two independently defined context layers. *)
Lemma raw_coqTemplateShiftFive_after_renameEight : forall formula,
  templateFormulaShiftMany 5 (rawCoqTemplateRenameN 8 formula) =
    templateFormulaShiftMany 13 formula.
Proof.
  intro formula.
  cbn [rawCoqTemplateRenameN templateFormulaShiftMany].
  reflexivity.
Qed.

End
  PABoundedRawCodedDynamicTruthNativeDirectStrongStepGuardedPremiseIntegration.
