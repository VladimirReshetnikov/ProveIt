(**
  Downstream dispatcher integration for the admissibility-aware Bottom-E
  compiler.

  The original direct dispatcher asks for a semantic contradiction law in
  its Bottom-E slot.  The native recursive truth construction instead gives
  something both stronger and more honest: the exact implication root for
  the Bottom-E rule case, with admissibility retained in the conclusion.
  Replacing the old semantic law by that exact root cannot be expressed by
  the old twenty-three-field record without inventing an implication in the
  wrong direction.

  This file therefore introduces a V2 residual.  Seven fields are the small
  independently selected prefix of the existing semantic package; the eighth
  is the already-audited sixteen-field continuation after Bottom-E.  The
  Bottom field is an exact member of the seventeen-case implication family.
  Dispatch uses the existing case theorem in every other branch and returns
  the stored proof verbatim in the Bottom branch.

  The second half mirrors only the affine growing-tail combinators needed to
  reach that V2 package.  Bottom compilation runs first, the continuation is
  run on the enlarged tail, and the single exact Bottom implication is then
  transported through the continuation suffix.  No old contradiction-law
  premise is reconstructed, and no import points back from an existing rule
  module to this downstream integration.
*)

From Stdlib Require Import List.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAListCoding Require Import Representability.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA.
From BoundedPAConsistency Require Import
  CodedProof
  RawCodedSyntaxConstructors
  RawCodedContextLists
  RawCodedRestrictedPAProof
  RawCodedPALocalProofExistential
  RawCodedPAProvability
  RawCodedPAAxiomWitness
  RawCodedPAAxiomWitnessPrefix
  RawCodedPAInductionAxiomCertificate
  RawCodedTemplateSyntax
  RawCodedTemplateProofCompiler
  RawCodedTemplatePAEmbedding
  RawCodedTemplateDirectStructuralTranslation
  RawCodedTemplateDirectStructuralPAAgreement
  RawCodedTemplateLocalProofStandardWitnessTailTransport
  RawCodedPALocalProofWitnessedContextMerge
  RawCodedPALocalProofWitnessedContextMergeTransportComplete
  RawCodedRestrictedPADerivationSoundnessCarrierStrongPrefixDirectInductionShell
  RawCodedRestrictedPADerivationSoundnessCarrierStrongPrefixFinalizerCompilationDirect
  RawCodedRestrictedPADerivationSoundnessCarrierStrongPrefixGrowingFinalizer
  RawCodedRestrictedPADerivationSoundnessCarrierStrongPrefixGrowingIntegrationDirect
  RawCodedRestrictedPADerivationSoundnessDirectRuleDispatchFrontier
  RawCodedRestrictedPADerivationSoundnessDirectStrongStepShell
  RawCodedRestrictedPADerivationSoundnessDirectAssumptionCase
  RawCodedRestrictedPADerivationSoundnessDirectImpIntroductionCase
  RawCodedRestrictedPADerivationSoundnessDirectImpEliminationCase
  RawCodedRestrictedPADerivationSoundnessDirectBottomEliminationCase
  RawCodedRestrictedPADerivationSoundnessDirectExcludedMiddleCase
  RawCodedRestrictedPADerivationSoundnessDirectAndIntroductionCase
  RawCodedRestrictedPADerivationSoundnessDirectAndEliminationLeftCase
  RawCodedRestrictedPADerivationSoundnessDirectAndEliminationRightCase
  RawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftCase
  RawCodedRestrictedPADerivationSoundnessDirectOrIntroductionRightCase
  RawCodedRestrictedPADerivationSoundnessDirectOrEliminationCase
  RawCodedRestrictedPADerivationSoundnessDirectUniversalIntroductionCase
  RawCodedRestrictedPADerivationSoundnessDirectUniversalEliminationCase
  RawCodedRestrictedPADerivationSoundnessDirectExistentialIntroductionCase
  RawCodedRestrictedPADerivationSoundnessDirectExistentialEliminationCase
  RawCodedRestrictedPADerivationSoundnessDirectEqualityReflexivityCase
  RawCodedRestrictedPADerivationSoundnessDirectEqualityEliminationCase
  RawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftOpenedCoverageCompilation
  RawCodedRestrictedPADerivationSoundnessAssumptionNativeFieldCompilation
  RawCodedRestrictedPADerivationSoundnessDirectRuleCasesAfterAssumption
  RawCodedRestrictedPADerivationSoundnessDirectRuleCasesAfterOrIntroductionLeftTruth
  RawCodedRestrictedPADerivationSoundnessDirectRuleCasesAfterImpIntroductionRecursive
  RawCodedRestrictedPADerivationSoundnessDirectRuleCasesAfterImpIntroductionTruth
  RawCodedRestrictedPADerivationSoundnessDirectRuleCasesAfterImpElimination
  RawCodedRestrictedPADerivationSoundnessDirectRuleCasesAfterBottomElimination
  RawCodedRestrictedPADerivationSoundnessDirectBottomAdmissibilityAwareCompletion.

Import ListNotations.

Module
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectBottomAdmissibilityAwareDispatcherIntegration.

Import PA.
Import PAListRepresentability.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PABoundedCodedProof.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedContextLists.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPAProvability.
Import PABoundedRawCodedPAAxiomWitness.
Import PABoundedRawCodedPAAxiomWitnessPrefix.
Import PABoundedRawCodedPAInductionAxiomCertificate.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedTemplatePAEmbedding.
Import PABoundedRawCodedTemplateDirectStructuralTranslation.
Import PABoundedRawCodedTemplateDirectStructuralPAAgreement.
Import PABoundedRawCodedTemplateLocalProofStandardWitnessTailTransport.
Import PABoundedRawCodedPALocalProofWitnessedContextMerge.
Import
  PABoundedRawCodedPALocalProofWitnessedContextMergeTransportComplete.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessCarrierStrongPrefixDirectInductionShell.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessCarrierStrongPrefixFinalizerCompilationDirect.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessCarrierStrongPrefixGrowingFinalizer.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessCarrierStrongPrefixGrowingIntegrationDirect.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectRuleDispatchFrontier.
Import PABoundedRawCodedRestrictedPADerivationSoundnessDirectStrongStepShell.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectAssumptionCase.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectImpIntroductionCase.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectImpEliminationCase.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectBottomEliminationCase.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectExcludedMiddleCase.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndIntroductionCase.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndEliminationLeftCase.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndEliminationRightCase.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftCase.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrIntroductionRightCase.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrEliminationCase.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectUniversalIntroductionCase.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectUniversalEliminationCase.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectExistentialIntroductionCase.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectExistentialEliminationCase.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectEqualityReflexivityCase.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectEqualityEliminationCase.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftOpenedCoverageCompilation.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessAssumptionNativeFieldCompilation.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectRuleCasesAfterAssumption.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectRuleCasesAfterOrIntroductionLeftTruth.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectRuleCasesAfterImpIntroductionRecursive.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectRuleCasesAfterImpIntroductionTruth.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectRuleCasesAfterImpElimination.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectRuleCasesAfterBottomElimination.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectBottomAdmissibilityAwareCompletion.

(** ------------------------------------------------------------------
    The exact Bottom dispatcher slot and its affine transport. *)

Definition RawCoqRestrictedPADirectStrongStepBottomCaseImplicationRoot
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    (tail : TemplateContext) : Prop :=
  exists root : M,
    RawCodedPALocalProofOf M
      (rawTemplateContextCode
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        (rawCoqRestrictedPADirectEndpointWitnessBodyTemplate ::
          rawCoqRestrictedPADirectEndpointDeepTail
            (rawCoqRestrictedPADirectStrongStepEndpointTail tail)))
      (rawFormulaImpCode M
        (rawDirectTemplateFormula inputs
          (rawCoqRestrictedPAProofRuleCaseTemplate
            rawCoqRuleBottomElimination
            (liftTerm 8 (tVar 4)) (tVar 7) (liftTerm 8 (tVar 2))
            (tVar 6) (tVar 5) (tVar 4) (tVar 3)
            (tVar 2) (tVar 1) (tVar 0)))
        (rawDirectTemplateFormula inputs
          (rawCoqTemplateRenameN 8
            rawCoqRestrictedPADirectStrongStepRemainingTemplate)))
      root.

Arguments RawCoqRestrictedPADirectStrongStepBottomCaseImplicationRoot
  M hPA inputs tail : clear implicits.

(** The compact Bottom deep context is a fixed prefix followed by the
    embedded standard-axiom tail.  Deriving this from the existing case
    context lemma avoids unfolding the enormous renamed remaining formula. *)
Lemma coqRestrictedPADirectBottomDeepContext_app_witnesses :
  forall witnesses,
  coqRestrictedPADirectBottomDeepContext
      (embedPAContext (map witnessedAxiom witnesses)) =
  coqRestrictedPADirectBottomDeepContext [] ++
    embedPAContext (map witnessedAxiom witnesses).
Proof.
  intro witnesses.
  pose proof
    (coqRestrictedPADirectBottomCaseContext_app_witnesses witnesses)
    as hcase.
  pose proof (f_equal (skipn 1) hcase) as hdeep.
  unfold coqRestrictedPADirectBottomCaseContext in hdeep.
  cbn [skipn List.app] in hdeep.
  exact hdeep.
Qed.

(** Convert the compact conclusion of the admissibility-aware producer to
    the literal component type selected by the strong-step dispatcher. *)
Lemma raw_bottomStrongStepCaseImplicationRoot_of_compact : forall
    (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (inputs : RawCodedTemplateDirectStructuralInputs M) tail root,
  RawCodedPALocalProofOf M
    (rawTemplateContextCode
      (rawDirectStructuralTemplateTranslation M hPA inputs)
      (coqRestrictedPADirectBottomDeepContext tail))
    (rawFormulaImpCode M
      (rawDirectTemplateFormula inputs
        coqRestrictedPADirectBottomCaseTemplate)
      (rawDirectTemplateFormula inputs
        coqRestrictedPADirectBottomRemainingTemplate))
    root ->
  RawCoqRestrictedPADirectStrongStepBottomCaseImplicationRoot
    M hPA inputs tail.
Proof.
  intros M hPA inputs tail root hroot.
  unfold RawCoqRestrictedPADirectStrongStepBottomCaseImplicationRoot.
  exists root.
  unfold coqRestrictedPADirectBottomDeepContext in hroot.
  rewrite raw_coqRestrictedPADirectEndpointDeepContext_shape in hroot.
  rewrite <- coqRestrictedPADirectBottom_remaining_shape.
  exact hroot.
Qed.

(** Transport exactly one Bottom implication through independently selected
    standard witnesses.  Nothing about the other sixteen rule cases is
    transported here. *)
Theorem raw_bottomStrongStepCaseImplicationRoot_surround_witnessed_tail :
  forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    prefix witnesses suffix,
  RawCoqRestrictedPADirectStrongStepBottomCaseImplicationRoot
    M hPA inputs (embedPAContext (map witnessedAxiom witnesses)) ->
  RawCoqRestrictedPADirectStrongStepBottomCaseImplicationRoot
    M hPA inputs
      (embedPAContext
        (map witnessedAxiom (prefix ++ (witnesses ++ suffix)))).
Proof.
  intros M hPA inputs prefix witnesses suffix [root hroot].
  rewrite <- raw_coqRestrictedPADirectEndpointDeepContext_shape in hroot.
  rewrite <- coqRestrictedPADirectBottom_remaining_shape in hroot.
  change (RawCodedPALocalProofOf M
    (rawTemplateContextCode
      (rawDirectStructuralTemplateTranslation M hPA inputs)
      (coqRestrictedPADirectBottomDeepContext
        (embedPAContext (map witnessedAxiom witnesses))))
    (rawFormulaImpCode M
      (rawDirectTemplateFormula inputs
        coqRestrictedPADirectBottomCaseTemplate)
      (rawDirectTemplateFormula inputs
        coqRestrictedPADirectBottomRemainingTemplate))
    root) in hroot.
  rewrite coqRestrictedPADirectBottomDeepContext_app_witnesses in hroot.
  destruct
    (raw_codedPALocalProof_standardWitnessTail_surround_under_prefix
      M hPA
      (rawDirectStructuralTemplateTranslation M hPA inputs)
      (rawDirectStructuralTemplatePAAgreement M hPA inputs)
      (coqRestrictedPADirectBottomDeepContext [])
      prefix witnesses suffix
      (rawFormulaImpCode M
        (rawDirectTemplateFormula inputs
          coqRestrictedPADirectBottomCaseTemplate)
        (rawDirectTemplateFormula inputs
          coqRestrictedPADirectBottomRemainingTemplate))
      root hroot) as [transportedRoot htransported].
  apply
    (raw_bottomStrongStepCaseImplicationRoot_of_compact
      M hPA inputs
      (embedPAContext
        (map witnessedAxiom (prefix ++ (witnesses ++ suffix))))
      transportedRoot).
  rewrite coqRestrictedPADirectBottomDeepContext_app_witnesses.
  exact htransported.
Qed.

(** ------------------------------------------------------------------
    Eight-field V2 semantic package and exact finite dispatch. *)

Record RawCoqRestrictedPADirectRuleCaseSemanticRootsV2
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    (tail : TemplateContext) : Prop := {
  rawCoqRestrictedPADirectRuleCasesV2_assumption :
    RawCoqRestrictedPADirectStrongStepAssumptionMembershipTruthLawRoot
      M hPA inputs tail;
  rawCoqRestrictedPADirectRuleCasesV2_impIntroductionRecursive :
    RawCoqRestrictedPADirectImpIntroductionRecursiveChildLawRoot
      M hPA inputs tail;
  rawCoqRestrictedPADirectRuleCasesV2_impIntroductionTruth :
    RawCoqRestrictedPADirectImpIntroductionDynamicTruthLawRoot
      M hPA inputs tail;
  rawCoqRestrictedPADirectRuleCasesV2_impElimination :
    RawCoqRestrictedPADirectImpERecursiveModusPonensLawRoot M
      (rawDirectStructuralTemplateTranslation M hPA inputs) tail;
  rawCoqRestrictedPADirectRuleCasesV2_bottomElimination :
    RawCoqRestrictedPADirectStrongStepBottomCaseImplicationRoot
      M hPA inputs tail;
  rawCoqRestrictedPADirectRuleCasesV2_orIntroductionLeftRecursive :
    RawCoqRestrictedPADirectOrIntroductionLeftRecursiveChildLawRoot
      M hPA inputs tail;
  rawCoqRestrictedPADirectRuleCasesV2_orIntroductionLeftTruth :
    RawCoqRestrictedPADirectOrIntroductionLeftDynamicTruthLawRoot
      M hPA inputs tail;
  rawCoqRestrictedPADirectRuleCasesV2_afterBottomElimination :
    RawCoqRestrictedPADirectRuleCaseSemanticRootsAfterBottomElimination
      M hPA inputs tail
}.

Arguments RawCoqRestrictedPADirectRuleCaseSemanticRootsV2
  M hPA inputs tail : clear implicits.

(** The selected Bottom constructor is the only branch that does not invoke
    an old semantic-case theorem.  Every other branch is byte-for-byte the
    same finite case selection as the original dispatcher. *)
Theorem
    raw_coqRestrictedPADirectStrongStepRuleCaseImplicationRoots_of_semantic_roots_v2 :
  forall (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M) tail,
  RawCoqRestrictedPADirectRuleCaseSemanticRootsV2 M hPA inputs tail ->
  RawCoqRestrictedPADirectStrongStepRuleCaseImplicationRoots
    M hPA inputs tail.
Proof.
  intros M hPA inputs tail hsemantic.
  destruct hsemantic as
    [hAssumption hImpIntroductionRecursive hImpIntroductionTruth
     hImpElimination hBottomElimination
     hOrIntroductionLeftRecursive hOrIntroductionLeftTruth hremaining].
  destruct hremaining as
    [hExcludedMiddle hAndIntroduction
     hAndEliminationLeftRecursive hAndEliminationLeftTruth
     hAndEliminationRightRecursive hAndEliminationRightTruth
     hOrIntroductionRightRecursive hOrIntroductionRightTruth
     hOrElimination hUniversalIntroduction
     hUniversalEliminationRecursive hUniversalEliminationTruth
     hExistentialIntroduction hExistentialElimination
     hEqualityReflexivity hEqualityElimination].
  apply (proj2
    (raw_coqRestrictedPADirectStrongStepRuleCaseImplicationRoots_view
      M hPA inputs tail)).
  intro selected.
  destruct selected.
  - exact
      (raw_coqRestrictedPADirectStrongStepAssumptionCaseImplicationRoot
        M hPA inputs tail hAssumption).
  - exact
      (raw_coqRestrictedPADirectStrongStepImpIntroductionCaseRoot
        M hPA inputs tail
        hImpIntroductionRecursive hImpIntroductionTruth).
  - exact
      (raw_coqRestrictedPADirectStrongStepImpEliminationCaseRoot
        M hPA inputs tail hImpElimination).
  - unfold RawCoqRestrictedPADirectStrongStepBottomCaseImplicationRoot
      in hBottomElimination.
    exact hBottomElimination.
  - exact
      (raw_coqRestrictedPADirectStrongStepExcludedMiddleCaseRoot
        M hPA inputs tail hExcludedMiddle).
  - exact
      (raw_coqRestrictedPADirectStrongStepAndIntroductionCaseImplicationRoot
        M hPA inputs tail hAndIntroduction).
  - exact
      (raw_coqRestrictedPADirectStrongStepAndEliminationLeftCaseRoot
        M hPA inputs tail
        hAndEliminationLeftRecursive hAndEliminationLeftTruth).
  - exact
      (raw_coqRestrictedPADirectStrongStepAndEliminationRightCaseRoot
        M hPA inputs tail
        hAndEliminationRightRecursive hAndEliminationRightTruth).
  - exact
      (raw_coqRestrictedPADirectStrongStepOrIntroductionLeftCaseRoot
        M hPA inputs tail
        hOrIntroductionLeftRecursive hOrIntroductionLeftTruth).
  - exact
      (raw_coqRestrictedPADirectStrongStepOrIntroductionRightCaseRoot
        M hPA inputs tail
        hOrIntroductionRightRecursive hOrIntroductionRightTruth).
  - exact
      (raw_coqRestrictedPADirectStrongStepOrEliminationCaseRoot
        M hPA inputs tail hOrElimination).
  - exact
      (raw_coqRestrictedPADirectStrongStepUniversalIntroductionCaseRoot
        M hPA inputs tail hUniversalIntroduction).
  - exact
      (raw_coqRestrictedPADirectStrongStepUniversalEliminationCaseRoot
        M hPA inputs tail
        hUniversalEliminationRecursive hUniversalEliminationTruth).
  - exact
      (raw_coqRestrictedPADirectStrongStepExistentialIntroductionCaseImplicationRoot
        M hPA inputs tail hExistentialIntroduction).
  - exact
      (raw_coqRestrictedPADirectStrongStepExistentialEliminationCaseRoot
        M hPA inputs tail hExistentialElimination).
  - exact
      (raw_coqRestrictedPADirectStrongStepEqualityReflexivityCaseRoot
        M hPA inputs tail hEqualityReflexivity).
  - exact
      (raw_coqRestrictedPADirectStrongStepEqualityEliminationCaseImplicationRoot
        M hPA inputs tail hEqualityElimination).
Qed.

Theorem
    raw_codedPALocalProofOf_coqRestrictedPADirectStrongStep_of_rule_case_semantic_roots_v2 :
  forall (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M) tail,
  RawCoqRestrictedPADirectRuleCaseSemanticRootsV2 M hPA inputs tail ->
  exists strongStepRoot : M,
    RawCodedPALocalProofOf M
      (rawTemplateContextCode
        (rawDirectStructuralTemplateTranslation M hPA inputs) tail)
      (rawCoqRestrictedPADerivationSoundnessCarrierStrongStepDirectCode
        M inputs)
      strongStepRoot.
Proof.
  intros M hPA inputs tail hsemantic.
  apply
    (raw_codedPALocalProofOf_coqRestrictedPADirectStrongStep
      M hPA inputs tail).
  exact
    (raw_coqRestrictedPADirectStrongStepRuleCaseImplicationRoots_of_semantic_roots_v2
      M hPA inputs tail hsemantic).
Qed.

(** The growing integration only needs the implication family, not the old
    semantic record.  Keeping this adapter at that weaker boundary makes the
    exact-Bottom dispatcher reusable by future case packages. *)
Theorem
    raw_codedPAProofOf_coqRestrictedPADerivationSoundnessUniversalDirect_of_rule_case_implication_roots_on_witnessed_tail :
  forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    (tail : TemplateContext)
    replacement axiom closureCount baseWitnessList,
  RawCodedPAAxiomWitnessContext M baseWitnessList
    (rawTemplateContextCode
      (rawDirectStructuralTemplateTranslation M hPA inputs) tail) ->
  RawCoqRestrictedPADerivationSoundnessStrongPrefixDirectClosureRemainder
    M inputs replacement axiom closureCount ->
  RawCoqRestrictedPADirectStrongStepRuleCaseImplicationRoots
    M hPA inputs tail ->
  exists soundnessCertificate : M,
    RawCodedPAProofOf M
      (rawCoqRestrictedPADerivationSoundnessUniversalDirectCode M inputs)
      soundnessCertificate.
Proof.
  intros M hPA inputs tail replacement axiom closureCount
    baseWitnessList hbase hremainder hcaseRoots.
  set (translation :=
    rawDirectStructuralTemplateTranslation M hPA inputs).
  set (baseContext := rawTemplateContextCode translation tail).
  set (extendedWitnessList :=
    rawPAInductionExtendedWitnessList M baseWitnessList
      (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixDirectCode
        M inputs)).
  set (extendedContext :=
    rawPAInductionExtendedContext M baseContext axiom).

  assert (hextended : RawCodedPAAxiomWitnessContext M
      extendedWitnessList extendedContext).
  {
    unfold extendedWitnessList, extendedContext, baseContext.
    exact
      (raw_coqRestrictedPADerivationSoundnessCarrierFinalizerDirect_extendedContext_witnessed
        M hPA inputs replacement axiom closureCount
        baseWitnessList
        (rawTemplateContextCode translation tail)
        hbase hremainder).
  }
  assert (hbaseRealizable : RawContextListRealizable M baseContext).
  {
    exact (raw_codedPAAxiomWitnessContext_context_realizable M
      baseWitnessList baseContext hbase).
  }
  assert (hextendedRealizable : RawContextListRealizable M extendedContext).
  {
    exact (raw_codedPAAxiomWitnessContext_context_realizable M
      extendedWitnessList extendedContext hextended).
  }
  assert (hbaseIncluded : RawContextListIncluded M
      baseContext extendedContext).
  {
    unfold extendedContext, rawPAInductionExtendedContext.
    apply (raw_contextListIncluded_cons_target M hPA
      baseContext baseContext axiom).
    exact (raw_contextListIncluded_refl M baseContext).
  }
  assert (hbaseReady : RawContextBinderReady M
      baseContext extendedContext).
  {
    exact (raw_contextBinderReady_witnessed_target M hPA
      baseContext extendedContext extendedWitnessList
      hbaseIncluded hextended).
  }

  destruct
    (raw_codedPALocalProofOf_coqRestrictedPADirectStrongStep
      M hPA inputs tail hcaseRoots)
    as [baseStrongStepRoot hbaseStrongStep].
  change (RawCodedPALocalProofOf M baseContext
    (rawCoqRestrictedPADerivationSoundnessCarrierStrongStepDirectCode
      M inputs) baseStrongStepRoot) in hbaseStrongStep.
  destruct
    (raw_codedPALocalProof_contextInclusionWeakening_of_binderReady
      M hPA baseContext extendedContext
      (rawCoqRestrictedPADerivationSoundnessCarrierStrongStepDirectCode
        M inputs)
      baseStrongStepRoot hbaseRealizable hextendedRealizable
      hbaseIncluded hbaseReady hbaseStrongStep)
    as [strongStepRoot hstrongStep].
  destruct
    (raw_codedPAProofOf_coqRestrictedPADerivationSoundnessUniversalDirect_of_growing_case_and_finalizer
      M hPA inputs replacement axiom closureCount
      baseWitnessList baseContext strongStepRoot
      hbase hremainder hstrongStep)
    as (prefix & zeroChild & stepChild & arithmeticOpenRoot & bodyChild &
      hsoundness).
  exists
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
  exact hsoundness.
Qed.

(** ------------------------------------------------------------------
    Nested V2 continuations.  Each record adds exactly one selected field. *)

Record RawCoqRestrictedPADirectRuleCaseSemanticRootsV2AfterImpElimination
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    (tail : TemplateContext) : Prop := {
  rawCoqRestrictedPADirectV2AfterImpE_bottomElimination :
    RawCoqRestrictedPADirectStrongStepBottomCaseImplicationRoot
      M hPA inputs tail;
  rawCoqRestrictedPADirectV2AfterImpE_remaining :
    RawCoqRestrictedPADirectRuleCaseSemanticRootsAfterBottomElimination
      M hPA inputs tail
}.

Record
    RawCoqRestrictedPADirectRuleCaseSemanticRootsV2AfterImpIntroductionTruth
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    (tail : TemplateContext) : Prop := {
  rawCoqRestrictedPADirectV2AfterImpTruth_impElimination :
    RawCoqRestrictedPADirectImpERecursiveModusPonensLawRoot M
      (rawDirectStructuralTemplateTranslation M hPA inputs) tail;
  rawCoqRestrictedPADirectV2AfterImpTruth_remaining :
    RawCoqRestrictedPADirectRuleCaseSemanticRootsV2AfterImpElimination
      M hPA inputs tail
}.

Record
    RawCoqRestrictedPADirectRuleCaseSemanticRootsV2AfterImpIntroductionRecursive
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    (tail : TemplateContext) : Prop := {
  rawCoqRestrictedPADirectV2AfterImpRecursive_impIntroductionTruth :
    RawCoqRestrictedPADirectImpIntroductionDynamicTruthLawRoot
      M hPA inputs tail;
  rawCoqRestrictedPADirectV2AfterImpRecursive_remaining :
    RawCoqRestrictedPADirectRuleCaseSemanticRootsV2AfterImpIntroductionTruth
      M hPA inputs tail
}.

Record
    RawCoqRestrictedPADirectRuleCaseSemanticRootsV2AfterOrIntroductionLeftTruth
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    (tail : TemplateContext) : Prop := {
  rawCoqRestrictedPADirectV2AfterOrLeftTruth_impIntroductionRecursive :
    RawCoqRestrictedPADirectImpIntroductionRecursiveChildLawRoot
      M hPA inputs tail;
  rawCoqRestrictedPADirectV2AfterOrLeftTruth_remaining :
    RawCoqRestrictedPADirectRuleCaseSemanticRootsV2AfterImpIntroductionRecursive
      M hPA inputs tail
}.

Record RawCoqRestrictedPADirectRuleCaseSemanticRootsV2AfterAssumption
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    (tail : TemplateContext) : Prop := {
  rawCoqRestrictedPADirectV2AfterAssumption_orIntroductionLeftTruth :
    RawCoqRestrictedPADirectOrIntroductionLeftDynamicTruthLawRoot
      M hPA inputs tail;
  rawCoqRestrictedPADirectV2AfterAssumption_remaining :
    RawCoqRestrictedPADirectRuleCaseSemanticRootsV2AfterOrIntroductionLeftTruth
      M hPA inputs tail
}.

Record RawCoqRestrictedPADirectRuleCaseSemanticRootsV2AfterOrIntroductionLeft
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    (tail : TemplateContext) : Prop := {
  rawCoqRestrictedPADirectV2AfterOrLeft_assumption :
    RawCoqRestrictedPADirectStrongStepAssumptionMembershipTruthLawRoot
      M hPA inputs tail;
  rawCoqRestrictedPADirectV2AfterOrLeft_remaining :
    RawCoqRestrictedPADirectRuleCaseSemanticRootsV2AfterAssumption
      M hPA inputs tail
}.

Arguments RawCoqRestrictedPADirectRuleCaseSemanticRootsV2AfterImpElimination
  M hPA inputs tail : clear implicits.
Arguments
  RawCoqRestrictedPADirectRuleCaseSemanticRootsV2AfterImpIntroductionTruth
  M hPA inputs tail : clear implicits.
Arguments
  RawCoqRestrictedPADirectRuleCaseSemanticRootsV2AfterImpIntroductionRecursive
  M hPA inputs tail : clear implicits.
Arguments
  RawCoqRestrictedPADirectRuleCaseSemanticRootsV2AfterOrIntroductionLeftTruth
  M hPA inputs tail : clear implicits.
Arguments RawCoqRestrictedPADirectRuleCaseSemanticRootsV2AfterAssumption
  M hPA inputs tail : clear implicits.
Arguments RawCoqRestrictedPADirectRuleCaseSemanticRootsV2AfterOrIntroductionLeft
  M hPA inputs tail : clear implicits.

Definition
    RawCoqRestrictedPADirectRemainingV2AfterImpEliminationStandardTailCompiler
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M) : Prop :=
  forall baseWitnesses : StandardPAAxiomWitnessPrefix,
  exists suffix : StandardPAAxiomWitnessPrefix,
    RawCoqRestrictedPADirectRuleCaseSemanticRootsV2AfterImpElimination
      M hPA inputs
      (embedPAContext
        (map witnessedAxiom (baseWitnesses ++ suffix))).

Definition
    RawCoqRestrictedPADirectRemainingV2AfterImpIntroductionTruthStandardTailCompiler
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M) : Prop :=
  forall baseWitnesses : StandardPAAxiomWitnessPrefix,
  exists suffix : StandardPAAxiomWitnessPrefix,
    RawCoqRestrictedPADirectRuleCaseSemanticRootsV2AfterImpIntroductionTruth
      M hPA inputs
      (embedPAContext
        (map witnessedAxiom (baseWitnesses ++ suffix))).

Definition
    RawCoqRestrictedPADirectRemainingV2AfterImpIntroductionRecursiveStandardTailCompiler
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M) : Prop :=
  forall baseWitnesses : StandardPAAxiomWitnessPrefix,
  exists suffix : StandardPAAxiomWitnessPrefix,
    RawCoqRestrictedPADirectRuleCaseSemanticRootsV2AfterImpIntroductionRecursive
      M hPA inputs
      (embedPAContext
        (map witnessedAxiom (baseWitnesses ++ suffix))).

Definition
    RawCoqRestrictedPADirectRemainingV2AfterOrIntroductionLeftTruthStandardTailCompiler
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M) : Prop :=
  forall baseWitnesses : StandardPAAxiomWitnessPrefix,
  exists suffix : StandardPAAxiomWitnessPrefix,
    RawCoqRestrictedPADirectRuleCaseSemanticRootsV2AfterOrIntroductionLeftTruth
      M hPA inputs
      (embedPAContext
        (map witnessedAxiom (baseWitnesses ++ suffix))).

Definition
    RawCoqRestrictedPADirectRemainingV2AfterAssumptionStandardTailCompiler
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M) : Prop :=
  forall baseWitnesses : StandardPAAxiomWitnessPrefix,
  exists suffix : StandardPAAxiomWitnessPrefix,
    RawCoqRestrictedPADirectRuleCaseSemanticRootsV2AfterAssumption
      M hPA inputs
      (embedPAContext
        (map witnessedAxiom (baseWitnesses ++ suffix))).

Definition RawCoqRestrictedPADirectRemainingRuleCasesV2StandardTailCompiler
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M) : Prop :=
  forall baseWitnesses : StandardPAAxiomWitnessPrefix,
  exists suffix : StandardPAAxiomWitnessPrefix,
    RawCoqRestrictedPADirectRuleCaseSemanticRootsV2AfterOrIntroductionLeft
      M hPA inputs
      (embedPAContext
        (map witnessedAxiom (baseWitnesses ++ suffix))).

Arguments
  RawCoqRestrictedPADirectRemainingV2AfterImpEliminationStandardTailCompiler
  M hPA inputs : clear implicits.
Arguments
  RawCoqRestrictedPADirectRemainingV2AfterImpIntroductionTruthStandardTailCompiler
  M hPA inputs : clear implicits.
Arguments
  RawCoqRestrictedPADirectRemainingV2AfterImpIntroductionRecursiveStandardTailCompiler
  M hPA inputs : clear implicits.
Arguments
  RawCoqRestrictedPADirectRemainingV2AfterOrIntroductionLeftTruthStandardTailCompiler
  M hPA inputs : clear implicits.
Arguments
  RawCoqRestrictedPADirectRemainingV2AfterAssumptionStandardTailCompiler
  M hPA inputs : clear implicits.
Arguments RawCoqRestrictedPADirectRemainingRuleCasesV2StandardTailCompiler
  M hPA inputs : clear implicits.

(** Synchronize the new Bottom producer with the old sixteen-case
    continuation.  The continuation sees every witness chosen by Bottom;
    Bottom's exact implication is then weakened through only the suffix
    chosen by that continuation. *)
Theorem
    raw_remainingV2AfterImpEliminationCompiler_of_admissibilityAwareBottom :
  forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (inputs : RawCodedTemplateDirectStructuralInputs M),
  RawCoqRestrictedPADirectBottomAdmissibilityAwareCaseStandardTailCompiler
    M hPA inputs ->
  RawCoqRestrictedPADirectRemainingAfterBottomEliminationStandardTailCompiler
    M hPA inputs ->
  RawCoqRestrictedPADirectRemainingV2AfterImpEliminationStandardTailCompiler
    M hPA inputs.
Proof.
  intros M hPA inputs hbottom hremaining baseWitnesses.
  destruct (hbottom baseWitnesses)
    as (bottomSuffix & bottomRoot & hbottomRoot).
  destruct (hremaining (baseWitnesses ++ bottomSuffix))
    as [remainingSuffix hremainingTail].
  exists (bottomSuffix ++ remainingSuffix).
  constructor.
  - pose proof
      (raw_bottomStrongStepCaseImplicationRoot_of_compact
        M hPA inputs
        (embedPAContext
          (map witnessedAxiom (baseWitnesses ++ bottomSuffix)))
        bottomRoot hbottomRoot) as hbottomExact.
    pose proof
      (raw_bottomStrongStepCaseImplicationRoot_surround_witnessed_tail
        M hPA inputs [] (baseWitnesses ++ bottomSuffix)
        remainingSuffix hbottomExact) as htransported.
    cbn [List.app] in htransported.
    replace ((baseWitnesses ++ bottomSuffix) ++ remainingSuffix)
      with (baseWitnesses ++ (bottomSuffix ++ remainingSuffix))
      in htransported by apply app_assoc.
    exact htransported.
  - replace ((baseWitnesses ++ bottomSuffix) ++ remainingSuffix)
      with (baseWitnesses ++ (bottomSuffix ++ remainingSuffix))
      in hremainingTail by apply app_assoc.
    exact hremainingTail.
Qed.

(** The five upstream merges are deliberately small copies of the existing
    continuation combinators.  Their only difference is the nested V2
    remainder carried unchanged in the second record field. *)
Theorem raw_remainingV2AfterImpIntroductionTruthCompiler_of_selectedImpECore :
  forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (inputs : RawCodedTemplateDirectStructuralInputs M),
  RawCoqRestrictedPADirectSelectedImpECoreTail M hPA inputs ->
  RawCoqRestrictedPADirectRemainingV2AfterImpEliminationStandardTailCompiler
    M hPA inputs ->
  RawCoqRestrictedPADirectRemainingV2AfterImpIntroductionTruthStandardTailCompiler
    M hPA inputs.
Proof.
  intros M hPA inputs
    (coreWitnesses & hcoreWitnessed & hcore) hremaining baseWitnesses.
  clear hcoreWitnessed.
  destruct (hremaining (baseWitnesses ++ coreWitnesses))
    as [suffix hremainingTail].
  exists (coreWitnesses ++ suffix).
  constructor.
  - apply raw_impERecursiveModusPonensLawRoot_of_coreLawRoot.
    exact (raw_impECoreLawRoot_surround_witnessed_tail
      M hPA inputs baseWitnesses coreWitnesses suffix hcore).
  - replace ((baseWitnesses ++ coreWitnesses) ++ suffix)
      with (baseWitnesses ++ (coreWitnesses ++ suffix))
      in hremainingTail by apply app_assoc.
    exact hremainingTail.
Qed.

Theorem
    raw_remainingV2AfterImpIntroductionRecursiveCompiler_of_selectedImpIntroductionTruth :
  forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (inputs : RawCodedTemplateDirectStructuralInputs M),
  RawCoqRestrictedPADirectSelectedImpIntroductionTruthTail M hPA inputs ->
  RawCoqRestrictedPADirectRemainingV2AfterImpIntroductionTruthStandardTailCompiler
    M hPA inputs ->
  RawCoqRestrictedPADirectRemainingV2AfterImpIntroductionRecursiveStandardTailCompiler
    M hPA inputs.
Proof.
  intros M hPA inputs
    (truthWitnesses & htruthWitnessed & htruth) hremaining baseWitnesses.
  clear htruthWitnessed.
  destruct (hremaining (baseWitnesses ++ truthWitnesses))
    as [suffix hremainingTail].
  exists (truthWitnesses ++ suffix).
  constructor.
  - exact (raw_impIntroductionTruthLawRoot_surround_witnessed_tail
      M hPA inputs baseWitnesses truthWitnesses suffix htruth).
  - replace ((baseWitnesses ++ truthWitnesses) ++ suffix)
      with (baseWitnesses ++ (truthWitnesses ++ suffix))
      in hremainingTail by apply app_assoc.
    exact hremainingTail.
Qed.

Corollary
    raw_remainingV2AfterImpIntroductionRecursiveCompiler_of_fixedRowSplit :
  forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (inputs : RawCodedTemplateDirectStructuralInputs M),
  RawCoqRestrictedPADirectSelectedImpIntroductionFixedRowSplitTail
    M hPA inputs ->
  RawCoqRestrictedPADirectRemainingV2AfterImpIntroductionTruthStandardTailCompiler
    M hPA inputs ->
  RawCoqRestrictedPADirectRemainingV2AfterImpIntroductionRecursiveStandardTailCompiler
    M hPA inputs.
Proof.
  intros M hPA inputs hsplit hremaining.
  exact
    (raw_remainingV2AfterImpIntroductionRecursiveCompiler_of_selectedImpIntroductionTruth
      M hPA inputs
      (raw_selectedImpIntroductionTruthTail_of_fixedRowSplit
        M hPA inputs hsplit)
      hremaining).
Qed.

Theorem
    raw_remainingV2AfterOrIntroductionLeftTruthCompiler_of_selectedImpIntroductionRecursive :
  forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (inputs : RawCodedTemplateDirectStructuralInputs M),
  RawCoqRestrictedPADirectSelectedImpIntroductionRecursiveTail
    M hPA inputs ->
  RawCoqRestrictedPADirectRemainingV2AfterImpIntroductionRecursiveStandardTailCompiler
    M hPA inputs ->
  RawCoqRestrictedPADirectRemainingV2AfterOrIntroductionLeftTruthStandardTailCompiler
    M hPA inputs.
Proof.
  intros M hPA inputs
    (recursiveWitnesses & hrecursiveWitnessed & hrecursive)
    hremaining baseWitnesses.
  clear hrecursiveWitnessed.
  destruct (hremaining (baseWitnesses ++ recursiveWitnesses))
    as [suffix hremainingTail].
  exists (recursiveWitnesses ++ suffix).
  constructor.
  - exact
      (raw_impIntroductionRecursiveChildLawRoot_surround_witnessed_tail
        M hPA inputs baseWitnesses recursiveWitnesses suffix hrecursive).
  - replace ((baseWitnesses ++ recursiveWitnesses) ++ suffix)
      with (baseWitnesses ++ (recursiveWitnesses ++ suffix))
      in hremainingTail by apply app_assoc.
    exact hremainingTail.
Qed.

Theorem raw_remainingV2AfterAssumptionCompiler_of_selectedOrIntroductionLeftTruth :
  forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (inputs : RawCodedTemplateDirectStructuralInputs M),
  RawCoqRestrictedPADirectSelectedOrIntroductionLeftTruthTail M hPA inputs ->
  RawCoqRestrictedPADirectRemainingV2AfterOrIntroductionLeftTruthStandardTailCompiler
    M hPA inputs ->
  RawCoqRestrictedPADirectRemainingV2AfterAssumptionStandardTailCompiler
    M hPA inputs.
Proof.
  intros M hPA inputs
    (orTruthWitnesses & horTruthWitnessed & horTruth)
    hremaining baseWitnesses.
  clear horTruthWitnessed.
  destruct (hremaining (baseWitnesses ++ orTruthWitnesses))
    as [suffix hremainingTail].
  exists (orTruthWitnesses ++ suffix).
  constructor.
  - exact
      (raw_orIntroductionLeftTruthLawRoot_surround_witnessed_tail
        M hPA inputs baseWitnesses orTruthWitnesses suffix horTruth).
  - replace ((baseWitnesses ++ orTruthWitnesses) ++ suffix)
      with (baseWitnesses ++ (orTruthWitnesses ++ suffix))
      in hremainingTail by apply app_assoc.
    exact hremainingTail.
Qed.

Theorem raw_remainingRuleCasesV2Compiler_of_selectedAssumption :
  forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (inputs : RawCodedTemplateDirectStructuralInputs M),
  RawCoqRestrictedPADirectSelectedAssumptionTail M hPA inputs ->
  RawCoqRestrictedPADirectRemainingV2AfterAssumptionStandardTailCompiler
    M hPA inputs ->
  RawCoqRestrictedPADirectRemainingRuleCasesV2StandardTailCompiler
    M hPA inputs.
Proof.
  intros M hPA inputs
    (assumptionWitnesses & hassumptionWitnessed & hassumption)
    hremaining baseWitnesses.
  clear hassumptionWitnessed.
  destruct (hremaining (baseWitnesses ++ assumptionWitnesses))
    as [suffix hremainingTail].
  exists (assumptionWitnesses ++ suffix).
  constructor.
  - exact (raw_assumptionLawRoot_surround_witnessed_tail
      M hPA inputs baseWitnesses assumptionWitnesses suffix hassumption).
  - replace ((baseWitnesses ++ assumptionWitnesses) ++ suffix)
      with (baseWitnesses ++ (assumptionWitnesses ++ suffix))
      in hremainingTail by apply app_assoc.
    exact hremainingTail.
Qed.

(** Compose the five explicit selected packages with the new Bottom merge.
    This extracted composition is the boundary expected by a later native
    producer: each repeated append argument appears in exactly one lemma. *)
Theorem raw_remainingRuleCasesV2Compiler_of_selected_prefix_and_bottom :
  forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (inputs : RawCodedTemplateDirectStructuralInputs M),
  RawCoqRestrictedPADirectSelectedAssumptionTail M hPA inputs ->
  RawCoqRestrictedPADirectSelectedOrIntroductionLeftTruthTail M hPA inputs ->
  RawCoqRestrictedPADirectSelectedImpIntroductionRecursiveTail M hPA inputs ->
  RawCoqRestrictedPADirectSelectedImpIntroductionTruthTail M hPA inputs ->
  RawCoqRestrictedPADirectSelectedImpECoreTail M hPA inputs ->
  RawCoqRestrictedPADirectBottomAdmissibilityAwareCaseStandardTailCompiler
    M hPA inputs ->
  RawCoqRestrictedPADirectRemainingAfterBottomEliminationStandardTailCompiler
    M hPA inputs ->
  RawCoqRestrictedPADirectRemainingRuleCasesV2StandardTailCompiler
    M hPA inputs.
Proof.
  intros M hPA inputs hassumption horTruth himpRecursive himpTruth
    himpE hbottom hremaining.
  apply (raw_remainingRuleCasesV2Compiler_of_selectedAssumption
    M hPA inputs hassumption).
  apply (raw_remainingV2AfterAssumptionCompiler_of_selectedOrIntroductionLeftTruth
    M hPA inputs horTruth).
  apply
    (raw_remainingV2AfterOrIntroductionLeftTruthCompiler_of_selectedImpIntroductionRecursive
      M hPA inputs himpRecursive).
  apply
    (raw_remainingV2AfterImpIntroductionRecursiveCompiler_of_selectedImpIntroductionTruth
      M hPA inputs himpTruth).
  apply (raw_remainingV2AfterImpIntroductionTruthCompiler_of_selectedImpECore
    M hPA inputs himpE).
  exact
    (raw_remainingV2AfterImpEliminationCompiler_of_admissibilityAwareBottom
      M hPA inputs hbottom hremaining).
Qed.

Corollary raw_remainingRuleCasesV2Compiler_of_fixedRowSplit_and_bottom :
  forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (inputs : RawCodedTemplateDirectStructuralInputs M),
  RawCoqRestrictedPADirectSelectedAssumptionTail M hPA inputs ->
  RawCoqRestrictedPADirectSelectedOrIntroductionLeftTruthTail M hPA inputs ->
  RawCoqRestrictedPADirectSelectedImpIntroductionRecursiveTail M hPA inputs ->
  RawCoqRestrictedPADirectSelectedImpIntroductionFixedRowSplitTail
    M hPA inputs ->
  RawCoqRestrictedPADirectSelectedImpECoreTail M hPA inputs ->
  RawCoqRestrictedPADirectBottomAdmissibilityAwareCaseStandardTailCompiler
    M hPA inputs ->
  RawCoqRestrictedPADirectRemainingAfterBottomEliminationStandardTailCompiler
    M hPA inputs ->
  RawCoqRestrictedPADirectRemainingRuleCasesV2StandardTailCompiler
    M hPA inputs.
Proof.
  intros M hPA inputs hassumption horTruth himpRecursive hsplit
    himpE hbottom hremaining.
  apply (raw_remainingRuleCasesV2Compiler_of_selectedAssumption
    M hPA inputs hassumption).
  apply (raw_remainingV2AfterAssumptionCompiler_of_selectedOrIntroductionLeftTruth
    M hPA inputs horTruth).
  apply
    (raw_remainingV2AfterOrIntroductionLeftTruthCompiler_of_selectedImpIntroductionRecursive
      M hPA inputs himpRecursive).
  apply
    (raw_remainingV2AfterImpIntroductionRecursiveCompiler_of_fixedRowSplit
      M hPA inputs hsplit).
  apply (raw_remainingV2AfterImpIntroductionTruthCompiler_of_selectedImpECore
    M hPA inputs himpE).
  exact
    (raw_remainingV2AfterImpEliminationCompiler_of_admissibilityAwareBottom
      M hPA inputs hbottom hremaining).
Qed.

(** The sixth and final affine merge selects Or-I-left recursion, transports
    it through the V2 continuation suffix, and flattens the nested records
    into the advertised eight fields. *)
Theorem raw_ruleCaseSemanticRootsV2_on_selected_witnessed_tail_of_remaining :
  forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (inputs : RawCodedTemplateDirectStructuralInputs M),
  RawCoqRestrictedPADirectRemainingRuleCasesV2StandardTailCompiler
    M hPA inputs ->
  exists witnesses : StandardPAAxiomWitnessPrefix,
    RawCodedPAAxiomWitnessContext M
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        witnesses (raw_zero M))
      (rawTemplateContextCode
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        (embedPAContext (map witnessedAxiom witnesses))) /\
    RawCoqRestrictedPADirectRuleCaseSemanticRootsV2 M hPA inputs
      (embedPAContext (map witnessedAxiom witnesses)).
Proof.
  intros M hPA inputs hremainingCompiler.
  destruct
    (raw_orIntroductionLeft_recursiveChildLawRoot_on_selected_witnessed_tail
      M hPA inputs)
    as (orWitnesses & horWitnessed & horRoot).
  clear horWitnessed.
  destruct (hremainingCompiler orWitnesses)
    as [suffix hremaining].
  set (witnesses := orWitnesses ++ suffix).
  exists witnesses. split.
  - unfold witnesses.
    exact (raw_directEmbeddedPAAxiomWitnessContext M hPA inputs
      (orWitnesses ++ suffix)).
  - unfold witnesses in *.
    destruct hremaining as [hassumption hafterAssumption].
    destruct hafterAssumption as [horTruth hafterOrTruth].
    destruct hafterOrTruth as [himpRecursive hafterImpRecursive].
    destruct hafterImpRecursive as [himpTruth hafterImpTruth].
    destruct hafterImpTruth as [himpE hafterImpE].
    destruct hafterImpE as [hbottom hafterBottom].
    constructor.
    + exact hassumption.
    + exact himpRecursive.
    + exact himpTruth.
    + exact himpE.
    + exact hbottom.
    + exact
        (raw_orIntroductionLeft_recursiveChildLawRoot_append_witnessed_tail
          M hPA inputs orWitnesses suffix horRoot).
    + exact horTruth.
    + exact hafterBottom.
Qed.

(** Final witnessed-tail endpoint.  It feeds the V2 implication family into
    the weaker growing adapter above, so no old semantic Bottom field is ever
    constructed. *)
Corollary
    raw_codedPAProofOf_coqRestrictedPADerivationSoundnessUniversalDirect_of_remaining_v2_after_orIntroductionLeft :
  forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (inputs : RawCodedTemplateDirectStructuralInputs M),
  RawCoqRestrictedPADirectRemainingRuleCasesV2StandardTailCompiler
    M hPA inputs ->
  forall replacement axiom closureCount,
  RawCoqRestrictedPADerivationSoundnessStrongPrefixDirectClosureRemainder
    M inputs replacement axiom closureCount ->
  exists soundnessCertificate : M,
    RawCodedPAProofOf M
      (rawCoqRestrictedPADerivationSoundnessUniversalDirectCode M inputs)
      soundnessCertificate.
Proof.
  intros M hPA inputs hremainingCompiler
    replacement axiom closureCount hremainder.
  destruct
    (raw_ruleCaseSemanticRootsV2_on_selected_witnessed_tail_of_remaining
      M hPA inputs hremainingCompiler)
    as (witnesses & hwitnessed & hsemantic).
  apply
    (raw_codedPAProofOf_coqRestrictedPADerivationSoundnessUniversalDirect_of_rule_case_implication_roots_on_witnessed_tail
      M hPA inputs
      (embedPAContext (map witnessedAxiom witnesses))
      replacement axiom closureCount
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        witnesses (raw_zero M))).
  - exact hwitnessed.
  - exact hremainder.
  - exact
      (raw_coqRestrictedPADirectStrongStepRuleCaseImplicationRoots_of_semantic_roots_v2
        M hPA inputs
        (embedPAContext (map witnessedAxiom witnesses)) hsemantic).
Qed.

End
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectBottomAdmissibilityAwareDispatcherIntegration.
