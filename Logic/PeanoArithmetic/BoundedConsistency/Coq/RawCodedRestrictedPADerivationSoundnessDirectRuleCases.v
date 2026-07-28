(**
  Consolidation of the seventeen exact constructor cases for the direct
  restricted-PA derivation-soundness strong step.

  Every constructor module deliberately stops at its own semantic laws.
  This file merely packages those laws, performs the finite dispatch on
  [RawCoqRestrictedPAProofRuleCase], and hands the resulting family of exact
  implication roots to the already-verified strong-step shell.  In
  particular, the package below contains no branch result, conclusion
  proof, or completed strong-step proof.
*)

From Stdlib Require Import List.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA.
From BoundedPAConsistency Require Import
  RawCodedPALocalProofExistential
  RawCodedTemplateSyntax
  RawCodedTemplateProofCompiler
  RawCodedTemplateDirectStructuralTranslation
  RawCodedRestrictedPADerivationSoundnessCarrierStrongPrefixDirectInductionShell
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
  RawCodedRestrictedPADerivationSoundnessDirectEqualityEliminationCase.

Module PABoundedRawCodedRestrictedPADerivationSoundnessDirectRuleCases.

Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedTemplateDirectStructuralTranslation.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessCarrierStrongPrefixDirectInductionShell.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectStrongStepShell.
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

(** The honest residual-only boundary for the complete finite dispatcher.
    Fields correspond exactly to the public residuals of the case modules.
    Modules whose semantic boundary has two independent laws contribute two
    fields; modules whose boundary is already a named package contribute one.
*)
Record RawCoqRestrictedPADirectRuleCaseSemanticRoots
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    (tail : TemplateContext) : Prop := {
  rawCoqRestrictedPADirectRuleCases_assumption :
    RawCoqRestrictedPADirectStrongStepAssumptionMembershipTruthLawRoot
      M hPA inputs tail;

  rawCoqRestrictedPADirectRuleCases_impIntroductionRecursive :
    RawCoqRestrictedPADirectImpIntroductionRecursiveChildLawRoot
      M hPA inputs tail;
  rawCoqRestrictedPADirectRuleCases_impIntroductionTruth :
    RawCoqRestrictedPADirectImpIntroductionDynamicTruthLawRoot
      M hPA inputs tail;

  rawCoqRestrictedPADirectRuleCases_impElimination :
    RawCoqRestrictedPADirectImpERecursiveModusPonensLawRoot M
      (rawDirectStructuralTemplateTranslation M hPA inputs) tail;
  rawCoqRestrictedPADirectRuleCases_bottomElimination :
    RawCoqRestrictedPADirectBottomRecursiveContradictionLawRoot M
      (rawDirectStructuralTemplateTranslation M hPA inputs) tail;
  rawCoqRestrictedPADirectRuleCases_excludedMiddle :
    RawCoqRestrictedPADirectExcludedMiddleTruthLawRoot M
      (rawDirectStructuralTemplateTranslation M hPA inputs) tail;

  rawCoqRestrictedPADirectRuleCases_andIntroduction :
    RawCoqRestrictedPADirectStrongStepAndIntroductionSemanticRoots
      M hPA inputs tail;
  rawCoqRestrictedPADirectRuleCases_andEliminationLeftRecursive :
    RawCoqRestrictedPADirectAndEliminationLeftRecursiveChildLawRoot
      M hPA inputs tail;
  rawCoqRestrictedPADirectRuleCases_andEliminationLeftTruth :
    RawCoqRestrictedPADirectAndEliminationLeftDynamicTruthLawRoot
      M hPA inputs tail;
  rawCoqRestrictedPADirectRuleCases_andEliminationRightRecursive :
    RawCoqRestrictedPADirectAndEliminationRightRecursiveChildLawRoot
      M hPA inputs tail;
  rawCoqRestrictedPADirectRuleCases_andEliminationRightTruth :
    RawCoqRestrictedPADirectAndEliminationRightDynamicTruthLawRoot
      M hPA inputs tail;

  rawCoqRestrictedPADirectRuleCases_orIntroductionLeftRecursive :
    RawCoqRestrictedPADirectOrIntroductionLeftRecursiveChildLawRoot
      M hPA inputs tail;
  rawCoqRestrictedPADirectRuleCases_orIntroductionLeftTruth :
    RawCoqRestrictedPADirectOrIntroductionLeftDynamicTruthLawRoot
      M hPA inputs tail;
  rawCoqRestrictedPADirectRuleCases_orIntroductionRightRecursive :
    RawCoqRestrictedPADirectOrIntroductionRightRecursiveChildLawRoot
      M hPA inputs tail;
  rawCoqRestrictedPADirectRuleCases_orIntroductionRightTruth :
    RawCoqRestrictedPADirectOrIntroductionRightDynamicTruthLawRoot
      M hPA inputs tail;
  rawCoqRestrictedPADirectRuleCases_orElimination :
    RawCoqRestrictedPADirectOrEliminationSemanticRoots M hPA inputs tail;

  rawCoqRestrictedPADirectRuleCases_universalIntroduction :
    RawCoqRestrictedPADirectUniversalIntroductionSemanticRoots
      M hPA inputs tail;
  rawCoqRestrictedPADirectRuleCases_universalEliminationRecursive :
    RawCoqRestrictedPADirectUniversalEliminationRecursiveChildLawRoot
      M hPA inputs tail;
  rawCoqRestrictedPADirectRuleCases_universalEliminationTruth :
    RawCoqRestrictedPADirectUniversalEliminationDynamicTruthLawRoot
      M hPA inputs tail;

  rawCoqRestrictedPADirectRuleCases_existentialIntroduction :
    RawCoqRestrictedPADirectStrongStepExistentialIntroductionSemanticRoots
      M hPA inputs tail;
  rawCoqRestrictedPADirectRuleCases_existentialElimination :
    RawCoqRestrictedPADirectExistentialEliminationSemanticRoots
      M hPA inputs tail;

  rawCoqRestrictedPADirectRuleCases_equalityReflexivity :
    RawCoqRestrictedPADirectEqualityReflexivityAtomicTruthLawRoot M
      (rawDirectStructuralTemplateTranslation M hPA inputs) tail;
  rawCoqRestrictedPADirectRuleCases_equalityElimination :
    RawCoqRestrictedPADirectStrongStepEqualityEliminationSemanticRoots
      M hPA inputs tail
}.

Arguments RawCoqRestrictedPADirectRuleCaseSemanticRoots
  M hPA inputs tail : clear implicits.

(** Exhaust the finite rule tag and invoke the corresponding exact case
    theorem.  The public view lemma makes the target visibly one implication
    root per constructor, so this proof performs no semantic reasoning of
    its own. *)
Theorem
    raw_coqRestrictedPADirectStrongStepRuleCaseImplicationRoots_of_semantic_roots :
  forall (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M) tail,
  RawCoqRestrictedPADirectRuleCaseSemanticRoots M hPA inputs tail ->
  RawCoqRestrictedPADirectStrongStepRuleCaseImplicationRoots
    M hPA inputs tail.
Proof.
  intros M hPA inputs tail hsemantic.
  destruct hsemantic as
    [hAssumption
     hImpIntroductionRecursive hImpIntroductionTruth
     hImpElimination hBottomElimination hExcludedMiddle
     hAndIntroduction
     hAndEliminationLeftRecursive hAndEliminationLeftTruth
     hAndEliminationRightRecursive hAndEliminationRightTruth
     hOrIntroductionLeftRecursive hOrIntroductionLeftTruth
     hOrIntroductionRightRecursive hOrIntroductionRightTruth
     hOrElimination
     hUniversalIntroduction
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
  - exact
      (raw_coqRestrictedPADirectStrongStepBottomEliminationCaseRoot
        M hPA inputs tail hBottomElimination).
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

(** Close the exact strong-step shell.  This is a thin corollary: all
    constructor-specific work remains visible in the residual package. *)
Theorem
    raw_codedPALocalProofOf_coqRestrictedPADirectStrongStep_of_rule_case_semantic_roots :
  forall (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M) tail,
  RawCoqRestrictedPADirectRuleCaseSemanticRoots M hPA inputs tail ->
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
    (raw_coqRestrictedPADirectStrongStepRuleCaseImplicationRoots_of_semantic_roots
      M hPA inputs tail hsemantic).
Qed.

End PABoundedRawCodedRestrictedPADerivationSoundnessDirectRuleCases.
