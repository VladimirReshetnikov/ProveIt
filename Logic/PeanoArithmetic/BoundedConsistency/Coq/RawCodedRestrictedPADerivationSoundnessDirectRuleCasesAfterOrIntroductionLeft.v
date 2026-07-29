(**
  Direct rule-case integration after discharging Or-I-left recursion.

  The complete dispatcher previously required twenty-three semantic roots on
  one literal template tail.  The opened-coverage development now constructs
  the Or-I-left recursive root unconditionally on a finite standard PA tail
  and transports it across later standard tail extensions.  This module
  therefore exposes the honest twenty-two-field remainder and a continuation
  interface under which subsequent compilers may extend the incoming tail.
*)

From Stdlib Require Import List.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA.
From BoundedPAConsistency Require Import
  CodedProof
  RawCodedSyntaxConstructors
  RawCodedRestrictedPAProof
  RawCodedPAProvability
  RawCodedPAAxiomWitnessPrefix
  RawCodedTemplateSyntax
  RawCodedTemplateProofCompiler
  RawCodedTemplateDirectStructuralTranslation
  RawCodedRestrictedPADerivationSoundnessCarrierStrongPrefixDirectInductionShell
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
  RawCodedRestrictedPADerivationSoundnessDirectRuleCases
  RawCodedRestrictedPADerivationSoundnessDirectGrowingIntegrationFromWitnessedRuleCases
  RawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftOpenedCoverageCompilation.

Import ListNotations.

Module
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectRuleCasesAfterOrIntroductionLeft.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PABoundedCodedProof.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedPAProvability.
Import PABoundedRawCodedPAAxiomWitnessPrefix.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedTemplateDirectStructuralTranslation.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessCarrierStrongPrefixDirectInductionShell.
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
Import PABoundedRawCodedRestrictedPADerivationSoundnessDirectRuleCases.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectGrowingIntegrationFromWitnessedRuleCases.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftOpenedCoverageCompilation.

(** Exact remainder of [RawCoqRestrictedPADirectRuleCaseSemanticRoots] after
    deleting only its Or-I-left recursive-child field.  Every other residual
    remains visible with its original type and literal tail. *)
Record RawCoqRestrictedPADirectRuleCaseSemanticRootsAfterOrIntroductionLeft
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    (tail : TemplateContext) : Prop := {
  rawCoqRestrictedPADirectRemaining_assumption :
    RawCoqRestrictedPADirectStrongStepAssumptionMembershipTruthLawRoot
      M hPA inputs tail;

  rawCoqRestrictedPADirectRemaining_impIntroductionRecursive :
    RawCoqRestrictedPADirectImpIntroductionRecursiveChildLawRoot
      M hPA inputs tail;
  rawCoqRestrictedPADirectRemaining_impIntroductionTruth :
    RawCoqRestrictedPADirectImpIntroductionDynamicTruthLawRoot
      M hPA inputs tail;

  rawCoqRestrictedPADirectRemaining_impElimination :
    RawCoqRestrictedPADirectImpERecursiveModusPonensLawRoot M
      (rawDirectStructuralTemplateTranslation M hPA inputs) tail;
  rawCoqRestrictedPADirectRemaining_bottomElimination :
    RawCoqRestrictedPADirectBottomRecursiveContradictionLawRoot M
      (rawDirectStructuralTemplateTranslation M hPA inputs) tail;
  rawCoqRestrictedPADirectRemaining_excludedMiddle :
    RawCoqRestrictedPADirectExcludedMiddleTruthLawRoot M
      (rawDirectStructuralTemplateTranslation M hPA inputs) tail;

  rawCoqRestrictedPADirectRemaining_andIntroduction :
    RawCoqRestrictedPADirectStrongStepAndIntroductionSemanticRoots
      M hPA inputs tail;
  rawCoqRestrictedPADirectRemaining_andEliminationLeftRecursive :
    RawCoqRestrictedPADirectAndEliminationLeftRecursiveChildLawRoot
      M hPA inputs tail;
  rawCoqRestrictedPADirectRemaining_andEliminationLeftTruth :
    RawCoqRestrictedPADirectAndEliminationLeftDynamicTruthLawRoot
      M hPA inputs tail;
  rawCoqRestrictedPADirectRemaining_andEliminationRightRecursive :
    RawCoqRestrictedPADirectAndEliminationRightRecursiveChildLawRoot
      M hPA inputs tail;
  rawCoqRestrictedPADirectRemaining_andEliminationRightTruth :
    RawCoqRestrictedPADirectAndEliminationRightDynamicTruthLawRoot
      M hPA inputs tail;

  rawCoqRestrictedPADirectRemaining_orIntroductionLeftTruth :
    RawCoqRestrictedPADirectOrIntroductionLeftDynamicTruthLawRoot
      M hPA inputs tail;
  rawCoqRestrictedPADirectRemaining_orIntroductionRightRecursive :
    RawCoqRestrictedPADirectOrIntroductionRightRecursiveChildLawRoot
      M hPA inputs tail;
  rawCoqRestrictedPADirectRemaining_orIntroductionRightTruth :
    RawCoqRestrictedPADirectOrIntroductionRightDynamicTruthLawRoot
      M hPA inputs tail;
  rawCoqRestrictedPADirectRemaining_orElimination :
    RawCoqRestrictedPADirectOrEliminationSemanticRoots M hPA inputs tail;

  rawCoqRestrictedPADirectRemaining_universalIntroduction :
    RawCoqRestrictedPADirectUniversalIntroductionSemanticRoots
      M hPA inputs tail;
  rawCoqRestrictedPADirectRemaining_universalEliminationRecursive :
    RawCoqRestrictedPADirectUniversalEliminationRecursiveChildLawRoot
      M hPA inputs tail;
  rawCoqRestrictedPADirectRemaining_universalEliminationTruth :
    RawCoqRestrictedPADirectUniversalEliminationDynamicTruthLawRoot
      M hPA inputs tail;

  rawCoqRestrictedPADirectRemaining_existentialIntroduction :
    RawCoqRestrictedPADirectStrongStepExistentialIntroductionSemanticRoots
      M hPA inputs tail;
  rawCoqRestrictedPADirectRemaining_existentialElimination :
    RawCoqRestrictedPADirectExistentialEliminationSemanticRoots
      M hPA inputs tail;

  rawCoqRestrictedPADirectRemaining_equalityReflexivity :
    RawCoqRestrictedPADirectEqualityReflexivityAtomicTruthLawRoot M
      (rawDirectStructuralTemplateTranslation M hPA inputs) tail;
  rawCoqRestrictedPADirectRemaining_equalityElimination :
    RawCoqRestrictedPADirectStrongStepEqualityEliminationSemanticRoots
      M hPA inputs tail
}.

Arguments RawCoqRestrictedPADirectRuleCaseSemanticRootsAfterOrIntroductionLeft
  M hPA inputs tail : clear implicits.

(** Reinsert the now-compiled field into the complete dispatcher record. *)
Theorem raw_ruleCaseSemanticRoots_of_remaining_after_orIntroductionLeft :
  forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (inputs : RawCodedTemplateDirectStructuralInputs M) tail,
  RawCoqRestrictedPADirectOrIntroductionLeftRecursiveChildLawRoot
    M hPA inputs tail ->
  RawCoqRestrictedPADirectRuleCaseSemanticRootsAfterOrIntroductionLeft
    M hPA inputs tail ->
  RawCoqRestrictedPADirectRuleCaseSemanticRoots M hPA inputs tail.
Proof.
  intros M hPA inputs tail hOrIntroductionLeftRecursive hremaining.
  destruct hremaining.
  constructor; assumption.
Qed.

(** A remaining-root compiler may extend any incoming finite standard PA
    prefix.  This continuation form supports sequential composition: each
    future rule compiler receives all previously selected axiom witnesses and
    returns only a finite suffix plus its twenty-two-field result. *)
Definition RawCoqRestrictedPADirectRemainingRuleCasesStandardTailCompiler
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M) : Prop :=
  forall baseWitnesses : StandardPAAxiomWitnessPrefix,
  exists suffix : StandardPAAxiomWitnessPrefix,
    RawCoqRestrictedPADirectRuleCaseSemanticRootsAfterOrIntroductionLeft
      M hPA inputs
      (embedPAContext
        (map witnessedAxiom (baseWitnesses ++ suffix))).

Arguments RawCoqRestrictedPADirectRemainingRuleCasesStandardTailCompiler
  M hPA inputs : clear implicits.

(** Select the Or-I-left source prefix, let the remaining compiler append its
    suffix, transport the compiled recursive law to the combined tail, and
    construct the complete semantic-root record there. *)
Theorem raw_ruleCaseSemanticRoots_on_selected_witnessed_tail_of_remaining :
  forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (inputs : RawCodedTemplateDirectStructuralInputs M),
  RawCoqRestrictedPADirectRemainingRuleCasesStandardTailCompiler
    M hPA inputs ->
  exists witnesses : StandardPAAxiomWitnessPrefix,
    RawCodedPAAxiomWitnessContext M
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        witnesses (raw_zero M))
      (rawTemplateContextCode
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        (embedPAContext (map witnessedAxiom witnesses))) /\
    RawCoqRestrictedPADirectRuleCaseSemanticRoots M hPA inputs
      (embedPAContext (map witnessedAxiom witnesses)).
Proof.
  intros M hPA inputs hremainingCompiler.
  destruct
    (raw_orIntroductionLeft_recursiveChildLawRoot_on_selected_witnessed_tail
      M hPA inputs)
    as (orWitnesses & horWitnessed & horRoot).
  destruct (hremainingCompiler orWitnesses)
    as [suffix hremaining].
  set (witnesses := orWitnesses ++ suffix).
  exists witnesses. split.
  - unfold witnesses.
    exact (raw_directEmbeddedPAAxiomWitnessContext M hPA inputs
      (orWitnesses ++ suffix)).
  - apply raw_ruleCaseSemanticRoots_of_remaining_after_orIntroductionLeft.
    + unfold witnesses.
      exact
        (raw_orIntroductionLeft_recursiveChildLawRoot_append_witnessed_tail
          M hPA inputs orWitnesses suffix horRoot).
    + unfold witnesses. exact hremaining.
Qed.

(** Feed the completed common-tail rule record through the existing growing
    strong-prefix integration.  The old 23-field premise has disappeared;
    only the explicit 22-field continuation and the independent closure
    remainder remain. *)
Corollary
    raw_codedPAProofOf_coqRestrictedPADerivationSoundnessUniversalDirect_of_remaining_after_orIntroductionLeft :
  forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (inputs : RawCodedTemplateDirectStructuralInputs M),
  RawCoqRestrictedPADirectRemainingRuleCasesStandardTailCompiler
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
    (raw_ruleCaseSemanticRoots_on_selected_witnessed_tail_of_remaining
      M hPA inputs hremainingCompiler)
    as (witnesses & hwitnessed & hsemantic).
  exact
    (raw_codedPAProofOf_coqRestrictedPADerivationSoundnessUniversalDirect_of_rule_case_semantic_roots_on_witnessed_tail
      M hPA inputs
      (embedPAContext (map witnessedAxiom witnesses))
      replacement axiom closureCount
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        witnesses (raw_zero M))
      hwitnessed hremainder hsemantic).
Qed.

End
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectRuleCasesAfterOrIntroductionLeft.
