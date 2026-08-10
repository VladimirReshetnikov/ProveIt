(**
  Remove the All-E and Ex-I arithmetic child coordinates from the refined
  post-And-I boundary.

  The quantifier-unary source compiler produces those two roots on one
  synchronized standard witness tail.  The genuinely remaining child-only
  continuation therefore has five fields: the two And-E truth laws, Or-E,
  Ex-E, and the Eq-E child pair.  No dynamic truth law is hidden here.
*)

From Stdlib Require Import List.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  CodedProof
  RawCodedPAAxiomWitness
  RawCodedPAAxiomWitnessPrefix
  RawCodedTemplateSyntax
  RawCodedTemplatePAEmbedding
  RawCodedTemplateDirectStructuralTranslation
  RawCodedTemplateLocalProofAffineStandardWitnessTailTransport
  RawCodedRestrictedPADerivationSoundnessDirectAndEliminationLeftCase
  RawCodedRestrictedPADerivationSoundnessDirectAndEliminationRightCase
  RawCodedRestrictedPADerivationSoundnessDirectOrEliminationCase
  RawCodedRestrictedPADerivationSoundnessDirectExistentialEliminationCase
  RawCodedRestrictedPADerivationSoundnessDirectPostAndIntroductionSevenFieldChildOnlyRemainderIntegration
  RawCodedRestrictedPADerivationSoundnessQuantifierUnaryChildInterfaceOpenedCoverageCompilation.

Import ListNotations.

Module
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectPostAndIntroductionFiveFieldChildOnlyRemainderIntegration.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedCodedProof.
Import PABoundedRawCodedPAAxiomWitness.
Import PABoundedRawCodedPAAxiomWitnessPrefix.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplatePAEmbedding.
Import PABoundedRawCodedTemplateDirectStructuralTranslation.
Import PABoundedRawCodedTemplateLocalProofAffineStandardWitnessTailTransport.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndEliminationLeftCase.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndEliminationRightCase.
Import PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrEliminationCase.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectExistentialEliminationCase.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectPostAndIntroductionSevenFieldChildOnlyRemainderIntegration.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessQuantifierUnaryChildInterfaceOpenedCoverageCompilation.

Record
    RawCoqRestrictedPADirectRuleCaseSemanticRootsAfterAndIntroductionFiveFieldChildOnlyRemainder
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    (tail : TemplateContext) : Prop := {
  rawCoqRestrictedPADirectAfterAndIFiveChildOnly_andEliminationLeftTruth :
    RawCoqRestrictedPADirectAndEliminationLeftDynamicTruthLawRoot
      M hPA inputs tail;
  rawCoqRestrictedPADirectAfterAndIFiveChildOnly_andEliminationRightTruth :
    RawCoqRestrictedPADirectAndEliminationRightDynamicTruthLawRoot
      M hPA inputs tail;
  rawCoqRestrictedPADirectAfterAndIFiveChildOnly_orElimination :
    RawCoqRestrictedPADirectOrEliminationSemanticRoots M hPA inputs tail;
  rawCoqRestrictedPADirectAfterAndIFiveChildOnly_existentialElimination :
    RawCoqRestrictedPADirectExistentialEliminationSemanticRoots
      M hPA inputs tail;
  rawCoqRestrictedPADirectAfterAndIFiveChildOnly_equalityEliminationChildren :
    RawCoqRestrictedPADirectEqualityEliminationChildInterfaceRoots
      M hPA inputs tail
}.

Arguments
  RawCoqRestrictedPADirectRuleCaseSemanticRootsAfterAndIntroductionFiveFieldChildOnlyRemainder
  M hPA inputs tail : clear implicits.

Definition
    RawCoqRestrictedPADirectRemainingAfterAndIntroductionFiveFieldChildOnlyAtWitnesses
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    (witnesses : StandardPAAxiomWitnessPrefix) : Prop :=
  RawCoqRestrictedPADirectRuleCaseSemanticRootsAfterAndIntroductionFiveFieldChildOnlyRemainder
    M hPA inputs (embedPAContext (map witnessedAxiom witnesses)).

Definition
    RawCoqRestrictedPADirectRemainingAfterAndIntroductionFiveFieldChildOnlyStandardTailCompiler
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M) : Prop :=
  RawCoqStandardWitnessTailCompiler
    (RawCoqRestrictedPADirectRemainingAfterAndIntroductionFiveFieldChildOnlyAtWitnesses
      M hPA inputs).

Arguments
  RawCoqRestrictedPADirectRemainingAfterAndIntroductionFiveFieldChildOnlyAtWitnesses
  M hPA inputs witnesses : clear implicits.
Arguments
  RawCoqRestrictedPADirectRemainingAfterAndIntroductionFiveFieldChildOnlyStandardTailCompiler
  M hPA inputs : clear implicits.

Theorem
    raw_sevenFieldChildOnlyRemainder_of_quantifierUnaryChildren_and_fiveFieldRemainder :
  forall (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M) witnesses,
  RawCoqRestrictedPAQuantifierUnaryChildRootsAtWitnesses
      M hPA inputs witnesses ->
  RawCoqRestrictedPADirectRemainingAfterAndIntroductionFiveFieldChildOnlyAtWitnesses
      M hPA inputs witnesses ->
  RawCoqRestrictedPADirectRemainingAfterAndIntroductionSevenFieldChildOnlyAtWitnesses
      M hPA inputs witnesses.
Proof.
  intros M hPA inputs witnesses [huniversal hexistential] hremaining.
  destruct hremaining as
    [hleftTruth hrightTruth horElimination hexistentialElimination
      hequalityChildren].
  constructor.
  - exact hleftTruth.
  - exact hrightTruth.
  - exact horElimination.
  - exact huniversal.
  - exact hexistential.
  - exact hexistentialElimination.
  - exact hequalityChildren.
Qed.

(** The quantifier pair is compiled first because its exported append law
    transports both roots across the suffix selected by the five-field
    continuation. *)
Theorem
    raw_remainingAfterAndIntroductionSevenFieldChildOnlyStandardTailCompiler_of_fiveFieldRemainder :
  forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (inputs : RawCodedTemplateDirectStructuralInputs M),
  RawCoqRestrictedPADirectRemainingAfterAndIntroductionFiveFieldChildOnlyStandardTailCompiler
      M hPA inputs ->
  RawCoqRestrictedPADirectRemainingAfterAndIntroductionSevenFieldChildOnlyStandardTailCompiler
      M hPA inputs.
Proof.
  intros M hPA inputs hremaining.
  change (RawCoqStandardWitnessTailCompiler
    (RawCoqRestrictedPADirectRemainingAfterAndIntroductionSevenFieldChildOnlyAtWitnesses
      M hPA inputs)).
  apply (raw_coqStandardWitnessTailCompiler_apply
    (RawCoqRestrictedPAQuantifierUnaryChildRootsAtWitnesses M hPA inputs)
    (RawCoqRestrictedPADirectRemainingAfterAndIntroductionSevenFieldChildOnlyAtWitnesses
      M hPA inputs)).
  - apply raw_quantifierUnaryChildRootsAtWitnesses_append_stable.
  - apply raw_quantifierUnaryChildRoots_standardTailCompiler.
  - intros baseWitnesses.
    destruct (hremaining baseWitnesses) as [suffix hremainingAt].
    exists suffix.
    intro hquantifier.
    exact
      (raw_sevenFieldChildOnlyRemainder_of_quantifierUnaryChildren_and_fiveFieldRemainder
        M hPA inputs (baseWitnesses ++ suffix)
        hquantifier hremainingAt).
Qed.

End
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectPostAndIntroductionFiveFieldChildOnlyRemainderIntegration.
