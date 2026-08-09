(**
  Low-memory integration of the genuine And-I child pair with outer truth.

  [RawCodedRestrictedPADerivationSoundnessDirectAndIntroductionChildInterfaceCompilation]
  constructs the left and right recursive-child roots on one certified
  standard-PA witness tail.  That reusable core deliberately does not import
  the large post-And-I continuation.  This module is the unique dependency
  boundary that does: it asks only for a growing compiler for truth of the
  outer conjunction, transports both child roots to the compiler's extended
  tail, and assembles the existing three-root selected-tail interface.

  The two public identifiers below retain their original unqualified names.
  Clients that need the final three-root merger should import this integration
  module; clients that need only the structural child roots can import the
  smaller core module alone.
*)

From Stdlib Require Import List.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  CodedProof
  RawCodedRestrictedPAProof
  RawCodedPAAxiomWitnessPrefix
  RawCodedPALocalProofExistential
  RawCodedTemplateSyntax
  RawCodedTemplateProofCompiler
  RawCodedTemplateDirectStructuralTranslation
  RawCodedRestrictedPADerivationSoundnessDirectAndIntroductionCase
  RawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftOpenedCoverageCompilation
  RawCodedRestrictedPADerivationSoundnessDirectAndIntroductionChildInterfaceSemanticCompilation
  RawCodedRestrictedPADerivationSoundnessDirectAndIntroductionOpenedCoverageValidity
  RawCodedRestrictedPADerivationSoundnessDirectAndIntroductionOpenedCoverageSourceCompilation
  RawCodedRestrictedPADerivationSoundnessDirectAndIntroductionChildCoreExtraction
  RawCodedRestrictedPADerivationSoundnessDirectAndIntroductionChildTailCompilation
  RawCodedRestrictedPADerivationSoundnessDirectRuleCasesAfterAndIntroduction.

Import ListNotations.

Module
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndIntroductionChildInterfaceIntegration.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedCodedProof.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedPAAxiomWitnessPrefix.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedTemplateDirectStructuralTranslation.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndIntroductionCase.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftOpenedCoverageCompilation.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndIntroductionChildInterfaceSemanticCompilation.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndIntroductionOpenedCoverageValidity.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndIntroductionOpenedCoverageSourceCompilation.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndIntroductionChildCoreExtraction.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndIntroductionChildTailCompilation.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectRuleCasesAfterAndIntroduction.

(** Exact one-root remainder: dynamic truth of the outer conjunction.  The
    suffix is existential because the truth producer may need an additional
    finite batch of standard PA axioms after the child compiler's batch. *)
Definition
    RawCoqRestrictedPADirectAndIntroductionTruthCoreStandardTailCompiler
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M) : Prop :=
  forall baseWitnesses : StandardPAAxiomWitnessPrefix,
  exists (suffix : StandardPAAxiomWitnessPrefix) (truthRoot : M),
    RawCodedPALocalProofOf M
      (rawTemplateContextCode
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        (coqRestrictedPADirectStrongStepAndIntroductionReadyContext
          (embedPAContext
            (map witnessedAxiom (baseWitnesses ++ suffix)))))
      (rawTemplateFormula
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        coqRestrictedPADirectAndIntroductionOuterConclusionTruthTemplate)
      truthRoot.

Arguments
  RawCoqRestrictedPADirectAndIntroductionTruthCoreStandardTailCompiler
  M hPA inputs : clear implicits.

(** Synchronize the two genuine child roots with the truth producer's suffix
    before exposing the already-published post-And-I three-core tail.  The
    represented roots themselves are transported; no equality of unequal
    context codes is assumed. *)
Theorem raw_selectedAndIntroductionCoreTail_of_children_and_truth : forall
    (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (inputs : RawCodedTemplateDirectStructuralInputs M),
  RawCoqRestrictedPADirectSelectedAndIntroductionChildCoreTail
    M hPA inputs ->
  RawCoqRestrictedPADirectAndIntroductionTruthCoreStandardTailCompiler
    M hPA inputs ->
  RawCoqRestrictedPADirectSelectedAndIntroductionCoreTail M hPA inputs.
Proof.
  intros M hPA inputs
    (childWitnesses & _hchildWitnessed &
      [(leftRoot & hleft) (rightRoot & hright)])
    htruth.
  destruct (htruth childWitnesses) as
    (suffix & truthRoot & htruthRoot).
  destruct (raw_andIntroductionReadyRoot_surround_witnessed_tail
    M hPA inputs [] childWitnesses suffix
    coqRestrictedPADirectAndIntroductionLeftInterfaceResultTemplate
    leftRoot hleft) as [leftTransported hleftTransported].
  destruct (raw_andIntroductionReadyRoot_surround_witnessed_tail
    M hPA inputs [] childWitnesses suffix
    coqRestrictedPADirectAndIntroductionRightInterfaceResultTemplate
    rightRoot hright) as [rightTransported hrightTransported].
  exists (childWitnesses ++ suffix). split.
  - apply raw_directEmbeddedPAAxiomWitnessContext.
  - split.
    + exists leftTransported.
      cbn [List.app] in hleftTransported.
      exact hleftTransported.
    + split.
      * exists rightTransported.
        cbn [List.app] in hrightTransported.
        exact hrightTransported.
      * exists truthRoot. exact htruthRoot.
Qed.

End
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndIntroductionChildInterfaceIntegration.
