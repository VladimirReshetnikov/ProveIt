(**
  Package the direct Imp-I split on an explicit standard witness extension.

  The ready evidence-decision compiler returns a disjunction directly in the
  caller prefix, so this bridge never requests simultaneous proofs of the
  exclusive predecessor Sigma/Pi state atoms.  Its two remaining row inputs
  are honest positive bodies: each conclusion truth formula is proved only
  under the literal formula-code and branch-evidence assumptions.  Two
  represented Imp-I nodes turn each body into the law consumed by the
  existing propositional split.

  The standard-tail theorem uses the exact context form returned by standard
  witness compilers.  PA agreement and the affine ready-context lemma identify
  it with the metatheoretic tail required by
  [RawCoqRestrictedPADirectSelectedImpIntroductionFixedRowSplitTail].
*)

From Stdlib Require Import List.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA.
From BoundedPAConsistency Require Import
  CodedProof
  RawCodedSyntaxConstructors
  RawCodedFixedLevelTruthTotality
  RawCodedProofImpIConstructor
  RawCodedRestrictedPAProof
  RawCodedPAAxiomWitnessPrefix
  RawCodedPALocalProofExistential
  RawCodedPALocalProofPropositionalRules
  RawCodedTemplateSyntax
  RawCodedTemplateProofCompiler
  RawCodedTemplateProofCompilerSelfShiftTail
  RawCodedTemplatePAEmbedding
  RawCodedTemplateDirectStructuralTranslation
  RawCodedTemplateDirectStructuralPAAgreement
  RawCodedTemplateLocalProofStandardWitnessTailTransport
  RawCodedFourStateTableAppendRowLtSuccCases
  RawCodedRestrictedPADerivationSoundnessTemplateDirectInputs
  RawCodedRestrictedPADerivationSoundnessDirectAssumptionCase
  RawCodedRestrictedPADerivationSoundnessDirectImpIntroductionCase
  RawCodedRestrictedPADerivationSoundnessDirectRuleCasesAfterImpIntroductionRecursive
  RawCodedRestrictedPADerivationSoundnessDirectRuleCasesAfterImpIntroductionTruth.

Module
  PABoundedRawCodedRestrictedPADirectImpIntroductionStandardReadySplitCompilation.

Import ListNotations.
Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PABoundedCodedProof.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedFixedLevelTruthTotality.
Import PABoundedRawCodedProofImpIConstructor.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedPAAxiomWitnessPrefix.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPALocalProofPropositionalRules.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedTemplateProofCompilerSelfShiftTail.
Import PABoundedRawCodedTemplatePAEmbedding.
Import PABoundedRawCodedTemplateDirectStructuralTranslation.
Import PABoundedRawCodedTemplateDirectStructuralPAAgreement.
Import PABoundedRawCodedTemplateLocalProofStandardWitnessTailTransport.
Import PABoundedRawCodedFourStateTableAppendRowLtSuccCases.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessTemplateDirectInputs.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectAssumptionCase.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectImpIntroductionCase.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectRuleCasesAfterImpIntroductionRecursive.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectRuleCasesAfterImpIntroductionTruth.

(** Direct ready-context packaging, independent of how its three represented
    roots were obtained.  This is the reusable logical core of the standard
    witness specialization below. *)
Theorem
    raw_impIntroductionFixedRowSplitRoots_of_ready_decision_and_positive_bodies :
  forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (inputs : RawCodedTemplateDirectStructuralInputs M) tail
    piLeft decisionRoot falseBodyRoot trueBodyRoot,
  let translation := rawDirectStructuralTemplateTranslation M hPA inputs in
  let readyContext := rawTemplateContextCode translation
    (coqRestrictedPADirectStrongStepImpIntroductionReadyContext tail) in
  let formulaRelation := rawDirectTemplateFormula inputs
    coqRestrictedPADirectImpIntroductionFormulaCodeTemplate in
  let sigmaLeft := rawDirectTemplateFormula inputs
    coqRestrictedPADirectImpIntroductionAntecedentTruthTemplate in
  let sigmaRight := rawDirectTemplateFormula inputs
    coqRestrictedPADirectImpIntroductionConsequentTruthTemplate in
  let sigmaImp := rawDirectTemplateFormula inputs
    coqRestrictedPADirectAssumptionOuterConclusionTruthTemplate in
  RawCodedFormulaAtomicallyAdequate M piLeft ->
  RawCodedPALocalProofOf M readyContext
    (rawFormulaOrCode M sigmaLeft piLeft) decisionRoot ->
  RawCodedPALocalProofOf M
    (rawListNode M piLeft
      (rawListNode M formulaRelation readyContext))
    sigmaImp falseBodyRoot ->
  RawCodedPALocalProofOf M
    (rawListNode M sigmaRight
      (rawListNode M formulaRelation readyContext))
    sigmaImp trueBodyRoot ->
  RawCoqRestrictedPADirectImpIntroductionFixedRowSplitRoots
    M hPA inputs tail.
Proof.
  intros M hPA inputs tail piLeft
    decisionRoot falseBodyRoot trueBodyRoot
    translation readyContext formulaRelation sigmaLeft sigmaRight sigmaImp
    hpiAdequate hdecision hfalseBody htrueBody.
  cbn zeta in *.
  pose proof
    (raw_codedPALocalProofOf_impI M hPA
      (rawListNode M formulaRelation readyContext)
      piLeft sigmaImp falseBodyRoot hfalseBody) as hfalseInner.
  lazymatch type of hfalseInner with
  | RawCodedPALocalProofOf _ _ _ ?falseInnerRoot =>
      pose proof
        (raw_codedPALocalProofOf_impI M hPA readyContext
          formulaRelation (rawFormulaImpCode M piLeft sigmaImp)
          falseInnerRoot hfalseInner) as hfalseLaw
  end.
  pose proof
    (raw_codedPALocalProofOf_impI M hPA
      (rawListNode M formulaRelation readyContext)
      sigmaRight sigmaImp trueBodyRoot htrueBody) as htrueInner.
  lazymatch type of htrueInner with
  | RawCodedPALocalProofOf _ _ _ ?trueInnerRoot =>
      pose proof
        (raw_codedPALocalProofOf_impI M hPA readyContext
          formulaRelation (rawFormulaImpCode M sigmaRight sigmaImp)
          trueInnerRoot htrueInner) as htrueLaw
  end.
  exists piLeft. split; [exact hpiAdequate |].
  split.
  - exists decisionRoot. exact hdecision.
  - split.
    + lazymatch type of hfalseLaw with
      | RawCodedPALocalProofOf _ _ _ ?falseLawRoot =>
          exists falseLawRoot; exact hfalseLaw
      end.
    + lazymatch type of htrueLaw with
      | RawCodedPALocalProofOf _ _ _ ?trueLawRoot =>
          exists trueLawRoot; exact htrueLaw
      end.
Qed.

(** Consume roots in the exact context emitted by the ready-decision
    standard-extension theorem.  The sole context calculation below is an
    equality: no weakening, contraction, or semantic transport is hidden. *)
Theorem
    raw_selectedImpIntroductionFixedRowSplitTail_of_standard_ready_decision_and_positive_bodies :
  forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    (witnesses : StandardPAAxiomWitnessPrefix)
    piLeft decisionRoot falseBodyRoot trueBodyRoot,
  let translation := rawDirectStructuralTemplateTranslation M hPA inputs in
  let standardContext := rawStandardPAAxiomWitnessPrefixContextCode M
    witnesses (raw_zero M) in
  let readyContext := rawTemplateContextCodeOnTail translation
    standardContext
    (coqRestrictedPADirectStrongStepImpIntroductionReadyContext []) in
  let formulaRelation := rawDirectTemplateFormula inputs
    coqRestrictedPADirectImpIntroductionFormulaCodeTemplate in
  let sigmaLeft := rawDirectTemplateFormula inputs
    coqRestrictedPADirectImpIntroductionAntecedentTruthTemplate in
  let sigmaRight := rawDirectTemplateFormula inputs
    coqRestrictedPADirectImpIntroductionConsequentTruthTemplate in
  let sigmaImp := rawDirectTemplateFormula inputs
    coqRestrictedPADirectAssumptionOuterConclusionTruthTemplate in
  RawCodedPAAxiomWitnessContext M
    (rawStandardPAAxiomWitnessPrefixWitnessListCode M
      witnesses (raw_zero M)) standardContext ->
  RawCodedFormulaAtomicallyAdequate M piLeft ->
  RawCodedPALocalProofOf M readyContext
    (rawFormulaOrCode M sigmaLeft piLeft) decisionRoot ->
  RawCodedPALocalProofOf M
    (rawListNode M piLeft
      (rawListNode M formulaRelation readyContext))
    sigmaImp falseBodyRoot ->
  RawCodedPALocalProofOf M
    (rawListNode M sigmaRight
      (rawListNode M formulaRelation readyContext))
    sigmaImp trueBodyRoot ->
  RawCoqRestrictedPADirectSelectedImpIntroductionFixedRowSplitTail
    M hPA inputs.
Proof.
  intros M hPA inputs witnesses piLeft
    decisionRoot falseBodyRoot trueBodyRoot
    translation standardContext readyContext
    formulaRelation sigmaLeft sigmaRight sigmaImp
    hwitnessed hpiAdequate hdecision hfalseBody htrueBody.
  cbn zeta in *.
  assert (hreadyContextCode :
      readyContext =
      rawTemplateContextCode translation
        (coqRestrictedPADirectStrongStepImpIntroductionReadyContext
          (embedPAContext (map witnessedAxiom witnesses)))).
  {
    unfold readyContext, standardContext.
    rewrite <- (raw_templateContextCode_embedPAAxiomWitnesses
      M translation
      (rawDirectStructuralTemplatePAAgreement M hPA inputs) witnesses).
    rewrite <- (raw_templateContextCode_app_on_tail_general
      M translation
      (coqRestrictedPADirectStrongStepImpIntroductionReadyContext [])
      (embedPAContext (map witnessedAxiom witnesses))).
    rewrite <- coqRestrictedPADirectImpIntroductionReadyContext_app_witnesses.
    reflexivity.
  }
  assert (htargetWitnessed : RawCodedPAAxiomWitnessContext M
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        witnesses (raw_zero M))
      (rawTemplateContextCode translation
        (embedPAContext (map witnessedAxiom witnesses)))).
  {
    rewrite (raw_templateContextCode_embedPAAxiomWitnesses
      M translation
      (rawDirectStructuralTemplatePAAgreement M hPA inputs) witnesses).
    exact hwitnessed.
  }
  rewrite hreadyContextCode in hdecision, hfalseBody, htrueBody.
  exists witnesses. split; [exact htargetWitnessed |].
  exact
    (raw_impIntroductionFixedRowSplitRoots_of_ready_decision_and_positive_bodies
      M hPA inputs (embedPAContext (map witnessedAxiom witnesses))
      piLeft decisionRoot falseBodyRoot trueBodyRoot
      hpiAdequate hdecision hfalseBody htrueBody).
Qed.

End
  PABoundedRawCodedRestrictedPADirectImpIntroductionStandardReadySplitCompilation.
