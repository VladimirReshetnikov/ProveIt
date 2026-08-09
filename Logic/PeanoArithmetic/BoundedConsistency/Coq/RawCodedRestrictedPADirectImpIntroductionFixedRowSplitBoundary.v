(**
  Diagnostic pre-Imp-I boundary for the direct implication truth split.

  The native predecessor decision is initially compiled under literal Pi and
  Sigma state assumptions.  Represented proofs of those state atoms reroot it
  into the unchanged direct ready context.  The two positive implication-row
  computations are consumed one step earlier than their public laws: each
  supplies only the conclusion body under the literal formula-code and child
  truth assumptions.  Two ordinary Imp-I nodes then build each row law.

  Consequently this boundary assumes neither the target implication truth law
  nor either fixed-row implication law.  It is deliberately retained as a
  checked decomposition lemma, but it is not the final producer interface:
  predecessor-state exclusivity makes simultaneous ready-context proofs of
  Pi state and Sigma state impossible.  The non-vacuous compiler therefore
  bypasses this joint wrapper and invokes the elimination chain directly in
  the ready context.
*)

From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors
  RawCodedContextLists
  RawCodedFixedLevelTruthTotality
  RawCodedProofImpIConstructor
  RawCodedPALocalProofExistential
  RawCodedPALocalProofPropositionalRules
  RawCodedTemplateSyntax
  RawCodedTemplateProofCompiler
  RawCodedTemplateDirectStructuralTranslation
  RawCodedTemplateDirectStructuralPAAgreement
  RawCodedDynamicTruthPredecessorStateExclusivityCompilation
  RawCodedDynamicTruthPredecessorJointStateDischarge
  RawCodedRestrictedPADerivationSoundnessTemplateDirectInputs
  RawCodedRestrictedPADerivationSoundnessDirectAssumptionCase
  RawCodedRestrictedPADerivationSoundnessDirectImpIntroductionCase
  RawCodedRestrictedPADerivationSoundnessDirectRuleCasesAfterImpIntroductionTruth.

Module
  PABoundedRawCodedRestrictedPADirectImpIntroductionFixedRowSplitBoundary.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedContextLists.
Import PABoundedRawCodedFixedLevelTruthTotality.
Import PABoundedRawCodedProofImpIConstructor.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPALocalProofPropositionalRules.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedTemplateDirectStructuralTranslation.
Import PABoundedRawCodedTemplateDirectStructuralPAAgreement.
Import
  PABoundedRawCodedDynamicTruthPredecessorStateExclusivityCompilation.
Import PABoundedRawCodedDynamicTruthPredecessorJointStateDischarge.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessTemplateDirectInputs.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectAssumptionCase.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectImpIntroductionCase.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectRuleCasesAfterImpIntroductionTruth.

(** Package the three roots needed by the represented propositional
    split.  The false and true body contexts spell the discharge order
    literally: the child truth is the outer head and the formula relation is
    the next head above the ready context.  The two state premises make this
    theorem useful for structural auditing, but not directly instantiable in
    the intended consistent predecessor context. *)
Theorem
    raw_impIntroductionFixedRowSplitRoots_of_joint_decision_and_positive_bodies :
  forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (inputs : RawCodedTemplateDirectStructuralInputs M) tail
    piLeft piStateRoot sigmaStateRoot decisionRoot
    falseBodyRoot trueBodyRoot,
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
    (rawDynamicTruthPredecessorPiStateMemberBodyCode M) piStateRoot ->
  RawCodedPALocalProofOf M readyContext
    (rawDynamicTruthPredecessorSigmaStateMemberBodyCode M) sigmaStateRoot ->
  RawCodedPALocalProofOf M
    (rawDynamicTruthPredecessorJointStateContext M readyContext)
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
  intros M hPA inputs tail
    piLeft piStateRoot sigmaStateRoot decisionRoot
    falseBodyRoot trueBodyRoot
    translation readyContext formulaRelation sigmaLeft sigmaRight sigmaImp
    hpiAdequate hpiState hsigmaState hdecision hfalseBody htrueBody.
  cbn zeta in *.
  assert (hready : RawContextListRealizable M readyContext).
  {
    unfold readyContext, translation.
    apply raw_templateContext_realizable. exact hPA.
  }
  destruct
    (raw_codedPALocalProofOf_predecessor_joint_state_discharge
      M hPA translation
      (rawDirectStructuralTemplatePAAgreement M hPA inputs)
      readyContext (rawFormulaOrCode M sigmaLeft piLeft)
      piStateRoot sigmaStateRoot decisionRoot
      hready hpiState hsigmaState hdecision) as
    [readyDecisionRoot hreadyDecision].

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
  - exists readyDecisionRoot. exact hreadyDecision.
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

End
  PABoundedRawCodedRestrictedPADirectImpIntroductionFixedRowSplitBoundary.
