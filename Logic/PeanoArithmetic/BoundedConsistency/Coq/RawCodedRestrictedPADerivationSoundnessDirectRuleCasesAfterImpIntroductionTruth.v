(**
  Direct rule-case integration after the Imp-I dynamic-truth law.

  Truth of an implication is obtained by an honest represented case split
  on its predecessor truth evidence.  If the antecedent is Sigma-true, the
  implication premise yields Sigma truth of the consequent and the
  ImpTrueRight row yields Sigma truth of the implication.  If the antecedent
  is Pi-true (hence false at the Sigma polarity), the ImpFalseLeft row yields
  the same conclusion directly.

  The generic predecessor compiler
  [raw_dynamicTruthPredecessorEvidenceDecision_of_projected_decision_under_prefix_atomic_and_domain]
  already produces the represented [Sigma(left) \/ Pi(left)] disjunction.
  What is not yet available in the library is a positive ImpFalseLeft or
  ImpTrueRight fixed-row compiler rerooted in the direct Imp-I ready context:
  the existing implication-cell modules compile collision/exclusivity, while
  the positive fixed-production template is currently specific to Sigma/Or.

  This file therefore stops at the smallest non-circular boundary.  It asks
  for the represented predecessor decision and the two positive implication
  row laws, never for the target Tarski law.  The proof below performs the
  split explicitly with represented Or-E, applies the recursive implication
  premise only in the Sigma branch, and closes the target with two Imp-I
  nodes.  A selected finite standard-PA tail packages those three roots; the
  ordinary growing-tail adapter then deletes the dynamic-truth field from the
  post-Imp-recursive continuation.
*)

From Stdlib Require Import List.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA.
From BoundedPAConsistency Require Import
  CodedProof
  RawCodedContextLists
  RawCodedContextStructure
  RawCodedSyntaxConstructors
  RawCodedFixedLevelTruthTotality
  RawCodedProofAssumptionLeaf
  RawCodedProofBinaryConstructors
  RawCodedProofImpIConstructor
  RawCodedProofOrEConstructor
  RawCodedRestrictedPAProof
  RawCodedPAProvability
  RawCodedPAAxiomWitnessPrefix
  RawCodedPALocalProofExistential
  RawCodedPALocalProofComposition
  RawCodedPALocalProofPropositionalRules
  RawCodedPALocalProofContextInsertUnconditional
  RawCodedTemplateSyntax
  RawCodedTemplateNumeralParameters
  RawCodedTemplateProofCompiler
  RawCodedTemplateDirectStructuralTranslation
  RawCodedTemplateDirectStructuralPAAgreement
  RawCodedTemplateLocalProofStandardWitnessTailTransport
  RawCodedFormulaBoundAllCarrierBoundary
  RawCodedDynamicTruthPredecessorDirectEvidenceLogicalRoots
  RawCodedRestrictedPADerivationSoundnessTemplateDirectInputs
  RawCodedRestrictedPADerivationSoundnessCarrierStrongPrefixDirectInductionShell
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
  RawCodedRestrictedPADerivationSoundnessDirectOrIntroductionRightCase
  RawCodedRestrictedPADerivationSoundnessDirectOrEliminationCase
  RawCodedRestrictedPADerivationSoundnessDirectUniversalIntroductionCase
  RawCodedRestrictedPADerivationSoundnessDirectUniversalEliminationCase
  RawCodedRestrictedPADerivationSoundnessDirectExistentialIntroductionCase
  RawCodedRestrictedPADerivationSoundnessDirectExistentialEliminationCase
  RawCodedRestrictedPADerivationSoundnessDirectEqualityReflexivityCase
  RawCodedRestrictedPADerivationSoundnessDirectEqualityEliminationCase
  RawCodedRestrictedPADerivationSoundnessDirectRuleCasesAfterOrIntroductionLeftTruth
  RawCodedRestrictedPADerivationSoundnessDirectRuleCasesAfterImpIntroductionRecursive
  RawCodedRestrictedPADerivationSoundnessNativeDirectClosureRemainder.

Import ListNotations.

Module
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectRuleCasesAfterImpIntroductionTruth.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PABoundedCodedProof.
Import PABoundedRawCodedContextLists.
Import PABoundedRawCodedContextStructure.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedFixedLevelTruthTotality.
Import PABoundedRawCodedProofAssumptionLeaf.
Import PABoundedRawCodedProofBinaryConstructors.
Import PABoundedRawCodedProofImpIConstructor.
Import PABoundedRawCodedProofOrEConstructor.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedPAProvability.
Import PABoundedRawCodedPAAxiomWitnessPrefix.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPALocalProofComposition.
Import PABoundedRawCodedPALocalProofPropositionalRules.
Import PABoundedRawCodedPALocalProofContextInsertUnconditional.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateNumeralParameters.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedTemplateDirectStructuralTranslation.
Import PABoundedRawCodedTemplateDirectStructuralPAAgreement.
Import PABoundedRawCodedTemplateLocalProofStandardWitnessTailTransport.
Import PABoundedRawCodedFormulaBoundAllCarrierBoundary.
Import PABoundedRawCodedDynamicTruthPredecessorDirectEvidenceLogicalRoots.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessTemplateDirectInputs.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessCarrierStrongPrefixDirectInductionShell.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectRuleDispatchFrontier.
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
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectRuleCasesAfterOrIntroductionLeftTruth.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectRuleCasesAfterImpIntroductionRecursive.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessNativeDirectClosureRemainder.

(** The represented propositional core.  All three resources begin in one
    context.  Explicit guarded insertion moves them below the two hypotheses
    discharged by Imp-I and below the branch assumption consumed by Or-E. *)
Theorem raw_codedPALocalProofOf_impTruth_of_predecessor_split : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      context formulaRelation sigmaLeft sigmaRight sigmaImp piLeft
      decisionRoot falseLeftRoot trueRightRoot,
  RawContextListRealizable M context ->
  RawCodedFormulaAtomicallyAdequate M formulaRelation ->
  RawCodedFormulaAtomicallyAdequate M
    (rawFormulaImpCode M sigmaLeft sigmaRight) ->
  RawCodedFormulaAtomicallyAdequate M sigmaLeft ->
  RawCodedFormulaAtomicallyAdequate M piLeft ->
  RawCodedPALocalProofOf M context
    (rawFormulaOrCode M sigmaLeft piLeft) decisionRoot ->
  RawCodedPALocalProofOf M context
    (rawFormulaImpCode M formulaRelation
      (rawFormulaImpCode M piLeft sigmaImp)) falseLeftRoot ->
  RawCodedPALocalProofOf M context
    (rawFormulaImpCode M formulaRelation
      (rawFormulaImpCode M sigmaRight sigmaImp)) trueRightRoot ->
  exists root,
    RawCodedPALocalProofOf M context
      (rawFormulaImpCode M formulaRelation
        (rawFormulaImpCode M
          (rawFormulaImpCode M sigmaLeft sigmaRight) sigmaImp)) root.
Proof.
  intros M hPA context formulaRelation sigmaLeft sigmaRight sigmaImp
    piLeft decisionRoot falseLeftRoot trueRightRoot
    hcontext hformulaAdequate himplicationAdequate
    hsigmaLeftAdequate hpiLeftAdequate
    hdecision hfalseLeft htrueRight.
  set (truthPremise := rawFormulaImpCode M sigmaLeft sigmaRight).
  set (formulaContext := rawListNode M formulaRelation context).
  assert (hformulaContext : RawContextListRealizable M formulaContext).
  { unfold formulaContext. exact (raw_contextList_cons_realizable
      M hPA context formulaRelation hcontext). }

  destruct (raw_codedPALocalProof_adequateConsTransplant
    M hPA context formulaRelation
    (rawFormulaOrCode M sigmaLeft piLeft) decisionRoot
    hformulaAdequate hcontext hdecision)
    as [decisionFormulaRoot hdecisionFormula].
  destruct (raw_codedPALocalProof_adequateConsTransplant
    M hPA context formulaRelation
    (rawFormulaImpCode M formulaRelation
      (rawFormulaImpCode M piLeft sigmaImp)) falseLeftRoot
    hformulaAdequate hcontext hfalseLeft)
    as [falseFormulaRoot hfalseFormula].
  destruct (raw_codedPALocalProof_adequateConsTransplant
    M hPA context formulaRelation
    (rawFormulaImpCode M formulaRelation
      (rawFormulaImpCode M sigmaRight sigmaImp)) trueRightRoot
    hformulaAdequate hcontext htrueRight)
    as [trueFormulaRoot htrueFormula].
  pose proof (raw_codedPALocalProofOf_assumption
    M hPA context formulaRelation hcontext) as hformulaHead.

  set (premiseContext := rawListNode M truthPremise formulaContext).
  assert (hpremiseContext : RawContextListRealizable M premiseContext).
  { unfold premiseContext. exact (raw_contextList_cons_realizable
      M hPA formulaContext truthPremise hformulaContext). }
  destruct (raw_codedPALocalProof_adequateConsTransplant
    M hPA formulaContext truthPremise
    (rawFormulaOrCode M sigmaLeft piLeft) decisionFormulaRoot
    himplicationAdequate hformulaContext hdecisionFormula)
    as [decisionPremiseRoot hdecisionPremise].
  destruct (raw_codedPALocalProof_adequateConsTransplant
    M hPA formulaContext truthPremise
    (rawFormulaImpCode M formulaRelation
      (rawFormulaImpCode M piLeft sigmaImp)) falseFormulaRoot
    himplicationAdequate hformulaContext hfalseFormula)
    as [falsePremiseRoot hfalsePremise].
  destruct (raw_codedPALocalProof_adequateConsTransplant
    M hPA formulaContext truthPremise
    (rawFormulaImpCode M formulaRelation
      (rawFormulaImpCode M sigmaRight sigmaImp)) trueFormulaRoot
    himplicationAdequate hformulaContext htrueFormula)
    as [truePremiseRoot htruePremise].
  destruct (raw_codedPALocalProof_adequateConsTransplant
    M hPA formulaContext truthPremise formulaRelation
    (rawProofAssumptionRoot M formulaContext formulaRelation)
    himplicationAdequate hformulaContext hformulaHead)
    as [formulaPremiseRoot hformulaPremise].
  pose proof (raw_codedPALocalProofOf_assumption
    M hPA formulaContext truthPremise hformulaContext) as hpremiseHead.

  (** Sigma(left): apply the assumed preservation implication, then the
      ImpTrueRight row. *)
  set (sigmaContext := rawListNode M sigmaLeft premiseContext).
  assert (hsigmaContext : RawContextListRealizable M sigmaContext).
  { unfold sigmaContext. exact (raw_contextList_cons_realizable
      M hPA premiseContext sigmaLeft hpremiseContext). }
  destruct (raw_codedPALocalProof_adequateConsTransplant
    M hPA premiseContext sigmaLeft
    (rawFormulaImpCode M formulaRelation
      (rawFormulaImpCode M sigmaRight sigmaImp)) truePremiseRoot
    hsigmaLeftAdequate hpremiseContext htruePremise)
    as [trueSigmaRoot htrueSigma].
  destruct (raw_codedPALocalProof_adequateConsTransplant
    M hPA premiseContext sigmaLeft formulaRelation formulaPremiseRoot
    hsigmaLeftAdequate hpremiseContext hformulaPremise)
    as [formulaSigmaRoot hformulaSigma].
  destruct (raw_codedPALocalProof_adequateConsTransplant
    M hPA premiseContext sigmaLeft truthPremise
    (rawProofAssumptionRoot M premiseContext truthPremise)
    hsigmaLeftAdequate hpremiseContext hpremiseHead)
    as [premiseSigmaRoot hpremiseSigma].
  pose proof (raw_codedPALocalProofOf_assumption
    M hPA premiseContext sigmaLeft hpremiseContext) as hsigmaHead.
  set (sigmaRightRoot := rawProofImpERoot M sigmaContext
    sigmaLeft sigmaRight premiseSigmaRoot
    (rawProofAssumptionRoot M sigmaContext sigmaLeft)).
  assert (hsigmaRight : RawCodedPALocalProofOf M sigmaContext
      sigmaRight sigmaRightRoot).
  {
    unfold sigmaRightRoot, truthPremise in hpremiseSigma.
    exact (raw_codedPALocalProofOf_impE M hPA sigmaContext
      sigmaLeft sigmaRight premiseSigmaRoot
      (rawProofAssumptionRoot M sigmaContext sigmaLeft)
      hpremiseSigma hsigmaHead).
  }
  set (trueAfterFormulaRoot := rawProofImpERoot M sigmaContext
    formulaRelation (rawFormulaImpCode M sigmaRight sigmaImp)
    trueSigmaRoot formulaSigmaRoot).
  assert (htrueAfterFormula : RawCodedPALocalProofOf M sigmaContext
      (rawFormulaImpCode M sigmaRight sigmaImp) trueAfterFormulaRoot).
  {
    unfold trueAfterFormulaRoot.
    exact (raw_codedPALocalProofOf_impE M hPA sigmaContext
      formulaRelation (rawFormulaImpCode M sigmaRight sigmaImp)
      trueSigmaRoot formulaSigmaRoot htrueSigma hformulaSigma).
  }
  set (sigmaBranchRoot := rawProofImpERoot M sigmaContext
    sigmaRight sigmaImp trueAfterFormulaRoot sigmaRightRoot).
  assert (hsigmaBranch : RawCodedPALocalProofOf M sigmaContext
      sigmaImp sigmaBranchRoot).
  {
    unfold sigmaBranchRoot.
    exact (raw_codedPALocalProofOf_impE M hPA sigmaContext
      sigmaRight sigmaImp trueAfterFormulaRoot sigmaRightRoot
      htrueAfterFormula hsigmaRight).
  }

  (** Pi(left): the ImpFalseLeft row needs no use of the preservation
      premise, but it still shares the exact same parent context. *)
  set (piContext := rawListNode M piLeft premiseContext).
  assert (hpiContext : RawContextListRealizable M piContext).
  { unfold piContext. exact (raw_contextList_cons_realizable
      M hPA premiseContext piLeft hpremiseContext). }
  destruct (raw_codedPALocalProof_adequateConsTransplant
    M hPA premiseContext piLeft
    (rawFormulaImpCode M formulaRelation
      (rawFormulaImpCode M piLeft sigmaImp)) falsePremiseRoot
    hpiLeftAdequate hpremiseContext hfalsePremise)
    as [falsePiRoot hfalsePi].
  destruct (raw_codedPALocalProof_adequateConsTransplant
    M hPA premiseContext piLeft formulaRelation formulaPremiseRoot
    hpiLeftAdequate hpremiseContext hformulaPremise)
    as [formulaPiRoot hformulaPi].
  pose proof (raw_codedPALocalProofOf_assumption
    M hPA premiseContext piLeft hpremiseContext) as hpiHead.
  set (falseAfterFormulaRoot := rawProofImpERoot M piContext
    formulaRelation (rawFormulaImpCode M piLeft sigmaImp)
    falsePiRoot formulaPiRoot).
  assert (hfalseAfterFormula : RawCodedPALocalProofOf M piContext
      (rawFormulaImpCode M piLeft sigmaImp) falseAfterFormulaRoot).
  {
    unfold falseAfterFormulaRoot.
    exact (raw_codedPALocalProofOf_impE M hPA piContext
      formulaRelation (rawFormulaImpCode M piLeft sigmaImp)
      falsePiRoot formulaPiRoot hfalsePi hformulaPi).
  }
  set (piBranchRoot := rawProofImpERoot M piContext
    piLeft sigmaImp falseAfterFormulaRoot
    (rawProofAssumptionRoot M piContext piLeft)).
  assert (hpiBranch : RawCodedPALocalProofOf M piContext
      sigmaImp piBranchRoot).
  {
    unfold piBranchRoot.
    exact (raw_codedPALocalProofOf_impE M hPA piContext
      piLeft sigmaImp falseAfterFormulaRoot
      (rawProofAssumptionRoot M piContext piLeft)
      hfalseAfterFormula hpiHead).
  }

  set (splitRoot := rawProofOrERoot M premiseContext
    sigmaLeft piLeft sigmaImp decisionPremiseRoot
    sigmaBranchRoot piBranchRoot).
  assert (hsplit : RawCodedPALocalProofOf M premiseContext
      sigmaImp splitRoot).
  {
    unfold splitRoot.
    exact (raw_codedPALocalProofOf_orE M hPA premiseContext
      sigmaLeft piLeft sigmaImp decisionPremiseRoot
      sigmaBranchRoot piBranchRoot
      hdecisionPremise hsigmaBranch hpiBranch).
  }
  set (premiseImpRoot := rawProofImpIRoot M formulaContext
    truthPremise sigmaImp splitRoot).
  assert (hpremiseImp : RawCodedPALocalProofOf M formulaContext
      (rawFormulaImpCode M truthPremise sigmaImp) premiseImpRoot).
  {
    unfold premiseImpRoot, premiseContext.
    exact (raw_codedPALocalProofOf_impI M hPA formulaContext
      truthPremise sigmaImp splitRoot hsplit).
  }
  exists (rawProofImpIRoot M context formulaRelation
    (rawFormulaImpCode M truthPremise sigmaImp) premiseImpRoot).
  unfold formulaContext.
  exact (raw_codedPALocalProofOf_impI M hPA context formulaRelation
    (rawFormulaImpCode M truthPremise sigmaImp) premiseImpRoot
    hpremiseImp).
Qed.

(** Exact non-circular production boundary in the direct Imp-I ready
    context.  The Pi code is retained because the direct structural input
    exposes only the Sigma truth selector. *)
Definition RawCoqRestrictedPADirectImpIntroductionFixedRowSplitRoots
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    (tail : TemplateContext) : Prop :=
  exists piLeft : M,
  RawCodedFormulaAtomicallyAdequate M piLeft /\
  (exists decisionRoot,
    RawCodedPALocalProofOf M
      (rawTemplateContextCode
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        (coqRestrictedPADirectStrongStepImpIntroductionReadyContext tail))
      (rawFormulaOrCode M
        (rawDirectTemplateFormula inputs
          coqRestrictedPADirectImpIntroductionAntecedentTruthTemplate)
        piLeft) decisionRoot) /\
  (exists falseLeftRoot,
    RawCodedPALocalProofOf M
      (rawTemplateContextCode
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        (coqRestrictedPADirectStrongStepImpIntroductionReadyContext tail))
      (rawFormulaImpCode M
        (rawDirectTemplateFormula inputs
          coqRestrictedPADirectImpIntroductionFormulaCodeTemplate)
        (rawFormulaImpCode M
          piLeft
          (rawDirectTemplateFormula inputs
            coqRestrictedPADirectAssumptionOuterConclusionTruthTemplate)))
      falseLeftRoot) /\
  (exists trueRightRoot,
    RawCodedPALocalProofOf M
      (rawTemplateContextCode
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        (coqRestrictedPADirectStrongStepImpIntroductionReadyContext tail))
      (rawFormulaImpCode M
        (rawDirectTemplateFormula inputs
          coqRestrictedPADirectImpIntroductionFormulaCodeTemplate)
        (rawFormulaImpCode M
          (rawDirectTemplateFormula inputs
            coqRestrictedPADirectImpIntroductionConsequentTruthTemplate)
          (rawDirectTemplateFormula inputs
            coqRestrictedPADirectAssumptionOuterConclusionTruthTemplate)))
      trueRightRoot).

Arguments RawCoqRestrictedPADirectImpIntroductionFixedRowSplitRoots
  M hPA inputs tail : clear implicits.

Theorem raw_impIntroductionDynamicTruthLawRoot_of_fixedRowSplitRoots :
  forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (inputs : RawCodedTemplateDirectStructuralInputs M) tail,
  RawCoqRestrictedPADirectImpIntroductionFixedRowSplitRoots
    M hPA inputs tail ->
  RawCoqRestrictedPADirectImpIntroductionDynamicTruthLawRoot
    M hPA inputs tail.
Proof.
  intros M hPA inputs tail hsplit.
  destruct hsplit as
    (piLeft & hpiAdequate &
      (decisionRoot & hdecision) &
      (falseLeftRoot & hfalseLeft) &
      (trueRightRoot & htrueRight)).
  set (translation := rawDirectStructuralTemplateTranslation M hPA inputs).
  set (context := rawTemplateContextCode translation
    (coqRestrictedPADirectStrongStepImpIntroductionReadyContext tail)).
  set (formulaRelation := rawDirectTemplateFormula inputs
    coqRestrictedPADirectImpIntroductionFormulaCodeTemplate).
  set (sigmaLeft := rawDirectTemplateFormula inputs
    coqRestrictedPADirectImpIntroductionAntecedentTruthTemplate).
  set (sigmaRight := rawDirectTemplateFormula inputs
    coqRestrictedPADirectImpIntroductionConsequentTruthTemplate).
  set (sigmaImp := rawDirectTemplateFormula inputs
    coqRestrictedPADirectAssumptionOuterConclusionTruthTemplate).
  assert (hcontext : RawContextListRealizable M context).
  {
    unfold context, translation.
    apply raw_templateContext_realizable. exact hPA.
  }
  assert (hformulaAdequate : RawCodedFormulaAtomicallyAdequate M
      formulaRelation).
  {
    unfold formulaRelation.
    exact (rawDirectTemplateFormula_atomically_adequate M hPA inputs _).
  }
  assert (himplicationAdequate : RawCodedFormulaAtomicallyAdequate M
      (rawFormulaImpCode M sigmaLeft sigmaRight)).
  {
    pose proof (rawDirectTemplateFormula_atomically_adequate
      M hPA inputs
      (tfImp
        coqRestrictedPADirectImpIntroductionAntecedentTruthTemplate
        coqRestrictedPADirectImpIntroductionConsequentTruthTemplate))
      as himplicationTemplateAdequate.
    rewrite rawDirectTemplateFormula_imp_code
      in himplicationTemplateAdequate.
    unfold sigmaLeft, sigmaRight.
    exact himplicationTemplateAdequate.
  }
  assert (hsigmaLeftAdequate : RawCodedFormulaAtomicallyAdequate M
      sigmaLeft).
  {
    unfold sigmaLeft.
    exact (rawDirectTemplateFormula_atomically_adequate M hPA inputs _).
  }
  destruct
    (raw_codedPALocalProofOf_impTruth_of_predecessor_split
      M hPA context formulaRelation sigmaLeft sigmaRight sigmaImp piLeft
      decisionRoot falseLeftRoot trueRightRoot
      hcontext hformulaAdequate himplicationAdequate
      hsigmaLeftAdequate hpiAdequate
      hdecision hfalseLeft htrueRight)
    as [root hroot].
  exists root.
  change (RawCodedPALocalProofOf M context
    (rawFormulaImpCode M formulaRelation
      (rawFormulaImpCode M
        (rawFormulaImpCode M sigmaLeft sigmaRight) sigmaImp)) root).
  exact hroot.
Qed.

(** Exact eighteen-field remainder after deleting the dynamic Imp-I truth
    field from the post-recursive record. *)
Record RawCoqRestrictedPADirectRuleCaseSemanticRootsAfterImpIntroductionTruth
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    (tail : TemplateContext) : Prop := {
  rawCoqRestrictedPADirectAfterImpTruth_impElimination :
    RawCoqRestrictedPADirectImpERecursiveModusPonensLawRoot M
      (rawDirectStructuralTemplateTranslation M hPA inputs) tail;
  rawCoqRestrictedPADirectAfterImpTruth_bottomElimination :
    RawCoqRestrictedPADirectBottomRecursiveContradictionLawRoot M
      (rawDirectStructuralTemplateTranslation M hPA inputs) tail;
  rawCoqRestrictedPADirectAfterImpTruth_excludedMiddle :
    RawCoqRestrictedPADirectExcludedMiddleTruthLawRoot M
      (rawDirectStructuralTemplateTranslation M hPA inputs) tail;
  rawCoqRestrictedPADirectAfterImpTruth_andIntroduction :
    RawCoqRestrictedPADirectStrongStepAndIntroductionSemanticRoots
      M hPA inputs tail;
  rawCoqRestrictedPADirectAfterImpTruth_andEliminationLeftRecursive :
    RawCoqRestrictedPADirectAndEliminationLeftRecursiveChildLawRoot
      M hPA inputs tail;
  rawCoqRestrictedPADirectAfterImpTruth_andEliminationLeftTruth :
    RawCoqRestrictedPADirectAndEliminationLeftDynamicTruthLawRoot
      M hPA inputs tail;
  rawCoqRestrictedPADirectAfterImpTruth_andEliminationRightRecursive :
    RawCoqRestrictedPADirectAndEliminationRightRecursiveChildLawRoot
      M hPA inputs tail;
  rawCoqRestrictedPADirectAfterImpTruth_andEliminationRightTruth :
    RawCoqRestrictedPADirectAndEliminationRightDynamicTruthLawRoot
      M hPA inputs tail;
  rawCoqRestrictedPADirectAfterImpTruth_orIntroductionRightRecursive :
    RawCoqRestrictedPADirectOrIntroductionRightRecursiveChildLawRoot
      M hPA inputs tail;
  rawCoqRestrictedPADirectAfterImpTruth_orIntroductionRightTruth :
    RawCoqRestrictedPADirectOrIntroductionRightDynamicTruthLawRoot
      M hPA inputs tail;
  rawCoqRestrictedPADirectAfterImpTruth_orElimination :
    RawCoqRestrictedPADirectOrEliminationSemanticRoots M hPA inputs tail;
  rawCoqRestrictedPADirectAfterImpTruth_universalIntroduction :
    RawCoqRestrictedPADirectUniversalIntroductionSemanticRoots
      M hPA inputs tail;
  rawCoqRestrictedPADirectAfterImpTruth_universalEliminationRecursive :
    RawCoqRestrictedPADirectUniversalEliminationRecursiveChildLawRoot
      M hPA inputs tail;
  rawCoqRestrictedPADirectAfterImpTruth_universalEliminationTruth :
    RawCoqRestrictedPADirectUniversalEliminationDynamicTruthLawRoot
      M hPA inputs tail;
  rawCoqRestrictedPADirectAfterImpTruth_existentialIntroduction :
    RawCoqRestrictedPADirectStrongStepExistentialIntroductionSemanticRoots
      M hPA inputs tail;
  rawCoqRestrictedPADirectAfterImpTruth_existentialElimination :
    RawCoqRestrictedPADirectExistentialEliminationSemanticRoots
      M hPA inputs tail;
  rawCoqRestrictedPADirectAfterImpTruth_equalityReflexivity :
    RawCoqRestrictedPADirectEqualityReflexivityAtomicTruthLawRoot M
      (rawDirectStructuralTemplateTranslation M hPA inputs) tail;
  rawCoqRestrictedPADirectAfterImpTruth_equalityElimination :
    RawCoqRestrictedPADirectStrongStepEqualityEliminationSemanticRoots
      M hPA inputs tail
}.

Arguments
  RawCoqRestrictedPADirectRuleCaseSemanticRootsAfterImpIntroductionTruth
  M hPA inputs tail : clear implicits.

Theorem raw_afterImpIntroductionRecursive_of_afterImpIntroductionTruth :
  forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (inputs : RawCodedTemplateDirectStructuralInputs M) tail,
  RawCoqRestrictedPADirectImpIntroductionDynamicTruthLawRoot
    M hPA inputs tail ->
  RawCoqRestrictedPADirectRuleCaseSemanticRootsAfterImpIntroductionTruth
    M hPA inputs tail ->
  RawCoqRestrictedPADirectRuleCaseSemanticRootsAfterImpIntroductionRecursive
    M hPA inputs tail.
Proof.
  intros M hPA inputs tail htruth hremaining.
  destruct hremaining.
  constructor; assumption.
Qed.

(** Selected non-circular inputs for the producer.  The three represented
    roots are exactly the predecessor-decision endpoint and the two missing
    positive implication fixed-row endpoints. *)
Definition RawCoqRestrictedPADirectSelectedImpIntroductionFixedRowSplitTail
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M) : Prop :=
  exists witnesses : StandardPAAxiomWitnessPrefix,
    RawCodedPAAxiomWitnessContext M
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        witnesses (raw_zero M))
      (rawTemplateContextCode
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        (embedPAContext (map witnessedAxiom witnesses))) /\
    RawCoqRestrictedPADirectImpIntroductionFixedRowSplitRoots
      M hPA inputs (embedPAContext (map witnessedAxiom witnesses)).

Arguments
  RawCoqRestrictedPADirectSelectedImpIntroductionFixedRowSplitTail
  M hPA inputs : clear implicits.

(** Actual target root produced from the split, retained separately so the
    later growing-tail merge never transports the residual row interface. *)
Definition RawCoqRestrictedPADirectSelectedImpIntroductionTruthTail
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M) : Prop :=
  exists witnesses : StandardPAAxiomWitnessPrefix,
    RawCodedPAAxiomWitnessContext M
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        witnesses (raw_zero M))
      (rawTemplateContextCode
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        (embedPAContext (map witnessedAxiom witnesses))) /\
    RawCoqRestrictedPADirectImpIntroductionDynamicTruthLawRoot
      M hPA inputs (embedPAContext (map witnessedAxiom witnesses)).

Arguments RawCoqRestrictedPADirectSelectedImpIntroductionTruthTail
  M hPA inputs : clear implicits.

Theorem raw_selectedImpIntroductionTruthTail_of_fixedRowSplit :
  forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (inputs : RawCodedTemplateDirectStructuralInputs M),
  RawCoqRestrictedPADirectSelectedImpIntroductionFixedRowSplitTail
    M hPA inputs ->
  RawCoqRestrictedPADirectSelectedImpIntroductionTruthTail M hPA inputs.
Proof.
  intros M hPA inputs (witnesses & hwitnessed & hsplit).
  exists witnesses. split; [exact hwitnessed |].
  exact (raw_impIntroductionDynamicTruthLawRoot_of_fixedRowSplitRoots
    M hPA inputs (embedPAContext (map witnessedAxiom witnesses)) hsplit).
Qed.

(** The target root uses the same affine ready prefix already audited for
    the preceding recursive-child increment. *)
Theorem raw_impIntroductionTruthLawRoot_surround_witnessed_tail :
  forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    prefix witnesses suffix,
  RawCoqRestrictedPADirectImpIntroductionDynamicTruthLawRoot
    M hPA inputs (embedPAContext (map witnessedAxiom witnesses)) ->
  RawCoqRestrictedPADirectImpIntroductionDynamicTruthLawRoot
    M hPA inputs
      (embedPAContext
        (map witnessedAxiom (prefix ++ (witnesses ++ suffix)))).
Proof.
  intros M hPA inputs prefix witnesses suffix [root hroot].
  rewrite coqRestrictedPADirectImpIntroductionReadyContext_app_witnesses
    in hroot.
  destruct
    (raw_codedPALocalProof_standardWitnessTail_surround_under_prefix
      M hPA
      (rawDirectStructuralTemplateTranslation M hPA inputs)
      (rawDirectStructuralTemplatePAAgreement M hPA inputs)
      (coqRestrictedPADirectStrongStepImpIntroductionReadyContext [])
      prefix witnesses suffix
      (rawDirectTemplateFormula inputs
        coqRestrictedPADirectImpIntroductionDynamicTruthLawTemplate)
      root hroot) as [transportedRoot htransported].
  exists transportedRoot.
  rewrite coqRestrictedPADirectImpIntroductionReadyContext_app_witnesses.
  exact htransported.
Qed.

Definition
    RawCoqRestrictedPADirectRemainingAfterImpIntroductionTruthStandardTailCompiler
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M) : Prop :=
  forall baseWitnesses : StandardPAAxiomWitnessPrefix,
  exists suffix : StandardPAAxiomWitnessPrefix,
    RawCoqRestrictedPADirectRuleCaseSemanticRootsAfterImpIntroductionTruth
      M hPA inputs
      (embedPAContext
        (map witnessedAxiom (baseWitnesses ++ suffix))).

Arguments
  RawCoqRestrictedPADirectRemainingAfterImpIntroductionTruthStandardTailCompiler
  M hPA inputs : clear implicits.

Theorem
    raw_remainingAfterImpIntroductionRecursiveCompiler_of_selectedImpIntroductionTruth
    : forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
      (inputs : RawCodedTemplateDirectStructuralInputs M),
  RawCoqRestrictedPADirectSelectedImpIntroductionTruthTail M hPA inputs ->
  RawCoqRestrictedPADirectRemainingAfterImpIntroductionTruthStandardTailCompiler
    M hPA inputs ->
  RawCoqRestrictedPADirectRemainingAfterImpIntroductionRecursiveStandardTailCompiler
    M hPA inputs.
Proof.
  intros M hPA inputs
    (truthWitnesses & _ & htruth) hremaining baseWitnesses.
  destruct (hremaining (baseWitnesses ++ truthWitnesses))
    as [suffix hremainingTail].
  exists (truthWitnesses ++ suffix).
  apply raw_afterImpIntroductionRecursive_of_afterImpIntroductionTruth.
  - exact (raw_impIntroductionTruthLawRoot_surround_witnessed_tail
      M hPA inputs baseWitnesses truthWitnesses suffix htruth).
  - replace ((baseWitnesses ++ truthWitnesses) ++ suffix)
      with (baseWitnesses ++ (truthWitnesses ++ suffix))
      in hremainingTail by apply app_assoc.
    exact hremainingTail.
Qed.

(** Public merge directly from the non-circular split boundary. *)
Corollary
    raw_remainingAfterImpIntroductionRecursiveCompiler_of_fixedRowSplit
    : forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
      (inputs : RawCodedTemplateDirectStructuralInputs M),
  RawCoqRestrictedPADirectSelectedImpIntroductionFixedRowSplitTail
    M hPA inputs ->
  RawCoqRestrictedPADirectRemainingAfterImpIntroductionTruthStandardTailCompiler
    M hPA inputs ->
  RawCoqRestrictedPADirectRemainingAfterImpIntroductionRecursiveStandardTailCompiler
    M hPA inputs.
Proof.
  intros M hPA inputs hsplit hremaining.
  exact
    (raw_remainingAfterImpIntroductionRecursiveCompiler_of_selectedImpIntroductionTruth
      M hPA inputs
      (raw_selectedImpIntroductionTruthTail_of_fixedRowSplit
        M hPA inputs hsplit)
      hremaining).
Qed.

(** Native endpoint with both Imp-I fields absent from the final
    continuation.  The predecessor decision and two fixed-row producers are
    still explicit in the selected split package. *)
Theorem
    raw_codedPAProofOf_coqRestrictedPADerivationSoundnessUniversalDirect_of_nativeInputs_afterImpIntroductionTruth
    : forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
      (parameters : RawCodedTemplateNumeralParameters M)
      currentGlobalSigma currentGlobalPi predecessorLevel nextSigmaEvidence,
  RawCoqRestrictedPANativeDirectTruthInputsWithClosureAt M hPA parameters
    currentGlobalSigma currentGlobalPi predecessorLevel nextSigmaEvidence ->
  (forall contextTruth conclusionTruth,
    let inputs :=
      rawCoqRestrictedPADerivationSoundnessTemplateDirectStructuralInputs
        M hPA parameters contextTruth conclusionTruth in
    RawCoqRestrictedPADirectSelectedOrIntroductionLeftTruthTail
      M hPA inputs /\
    (RawCoqRestrictedPADirectSelectedImpIntroductionRecursiveTail
      M hPA inputs /\
     (RawCoqRestrictedPADirectSelectedImpIntroductionFixedRowSplitTail
        M hPA inputs /\
      RawCoqRestrictedPADirectRemainingAfterImpIntroductionTruthStandardTailCompiler
        M hPA inputs))) ->
  exists contextTruth conclusionTruth soundnessCertificate,
    RawCodedPAProofOf M
      (rawCoqRestrictedPADerivationSoundnessUniversalDirectCode M
        (rawCoqRestrictedPADerivationSoundnessTemplateDirectStructuralInputs
          M hPA parameters contextTruth conclusionTruth))
      soundnessCertificate.
Proof.
  intros M hPA parameters currentGlobalSigma currentGlobalPi
    predecessorLevel nextSigmaEvidence hinputs hcontinuation.
  apply
    (raw_codedPAProofOf_coqRestrictedPADerivationSoundnessUniversalDirect_of_nativeInputs_afterImpIntroductionRecursive
      M hPA parameters currentGlobalSigma currentGlobalPi predecessorLevel
      nextSigmaEvidence hinputs).
  intros contextTruth conclusionTruth.
  destruct (hcontinuation contextTruth conclusionTruth)
    as [horTruth [hrecursive [hsplit hremaining]]].
  split; [exact horTruth |].
  split; [exact hrecursive |].
  exact
    (raw_remainingAfterImpIntroductionRecursiveCompiler_of_fixedRowSplit
      M hPA
      (rawCoqRestrictedPADerivationSoundnessTemplateDirectStructuralInputs
        M hPA parameters contextTruth conclusionTruth)
      hsplit hremaining).
Qed.

End
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectRuleCasesAfterImpIntroductionTruth.
