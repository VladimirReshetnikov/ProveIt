(**
  Reduce the excluded-middle truth core to an explicit evidence split.

  The direct excluded-middle case ultimately asks for

      admissible(q) -> Sigma(q).

  Native dynamic truth does not establish this implication as one opaque
  step.  It first decides a selected child evidence code and then proves the
  target in each evidence branch.  This file records exactly that
  propositional interface.  A represented Or-E node combines the two branch
  proofs and a represented Imp-I node discharges admissibility.

  The carrier codes selected for the two evidence alternatives remain
  abstract here.  Later native compilers may instantiate them with the
  concrete Sigma/Pi applications without requiring this structural module to
  know their implementation.  The selected-tail theorem retains the exact
  standard PA witness batch on which all three roots were produced.
*)

From Stdlib Require Import List.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA.
From BoundedPAConsistency Require Import
  CodedProof
  RawCodedSyntaxConstructors
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
  RawCodedRestrictedPADerivationSoundnessDirectExcludedMiddleCase
  RawCodedRestrictedPADerivationSoundnessDirectRuleCasesAfterExcludedMiddle.

Import ListNotations.

Module
  PABoundedRawCodedRestrictedPADirectExcludedMiddleDecisionSplitReduction.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PABoundedCodedProof.
Import PABoundedRawCodedSyntaxConstructors.
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
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectExcludedMiddleCase.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectRuleCasesAfterExcludedMiddle.

(** The branch children are stated in the literal cons contexts required by
    Or-E.  No weakening or hidden context equality is part of this record. *)
Definition RawCoqRestrictedPADirectExcludedMiddleDecisionSplitRoots
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    (tail : TemplateContext) : Prop :=
  let translation := rawDirectStructuralTemplateTranslation M hPA inputs in
  let caseContext := rawTemplateContextCode translation
    (coqRestrictedPADirectExcludedMiddleCaseContext tail) in
  let admissible := rawTemplateFormula translation
    coqRestrictedPADirectExcludedMiddleAdmissibleTemplate in
  let target := rawTemplateFormula translation
    coqRestrictedPADirectExcludedMiddleConclusionTruthTemplate in
  let admissibleContext := rawListNode M admissible caseContext in
  exists sigmaEvidence piEvidence decisionRoot leftRoot rightRoot : M,
    RawCodedPALocalProofOf M admissibleContext
      (rawFormulaOrCode M sigmaEvidence piEvidence) decisionRoot /\
    RawCodedPALocalProofOf M
      (rawListNode M sigmaEvidence admissibleContext) target leftRoot /\
    RawCodedPALocalProofOf M
      (rawListNode M piEvidence admissibleContext) target rightRoot.

Arguments RawCoqRestrictedPADirectExcludedMiddleDecisionSplitRoots
  M hPA inputs tail : clear implicits.

(** Or-E combines the exhaustive evidence alternatives under admissibility;
    Imp-I then produces exactly the historical positive truth core. *)
Theorem raw_excludedMiddleTruthCoreLawRoot_of_decision_split_roots : forall
    (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (inputs : RawCodedTemplateDirectStructuralInputs M) tail,
  RawCoqRestrictedPADirectExcludedMiddleDecisionSplitRoots
    M hPA inputs tail ->
  RawCoqRestrictedPADirectExcludedMiddleTruthCoreLawRoot M
    (rawDirectStructuralTemplateTranslation M hPA inputs) tail.
Proof.
  intros M hPA inputs tail hsplit.
  unfold RawCoqRestrictedPADirectExcludedMiddleDecisionSplitRoots in hsplit.
  cbn zeta in hsplit.
  destruct hsplit as
    (sigmaEvidence & piEvidence & decisionRoot & leftRoot & rightRoot &
      hdecision & hleft & hright).
  set (translation := rawDirectStructuralTemplateTranslation M hPA inputs).
  set (caseContext := rawTemplateContextCode translation
    (coqRestrictedPADirectExcludedMiddleCaseContext tail)).
  set (admissible := rawTemplateFormula translation
    coqRestrictedPADirectExcludedMiddleAdmissibleTemplate).
  set (target := rawTemplateFormula translation
    coqRestrictedPADirectExcludedMiddleConclusionTruthTemplate).
  set (admissibleContext := rawListNode M admissible caseContext).
  pose proof
    (raw_codedPALocalProofOf_orE M hPA admissibleContext
      sigmaEvidence piEvidence target
      decisionRoot leftRoot rightRoot hdecision hleft hright) as htarget.
  lazymatch type of htarget with
  | RawCodedPALocalProofOf _ _ _ ?splitRoot =>
      pose proof
        (raw_codedPALocalProofOf_impI M hPA caseContext
          admissible target splitRoot htarget) as hcore
  end.
  unfold RawCoqRestrictedPADirectExcludedMiddleTruthCoreLawRoot.
  lazymatch type of hcore with
  | RawCodedPALocalProofOf _ _ _ ?root => exists root
  end.
  unfold coqRestrictedPADirectExcludedMiddleTruthCoreTemplate.
  rewrite rawTemplateFormula_imp.
  exact hcore.
Qed.

(** Standard-tail form matching the selected-core consumer used by the
    growing direct rule-case continuation.  All three supplied roots remain
    on the one standard context; only the affine context-code equality is
    used to view that context as a metatheoretic template tail. *)
Theorem
    raw_selectedExcludedMiddleTruthCoreTail_of_standard_decision_split :
  forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    (witnesses : StandardPAAxiomWitnessPrefix)
    sigmaEvidence piEvidence decisionRoot leftRoot rightRoot,
  let translation := rawDirectStructuralTemplateTranslation M hPA inputs in
  let standardContext := rawStandardPAAxiomWitnessPrefixContextCode M
    witnesses (raw_zero M) in
  let caseContext := rawTemplateContextCodeOnTail translation standardContext
    (coqRestrictedPADirectExcludedMiddleCaseContext []) in
  let admissible := rawTemplateFormula translation
    coqRestrictedPADirectExcludedMiddleAdmissibleTemplate in
  let target := rawTemplateFormula translation
    coqRestrictedPADirectExcludedMiddleConclusionTruthTemplate in
  let admissibleContext := rawListNode M admissible caseContext in
  RawCodedPAAxiomWitnessContext M
    (rawStandardPAAxiomWitnessPrefixWitnessListCode M
      witnesses (raw_zero M)) standardContext ->
  RawCodedPALocalProofOf M admissibleContext
    (rawFormulaOrCode M sigmaEvidence piEvidence) decisionRoot ->
  RawCodedPALocalProofOf M
    (rawListNode M sigmaEvidence admissibleContext) target leftRoot ->
  RawCodedPALocalProofOf M
    (rawListNode M piEvidence admissibleContext) target rightRoot ->
  RawCoqRestrictedPADirectSelectedExcludedMiddleTruthCoreTail
    M hPA inputs.
Proof.
  intros M hPA inputs witnesses
    sigmaEvidence piEvidence decisionRoot leftRoot rightRoot
    translation standardContext caseContext admissible target
    admissibleContext hwitnessed hdecision hleft hright.
  cbn zeta in *.
  assert (hcaseContextCode :
      caseContext =
      rawTemplateContextCode translation
        (coqRestrictedPADirectExcludedMiddleCaseContext
          (embedPAContext (map witnessedAxiom witnesses)))).
  {
    unfold caseContext, standardContext.
    rewrite <- (raw_templateContextCode_embedPAAxiomWitnesses
      M translation
      (rawDirectStructuralTemplatePAAgreement M hPA inputs) witnesses).
    rewrite <- (raw_templateContextCode_app_on_tail_general
      M translation
      (coqRestrictedPADirectExcludedMiddleCaseContext [])
      (embedPAContext (map witnessedAxiom witnesses))).
    rewrite <- coqRestrictedPADirectExcludedMiddleCaseContext_app_witnesses.
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
  unfold admissibleContext in hdecision, hleft, hright.
  rewrite hcaseContextCode in hdecision, hleft, hright.
  exists witnesses. split; [exact htargetWitnessed |].
  apply raw_excludedMiddleTruthCoreLawRoot_of_decision_split_roots.
  unfold RawCoqRestrictedPADirectExcludedMiddleDecisionSplitRoots.
  cbn zeta.
  exists sigmaEvidence, piEvidence, decisionRoot, leftRoot, rightRoot.
  split; [exact hdecision |].
  split; [exact hleft | exact hright].
Qed.

End
  PABoundedRawCodedRestrictedPADirectExcludedMiddleDecisionSplitReduction.
