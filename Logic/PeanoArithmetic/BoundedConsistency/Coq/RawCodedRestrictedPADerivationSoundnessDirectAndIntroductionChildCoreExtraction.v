(**
  Represented Ex-E/And-E extraction of both And-I child-interface roots.

  This is one acyclic strict-check boundary of the And-I child compiler.
  Later stages import this module opaquely so Rocq need not recheck its proof
  terms while validating the next represented-proof construction.
*)

From Stdlib Require Import List Lia.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAListCoding Require Import Representability.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelector CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  CodedProof
  PolynomialPairInjectivity
  RawModelCompleteness
  RawCodedAssignment
  RawCodedSyntaxConstructors
  RawCodedFormulaOperations
  RawCodedContextLists
  RawCodedProofConstructors
  RawCodedProofDescent
  RawCodedProofTraversal
  RawCodedProofEndpoints
  RawCodedProofRules
  RawCodedProofAndIConstructor
  RawCodedProofAtomicAdequacy
  RawCodedProofFormulaCoverage
  RawCodedProofRuleCoverage
  RawCodedFixedLevelTruthTotality
  RawCodedFixedLevelTruthAdmissibleLowering
  RawCodedRestrictedPAProof
  RawCodedRestrictedProofAdmissibility
  RawCodedCarrierRestrictedProofReroot
  RawCodedRestrictedPADerivationSoundnessRecursiveChildInterface
  RawCodedRestrictedPAConsistencyFormulaCode
  RawCodedRestrictedTargetTemplateContext
  RawCodedRestrictedTargetTemplateSemantics
  RawCodedPALocalProofExistential
  RawCodedPALocalProofConjunction
  RawCodedPALocalProofUniversalSourceInstance
  RawCodedPAAxiomWitnessPrefix
  RawCodedTemplateSyntax
  RawCodedTemplateSemantics
  RawCodedTemplateProofCompiler
  RawCodedTemplatePAEmbedding
  RawCodedTemplateParameterAbstraction
  RawCodedTemplateDirectStructuralTranslation
  RawCodedTemplateStructuralPAAgreement
  RawCodedTemplateDirectStructuralPAAgreement
  RawCodedTemplateProofCompilerSelfShiftTail
  RawCodedTemplatePAEmbeddingSelfShiftTail
  RawCodedRestrictedPAConsistencyFromUniversalSoundness
  RawCodedRestrictedPADerivationSoundnessDirectStrongStepShell
  RawCodedRestrictedPADerivationSoundnessDirectAndIntroductionCase
  RawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftRecursiveChildCompilation
  RawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftDynamicRerootValidity
  RawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftOpenedCoverageValidity
  RawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftOpenedCoverageCompilation.
From BoundedPAConsistency Require Import
  RawCodedRestrictedPADerivationSoundnessDirectAndIntroductionChildInterfaceSemanticCompilation
  RawCodedRestrictedPADerivationSoundnessDirectAndIntroductionOpenedCoverageValidity
  RawCodedRestrictedPADerivationSoundnessDirectAndIntroductionOpenedCoverageSourceCompilation.

Import ListNotations.

Module PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndIntroductionChildCoreExtraction.

Import PA.
Import PAListRepresentability.
Import PAHierarchyReduction.
Import PACanonicalSelector.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedCodedProof.
Import PABoundedPolynomialPairInjectivity.
Import PABoundedRawModelCompleteness.
Import PABoundedRawCodedAssignment.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedContextLists.
Import PABoundedRawCodedProofConstructors.
Import PABoundedRawCodedProofDescent.
Import PABoundedRawCodedProofTraversal.
Import PABoundedRawCodedProofEndpoints.
Import PABoundedRawCodedProofRules.
Import PABoundedRawCodedProofAndIConstructor.
Import PABoundedRawCodedProofAtomicAdequacy.
Import PABoundedRawCodedProofFormulaCoverage.
Import PABoundedRawCodedProofRuleCoverage.
Import PABoundedRawCodedFixedLevelTruthTotality.
Import PABoundedRawCodedFixedLevelTruthAdmissibleLowering.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedRestrictedProofAdmissibility.
Import PABoundedRawCodedCarrierRestrictedProofReroot.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessRecursiveChildInterface.
Import PABoundedRawCodedRestrictedPAConsistencyFormulaCode.
Import PABoundedRawCodedRestrictedTargetTemplateContext.
Import PABoundedRawCodedRestrictedTargetTemplateSemantics.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPALocalProofConjunction.
Import PABoundedRawCodedPALocalProofUniversalSourceInstance.
Import PABoundedRawCodedPAAxiomWitnessPrefix.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateSemantics.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedTemplatePAEmbedding.
Import PABoundedRawCodedTemplateParameterAbstraction.
Import PABoundedRawCodedTemplateDirectStructuralTranslation.
Import PABoundedRawCodedTemplateStructuralPAAgreement.
Import PABoundedRawCodedTemplateDirectStructuralPAAgreement.
Import PABoundedRawCodedTemplateProofCompilerSelfShiftTail.
Import PABoundedRawCodedTemplatePAEmbeddingSelfShiftTail.
Import PABoundedRawCodedRestrictedPAConsistencyFromUniversalSoundness.
Import PABoundedRawCodedRestrictedPADerivationSoundnessDirectStrongStepShell.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndIntroductionCase.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftRecursiveChildCompilation.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftDynamicRerootValidity.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftOpenedCoverageValidity.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftOpenedCoverageCompilation.
Import PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndIntroductionChildInterfaceSemanticCompilation.
Import PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndIntroductionOpenedCoverageValidity.
Import PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndIntroductionOpenedCoverageSourceCompilation.

(** ------------------------------------------------------------------
    Represented opening of common coverage and extraction of both roots. *)

Definition RawCoqRestrictedPADirectAndIntroductionChildCoreRoots
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    (tail : TemplateContext) : Prop :=
  let translation :=
    rawDirectStructuralTemplateTranslation M hPA inputs in
  let ready :=
    coqRestrictedPADirectStrongStepAndIntroductionReadyContext tail in
  (exists leftRoot : M,
    RawCodedPALocalProofOf M
      (rawTemplateContextCode translation ready)
      (rawTemplateFormula translation
        coqRestrictedPADirectAndIntroductionLeftInterfaceResultTemplate)
      leftRoot) /\
  (exists rightRoot : M,
    RawCodedPALocalProofOf M
      (rawTemplateContextCode translation ready)
      (rawTemplateFormula translation
        coqRestrictedPADirectAndIntroductionRightInterfaceResultTemplate)
      rightRoot).

Arguments RawCoqRestrictedPADirectAndIntroductionChildCoreRoots
  M hPA inputs tail : clear implicits.

Lemma coqRestrictedPADirectAndIntroduction_deep_restricted_agreement :
  coqRestrictedPADirectAndIntroductionDeepRestrictedTemplate =
  coqRestrictedPADirectOrIntroductionLeftDeepRestrictedTemplate.
Proof. reflexivity. Qed.

Lemma coqRestrictedPADirectAndIntroduction_deep_admissible_agreement :
  coqRestrictedPADirectAndIntroductionDeepAdmissibleTemplate =
  coqRestrictedPADirectOrIntroductionLeftDeepAdmissibleTemplate.
Proof. reflexivity. Qed.

Lemma coqRestrictedPADirectAndIntroduction_eigen_inherited : forall
    tail formula,
  In formula
    (coqRestrictedPADirectStrongStepAndIntroductionReadyContext tail) ->
  In (templateFormulaRename S formula)
    (coqRestrictedPADirectAndIntroductionCoverageEigenContext tail).
Proof.
  intros tail formula hin. right.
  unfold templateContextShift, templateContextRename.
  apply in_map. exact hin.
Qed.

Lemma coqRestrictedPADirectAndIntroduction_eigen_coverage_body_in : forall
    tail,
  In coqRestrictedPADirectOrIntroductionLeftDeepCommonCoverageBodyTemplate
    (coqRestrictedPADirectAndIntroductionCoverageEigenContext tail).
Proof. intro tail. left. reflexivity. Qed.

Lemma coqRestrictedPADirectAndIntroduction_eigen_restricted_in : forall
    tail,
  In (templateFormulaRename S
      coqRestrictedPADirectAndIntroductionDeepRestrictedTemplate)
    (coqRestrictedPADirectAndIntroductionCoverageEigenContext tail).
Proof.
  intro tail. apply coqRestrictedPADirectAndIntroduction_eigen_inherited.
  apply coqRestrictedPADirectAndIntroduction_ready_restricted_in.
Qed.

Lemma coqRestrictedPADirectAndIntroduction_eigen_admissible_in : forall
    tail,
  In (templateFormulaRename S
      coqRestrictedPADirectAndIntroductionDeepAdmissibleTemplate)
    (coqRestrictedPADirectAndIntroductionCoverageEigenContext tail).
Proof.
  intro tail. apply coqRestrictedPADirectAndIntroduction_eigen_inherited.
  apply coqRestrictedPADirectAndIntroduction_ready_admissible_in.
Qed.

Lemma coqRestrictedPADirectAndIntroduction_eigen_case_in : forall tail,
  In (templateFormulaRename S
      coqRestrictedPADirectAndIntroductionCaseTemplate)
    (coqRestrictedPADirectAndIntroductionCoverageEigenContext tail).
Proof.
  intro tail. apply coqRestrictedPADirectAndIntroduction_eigen_inherited.
  apply coqRestrictedPADirectAndIntroduction_ready_case_in.
Qed.

Theorem
    raw_andIntroductionChildCoreRoots_of_openedCoverageCompiler : forall
    (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (inputs : RawCodedTemplateDirectStructuralInputs M) tail,
  RawCoqRestrictedPADirectAndIntroductionOpenedCoverageCompilerLawRoot
    M hPA inputs tail ->
  RawCoqRestrictedPADirectAndIntroductionChildCoreRoots
    M hPA inputs tail.
Proof.
  intros M hPA inputs tail (openedRoot & hopened).
  set (translation :=
    rawDirectStructuralTemplateTranslation M hPA inputs).
  set (readyContext :=
    coqRestrictedPADirectStrongStepAndIntroductionReadyContext tail).
  set (eigenContext :=
    coqRestrictedPADirectAndIntroductionCoverageEigenContext tail).
  set (readyCode := rawTemplateContextCode translation readyContext).
  set (eigenCode := rawTemplateContextCode translation eigenContext).

  (** Project the common coverage existential before opening it. *)
  pose proof
    (raw_codedPALocalProofOf_coqRestrictedPADirect_templateAssumption
      M hPA translation readyContext
      coqRestrictedPADirectAndIntroductionDeepAdmissibleTemplate
      (coqRestrictedPADirectAndIntroduction_ready_admissible_in tail))
    as hadmissibleReady.
  rewrite coqRestrictedPADirectAndIntroduction_deep_admissible_agreement
    in hadmissibleReady.
  rewrite coqRestrictedPADirectOrIntroductionLeft_deep_admissible_shape
    in hadmissibleReady.
  rewrite rawTemplateFormula_and in hadmissibleReady.
  pose proof (raw_codedPALocalProofOf_andE2 M hPA _ _ _ _
    hadmissibleReady) as hcommonCoverage.
  rewrite coqRestrictedPADirectOrIntroductionLeft_common_coverage_ex_shape
    in hcommonCoverage.
  rewrite rawTemplateFormula_ex in hcommonCoverage.

  (** Project the four proof-wide parent fields in the eigencontext. *)
  pose proof
    (raw_codedPALocalProofOf_coqRestrictedPADirect_templateAssumption
      M hPA translation eigenContext
      (templateFormulaRename S
        coqRestrictedPADirectAndIntroductionDeepRestrictedTemplate)
      (coqRestrictedPADirectAndIntroduction_eigen_restricted_in tail))
    as hrestrictedEigen.
  rewrite coqRestrictedPADirectAndIntroduction_deep_restricted_agreement
    in hrestrictedEigen.
  rewrite coqRestrictedPADirectOrIntroductionLeft_deep_restricted_shape
    in hrestrictedEigen.
  cbn [templateFormulaRename] in hrestrictedEigen.
  rewrite rawTemplateFormula_and in hrestrictedEigen.
  pose proof (raw_codedPALocalProofOf_andE1 M hPA _ _ _ _
    hrestrictedEigen) as hrestrictedCore.
  pose proof (raw_codedPALocalProofOf_andE2 M hPA _ _ _ _
    hrestrictedEigen) as hrestrictedTail.
  rewrite rawTemplateFormula_and in hrestrictedTail.
  pose proof (raw_codedPALocalProofOf_andE1 M hPA _ _ _ _
    hrestrictedTail) as hatomic.
  pose proof (raw_codedPALocalProofOf_andE2 M hPA _ _ _ _
    hrestrictedTail) as hcoverageTail.
  rewrite rawTemplateFormula_and in hcoverageTail.
  pose proof (raw_codedPALocalProofOf_andE1 M hPA _ _ _ _
    hcoverageTail) as hformulaCoverage.
  pose proof (raw_codedPALocalProofOf_andE2 M hPA _ _ _ _
    hcoverageTail) as hruleCoverage.

  (** The admissibility core is inherited; the coverage body is the fresh
      eigenvariable assumption. *)
  pose proof
    (raw_codedPALocalProofOf_coqRestrictedPADirect_templateAssumption
      M hPA translation eigenContext
      (templateFormulaRename S
        coqRestrictedPADirectAndIntroductionDeepAdmissibleTemplate)
      (coqRestrictedPADirectAndIntroduction_eigen_admissible_in tail))
    as hadmissibleEigen.
  rewrite coqRestrictedPADirectAndIntroduction_deep_admissible_agreement
    in hadmissibleEigen.
  rewrite coqRestrictedPADirectOrIntroductionLeft_deep_admissible_shape
    in hadmissibleEigen.
  cbn [templateFormulaRename] in hadmissibleEigen.
  rewrite rawTemplateFormula_and in hadmissibleEigen.
  pose proof (raw_codedPALocalProofOf_andE1 M hPA _ _ _ _
    hadmissibleEigen) as hadmissibleCore.
  pose proof
    (raw_codedPALocalProofOf_coqRestrictedPADirect_templateAssumption
      M hPA translation eigenContext
      coqRestrictedPADirectOrIntroductionLeftDeepCommonCoverageBodyTemplate
      (coqRestrictedPADirectAndIntroduction_eigen_coverage_body_in tail))
    as hcoverageBody.
  pose proof
    (raw_codedPALocalProofOf_coqRestrictedPADirect_templateAssumption
      M hPA translation eigenContext
      (templateFormulaRename S
        coqRestrictedPADirectAndIntroductionCaseTemplate)
      (coqRestrictedPADirectAndIntroduction_eigen_case_in tail))
    as hcase.

  (** Apply the fixed arithmetic source to all seven literal premises. *)
  unfold
    coqRestrictedPADirectAndIntroductionOpenedCoverageCompilerLawTemplate
    in hopened.
  pose proof
    (raw_codedPALocalProofOf_coqRestrictedPADirect_templateImpE
      M hPA translation eigenContext _ _ openedRoot _
      hopened hrestrictedCore) as hopened1.
  pose proof
    (raw_codedPALocalProofOf_coqRestrictedPADirect_templateImpE
      M hPA translation eigenContext _ _ _ _ hopened1 hatomic)
    as hopened2.
  pose proof
    (raw_codedPALocalProofOf_coqRestrictedPADirect_templateImpE
      M hPA translation eigenContext _ _ _ _ hopened2 hformulaCoverage)
    as hopened3.
  pose proof
    (raw_codedPALocalProofOf_coqRestrictedPADirect_templateImpE
      M hPA translation eigenContext _ _ _ _ hopened3 hruleCoverage)
    as hopened4.
  pose proof
    (raw_codedPALocalProofOf_coqRestrictedPADirect_templateImpE
      M hPA translation eigenContext _ _ _ _ hopened4 hadmissibleCore)
    as hopened5.
  pose proof
    (raw_codedPALocalProofOf_coqRestrictedPADirect_templateImpE
      M hPA translation eigenContext _ _ _ _ hopened5 hcoverageBody)
    as hopened6.
  pose proof
    (raw_codedPALocalProofOf_coqRestrictedPADirect_templateImpE
      M hPA translation eigenContext _ _ _ _ hopened6 hcase)
    as hpairShifted.

  (** Eliminate the common coverage witness, then project both members of the
      resulting represented conjunction. *)
  pose proof
    (raw_codedPALocalProofOf_exE M hPA readyCode
      (rawTemplateContextCode translation
        (templateContextShift readyContext))
      (rawTemplateFormula translation
        coqRestrictedPADirectOrIntroductionLeftDeepCommonCoverageBodyTemplate)
      (rawTemplateFormula translation
        coqRestrictedPADirectAndIntroductionChildInterfacePairTemplate)
      (rawTemplateFormula translation
        (templateFormulaRename S
          coqRestrictedPADirectAndIntroductionChildInterfacePairTemplate))
      _ _ hcommonCoverage
      (raw_templateContext_shift M hPA translation readyContext)
      (rawTemplateFormula_shift translation
        coqRestrictedPADirectAndIntroductionChildInterfacePairTemplate)
      hpairShifted) as hpair.
  rewrite rawTemplateFormula_and in hpair.
  pose proof (raw_codedPALocalProofOf_andE1 M hPA _ _ _ _ hpair)
    as hleft.
  pose proof (raw_codedPALocalProofOf_andE2 M hPA _ _ _ _ hpair)
    as hright.
  split.
  - lazymatch type of hleft with
    | RawCodedPALocalProofOf _ _ _ ?root => exists root; exact hleft
    end.
  - lazymatch type of hright with
    | RawCodedPALocalProofOf _ _ _ ?root => exists root; exact hright
    end.
Qed.

End PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndIntroductionChildCoreExtraction.
