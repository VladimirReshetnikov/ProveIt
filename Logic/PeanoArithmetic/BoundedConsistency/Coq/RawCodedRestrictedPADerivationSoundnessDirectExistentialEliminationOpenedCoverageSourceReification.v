(**
  One opened arithmetic source for both recursive children of Ex-E.

  The existential child keeps the parent context, whereas the body child is
  checked in [body :: shift context].  The constructor-generic descent lemma
  previously identified those two contexts.  We first record the harmless
  generalization which separates the constructor's parent context from the
  endpoint context of the selected child, then instantiate it twice.

  The represented source exposes the common formula-coverage witness once
  and returns the two complete child interfaces as a conjunction.  Hence the
  two later recursive-law compilers start on one synchronized PA witness
  suffix rather than selecting unrelated arithmetic sources.
*)

From Stdlib Require Import List Lia.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAListCoding Require Import Representability ListFormulas.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelector CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawModelCompleteness
  RawCodedAssignment
  RawCodedSyntaxConstructors
  RawCodedFormulaOperations
  RawCodedProofConstructors
  RawCodedProofDescent
  RawCodedProofEndpoints
  RawCodedProofRules
  RawCodedProofAtomicAdequacy
  RawCodedProofFormulaCoverage
  RawCodedProofRuleCoverage
  RawCodedRestrictedPAProof
  RawCodedFixedLevelTruthTotality
  RawCodedRestrictedPAConsistencyFormulaCode
  RawCodedTemplateSyntax
  RawCodedTemplateSemantics
  RawCodedTemplateEmbeddedUniversalValidity
  RawCodedTemplateStructuralTranslation
  RawCodedTemplateStructuralPAAgreement
  RawCodedTemplateParameterAbstraction
  RawCodedTemplateDirectStructuralTranslation
  RawCodedRestrictedTargetTemplateContext
  RawCodedRestrictedTargetTemplateSemantics
  RawCodedCarrierRestrictedProofReroot
  RawCodedRestrictedPAConsistencyFromUniversalSoundness
  RawCodedRestrictedPADerivationSoundnessDirectAssumptionCase
  RawCodedRestrictedPADerivationSoundnessDirectAndIntroductionCase
  RawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftRecursiveChildCompilation
  RawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftDynamicRerootValidity
  RawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftOpenedCoverageValidity
  RawCodedRestrictedPADerivationSoundnessDirectAndIntroductionOpenedCoverageValidity
  RawCodedRestrictedPADerivationSoundnessDirectAndIntroductionOpenedCoverageReificationSupport
  RawCodedRestrictedPADerivationSoundnessDirectAndIntroductionOpenedCoverageReificationRestrictedCertificate
  RawCodedRestrictedPADerivationSoundnessDirectAndIntroductionOpenedCoverageReificationAtomicCertificate
  RawCodedRestrictedPADerivationSoundnessDirectAndIntroductionOpenedCoverageReificationFormulaCoverageCertificate
  RawCodedRestrictedPADerivationSoundnessDirectAndIntroductionOpenedCoverageReificationRuleCoverageCertificate
  RawCodedRestrictedPADerivationSoundnessDirectAndIntroductionOpenedCoverageReificationAdmissibleCoreCertificate
  RawCodedRestrictedPADerivationSoundnessDirectAndIntroductionOpenedCoverageReificationCommonCoverageCertificate
  RawCodedRestrictedPADerivationSoundnessRecursiveChildInterface
  RawCodedRestrictedPADerivationSoundnessRecursiveChildEndpointContextInterface
  RawCodedRestrictedPADerivationSoundnessSameContextUnaryChildInterfaceOpenedCoverageSource
  RawCodedProofExEConstructor
  RawCodedRestrictedPADerivationSoundnessDirectExistentialEliminationCase
  RawCodedRestrictedPADerivationSoundnessDirectExistentialEliminationOpenedCoverageDefinitions
  RawCodedRestrictedPADerivationSoundnessDirectExistentialEliminationOpenedCoverageReificationCaseCertificate
  RawCodedRestrictedPADerivationSoundnessDirectExistentialEliminationOpenedCoverageReificationExistentialChildCertificate
  RawCodedRestrictedPADerivationSoundnessDirectExistentialEliminationOpenedCoverageReificationBodyChildCertificate.

Import ListNotations.

Module
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectExistentialEliminationOpenedCoverageSourceReification.

Import PA.
Import PAListRepresentability.
Import PAListFormulas.
Import PAHierarchyReduction.
Import PACanonicalSelector.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawModelCompleteness.
Import PABoundedRawCodedAssignment.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedProofConstructors.
Import PABoundedRawCodedProofDescent.
Import PABoundedRawCodedProofEndpoints.
Import PABoundedRawCodedProofRules.
Import PABoundedRawCodedProofAtomicAdequacy.
Import PABoundedRawCodedProofFormulaCoverage.
Import PABoundedRawCodedProofRuleCoverage.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedFixedLevelTruthTotality.
Import PABoundedRawCodedRestrictedPAConsistencyFormulaCode.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateSemantics.
Import PABoundedRawCodedTemplateEmbeddedUniversalValidity.
Import PABoundedRawCodedTemplateStructuralTranslation.
Import PABoundedRawCodedTemplateStructuralPAAgreement.
Import PABoundedRawCodedTemplateParameterAbstraction.
Import PABoundedRawCodedTemplateDirectStructuralTranslation.
Import PABoundedRawCodedRestrictedTargetTemplateContext.
Import PABoundedRawCodedRestrictedTargetTemplateSemantics.
Import PABoundedRawCodedCarrierRestrictedProofReroot.
Import PABoundedRawCodedRestrictedPAConsistencyFromUniversalSoundness.
Import PABoundedRawCodedRestrictedPADerivationSoundnessDirectAssumptionCase.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndIntroductionCase.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftRecursiveChildCompilation.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftDynamicRerootValidity.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftOpenedCoverageValidity.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndIntroductionOpenedCoverageValidity.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndIntroductionOpenedCoverageReificationSupport.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndIntroductionOpenedCoverageReificationRestrictedCertificate.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndIntroductionOpenedCoverageReificationAtomicCertificate.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndIntroductionOpenedCoverageReificationFormulaCoverageCertificate.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndIntroductionOpenedCoverageReificationRuleCoverageCertificate.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndIntroductionOpenedCoverageReificationAdmissibleCoreCertificate.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndIntroductionOpenedCoverageReificationCommonCoverageCertificate.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessRecursiveChildInterface.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessRecursiveChildEndpointContextInterface.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessSameContextUnaryChildInterfaceOpenedCoverageSource.
Import PABoundedRawCodedProofExEConstructor.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectExistentialEliminationCase.
Export
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectExistentialEliminationOpenedCoverageDefinitions.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectExistentialEliminationOpenedCoverageReificationCaseCertificate.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectExistentialEliminationOpenedCoverageReificationExistentialChildCertificate.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectExistentialEliminationOpenedCoverageReificationBodyChildCertificate.

(** ------------------------------------------------------------------
    Specialized semantic views of the two complete interfaces. *)


(** Reification computations for the case and both child interfaces live in
    independent certificate modules.  The source process sees only their
    opaque equations and assembles the fixed seven-implication skeleton. *)

Lemma raw_existentialElimination_openedLeafFormula_reifies :
    forall input output,
  templateFormulaAsPAFormula
    (templateFormulaAbstractParameter
      coqRestrictedPASoundnessLowerLevelParameterName input) = Some output ->
  templateFormulaAsPAFormula
    (templateFormulaAbstractParameter
      coqRestrictedPASoundnessLowerLevelParameterName input) =
  Some
    (coqRestrictedPADirectExistentialEliminationOpenedLeafFormula input).
Proof.
  intros input output houtput.
  unfold coqRestrictedPADirectExistentialEliminationOpenedLeafFormula.
  now rewrite houtput.
Qed.

Lemma coqRestrictedPADirectExistentialEliminationOpenedCoverageSource_reifies :
  templateFormulaAsPAFormula
    coqRestrictedPADirectExistentialEliminationOpenedCoverageSourceBodyTemplate =
  Some
    coqRestrictedPADirectExistentialEliminationOpenedCoverageSourceBodyFormula.
Proof.
  destruct coqRestrictedPADirectAndIntroductionOpenedRestricted_reifies
    as [restricted hrestricted].
  destruct coqRestrictedPADirectAndIntroductionOpenedAtomic_reifies
    as [atomic hatomic].
  destruct coqRestrictedPADirectAndIntroductionOpenedFormulaCoverage_reifies
    as [formulaCoverage hformulaCoverage].
  destruct coqRestrictedPADirectAndIntroductionOpenedRuleCoverage_reifies
    as [ruleCoverage hruleCoverage].
  destruct coqRestrictedPADirectAndIntroductionOpenedAdmissibleCore_reifies
    as [admissibleCore hadmissibleCore].
  destruct coqRestrictedPADirectAndIntroductionOpenedCommonCoverage_reifies
    as [commonCoverage hcommonCoverage].
  destruct coqRestrictedPADirectExistentialEliminationOpenedCase_reifies
    as [case hcase].
  destruct
    coqRestrictedPADirectExistentialEliminationOpenedExistentialChild_reifies
    as [existentialChild hexistentialChild].
  destruct coqRestrictedPADirectExistentialEliminationOpenedBodyChild_reifies
    as [bodyChild hbodyChild].
  pose proof (raw_existentialElimination_openedLeafFormula_reifies
    _ _ hrestricted) as hrestrictedExact.
  pose proof (raw_existentialElimination_openedLeafFormula_reifies
    _ _ hatomic) as hatomicExact.
  pose proof (raw_existentialElimination_openedLeafFormula_reifies
    _ _ hformulaCoverage) as hformulaCoverageExact.
  pose proof (raw_existentialElimination_openedLeafFormula_reifies
    _ _ hruleCoverage) as hruleCoverageExact.
  pose proof (raw_existentialElimination_openedLeafFormula_reifies
    _ _ hadmissibleCore) as hadmissibleCoreExact.
  pose proof (raw_existentialElimination_openedLeafFormula_reifies
    _ _ hcommonCoverage) as hcommonCoverageExact.
  pose proof (raw_existentialElimination_openedLeafFormula_reifies
    _ _ hcase) as hcaseExact.
  pose proof (raw_existentialElimination_openedLeafFormula_reifies
    _ _ hexistentialChild) as hexistentialChildExact.
  pose proof (raw_existentialElimination_openedLeafFormula_reifies
    _ _ hbodyChild) as hbodyChildExact.
  unfold
    coqRestrictedPADirectExistentialEliminationOpenedCoverageSourceBodyTemplate,
    coqRestrictedPADirectExistentialEliminationOpenedCoverageLawTemplate,
    coqRestrictedPADirectExistentialEliminationChildInterfacesTemplate,
    coqRestrictedPADirectExistentialEliminationOpenedCoverageSourceBodyFormula.
  eapply templateFormulaAsPAFormula_abstract_imp_success.
  - exact hrestrictedExact.
  - eapply templateFormulaAsPAFormula_abstract_imp_success.
    + exact hatomicExact.
    + eapply templateFormulaAsPAFormula_abstract_imp_success.
      * exact hformulaCoverageExact.
      * eapply templateFormulaAsPAFormula_abstract_imp_success.
        -- exact hruleCoverageExact.
        -- eapply templateFormulaAsPAFormula_abstract_imp_success.
           ++ exact hadmissibleCoreExact.
           ++ eapply templateFormulaAsPAFormula_abstract_imp_success.
              ** exact hcommonCoverageExact.
              ** eapply templateFormulaAsPAFormula_abstract_imp_success.
                 --- exact hcaseExact.
                 --- change (templateFormulaAsPAFormula
                       (templateFormulaAbstractParameter
                         coqRestrictedPASoundnessLowerLevelParameterName
                         (tfAnd
                           (templateFormulaRename S
                             coqRestrictedPADirectExistentialEliminationExistentialChildInterfaceTemplate)
                           (templateFormulaRename S
                             coqRestrictedPADirectExistentialEliminationBodyChildInterfaceTemplate))) =
                     Some
                       (pAnd
                         coqRestrictedPADirectExistentialEliminationOpenedExistentialChildBodyFormula
                         coqRestrictedPADirectExistentialEliminationOpenedBodyChildBodyFormula)).
                     eapply templateFormulaAsPAFormula_abstract_and_success.
                     +++ exact hexistentialChildExact.
                     +++ exact hbodyChildExact.
Qed.

End
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectExistentialEliminationOpenedCoverageSourceReification.
