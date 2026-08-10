(** Definitions shared by the independently checked Or-E child shapes. *)

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
  RawCodedRestrictedPADerivationSoundnessDirectOrEliminationOpenedCoverageDefinitions
  RawCodedRestrictedPADerivationSoundnessRecursiveChildInterface
  RawCodedRestrictedPADerivationSoundnessRecursiveChildEndpointContextInterface
  RawCodedRestrictedPADerivationSoundnessSameContextUnaryChildInterfaceOpenedCoverageSource
  RawCodedProofOrEConstructor
  RawCodedRestrictedPADerivationSoundnessDirectOrEliminationCase.

Import ListNotations.

Module
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrEliminationOpenedCoverageSharedShapesDefinitions.

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
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrEliminationOpenedCoverageDefinitions.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessRecursiveChildInterface.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessRecursiveChildEndpointContextInterface.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessSameContextUnaryChildInterfaceOpenedCoverageSource.
Import PABoundedRawCodedProofOrEConstructor.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrEliminationCase.

(** Stable component names prevent later compilers from duplicating the
    strong-prefix destructors for each finite-selector branch. *)
Definition coqRestrictedPADirectOrEliminationChildRestrictedTemplate child :=
  coqRestrictedPADirectAndIntroductionChildRestrictedTemplate
    (coqRestrictedPADirectOrEliminationChildTerm child)
    (coqRestrictedPADirectOrEliminationChildContextTerm child)
    (coqRestrictedPADirectOrEliminationChildConclusionTerm child).

Definition coqRestrictedPADirectOrEliminationChildEndpointInterfaceTemplate
    child :=
  coqRestrictedPADirectAndIntroductionChildEndpointTemplate
    (coqRestrictedPADirectOrEliminationChildTerm child)
    (coqRestrictedPADirectOrEliminationChildContextTerm child)
    (coqRestrictedPADirectOrEliminationChildConclusionTerm child).

Definition coqRestrictedPADirectOrEliminationChildAdmissibleTemplate child :=
  coqRestrictedPADirectAndIntroductionChildAdmissibleTemplate
    (coqRestrictedPADirectOrEliminationChildTerm child)
    (coqRestrictedPADirectOrEliminationChildContextTerm child)
    (coqRestrictedPADirectOrEliminationChildConclusionTerm child).

(** The common formula-coverage witness shifts every constructor variable by
    one before the recursive child interface is interpreted. *)
Definition RawCoqRestrictedPAOrEliminationChildInterface
    (child : CoqRestrictedPAOrEliminationChild)
    (M : RawPAModel) (variables : nat -> M)
    (parameters : TemplateParameterName -> M) : Prop :=
  let shifted := fun index => variables (S index) in
  let childCode := raw_term_eval M shifted
    (coqRestrictedPADirectOrEliminationChildPATerm child) in
  let childContext := raw_term_eval M shifted
    (coqRestrictedPADirectOrEliminationChildContextPATerm child) in
  let childConclusion := raw_term_eval M shifted
    (coqRestrictedPADirectOrEliminationChildConclusionPATerm child) in
  rawLt M childCode (variables 13) /\
  RawCarrierRestrictedProofAt M shifted
    (parameters coqRestrictedPASoundnessLowerLevelParameterName)
    childCode /\
  RawProofAtomicallyAdequate M childCode /\
  RawProofHasFormulaCoverage M childCode /\
  RawProofRuleCoverage M childCode /\
  RawProofRuleValid M childCode childContext childConclusion /\
  RawCodedFormulaAtomicallyAdequate M childConclusion /\
  RawCodedAssignmentDefinedThrough M
    (variables 10) (variables 9) childConclusion /\
  RawCarrierFormulaQuantifierBounded M
    (parameters coqRestrictedPASoundnessLowerLevelParameterName)
    childConclusion /\
  exists coverageBound,
    RawProofFormulaCoverage M childCode coverageBound /\
    RawCodedAssignmentDefinedThrough M
      (variables 10) (variables 9) coverageBound.

End
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrEliminationOpenedCoverageSharedShapesDefinitions.
