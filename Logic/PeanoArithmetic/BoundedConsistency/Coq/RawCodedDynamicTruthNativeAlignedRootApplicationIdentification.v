(**
  Reroot the native aligned Sigma/Pi evidence at arbitrary template terms.

  Structural alignment identifies each global predecessor source with its
  direct truth selector only at the canonical three-variable interface
  [#2,#1,#0].  Rule compilers, however, consume evidence below their own
  existential witnesses.  Their formula and assignment arguments therefore
  occupy unrelated indices (for Imp-I, for example, [#6,#9,#8]).

  This module closes that code-identification gap without adding a semantic
  premise.  The generic ternary congruence theorem transports the canonical
  equality through a second represented application.  A finite scoped
  substitution calculation then shows that this second application is
  exactly simultaneous rerooting.  The main theorem is deliberately
  quantified over all three root terms, so every recursive rule case can
  reuse it rather than proving its own variable arithmetic.
*)

From Stdlib Require Import List Arith Lia.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedTemplateSyntax
  RawCodedTemplateRenamingSubstitution
  RawCodedTemplateDirectStructuralTranslation
  RawCodedTemplateTripleUniversalOpening
  RawCodedRestrictedPAConsistencyFromUniversalSoundness
  RawCodedRestrictedPATemplateTernaryApplicationCompilation
  RawCodedDirectTemplateTernaryApplicationCongruence
  RawCodedRestrictedPADerivationSoundnessTemplateDirectInputs
  RawCodedDynamicTruthPredecessorGlobalExistentialElimination
  RawCodedDynamicTruthSuccessorRowsAppendNormalization
  RawCodedDynamicTruthNativeGlobalEvidencePermutation
  RawCodedDynamicTruthNativeLocalStagedCallbackCompilation
  RawCodedFourStateTableAppendTemplateGlobalTraversalAssembly
  RawCodedFourStateTableAppendPermutedTemplateGlobalTraversalAssembly
  RawCodedDynamicTruthNativeAlignedStrongStepLogicalRootsCompilation
  RawCodedRestrictedPADerivationSoundnessDirectAssumptionCase
  RawCodedRestrictedPADerivationSoundnessDirectImpIntroductionCase
  RawCodedRestrictedPADirectImpIntroductionPositiveBodyCompilation.

Module
  PABoundedRawCodedDynamicTruthNativeAlignedRootApplicationIdentification.

Import ListNotations.
Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateRenamingSubstitution.
Import PABoundedRawCodedTemplateDirectStructuralTranslation.
Import PABoundedRawCodedTemplateTripleUniversalOpening.
Import PABoundedRawCodedRestrictedPAConsistencyFromUniversalSoundness.
Import
  PABoundedRawCodedRestrictedPATemplateTernaryApplicationCompilation.
Import PABoundedRawCodedDirectTemplateTernaryApplicationCongruence.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessTemplateDirectInputs.
Import
  PABoundedRawCodedDynamicTruthPredecessorGlobalExistentialElimination.
Import PABoundedRawCodedDynamicTruthSuccessorRowsAppendNormalization.
Import PABoundedRawCodedDynamicTruthNativeGlobalEvidencePermutation.
Import
  PABoundedRawCodedDynamicTruthNativeLocalStagedCallbackCompilation.
Import
  PABoundedRawCodedFourStateTableAppendTemplateGlobalTraversalAssembly.
Import
  PABoundedRawCodedFourStateTableAppendPermutedTemplateGlobalTraversalAssembly.
Import
  PABoundedRawCodedDynamicTruthNativeAlignedStrongStepLogicalRootsCompilation.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectAssumptionCase.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectImpIntroductionCase.
Import
  PABoundedRawCodedRestrictedPADirectImpIntroductionPositiveBodyCompilation.

(** Applying a reversed three-variable predicate to
    [step, assignment, formula] is the same as substituting
    [formula, assignment, step] into its original variable order.  The
    scoped premise is essential because both three-opening application and
    the append root substitution deliberately disagree above index two. *)
Lemma coqDirectTemplateTernaryApplication_reverse_reroot : forall
    predicate rootFormula rootAssignmentCode rootAssignmentStep,
  TemplateFormulaScoped 3 predicate ->
  coqRestrictedPATemplateTernaryApplication
      (templateFormulaRename templateReverseFirstThreeRenaming predicate)
      rootAssignmentStep rootAssignmentCode rootFormula =
    templateFormulaSubst
      (coqFourStateTableAppendRootTermsSubstitution
        rootFormula rootAssignmentCode rootAssignmentStep)
      predicate.
Proof.
  intros predicate rootFormula rootAssignmentCode rootAssignmentStep
    hscope.
  rewrite coqRestrictedPATemplateTernaryApplication_eq_subst.
  2:{
    apply (templateFormulaRename_scoped 3 3 predicate
      templateReverseFirstThreeRenaming hscope).
    intros index hindex.
    destruct index as [|[|[|index]]];
      cbn [templateReverseFirstThreeRenaming] in *; lia.
  }
  rewrite templateFormulaSubst_rename.
  apply (templateFormulaSubst_ext_scoped 3 predicate);
    [exact hscope |].
  intros index hindex.
  destruct index as [|[|[|index]]];
    cbn [coqDirectTemplateTernarySubstitution
      templateReverseFirstThreeRenaming
      coqFourStateTableAppendRootTermsSubstitution] in *;
    try reflexivity; lia.
Qed.

(** The two concrete native global sources have exactly the advertised
    three free argument slots after their ten traversal witnesses are bound.
    Boolean reflection keeps this large but finite syntax check out of the
    semantic proof below. *)
Lemma coqDynamicTruthSharedSigmaGlobalSource_scoped_three :
  TemplateFormulaScoped 3
    (coqDynamicTruthGlobalExistentialSource 0
      coqDynamicTruthSharedSigmaSuccessorRowTemplate
      coqDynamicTruthSharedPiSuccessorRowTemplate).
Proof.
  apply (proj1 (templateFormulaScopedBool_iff 3 _)).
  vm_compute.
  reflexivity.
Qed.

Lemma coqDynamicTruthSharedPiGlobalSource_scoped_three :
  TemplateFormulaScoped 3
    (coqDynamicTruthGlobalExistentialSource 1
      coqDynamicTruthSharedSigmaSuccessorRowTemplate
      coqDynamicTruthSharedPiSuccessorRowTemplate).
Proof.
  apply (proj1 (templateFormulaScopedBool_iff 3 _)).
  vm_compute.
  reflexivity.
Qed.

(** Direct truth leaves in their ordinary (unpermuted) argument order. *)
Definition coqDynamicTruthNativeAlignedSigmaEvidencePredicateTemplate
    : TemplateFormula :=
  tfOpaque coqRestrictedPAConclusionTruthPredicateName
    [coqRestrictedPASoundnessLowerLevelTerm;
     coqRestrictedPASoundnessUpperLevelTerm;
     ttVar 0; ttVar 1; ttVar 2].

Definition coqDynamicTruthNativeAlignedPiEvidencePredicateTemplate
    : TemplateFormula :=
  tfOpaque coqRestrictedPAContextTruthPredicateName
    [coqRestrictedPASoundnessLowerLevelTerm;
     coqRestrictedPASoundnessUpperLevelTerm;
     ttVar 0; ttVar 1; ttVar 2].

Definition coqDynamicTruthNativeAlignedSigmaEvidenceAtRootTerms
    (rootFormula rootAssignmentCode rootAssignmentStep : TemplateTerm)
    : TemplateFormula :=
  tfOpaque coqRestrictedPAConclusionTruthPredicateName
    [coqRestrictedPASoundnessLowerLevelTerm;
     coqRestrictedPASoundnessUpperLevelTerm;
     rootFormula; rootAssignmentCode; rootAssignmentStep].

Definition coqDynamicTruthNativeAlignedPiEvidenceAtRootTerms
    (rootFormula rootAssignmentCode rootAssignmentStep : TemplateTerm)
    : TemplateFormula :=
  tfOpaque coqRestrictedPAContextTruthPredicateName
    [coqRestrictedPASoundnessLowerLevelTerm;
     coqRestrictedPASoundnessUpperLevelTerm;
     rootFormula; rootAssignmentCode; rootAssignmentStep].

Lemma coqDynamicTruthNativeAlignedSigmaEvidencePredicate_scoped_three :
  TemplateFormulaScoped 3
    coqDynamicTruthNativeAlignedSigmaEvidencePredicateTemplate.
Proof. cbn. repeat split; lia. Qed.

Lemma coqDynamicTruthNativeAlignedPiEvidencePredicate_scoped_three :
  TemplateFormulaScoped 3
    coqDynamicTruthNativeAlignedPiEvidencePredicateTemplate.
Proof. cbn. repeat split; lia. Qed.

Lemma coqDynamicTruthNativeAlignedSigmaEvidenceConclusionTemplate_reverse :
  templateFormulaRename templateReverseFirstThreeRenaming
      coqDynamicTruthNativeAlignedSigmaEvidencePredicateTemplate =
    coqDynamicTruthNativeAlignedSigmaEvidenceConclusionTemplate.
Proof. reflexivity. Qed.

Lemma coqDynamicTruthNativeAlignedPiEvidenceConclusionTemplate_reverse :
  templateFormulaRename templateReverseFirstThreeRenaming
      coqDynamicTruthNativeAlignedPiEvidencePredicateTemplate =
    coqDynamicTruthNativeAlignedPiEvidenceConclusionTemplate.
Proof. reflexivity. Qed.

(** Structural alignment now determines both evidence applications at every
    rule-local root, not merely at the canonical variables. *)
Theorem raw_dynamicTruthNativeAligned_global_evidence_reroot : forall
    (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (tail : nat -> M) predecessorLevel baseContext currentLocal
    nextInputGlobalSigma nextInputGlobalPi
    (aligned : RawDynamicTruthNativeLocalAlignedPredecessorAt M tail
      predecessorLevel baseContext currentLocal
      nextInputGlobalSigma nextInputGlobalPi)
    inputLevelNumeral
    (inputs : RawCodedTemplateDirectStructuralInputs M),
  RawDynamicTruthNativeAlignedStrongStepStructuralInputsAt
      M hPA tail predecessorLevel baseContext currentLocal
      nextInputGlobalSigma nextInputGlobalPi aligned
      inputLevelNumeral inputs ->
  (forall rootFormula rootAssignmentCode rootAssignmentStep,
    rawDirectTemplateFormula inputs
      (coqFourStateTableAppendTemplateGlobalSourceAtRootTerms 0
        coqDynamicTruthSharedSigmaSuccessorRowTemplate
        coqDynamicTruthSharedPiSuccessorRowTemplate
        rootFormula rootAssignmentCode rootAssignmentStep) =
    rawDirectTemplateFormula inputs
      (coqDynamicTruthNativeAlignedSigmaEvidenceAtRootTerms
        rootFormula rootAssignmentCode rootAssignmentStep)) /\
  (forall rootFormula rootAssignmentCode rootAssignmentStep,
    rawDirectTemplateFormula inputs
      (coqFourStateTableAppendTemplateGlobalSourceAtRootTerms 1
        coqDynamicTruthSharedSigmaSuccessorRowTemplate
        coqDynamicTruthSharedPiSuccessorRowTemplate
        rootFormula rootAssignmentCode rootAssignmentStep) =
    rawDirectTemplateFormula inputs
      (coqDynamicTruthNativeAlignedPiEvidenceAtRootTerms
        rootFormula rootAssignmentCode rootAssignmentStep)).
Proof.
  intros M hPA tail predecessorLevel baseContext currentLocal
    nextInputGlobalSigma nextInputGlobalPi aligned inputLevelNumeral
    inputs hstructural.
  destruct hstructural as
    (localSigmaRow & localPiRow & _hwrapper & _hlower & _hsigmaRow &
     _hpiRow & hsigmaLeaf & hpiLeaf & hsigmaGlobal & hpiGlobal).
  assert (hsigmaBase :
    rawDirectTemplateFormula inputs
      (templateFormulaRename templateReverseFirstThreeRenaming
        (coqDynamicTruthGlobalExistentialSource 0
          coqDynamicTruthSharedSigmaSuccessorRowTemplate
          coqDynamicTruthSharedPiSuccessorRowTemplate)) =
    rawDirectTemplateFormula inputs
      coqDynamicTruthNativeAlignedSigmaEvidenceConclusionTemplate).
  { exact (eq_trans hsigmaGlobal (eq_sym hsigmaLeaf)). }
  assert (hpiBase :
    rawDirectTemplateFormula inputs
      (templateFormulaRename templateReverseFirstThreeRenaming
        (coqDynamicTruthGlobalExistentialSource 1
          coqDynamicTruthSharedSigmaSuccessorRowTemplate
          coqDynamicTruthSharedPiSuccessorRowTemplate)) =
    rawDirectTemplateFormula inputs
      coqDynamicTruthNativeAlignedPiEvidenceConclusionTemplate).
  { exact (eq_trans hpiGlobal (eq_sym hpiLeaf)). }
  split; intros rootFormula rootAssignmentCode rootAssignmentStep.
  - pose proof (raw_directTemplateTernaryApplication_congr
      M hPA inputs
      (templateFormulaRename templateReverseFirstThreeRenaming
        (coqDynamicTruthGlobalExistentialSource 0
          coqDynamicTruthSharedSigmaSuccessorRowTemplate
          coqDynamicTruthSharedPiSuccessorRowTemplate))
      coqDynamicTruthNativeAlignedSigmaEvidenceConclusionTemplate
      hsigmaBase rootAssignmentStep rootAssignmentCode rootFormula)
      as hreroot.
    rewrite <-
      coqDynamicTruthNativeAlignedSigmaEvidenceConclusionTemplate_reverse
      in hreroot.
    rewrite (coqDirectTemplateTernaryApplication_reverse_reroot
      (coqDynamicTruthGlobalExistentialSource 0
        coqDynamicTruthSharedSigmaSuccessorRowTemplate
        coqDynamicTruthSharedPiSuccessorRowTemplate)
      rootFormula rootAssignmentCode rootAssignmentStep
      coqDynamicTruthSharedSigmaGlobalSource_scoped_three) in hreroot.
    rewrite (coqDirectTemplateTernaryApplication_reverse_reroot
      coqDynamicTruthNativeAlignedSigmaEvidencePredicateTemplate
      rootFormula rootAssignmentCode rootAssignmentStep
      coqDynamicTruthNativeAlignedSigmaEvidencePredicate_scoped_three)
      in hreroot.
    exact hreroot.
  - pose proof (raw_directTemplateTernaryApplication_congr
      M hPA inputs
      (templateFormulaRename templateReverseFirstThreeRenaming
        (coqDynamicTruthGlobalExistentialSource 1
          coqDynamicTruthSharedSigmaSuccessorRowTemplate
          coqDynamicTruthSharedPiSuccessorRowTemplate))
      coqDynamicTruthNativeAlignedPiEvidenceConclusionTemplate
      hpiBase rootAssignmentStep rootAssignmentCode rootFormula)
      as hreroot.
    rewrite <-
      coqDynamicTruthNativeAlignedPiEvidenceConclusionTemplate_reverse
      in hreroot.
    rewrite (coqDirectTemplateTernaryApplication_reverse_reroot
      (coqDynamicTruthGlobalExistentialSource 1
        coqDynamicTruthSharedSigmaSuccessorRowTemplate
        coqDynamicTruthSharedPiSuccessorRowTemplate)
      rootFormula rootAssignmentCode rootAssignmentStep
      coqDynamicTruthSharedPiGlobalSource_scoped_three) in hreroot.
    rewrite (coqDirectTemplateTernaryApplication_reverse_reroot
      coqDynamicTruthNativeAlignedPiEvidencePredicateTemplate
      rootFormula rootAssignmentCode rootAssignmentStep
      coqDynamicTruthNativeAlignedPiEvidencePredicate_scoped_three)
      in hreroot.
    exact hreroot.
Qed.

(** These are precisely the three code identifications consumed by the
    synchronized Imp-I body theorem.  In particular, [piLeft] names the
    native Pi selector applied at the rule-local antecedent coordinates;
    its equality with the mode-one append source is the Pi half of the
    generic reroot theorem, rather than a reflexive alias of that source. *)
Corollary raw_dynamicTruthNativeAligned_impIntroduction_applications : forall
    (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (tail : nat -> M) predecessorLevel baseContext currentLocal
    nextInputGlobalSigma nextInputGlobalPi
    (aligned : RawDynamicTruthNativeLocalAlignedPredecessorAt M tail
      predecessorLevel baseContext currentLocal
      nextInputGlobalSigma nextInputGlobalPi)
    inputLevelNumeral
    (inputs : RawCodedTemplateDirectStructuralInputs M),
  RawDynamicTruthNativeAlignedStrongStepStructuralInputsAt
      M hPA tail predecessorLevel baseContext currentLocal
      nextInputGlobalSigma nextInputGlobalPi aligned
      inputLevelNumeral inputs ->
  let piLeft := rawDirectTemplateFormula inputs
    (coqDynamicTruthNativeAlignedPiEvidenceAtRootTerms
      (ttVar 6) (ttVar 9) (ttVar 8)) in
  rawDirectTemplateFormula inputs
      coqRestrictedPADirectImpIntroductionTrueRightSigmaEvidenceTemplate =
    rawDirectTemplateFormula inputs
      coqRestrictedPADirectImpIntroductionConsequentTruthTemplate /\
  rawDirectTemplateFormula inputs
      coqRestrictedPADirectImpIntroductionParentSigmaEvidenceTemplate =
    rawDirectTemplateFormula inputs
      coqRestrictedPADirectAssumptionOuterConclusionTruthTemplate /\
  rawDirectTemplateFormula inputs
      coqRestrictedPADirectImpIntroductionFalseLeftPiEvidenceTemplate =
    piLeft.
Proof.
  intros M hPA tail predecessorLevel baseContext currentLocal
    nextInputGlobalSigma nextInputGlobalPi aligned inputLevelNumeral
    inputs hstructural piLeft.
  destruct (raw_dynamicTruthNativeAligned_global_evidence_reroot
    M hPA tail predecessorLevel baseContext currentLocal
    nextInputGlobalSigma nextInputGlobalPi aligned inputLevelNumeral
    inputs hstructural) as [hsigma hpi].
  split.
  - exact (hsigma (ttVar 5) (ttVar 9) (ttVar 8)).
  - split.
    + exact (hsigma
        coqRestrictedPADirectAssumptionOuterConclusionTerm
        (ttVar 9) (ttVar 8)).
    + exact (hpi (ttVar 6) (ttVar 9) (ttVar 8)).
Qed.

End
  PABoundedRawCodedDynamicTruthNativeAlignedRootApplicationIdentification.
