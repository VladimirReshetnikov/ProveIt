(**
  Strong-prefix child truth below an arbitrary template renaming.

  Recursive soundness compilers often eliminate an existential coverage
  witness before invoking the induction hypothesis [K(d)].  Every ambient
  formula has then crossed one eigenvariable binder.  The original child
  truth compiler was stated only in its unrenamed context; this module proves
  the operation once for an arbitrary outer renaming and can therefore be
  reused by every such rule case.
*)

From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAListCoding Require Import Representability ListFormulas.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedFormulaOperations
  RawCodedPALocalProofExistential
  RawCodedPALocalProofConjunction
  RawCodedTemplateSyntax
  RawCodedTemplateProofCompiler
  RawCodedTemplateRenamingSubstitution
  RawCodedRestrictedPADerivationSoundnessDirectAndIntroductionCase.

Module
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectRenamedChildTruth.

Import PA.
Import PAListRepresentability.
Import PAListFormulas.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPALocalProofConjunction.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndIntroductionCase.
Import PABoundedRawCodedTemplateRenamingSubstitution.

(** This is the renaming-natural form of
    [raw_codedPALocalProofOf_coqRestrictedPADirectAndIntroductionChildTruth].
    No property of [renaming] is required: named carrier parameters remain
    fixed, while every de Bruijn variable is transported uniformly. *)
Theorem
    raw_codedPALocalProofOf_coqRestrictedPADirectAndIntroductionChildTruth_renamed :
  forall (M : RawPAModel) (hPA : RawPASatisfies M)
    (translation : RawCodedTemplateTranslation M)
    localContext renaming child witnessContext childConclusion
    interfaceRoot prefixRoot contextTruthRoot,
  RawCodedPALocalProofOf M
    (rawTemplateContextCode translation localContext)
    (rawTemplateFormula translation
      (templateFormulaRename renaming
        (coqRestrictedPADirectAndIntroductionChildInterfaceResultTemplate
          child witnessContext childConclusion))) interfaceRoot ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCode translation localContext)
    (rawTemplateFormula translation
      (templateFormulaRename renaming
        coqRestrictedPADirectAndIntroductionDeepStrongPrefixTemplate))
    prefixRoot ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCode translation localContext)
    (rawTemplateFormula translation
      (templateFormulaRename renaming
        (coqRestrictedPADirectAndIntroductionChildContextTruthTemplate
          child witnessContext childConclusion))) contextTruthRoot ->
  exists truthRoot : M,
    RawCodedPALocalProofOf M
      (rawTemplateContextCode translation localContext)
      (rawTemplateFormula translation
        (templateFormulaRename renaming
          (coqRestrictedPADirectAndIntroductionChildTruthTemplate
            child witnessContext childConclusion))) truthRoot.
Proof.
  intros M hPA translation localContext renaming child witnessContext
    childConclusion interfaceRoot prefixRoot contextTruthRoot
    hinterface hprefix hcontextTruth.
  set (contextCode := rawTemplateContextCode translation localContext).
  set (below :=
    coqRestrictedPADirectAndIntroductionChildBelowTemplate child).
  set (restricted :=
    coqRestrictedPADirectAndIntroductionChildRestrictedTemplate
      child witnessContext childConclusion).
  set (childEndpoint :=
    coqRestrictedPADirectAndIntroductionChildEndpointTemplate
      child witnessContext childConclusion).
  set (childAdmissible :=
    coqRestrictedPADirectAndIntroductionChildAdmissibleTemplate
      child witnessContext childConclusion).
  set (lastPair := tfAnd childEndpoint childAdmissible).
  set (rest := tfAnd restricted lastPair).

  unfold
    coqRestrictedPADirectAndIntroductionChildInterfaceResultTemplate
    in hinterface.
  cbn [templateFormulaRename] in hinterface.
  rewrite rawTemplateFormula_and in hinterface.
  pose proof (raw_codedPALocalProofOf_andE1 M hPA _ _ _
    interfaceRoot hinterface) as hbelow.
  pose proof (raw_codedPALocalProofOf_andE2 M hPA _ _ _
    interfaceRoot hinterface) as hrest.
  rewrite rawTemplateFormula_and in hrest.
  pose proof (raw_codedPALocalProofOf_andE1 M hPA _ _ _ _ hrest)
    as hrestricted.
  pose proof (raw_codedPALocalProofOf_andE2 M hPA _ _ _ _ hrest)
    as hlastPair.
  rewrite rawTemplateFormula_and in hlastPair.
  pose proof (raw_codedPALocalProofOf_andE1 M hPA _ _ _ _ hlastPair)
    as hchildEndpoint.
  pose proof (raw_codedPALocalProofOf_andE2 M hPA _ _ _ _ hlastPair)
    as hchildAdmissible.

  rewrite coqRestrictedPADirectAndIntroduction_deep_prefix_shape in hprefix.
  cbn [templateFormulaRename] in hprefix.
  pose proof
    (raw_codedPALocalProofOf_coqRestrictedPADirect_templateAllE
      M hPA translation localContext
      (templateFormulaRename (templateUpRenaming renaming)
        coqRestrictedPADirectAndIntroductionDeepStrongPrefixBodyTemplate)
      (templateTermRename renaming child) prefixRoot hprefix) as hguarded.
  rewrite <- templateFormulaRename_open in hguarded.
  lazymatch type of hguarded with
  | RawCodedPALocalProofOf _ _ _ ?root =>
      change (RawCodedPALocalProofOf M contextCode
        (rawTemplateFormula translation
          (templateFormulaRename renaming
            (coqRestrictedPADirectAndIntroductionChildGuardedTemplate child)))
        root) in hguarded
  end.
  rewrite coqRestrictedPADirectAndIntroduction_child_guarded_shape
    in hguarded.
  cbn [templateFormulaRename] in hguarded.
  pose proof
    (raw_codedPALocalProofOf_coqRestrictedPADirect_templateImpE
      M hPA translation localContext _ _ _ _ hguarded hbelow)
    as hpredicate.

  rewrite coqRestrictedPADirectAndIntroduction_child_predicate_all_shape
    in hpredicate.
  cbn [templateFormulaRename] in hpredicate.
  pose proof
    (raw_codedPALocalProofOf_coqRestrictedPADirect_templateAllE
      M hPA translation localContext _
      (templateTermRename renaming witnessContext) _ hpredicate)
    as hafterContext.
  rewrite <- templateFormulaRename_open in hafterContext.
  lazymatch type of hafterContext with
  | RawCodedPALocalProofOf _ _ _ ?root =>
      change (RawCodedPALocalProofOf M contextCode
        (rawTemplateFormula translation
          (templateFormulaRename renaming
            (coqRestrictedPADirectAndIntroductionChildAfterContextTemplate
              child witnessContext))) root) in hafterContext
  end.

  rewrite coqRestrictedPADirectAndIntroduction_child_after_context_all_shape
    in hafterContext.
  cbn [templateFormulaRename] in hafterContext.
  pose proof
    (raw_codedPALocalProofOf_coqRestrictedPADirect_templateAllE
      M hPA translation localContext _
      (templateTermRename renaming childConclusion) _ hafterContext)
    as hafterConclusion.
  rewrite <- templateFormulaRename_open in hafterConclusion.
  lazymatch type of hafterConclusion with
  | RawCodedPALocalProofOf _ _ _ ?root =>
      change (RawCodedPALocalProofOf M contextCode
        (rawTemplateFormula translation
          (templateFormulaRename renaming
            (coqRestrictedPADirectAndIntroductionChildAfterConclusionTemplate
              child witnessContext childConclusion))) root)
        in hafterConclusion
  end.

  rewrite
    coqRestrictedPADirectAndIntroduction_child_after_conclusion_all_shape
    in hafterConclusion.
  cbn [templateFormulaRename] in hafterConclusion.
  pose proof
    (raw_codedPALocalProofOf_coqRestrictedPADirect_templateAllE
      M hPA translation localContext _
      (templateTermRename renaming
        coqRestrictedPADirectAndIntroductionAssignmentCodeTerm)
      _ hafterConclusion) as hafterAssignmentCode.
  rewrite <- templateFormulaRename_open in hafterAssignmentCode.
  lazymatch type of hafterAssignmentCode with
  | RawCodedPALocalProofOf _ _ _ ?root =>
      change (RawCodedPALocalProofOf M contextCode
        (rawTemplateFormula translation
          (templateFormulaRename renaming
            (coqRestrictedPADirectAndIntroductionChildAfterAssignmentCodeTemplate
              child witnessContext childConclusion
              coqRestrictedPADirectAndIntroductionAssignmentCodeTerm))) root)
        in hafterAssignmentCode
  end.

  rewrite
    coqRestrictedPADirectAndIntroduction_child_after_assignment_all_shape
    in hafterAssignmentCode.
  cbn [templateFormulaRename] in hafterAssignmentCode.
  pose proof
    (raw_codedPALocalProofOf_coqRestrictedPADirect_templateAllE
      M hPA translation localContext _
      (templateTermRename renaming
        coqRestrictedPADirectAndIntroductionAssignmentStepTerm)
      _ hafterAssignmentCode) as hready.
  rewrite <- templateFormulaRename_open in hready.
  lazymatch type of hready with
  | RawCodedPALocalProofOf _ _ _ ?root =>
      change (RawCodedPALocalProofOf M contextCode
        (rawTemplateFormula translation
          (templateFormulaRename renaming
            (coqRestrictedPADirectAndIntroductionChildReadyTemplate
              child witnessContext childConclusion
              coqRestrictedPADirectAndIntroductionAssignmentCodeTerm
              coqRestrictedPADirectAndIntroductionAssignmentStepTerm))) root)
        in hready
  end.
  rewrite coqRestrictedPADirectAndIntroduction_child_ready_shape in hready.
  cbn [templateFormulaRename] in hready.

  pose proof
    (raw_codedPALocalProofOf_coqRestrictedPADirect_templateImpE
      M hPA translation localContext _ _ _ _ hready hrestricted)
    as hafterRestricted.
  pose proof
    (raw_codedPALocalProofOf_coqRestrictedPADirect_templateImpE
      M hPA translation localContext _ _ _ _
      hafterRestricted hchildEndpoint) as hafterEndpoint.
  pose proof
    (raw_codedPALocalProofOf_coqRestrictedPADirect_templateImpE
      M hPA translation localContext _ _ _ _
      hafterEndpoint hchildAdmissible) as hafterAdmissible.
  eexists.
  exact
    (raw_codedPALocalProofOf_coqRestrictedPADirect_templateImpE
      M hPA translation localContext _ _ _ contextTruthRoot
      hafterAdmissible hcontextTruth).
Qed.

End
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectRenamedChildTruth.
