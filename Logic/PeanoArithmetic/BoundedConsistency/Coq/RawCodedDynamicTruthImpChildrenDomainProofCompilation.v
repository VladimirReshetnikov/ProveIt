(**
  Represented inheritance of carrier-indexed rank domains by implication
  children.

  Dynamic truth indexes its Sigma and Pi rank bounds by a carrier element,
  rather than a metatheoretical hierarchy level.  For an implication, a
  Sigma bound on the parent gives a Pi bound on the left child and a Sigma
  bound on the right; a Pi bound gives the dual pair.  Consequently either
  parent domain is enough to put both children in the admissibility-domain
  disjunction at the same carrier level.

  This module proves that stronger polarity-sensitive fact semantically,
  internalizes its disjunctive consequence as one closed theorem of PA, and
  provides a capture-avoiding four-term compiler.  The final assembler
  reuses the generic two-premise context kernel from implication-child atomic
  adequacy, so both laws choose and synchronize witnessed PA extensions in
  exactly the same way.
*)

From Stdlib Require Import List Lia.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawModelCompleteness
  RawCodedSyntaxConstructors
  RawCodedFixedLevelDomainLaws
  RawCodedDynamicTruthFixedSyntaxFragments
  RawCodedRestrictedPAProof
  RawCodedPAAxiomWitnessPrefix
  RawCodedPALocalProofExistential
  RawCodedPALocalProofComposition
  RawCodedPALocalProofWitnessedContextMerge
  RawCodedTemplateSyntax
  RawCodedTemplateProofCompiler
  RawCodedTemplateProofCompilerSelfShiftTail
  RawCodedTemplatePAEmbedding
  RawCodedTemplateLocalProofWitnessedTailTransport
  RawCodedPALocalProofUniversalEliminationChain
  RawCodedFormulaImpChildrenAtomicAdequacyProofCompilation.

Module PABoundedRawCodedDynamicTruthImpChildrenDomainProofCompilation.

Import ListNotations.
Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawModelCompleteness.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedFixedLevelDomainLaws.
Import PABoundedRawCodedDynamicTruthFixedSyntaxFragments.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedPAAxiomWitnessPrefix.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPALocalProofComposition.
Import PABoundedRawCodedPALocalProofWitnessedContextMerge.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedTemplateProofCompilerSelfShiftTail.
Import PABoundedRawCodedTemplatePAEmbedding.
Import PABoundedRawCodedTemplateLocalProofWitnessedTailTransport.
Import PABoundedRawCodedPALocalProofUniversalEliminationChain.
Import
  PABoundedRawCodedFormulaImpChildrenAtomicAdequacyProofCompilation.

(** Carrier-parametric versions of the ordinary fixed-level implication
    domain laws.  No standardness of [level] is used: transitivity of the
    represented order is enough once the rank equation exposes the relevant
    child component below the parent maximum. *)
Lemma raw_dynamicTruthSigmaRecordDomain_imp : forall
    (M : RawPAModel), RawPASatisfies M -> forall level left right,
  RawDynamicTruthSigmaRecordDomain M level
    (rawFormulaImpCode M left right) ->
  RawDynamicTruthPiRecordDomain M level left /\
  RawDynamicTruthSigmaRecordDomain M level right.
Proof.
  intros M hPA level left right
    (sigma & pi & hrank & hsigmaBound).
  destruct (raw_codedFormulaRank_imp_view M hPA
    left right sigma pi hrank) as
    (leftSigma & leftPi & rightSigma & rightPi &
      hleftRank & hrightRank & [hsigmaMax hpiMax]).
  split.
  - exists leftSigma, leftPi. split; [exact hleftRank |].
    exact (raw_le_trans M hPA leftPi sigma level
      (raw_fixedLevel_max_left_le M hPA
        sigma leftPi rightSigma hsigmaMax) hsigmaBound).
  - exists rightSigma, rightPi. split; [exact hrightRank |].
    exact (raw_le_trans M hPA rightSigma sigma level
      (raw_fixedLevel_max_right_le M hPA
        sigma leftPi rightSigma hsigmaMax) hsigmaBound).
Qed.

Lemma raw_dynamicTruthPiRecordDomain_imp : forall
    (M : RawPAModel), RawPASatisfies M -> forall level left right,
  RawDynamicTruthPiRecordDomain M level
    (rawFormulaImpCode M left right) ->
  RawDynamicTruthSigmaRecordDomain M level left /\
  RawDynamicTruthPiRecordDomain M level right.
Proof.
  intros M hPA level left right
    (sigma & pi & hrank & hpiBound).
  destruct (raw_codedFormulaRank_imp_view M hPA
    left right sigma pi hrank) as
    (leftSigma & leftPi & rightSigma & rightPi &
      hleftRank & hrightRank & [hsigmaMax hpiMax]).
  split.
  - exists leftSigma, leftPi. split; [exact hleftRank |].
    exact (raw_le_trans M hPA leftSigma pi level
      (raw_fixedLevel_max_left_le M hPA
        pi leftSigma rightPi hpiMax) hpiBound).
  - exists rightSigma, rightPi. split; [exact hrightRank |].
    exact (raw_le_trans M hPA rightPi pi level
      (raw_fixedLevel_max_right_le M hPA
        pi leftSigma rightPi hpiMax) hpiBound).
Qed.

Lemma raw_dynamicTruthRecordDomain_imp_children : forall
    (M : RawPAModel), RawPASatisfies M -> forall level parent left right,
  parent = rawFormulaImpCode M left right ->
  (RawDynamicTruthSigmaRecordDomain M level parent \/
   RawDynamicTruthPiRecordDomain M level parent) ->
  (RawDynamicTruthSigmaRecordDomain M level left \/
   RawDynamicTruthPiRecordDomain M level left) /\
  (RawDynamicTruthSigmaRecordDomain M level right \/
   RawDynamicTruthPiRecordDomain M level right).
Proof.
  intros M hPA level parent left right hshape hdomain.
  subst parent.
  destruct hdomain as [hsigma | hpi].
  - destruct (raw_dynamicTruthSigmaRecordDomain_imp M hPA
      level left right hsigma) as [hleft hright].
    split; [right | left]; assumption.
  - destruct (raw_dynamicTruthPiRecordDomain_imp M hPA
      level left right hpi) as [hleft hright].
    split; [left | right]; assumption.
Qed.

(** Binder order is carrier level, parent, left child, right child. *)
Definition dynamicTruthImpChildrenDomainBodyFormula : formula :=
  pImp
    (formulaImpCodeTermAt (tVar 2) (tVar 1) (tVar 0))
    (pImp
      (pOr
        (dynamicTruthSigmaRecordDomainTermAt (tVar 3) (tVar 2))
        (dynamicTruthPiRecordDomainTermAt (tVar 3) (tVar 2)))
      (pAnd
        (pOr
          (dynamicTruthSigmaRecordDomainTermAt (tVar 3) (tVar 1))
          (dynamicTruthPiRecordDomainTermAt (tVar 3) (tVar 1)))
        (pOr
          (dynamicTruthSigmaRecordDomainTermAt (tVar 3) (tVar 0))
          (dynamicTruthPiRecordDomainTermAt (tVar 3) (tVar 0))))).

Definition dynamicTruthImpChildrenDomainFormula : formula :=
  pAll (pAll (pAll (pAll dynamicTruthImpChildrenDomainBodyFormula))).

Lemma raw_sat_dynamicTruthImpChildrenDomainFormula_iff : forall
    (M : RawPAModel) (e : nat -> M),
  raw_formula_sat M e dynamicTruthImpChildrenDomainFormula <->
  forall level parent left right : M,
    parent = rawFormulaImpCode M left right ->
    (RawDynamicTruthSigmaRecordDomain M level parent \/
     RawDynamicTruthPiRecordDomain M level parent) ->
    (RawDynamicTruthSigmaRecordDomain M level left \/
     RawDynamicTruthPiRecordDomain M level left) /\
    (RawDynamicTruthSigmaRecordDomain M level right \/
     RawDynamicTruthPiRecordDomain M level right).
Proof.
  intros M e.
  unfold dynamicTruthImpChildrenDomainFormula,
    dynamicTruthImpChildrenDomainBodyFormula.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_formulaImpCodeTermAt_iff.
  repeat setoid_rewrite raw_sat_dynamicTruthSigmaRecordDomainTermAt_iff.
  repeat setoid_rewrite raw_sat_dynamicTruthPiRecordDomainTermAt_iff.
  cbn [raw_term_eval scons]. reflexivity.
Qed.

Lemma dynamicTruthImpChildrenDomainFormula_sentence :
  Formula.Sentence dynamicTruthImpChildrenDomainFormula.
Proof.
  intros k hfree.
  unfold dynamicTruthImpChildrenDomainFormula,
    dynamicTruthImpChildrenDomainBodyFormula,
    dynamicTruthSigmaRecordDomainTermAt,
    dynamicTruthPiRecordDomainTermAt in hfree.
  cbn in hfree. lia.
Qed.

Theorem dynamicTruthImpChildrenDomainFormula_raw_valid : forall
    (M : RawPAModel), RawPASatisfies M -> forall e,
  raw_formula_sat M e dynamicTruthImpChildrenDomainFormula.
Proof.
  intros M hPA e.
  apply (proj2 (raw_sat_dynamicTruthImpChildrenDomainFormula_iff M e)).
  exact (raw_dynamicTruthRecordDomain_imp_children M hPA).
Qed.

Theorem PA_proves_dynamicTruthImpChildrenDomainFormula :
  Formula.BProv Formula.Ax_s [] dynamicTruthImpChildrenDomainFormula.
Proof.
  apply PA_BProv_of_raw_valid.
  - exact dynamicTruthImpChildrenDomainFormula_sentence.
  - exact dynamicTruthImpChildrenDomainFormula_raw_valid.
Qed.

Definition coqDynamicTruthImpChildrenDomainInstanceTemplate
    (level parent left right : TemplateTerm) : TemplateFormula :=
  templateUniversalOpenManyOrBot
    (embedPAFormula dynamicTruthImpChildrenDomainFormula)
    [level; parent; left; right].

Lemma coqDynamicTruthImpChildrenDomainInstanceTemplate_open : forall
    level parent left right,
  templateUniversalOpenMany
    (embedPAFormula dynamicTruthImpChildrenDomainFormula)
    [level; parent; left; right] =
  Some (coqDynamicTruthImpChildrenDomainInstanceTemplate
    level parent left right).
Proof.
  intros level parent left right.
  unfold coqDynamicTruthImpChildrenDomainInstanceTemplate,
    templateUniversalOpenManyOrBot,
    dynamicTruthImpChildrenDomainFormula.
  cbn [templateUniversalOpenMany embedPAFormula
    templateFormulaOpen templateFormulaSubst].
  reflexivity.
Qed.

Definition coqDynamicTruthImpChildrenDomainShapePremiseTemplate
    level parent left right :=
  templateImpAntecedent
    (coqDynamicTruthImpChildrenDomainInstanceTemplate
      level parent left right).

Definition coqDynamicTruthImpChildrenDomainParentPremiseTemplate
    level parent left right :=
  templateImpAntecedent (templateImpConsequent
    (coqDynamicTruthImpChildrenDomainInstanceTemplate
      level parent left right)).

Definition coqDynamicTruthImpChildrenDomainConclusionTemplate
    level parent left right :=
  templateImpConsequent (templateImpConsequent
    (coqDynamicTruthImpChildrenDomainInstanceTemplate
      level parent left right)).

Lemma coqDynamicTruthImpChildrenDomainInstanceTemplate_imp2_shape : forall
    level parent left right,
  coqDynamicTruthImpChildrenDomainInstanceTemplate
      level parent left right =
  tfImp
    (coqDynamicTruthImpChildrenDomainShapePremiseTemplate
      level parent left right)
    (tfImp
      (coqDynamicTruthImpChildrenDomainParentPremiseTemplate
        level parent left right)
      (coqDynamicTruthImpChildrenDomainConclusionTemplate
        level parent left right)).
Proof.
  intros level parent left right.
  unfold coqDynamicTruthImpChildrenDomainShapePremiseTemplate,
    coqDynamicTruthImpChildrenDomainParentPremiseTemplate,
    coqDynamicTruthImpChildrenDomainConclusionTemplate,
    coqDynamicTruthImpChildrenDomainInstanceTemplate,
    templateUniversalOpenManyOrBot,
    dynamicTruthImpChildrenDomainFormula,
    dynamicTruthImpChildrenDomainBodyFormula.
  cbn [templateUniversalOpenMany embedPAFormula
    templateFormulaOpen templateFormulaSubst
    templateImpAntecedent templateImpConsequent].
  reflexivity.
Qed.

Theorem
    raw_codedPALocalProofOf_dynamicTruthImpChildrenDomain_instance_on_witnessed_tail :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall baseWitnessList baseContext level parent left right,
  RawCodedPAAxiomWitnessContext M baseWitnessList baseContext ->
  exists (witnesses : StandardPAAxiomWitnessPrefix) proofRoot,
    RawCodedPAAxiomWitnessContext M
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        witnesses baseWitnessList)
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses baseContext) /\
    RawCodedPALocalProofOf M
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses baseContext)
      (rawTemplateFormula translation
        (coqDynamicTruthImpChildrenDomainInstanceTemplate
          level parent left right)) proofRoot.
Proof.
  intros M hPA translation hagreement baseWitnessList baseContext
    level parent left right hbase.
  exact
    (raw_codedTemplatePALocalProofOf_of_BProv_open_many_on_witnessed_tail
      M hPA translation hagreement baseWitnessList baseContext
      dynamicTruthImpChildrenDomainFormula
      [level; parent; left; right]
      (coqDynamicTruthImpChildrenDomainInstanceTemplate
        level parent left right)
      hbase PA_proves_dynamicTruthImpChildrenDomainFormula
      (coqDynamicTruthImpChildrenDomainInstanceTemplate_open
        level parent left right)).
Qed.

Theorem
    raw_codedPALocalProofOf_dynamicTruthImpChildrenDomain_instance_on_witnessed_tail_under_prefix :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall baseWitnessList baseContext prefix level parent left right,
  RawCodedTemplatePrefixAtomicallyAdequate M translation prefix ->
  RawCodedPAAxiomWitnessContext M baseWitnessList baseContext ->
  exists (witnesses : StandardPAAxiomWitnessPrefix) proofRoot,
    RawCodedPAAxiomWitnessContext M
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        witnesses baseWitnessList)
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses baseContext) /\
    RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation
        (rawStandardPAAxiomWitnessPrefixContextCode M
          witnesses baseContext) prefix)
      (rawTemplateFormula translation
        (coqDynamicTruthImpChildrenDomainInstanceTemplate
          level parent left right)) proofRoot.
Proof.
  intros M hPA translation hagreement baseWitnessList baseContext prefix
    level parent left right hprefix hbase.
  destruct
    (raw_codedPALocalProofOf_dynamicTruthImpChildrenDomain_instance_on_witnessed_tail
      M hPA translation hagreement baseWitnessList baseContext
      level parent left right hbase)
    as (witnesses & sourceRoot & hextended & hsource).
  set (extendedWitnessList :=
    rawStandardPAAxiomWitnessPrefixWitnessListCode M
      witnesses baseWitnessList).
  set (extendedContext :=
    rawStandardPAAxiomWitnessPrefixContextCode M
      witnesses baseContext).
  destruct (raw_codedPALocalProof_templatePrefix M hPA translation
    extendedContext prefix
    (rawTemplateFormula translation
      (coqDynamicTruthImpChildrenDomainInstanceTemplate
        level parent left right)) sourceRoot
    (raw_codedPAAxiomWitnessPrefix_context_realizable_of_witnessed M
      extendedWitnessList extendedContext hextended)
    hprefix hsource) as [proofRoot hproof].
  exists witnesses, proofRoot. split; assumption.
Qed.

Theorem
    raw_codedPALocalProofOf_dynamicTruthImpChildrenDomain_of_roots_on_witnessed_extension_under_prefix :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall baseWitnessList baseContext prefix level parent left right
      shapeRoot parentDomainRoot,
  RawCodedTemplatePrefixAtomicallyAdequate M translation prefix ->
  RawCodedPAAxiomWitnessContext M baseWitnessList baseContext ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail translation baseContext prefix)
    (rawTemplateFormula translation
      (coqDynamicTruthImpChildrenDomainShapePremiseTemplate
        level parent left right)) shapeRoot ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail translation baseContext prefix)
    (rawTemplateFormula translation
      (coqDynamicTruthImpChildrenDomainParentPremiseTemplate
        level parent left right)) parentDomainRoot ->
  exists (witnesses : StandardPAAxiomWitnessPrefix) resultRoot,
    RawCodedPAAxiomWitnessContext M
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        witnesses baseWitnessList)
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses baseContext) /\
    RawContextListIncluded M baseContext
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses baseContext) /\
    RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation
        (rawStandardPAAxiomWitnessPrefixContextCode M
          witnesses baseContext) prefix)
      (rawTemplateFormula translation
        (coqDynamicTruthImpChildrenDomainConclusionTemplate
          level parent left right)) resultRoot.
Proof.
  intros M hPA translation hagreement baseWitnessList baseContext prefix
    level parent left right shapeRoot parentDomainRoot
    hprefix hbase hshape hparentDomain.
  destruct
    (raw_codedPALocalProofOf_dynamicTruthImpChildrenDomain_instance_on_witnessed_tail_under_prefix
      M hPA translation hagreement baseWitnessList baseContext prefix
      level parent left right hprefix hbase)
    as (witnesses & implicationRoot & hextended & himplication).
  destruct
    (raw_codedPALocalProofOf_templateImp2_of_roots_on_standard_witnessed_extension_under_prefix
      M hPA translation hagreement baseWitnessList baseContext prefix
      witnesses
      (coqDynamicTruthImpChildrenDomainInstanceTemplate
        level parent left right)
      (coqDynamicTruthImpChildrenDomainShapePremiseTemplate
        level parent left right)
      (coqDynamicTruthImpChildrenDomainParentPremiseTemplate
        level parent left right)
      (coqDynamicTruthImpChildrenDomainConclusionTemplate
        level parent left right)
      implicationRoot shapeRoot parentDomainRoot hbase hextended
      (coqDynamicTruthImpChildrenDomainInstanceTemplate_imp2_shape
        level parent left right)
      himplication hshape hparentDomain)
    as (resultRoot & hincluded & hresult).
  exists witnesses, resultRoot.
  split; [exact hextended |].
  split; [exact hincluded | exact hresult].
Qed.

End PABoundedRawCodedDynamicTruthImpChildrenDomainProofCompilation.
