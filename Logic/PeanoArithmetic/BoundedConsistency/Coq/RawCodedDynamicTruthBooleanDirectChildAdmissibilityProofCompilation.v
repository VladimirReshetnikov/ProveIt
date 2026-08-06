(**
  Represented admissibility inheritance for a direct Boolean child.

  Conjunction and disjunction use the same syntax-tree traversal and the
  same rank maximum law.  This module factors that common proof through the
  metatheoretic constructor tag from the guarded Boolean cell module.  It
  then compiles the resulting four-premise PA theorem under an arbitrary
  adequate template prefix, synchronizing every caller root on the finite
  standard-axiom extension selected by the closed theorem compiler.
*)

From Stdlib Require Import List Lia.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawModelCompleteness
  RawCodedSyntaxConstructors
  RawCodedFormulaRankStep
  RawCodedFormulaRankTraversal
  RawCodedFixedLevelDomainLaws
  RawCodedFixedLevelTruthTotality
  RawCodedFormulaBoundAtomicallyAdequateTotality
  RawCodedFixedLevelTruthAdmissibleCoherence
  RawCodedDynamicTruthFixedSyntaxFragments
  RawCodedRestrictedPAProof
  RawCodedPAAxiomWitnessPrefix
  RawCodedPALocalProofExistential
  RawCodedPALocalProofComposition
  RawCodedPALocalProofConjunction
  RawCodedPALocalProofAndIntroduction
  RawCodedPALocalProofWitnessedContextMerge
  RawCodedTemplateSyntax
  RawCodedTemplateProofCompiler
  RawCodedTemplateProofCompilerSelfShiftTail
  RawCodedTemplatePAEmbedding
  RawCodedTemplateLocalProofWitnessedTailTransport
  RawCodedTemplateLocalProofStandardWitnessTailTransport
  RawCodedPALocalProofUniversalEliminationChain
  RawCodedAssignmentUniversalDefinednessProofCompilation
  RawCodedFormulaImpChildrenAtomicAdequacyProofCompilation
  RawCodedDynamicTruthImpDirectChildAdmissibilityProofCompilation
  RawCodedDynamicTruthImpGuardedChildAdmissibilityCompilation
  RawCodedDynamicTruthBooleanGuardedBranchExclusivity.

Module
  PABoundedRawCodedDynamicTruthBooleanDirectChildAdmissibilityProofCompilation.

Import ListNotations.
Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawModelCompleteness.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedFormulaRankStep.
Import PABoundedRawCodedFormulaRankTraversal.
Import PABoundedRawCodedFixedLevelDomainLaws.
Import PABoundedRawCodedFixedLevelTruthTotality.
Import PABoundedRawCodedFormulaBoundAtomicallyAdequateTotality.
Import PABoundedRawCodedFixedLevelTruthAdmissibleCoherence.
Import PABoundedRawCodedDynamicTruthFixedSyntaxFragments.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedPAAxiomWitnessPrefix.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPALocalProofComposition.
Import PABoundedRawCodedPALocalProofConjunction.
Import PABoundedRawCodedPALocalProofAndIntroduction.
Import PABoundedRawCodedPALocalProofWitnessedContextMerge.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedTemplateProofCompilerSelfShiftTail.
Import PABoundedRawCodedTemplatePAEmbedding.
Import PABoundedRawCodedTemplateLocalProofWitnessedTailTransport.
Import PABoundedRawCodedTemplateLocalProofStandardWitnessTailTransport.
Import PABoundedRawCodedPALocalProofUniversalEliminationChain.
Import PABoundedRawCodedAssignmentUniversalDefinednessProofCompilation.
Import PABoundedRawCodedFormulaImpChildrenAtomicAdequacyProofCompilation.
Import
  PABoundedRawCodedDynamicTruthImpDirectChildAdmissibilityProofCompilation.
Import
  PABoundedRawCodedDynamicTruthImpGuardedChildAdmissibilityCompilation.
Import PABoundedRawCodedDynamicTruthBooleanGuardedBranchExclusivity.

(** Atomic adequacy is inherited by both children for either Boolean
    constructor.  The proof is intentionally extracted from the later
    admissibility theorem because the rank-domain half is useful on its own. *)
Lemma raw_codedFormulaAtomicallyAdequate_and_children : forall
    (M : RawPAModel), RawPASatisfies M -> forall parent left right,
  RawCodedFormulaAtomicallyAdequate M parent ->
  parent = rawFormulaAndCode M left right ->
  RawCodedFormulaAtomicallyAdequate M left /\
  RawCodedFormulaAtomicallyAdequate M right.
Proof.
  intros M hPA parent left right hparent hshape.
  subst parent.
  destruct (raw_codedFormulaAtomicallyAdequate_shape_at M hPA
    (rawShapeAnd left right) hparent) as
    (formulaCode & formulaStep & bound & rootIndex &
      htraversal & hatomic & leftIndex & rightIndex &
      hleftBelow & hleftLookup & hrightBelow & hrightLookup).
  split.
  - exact (raw_codedFormulaAtomicallyAdequate_child_at M hPA
      formulaCode formulaStep bound rootIndex
      (rawFormulaAndCode M left right) leftIndex left
      htraversal hatomic hleftBelow hleftLookup).
  - exact (raw_codedFormulaAtomicallyAdequate_child_at M hPA
      formulaCode formulaStep bound rootIndex
      (rawFormulaAndCode M left right) rightIndex right
      htraversal hatomic hrightBelow hrightLookup).
Qed.

Lemma raw_codedFormulaAtomicallyAdequate_or_children : forall
    (M : RawPAModel), RawPASatisfies M -> forall parent left right,
  RawCodedFormulaAtomicallyAdequate M parent ->
  parent = rawFormulaOrCode M left right ->
  RawCodedFormulaAtomicallyAdequate M left /\
  RawCodedFormulaAtomicallyAdequate M right.
Proof.
  intros M hPA parent left right hparent hshape.
  subst parent.
  destruct (raw_codedFormulaAtomicallyAdequate_shape_at M hPA
    (rawShapeOr left right) hparent) as
    (formulaCode & formulaStep & bound & rootIndex &
      htraversal & hatomic & leftIndex & rightIndex &
      hleftBelow & hleftLookup & hrightBelow & hrightLookup).
  split.
  - exact (raw_codedFormulaAtomicallyAdequate_child_at M hPA
      formulaCode formulaStep bound rootIndex
      (rawFormulaOrCode M left right) leftIndex left
      htraversal hatomic hleftBelow hleftLookup).
  - exact (raw_codedFormulaAtomicallyAdequate_child_at M hPA
      formulaCode formulaStep bound rootIndex
      (rawFormulaOrCode M left right) rightIndex right
      htraversal hatomic hrightBelow hrightLookup).
Qed.

Lemma raw_codedFormulaAtomicallyAdequate_boolean_children : forall
    constructor (M : RawPAModel), RawPASatisfies M ->
    forall parent left right,
  RawCodedFormulaAtomicallyAdequate M parent ->
  parent = rawDynamicTruthBooleanConstructorCode M constructor left right ->
  RawCodedFormulaAtomicallyAdequate M left /\
  RawCodedFormulaAtomicallyAdequate M right.
Proof.
  intros constructor M hPA parent left right hparent hshape.
  destruct constructor; cbn [rawDynamicTruthBooleanConstructorCode]
    in hshape.
  - exact (raw_codedFormulaAtomicallyAdequate_and_children
      M hPA parent left right hparent hshape).
  - exact (raw_codedFormulaAtomicallyAdequate_or_children
      M hPA parent left right hparent hshape).
Qed.

(** Carrier-parametric domain inheritance for any binary connective whose
    rank equation is [RawFormulaRankAndOr].  Factoring over the rank view
    avoids duplicating the order argument for And and Or. *)
Lemma raw_dynamicTruthSigmaRecordDomain_and_or_from_view : forall
    (M : RawPAModel), RawPASatisfies M -> forall level code left right,
  (forall sigma pi,
    RawCodedFormulaRank M code sigma pi ->
    exists leftSigma leftPi rightSigma rightPi,
      RawCodedFormulaRank M left leftSigma leftPi /\
      RawCodedFormulaRank M right rightSigma rightPi /\
      RawFormulaRankAndOr M sigma pi
        leftSigma leftPi rightSigma rightPi) ->
  RawDynamicTruthSigmaRecordDomain M level code ->
  RawDynamicTruthSigmaRecordDomain M level left /\
  RawDynamicTruthSigmaRecordDomain M level right.
Proof.
  intros M hPA level code left right hview
    (sigma & pi & hrank & hsigmaBound).
  destruct (hview sigma pi hrank) as
    (leftSigma & leftPi & rightSigma & rightPi &
      hleftRank & hrightRank & [hsigmaMax hpiMax]).
  split.
  - exists leftSigma, leftPi. split; [exact hleftRank |].
    exact (raw_le_trans M hPA leftSigma sigma level
      (raw_fixedLevel_max_left_le M hPA
        sigma leftSigma rightSigma hsigmaMax) hsigmaBound).
  - exists rightSigma, rightPi. split; [exact hrightRank |].
    exact (raw_le_trans M hPA rightSigma sigma level
      (raw_fixedLevel_max_right_le M hPA
        sigma leftSigma rightSigma hsigmaMax) hsigmaBound).
Qed.

Lemma raw_dynamicTruthPiRecordDomain_and_or_from_view : forall
    (M : RawPAModel), RawPASatisfies M -> forall level code left right,
  (forall sigma pi,
    RawCodedFormulaRank M code sigma pi ->
    exists leftSigma leftPi rightSigma rightPi,
      RawCodedFormulaRank M left leftSigma leftPi /\
      RawCodedFormulaRank M right rightSigma rightPi /\
      RawFormulaRankAndOr M sigma pi
        leftSigma leftPi rightSigma rightPi) ->
  RawDynamicTruthPiRecordDomain M level code ->
  RawDynamicTruthPiRecordDomain M level left /\
  RawDynamicTruthPiRecordDomain M level right.
Proof.
  intros M hPA level code left right hview
    (sigma & pi & hrank & hpiBound).
  destruct (hview sigma pi hrank) as
    (leftSigma & leftPi & rightSigma & rightPi &
      hleftRank & hrightRank & [hsigmaMax hpiMax]).
  split.
  - exists leftSigma, leftPi. split; [exact hleftRank |].
    exact (raw_le_trans M hPA leftPi pi level
      (raw_fixedLevel_max_left_le M hPA
        pi leftPi rightPi hpiMax) hpiBound).
  - exists rightSigma, rightPi. split; [exact hrightRank |].
    exact (raw_le_trans M hPA rightPi pi level
      (raw_fixedLevel_max_right_le M hPA
        pi leftPi rightPi hpiMax) hpiBound).
Qed.

Lemma raw_dynamicTruthRecordDomain_boolean_children : forall
    constructor (M : RawPAModel), RawPASatisfies M ->
    forall level parent left right,
  parent = rawDynamicTruthBooleanConstructorCode M constructor left right ->
  (RawDynamicTruthSigmaRecordDomain M level parent \/
   RawDynamicTruthPiRecordDomain M level parent) ->
  (RawDynamicTruthSigmaRecordDomain M level left \/
   RawDynamicTruthPiRecordDomain M level left) /\
  (RawDynamicTruthSigmaRecordDomain M level right \/
   RawDynamicTruthPiRecordDomain M level right).
Proof.
  intros constructor M hPA level parent left right hshape hdomain.
  destruct constructor; cbn [rawDynamicTruthBooleanConstructorCode]
    in hshape; subst parent; destruct hdomain as [hsigma | hpi].
  - destruct (raw_dynamicTruthSigmaRecordDomain_and_or_from_view
      M hPA level (rawFormulaAndCode M left right) left right
      (raw_codedFormulaRank_and_view M hPA left right) hsigma)
      as [hleft hright].
    split; [left | left]; assumption.
  - destruct (raw_dynamicTruthPiRecordDomain_and_or_from_view
      M hPA level (rawFormulaAndCode M left right) left right
      (raw_codedFormulaRank_and_view M hPA left right) hpi)
      as [hleft hright].
    split; [right | right]; assumption.
  - destruct (raw_dynamicTruthSigmaRecordDomain_and_or_from_view
      M hPA level (rawFormulaOrCode M left right) left right
      (raw_codedFormulaRank_or_view M hPA left right) hsigma)
      as [hleft hright].
    split; [left | left]; assumption.
  - destruct (raw_dynamicTruthPiRecordDomain_and_or_from_view
      M hPA level (rawFormulaOrCode M left right) left right
      (raw_codedFormulaRank_or_view M hPA left right) hpi)
      as [hleft hright].
    split; [right | right]; assumption.
Qed.

Definition RawDynamicTruthBooleanDirectChildAdmissibilityCoreAt
    (constructor : DynamicTruthBooleanConstructor)
    (M : RawPAModel) (level parent left right child : M) : Prop :=
  RawCodedFormulaAtomicallyAdequate M child /\
  (RawDynamicTruthSigmaRecordDomain M level child \/
   RawDynamicTruthPiRecordDomain M level child).

Arguments RawDynamicTruthBooleanDirectChildAdmissibilityCoreAt
  constructor M level parent left right child : clear implicits.

Lemma raw_dynamicTruthBooleanDirectChild_admissibility_core : forall
    constructor (M : RawPAModel), RawPASatisfies M ->
    forall level parent left right child,
  RawCodedFormulaAtomicallyAdequate M parent ->
  (RawDynamicTruthSigmaRecordDomain M level parent \/
   RawDynamicTruthPiRecordDomain M level parent) ->
  parent = rawDynamicTruthBooleanConstructorCode M constructor left right ->
  (child = left \/ child = right) ->
  RawDynamicTruthBooleanDirectChildAdmissibilityCoreAt constructor M
    level parent left right child.
Proof.
  intros constructor M hPA level parent left right child
    hatomic hdomain hshape hdirect.
  pose proof (raw_codedFormulaAtomicallyAdequate_boolean_children
    constructor M hPA parent left right hatomic hshape)
    as [hleftAtomic hrightAtomic].
  pose proof (raw_dynamicTruthRecordDomain_boolean_children
    constructor M hPA level parent left right hshape hdomain)
    as [hleftDomain hrightDomain].
  destruct hdirect as [hchild | hchild]; subst child.
  - split; assumption.
  - split; assumption.
Qed.

(** Binder order: level, parent, left, right, child. *)
Definition dynamicTruthBooleanDirectChildAdmissibilityCoreBodyFormula
    (constructor : DynamicTruthBooleanConstructor) : formula :=
  pImp
    (codedFormulaAtomicallyAdequateTermAt (tVar 3))
    (pImp
      (pOr
        (dynamicTruthSigmaRecordDomainTermAt (tVar 4) (tVar 3))
        (dynamicTruthPiRecordDomainTermAt (tVar 4) (tVar 3)))
      (pImp
        (dynamicTruthBooleanConstructorCodeTermAt constructor
          (tVar 3) (tVar 2) (tVar 1))
        (pImp
          (pOr
            (pEq (tVar 0) (tVar 2))
            (pEq (tVar 0) (tVar 1)))
          (pAnd
            (codedFormulaAtomicallyAdequateTermAt (tVar 0))
            (pOr
              (dynamicTruthSigmaRecordDomainTermAt
                (tVar 4) (tVar 0))
              (dynamicTruthPiRecordDomainTermAt
                (tVar 4) (tVar 0))))))).

Definition dynamicTruthBooleanDirectChildAdmissibilityCoreFormula
    (constructor : DynamicTruthBooleanConstructor) : formula :=
  pAll (pAll (pAll (pAll (pAll
    (dynamicTruthBooleanDirectChildAdmissibilityCoreBodyFormula
      constructor))))).

Lemma raw_sat_dynamicTruthBooleanDirectChildAdmissibilityCoreFormula_iff :
    forall constructor (M : RawPAModel) (e : nat -> M),
  raw_formula_sat M e
    (dynamicTruthBooleanDirectChildAdmissibilityCoreFormula constructor) <->
  forall level parent left right child : M,
    RawCodedFormulaAtomicallyAdequate M parent ->
    (RawDynamicTruthSigmaRecordDomain M level parent \/
     RawDynamicTruthPiRecordDomain M level parent) ->
    parent = rawDynamicTruthBooleanConstructorCode M constructor
      left right ->
    (child = left \/ child = right) ->
    RawDynamicTruthBooleanDirectChildAdmissibilityCoreAt constructor M
      level parent left right child.
Proof.
  intros constructor M e.
  unfold dynamicTruthBooleanDirectChildAdmissibilityCoreFormula,
    dynamicTruthBooleanDirectChildAdmissibilityCoreBodyFormula,
    RawDynamicTruthBooleanDirectChildAdmissibilityCoreAt.
  cbn [raw_formula_sat].
  repeat setoid_rewrite raw_sat_codedFormulaAtomicallyAdequateTermAt_iff.
  repeat setoid_rewrite raw_sat_dynamicTruthSigmaRecordDomainTermAt_iff.
  repeat setoid_rewrite raw_sat_dynamicTruthPiRecordDomainTermAt_iff.
  setoid_rewrite
    raw_sat_dynamicTruthBooleanConstructorCodeTermAt_iff.
  cbn [raw_term_eval scons]. reflexivity.
Qed.

Lemma dynamicTruthBooleanDirectChildAdmissibilityCoreFormula_sentence :
    forall constructor,
  Formula.Sentence
    (dynamicTruthBooleanDirectChildAdmissibilityCoreFormula constructor).
Proof.
  intros constructor k hfree.
  destruct constructor;
  unfold dynamicTruthBooleanDirectChildAdmissibilityCoreFormula,
    dynamicTruthBooleanDirectChildAdmissibilityCoreBodyFormula,
    dynamicTruthBooleanConstructorCodeTermAt,
    codedFormulaAtomicallyAdequateTermAt,
    dynamicTruthSigmaRecordDomainTermAt,
    dynamicTruthPiRecordDomainTermAt in hfree;
  cbn in hfree; lia.
Qed.

Theorem dynamicTruthBooleanDirectChildAdmissibilityCoreFormula_raw_valid :
    forall constructor (M : RawPAModel), RawPASatisfies M -> forall e,
  raw_formula_sat M e
    (dynamicTruthBooleanDirectChildAdmissibilityCoreFormula constructor).
Proof.
  intros constructor M hPA e.
  apply (proj2
    (raw_sat_dynamicTruthBooleanDirectChildAdmissibilityCoreFormula_iff
      constructor M e)).
  exact (raw_dynamicTruthBooleanDirectChild_admissibility_core
    constructor M hPA).
Qed.

Theorem PA_proves_dynamicTruthBooleanDirectChildAdmissibilityCoreFormula :
    forall constructor,
  Formula.BProv Formula.Ax_s []
    (dynamicTruthBooleanDirectChildAdmissibilityCoreFormula constructor).
Proof.
  intro constructor.
  apply PA_BProv_of_raw_valid.
  - exact
      (dynamicTruthBooleanDirectChildAdmissibilityCoreFormula_sentence
        constructor).
  - exact
      (dynamicTruthBooleanDirectChildAdmissibilityCoreFormula_raw_valid
        constructor).
Qed.

Definition coqDynamicTruthBooleanDirectChildAdmissibilityCoreInstanceTemplate
    (constructor : DynamicTruthBooleanConstructor)
    (level parent left right child : TemplateTerm) : TemplateFormula :=
  templateUniversalOpenManyOrBot
    (embedPAFormula
      (dynamicTruthBooleanDirectChildAdmissibilityCoreFormula constructor))
    [level; parent; left; right; child].

Lemma
    coqDynamicTruthBooleanDirectChildAdmissibilityCoreInstanceTemplate_open :
    forall constructor level parent left right child,
  templateUniversalOpenMany
    (embedPAFormula
      (dynamicTruthBooleanDirectChildAdmissibilityCoreFormula constructor))
    [level; parent; left; right; child] =
  Some (coqDynamicTruthBooleanDirectChildAdmissibilityCoreInstanceTemplate
    constructor level parent left right child).
Proof.
  intros constructor level parent left right child.
  unfold coqDynamicTruthBooleanDirectChildAdmissibilityCoreInstanceTemplate,
    templateUniversalOpenManyOrBot,
    dynamicTruthBooleanDirectChildAdmissibilityCoreFormula.
  cbn [templateUniversalOpenMany embedPAFormula
    templateFormulaOpen templateFormulaSubst].
  reflexivity.
Qed.

Definition coqDynamicTruthBooleanDirectChildAtomicPremiseTemplate
    constructor level parent left right child :=
  templateImpAntecedent
    (coqDynamicTruthBooleanDirectChildAdmissibilityCoreInstanceTemplate
      constructor level parent left right child).

Definition coqDynamicTruthBooleanDirectChildDomainPremiseTemplate
    constructor level parent left right child :=
  templateImpAntecedent (templateImpConsequent
    (coqDynamicTruthBooleanDirectChildAdmissibilityCoreInstanceTemplate
      constructor level parent left right child)).

Definition coqDynamicTruthBooleanDirectChildShapePremiseTemplate
    constructor level parent left right child :=
  templateImpAntecedent (templateImpConsequent (templateImpConsequent
    (coqDynamicTruthBooleanDirectChildAdmissibilityCoreInstanceTemplate
      constructor level parent left right child))).

Definition coqDynamicTruthBooleanDirectChildGuardPremiseTemplate
    constructor level parent left right child :=
  templateImpAntecedent (templateImpConsequent (templateImpConsequent
    (templateImpConsequent
      (coqDynamicTruthBooleanDirectChildAdmissibilityCoreInstanceTemplate
        constructor level parent left right child)))).

Definition coqDynamicTruthBooleanDirectChildAdmissibilityCoreConclusionTemplate
    constructor level parent left right child :=
  templateImpConsequent (templateImpConsequent (templateImpConsequent
    (templateImpConsequent
      (coqDynamicTruthBooleanDirectChildAdmissibilityCoreInstanceTemplate
        constructor level parent left right child)))).

Lemma
    coqDynamicTruthBooleanDirectChildAdmissibilityCoreInstanceTemplate_imp4_shape :
  forall constructor level parent left right child,
  coqDynamicTruthBooleanDirectChildAdmissibilityCoreInstanceTemplate
      constructor level parent left right child =
  tfImp
    (coqDynamicTruthBooleanDirectChildAtomicPremiseTemplate
      constructor level parent left right child)
    (tfImp
      (coqDynamicTruthBooleanDirectChildDomainPremiseTemplate
        constructor level parent left right child)
      (tfImp
        (coqDynamicTruthBooleanDirectChildShapePremiseTemplate
          constructor level parent left right child)
        (tfImp
          (coqDynamicTruthBooleanDirectChildGuardPremiseTemplate
            constructor level parent left right child)
          (coqDynamicTruthBooleanDirectChildAdmissibilityCoreConclusionTemplate
            constructor level parent left right child)))).
Proof.
  intros constructor level parent left right child.
  unfold coqDynamicTruthBooleanDirectChildAtomicPremiseTemplate,
    coqDynamicTruthBooleanDirectChildDomainPremiseTemplate,
    coqDynamicTruthBooleanDirectChildShapePremiseTemplate,
    coqDynamicTruthBooleanDirectChildGuardPremiseTemplate,
    coqDynamicTruthBooleanDirectChildAdmissibilityCoreConclusionTemplate,
    coqDynamicTruthBooleanDirectChildAdmissibilityCoreInstanceTemplate,
    templateUniversalOpenManyOrBot,
    dynamicTruthBooleanDirectChildAdmissibilityCoreFormula,
    dynamicTruthBooleanDirectChildAdmissibilityCoreBodyFormula.
  cbn [templateUniversalOpenMany embedPAFormula
    templateFormulaOpen templateFormulaSubst
    templateImpAntecedent templateImpConsequent].
  reflexivity.
Qed.

(** The first two premises are constructor independent.  These identities
    let the native parent endpoint compiler be reused without rebuilding its
    roots merely because the branch later selects And or Or. *)
Lemma coqDynamicTruthBooleanDirectChildAtomicPremiseTemplate_eq_imp : forall
    constructor level parent left right child,
  coqDynamicTruthBooleanDirectChildAtomicPremiseTemplate
      constructor level parent left right child =
  coqDynamicTruthImpDirectChildAtomicPremiseTemplate
      level parent left right child.
Proof.
  intros constructor level parent left right child.
  destruct constructor;
  unfold coqDynamicTruthBooleanDirectChildAtomicPremiseTemplate,
    coqDynamicTruthImpDirectChildAtomicPremiseTemplate,
    coqDynamicTruthBooleanDirectChildAdmissibilityCoreInstanceTemplate,
    coqDynamicTruthImpDirectChildAdmissibilityCoreInstanceTemplate,
    templateUniversalOpenManyOrBot,
    dynamicTruthBooleanDirectChildAdmissibilityCoreFormula,
    dynamicTruthBooleanDirectChildAdmissibilityCoreBodyFormula,
    dynamicTruthImpDirectChildAdmissibilityCoreFormula,
    dynamicTruthImpDirectChildAdmissibilityCoreBodyFormula;
  cbn [templateUniversalOpenMany embedPAFormula
    templateFormulaOpen templateFormulaSubst templateImpAntecedent];
  reflexivity.
Qed.

Lemma coqDynamicTruthBooleanDirectChildDomainPremiseTemplate_eq_imp : forall
    constructor level parent left right child,
  coqDynamicTruthBooleanDirectChildDomainPremiseTemplate
      constructor level parent left right child =
  coqDynamicTruthImpDirectChildDomainPremiseTemplate
      level parent left right child.
Proof.
  intros constructor level parent left right child.
  destruct constructor;
  unfold coqDynamicTruthBooleanDirectChildDomainPremiseTemplate,
    coqDynamicTruthImpDirectChildDomainPremiseTemplate,
    coqDynamicTruthBooleanDirectChildAdmissibilityCoreInstanceTemplate,
    coqDynamicTruthImpDirectChildAdmissibilityCoreInstanceTemplate,
    templateUniversalOpenManyOrBot,
    dynamicTruthBooleanDirectChildAdmissibilityCoreFormula,
    dynamicTruthBooleanDirectChildAdmissibilityCoreBodyFormula,
    dynamicTruthImpDirectChildAdmissibilityCoreFormula,
    dynamicTruthImpDirectChildAdmissibilityCoreBodyFormula;
  cbn [templateUniversalOpenMany embedPAFormula
    templateFormulaOpen templateFormulaSubst
    templateImpAntecedent templateImpConsequent];
  reflexivity.
Qed.

Theorem
    raw_codedPALocalProofOf_dynamicTruthBooleanDirectChildAdmissibilityCore_instance_on_witnessed_tail_under_prefix :
  forall constructor (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall baseWitnessList baseContext prefix level parent left right child,
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
        (coqDynamicTruthBooleanDirectChildAdmissibilityCoreInstanceTemplate
          constructor level parent left right child)) proofRoot.
Proof.
  intros constructor M hPA translation hagreement
    baseWitnessList baseContext prefix level parent left right child
    hprefix hbase.
  destruct
    (raw_codedTemplatePALocalProofOf_of_BProv_open_many_on_witnessed_tail
      M hPA translation hagreement baseWitnessList baseContext
      (dynamicTruthBooleanDirectChildAdmissibilityCoreFormula constructor)
      [level; parent; left; right; child]
      (coqDynamicTruthBooleanDirectChildAdmissibilityCoreInstanceTemplate
        constructor level parent left right child)
      hbase
      (PA_proves_dynamicTruthBooleanDirectChildAdmissibilityCoreFormula
        constructor)
      (coqDynamicTruthBooleanDirectChildAdmissibilityCoreInstanceTemplate_open
        constructor level parent left right child))
    as (witnesses & sourceRoot & hextended & hsource).
  set (extendedContext :=
    rawStandardPAAxiomWitnessPrefixContextCode M
      witnesses baseContext).
  destruct (raw_codedPALocalProof_templatePrefix M hPA translation
    extendedContext prefix
    (rawTemplateFormula translation
      (coqDynamicTruthBooleanDirectChildAdmissibilityCoreInstanceTemplate
        constructor level parent left right child)) sourceRoot
    (raw_codedPAAxiomWitnessPrefix_context_realizable_of_witnessed M
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        witnesses baseWitnessList)
      extendedContext hextended)
    hprefix hsource) as [proofRoot hproof].
  exists witnesses, proofRoot. split; assumption.
Qed.

Theorem
    raw_codedPALocalProofOf_dynamicTruthBooleanDirectChildAdmissibilityCore_of_roots_on_witnessed_extension_under_prefix :
  forall constructor (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall baseWitnessList baseContext prefix level parent left right child
      atomicRoot domainRoot shapeRoot guardRoot,
  RawCodedTemplatePrefixAtomicallyAdequate M translation prefix ->
  RawCodedPAAxiomWitnessContext M baseWitnessList baseContext ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail translation baseContext prefix)
    (rawTemplateFormula translation
      (coqDynamicTruthBooleanDirectChildAtomicPremiseTemplate
        constructor level parent left right child)) atomicRoot ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail translation baseContext prefix)
    (rawTemplateFormula translation
      (coqDynamicTruthBooleanDirectChildDomainPremiseTemplate
        constructor level parent left right child)) domainRoot ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail translation baseContext prefix)
    (rawTemplateFormula translation
      (coqDynamicTruthBooleanDirectChildShapePremiseTemplate
        constructor level parent left right child)) shapeRoot ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail translation baseContext prefix)
    (rawTemplateFormula translation
      (coqDynamicTruthBooleanDirectChildGuardPremiseTemplate
        constructor level parent left right child)) guardRoot ->
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
        (coqDynamicTruthBooleanDirectChildAdmissibilityCoreConclusionTemplate
          constructor level parent left right child)) resultRoot.
Proof.
  intros constructor M hPA translation hagreement
    baseWitnessList baseContext prefix level parent left right child
    atomicRoot domainRoot shapeRoot guardRoot hprefix hbase
    hatomic hdomain hshape hguard.
  destruct
    (raw_codedPALocalProofOf_dynamicTruthBooleanDirectChildAdmissibilityCore_instance_on_witnessed_tail_under_prefix
      constructor M hPA translation hagreement
      baseWitnessList baseContext prefix level parent left right child
      hprefix hbase)
    as (witnesses & implicationRoot & hextended & himplication).
  destruct
    (raw_codedPALocalProofOf_templateImp4_of_roots_on_standard_witnessed_extension_under_prefix
      M hPA translation hagreement baseWitnessList baseContext prefix
      witnesses
      (coqDynamicTruthBooleanDirectChildAdmissibilityCoreInstanceTemplate
        constructor level parent left right child)
      (coqDynamicTruthBooleanDirectChildAtomicPremiseTemplate
        constructor level parent left right child)
      (coqDynamicTruthBooleanDirectChildDomainPremiseTemplate
        constructor level parent left right child)
      (coqDynamicTruthBooleanDirectChildShapePremiseTemplate
        constructor level parent left right child)
      (coqDynamicTruthBooleanDirectChildGuardPremiseTemplate
        constructor level parent left right child)
      (coqDynamicTruthBooleanDirectChildAdmissibilityCoreConclusionTemplate
        constructor level parent left right child)
      implicationRoot atomicRoot domainRoot shapeRoot guardRoot
      hbase hextended
      (coqDynamicTruthBooleanDirectChildAdmissibilityCoreInstanceTemplate_imp4_shape
        constructor level parent left right child)
      himplication hatomic hdomain hshape hguard)
    as (resultRoot & hincluded & hresult).
  exists witnesses, resultRoot.
  split; [exact hextended |].
  split; assumption.
Qed.

(** Assemble the constructor-only result with assignment definedness.  The
    definitions mirror the implication compiler deliberately: downstream
    local exclusivity consumes one constructor-independent admissibility
    formula, so selecting And or Or must not alter its endpoint code. *)
Definition coqDynamicTruthBooleanGuardedChildShapeTemplate
    constructor (level parent left right child : TemplateTerm)
    : TemplateFormula :=
  coqDynamicTruthBooleanDirectChildShapePremiseTemplate
    constructor level parent left right child.

Definition coqDynamicTruthBooleanGuardedChildGuardTemplate
    constructor (level parent left right child : TemplateTerm)
    : TemplateFormula :=
  coqDynamicTruthBooleanDirectChildGuardPremiseTemplate
    constructor level parent left right child.

Definition coqDynamicTruthBooleanGuardedChildAtomicTemplate
    constructor (level parent left right child : TemplateTerm)
    : TemplateFormula :=
  templateAndLeftOrBotLocal
    (coqDynamicTruthBooleanDirectChildAdmissibilityCoreConclusionTemplate
      constructor level parent left right child).

Definition coqDynamicTruthBooleanGuardedChildDomainTemplate
    constructor (level parent left right child : TemplateTerm)
    : TemplateFormula :=
  templateAndRightOrBotLocal
    (coqDynamicTruthBooleanDirectChildAdmissibilityCoreConclusionTemplate
      constructor level parent left right child).

Definition coqDynamicTruthBooleanGuardedChildAssignmentTemplate
    (assignmentCode assignmentStep child : TemplateTerm)
    : TemplateFormula :=
  coqAssignmentUniversalDefinednessInstanceTemplate
    assignmentCode assignmentStep child.

Definition coqDynamicTruthBooleanGuardedChildAdmissibleTemplate
    constructor
    (level parent left right child assignmentCode assignmentStep
      : TemplateTerm) : TemplateFormula :=
  tfAnd
    (coqDynamicTruthBooleanGuardedChildAtomicTemplate
      constructor level parent left right child)
    (tfAnd
      (coqDynamicTruthBooleanGuardedChildAssignmentTemplate
        assignmentCode assignmentStep child)
      (coqDynamicTruthBooleanGuardedChildDomainTemplate
        constructor level parent left right child)).

Lemma
    coqDynamicTruthBooleanDirectChildAdmissibilityCoreConclusionTemplate_shape :
  forall constructor level parent left right child,
  coqDynamicTruthBooleanDirectChildAdmissibilityCoreConclusionTemplate
      constructor level parent left right child =
  tfAnd
    (coqDynamicTruthBooleanGuardedChildAtomicTemplate
      constructor level parent left right child)
    (coqDynamicTruthBooleanGuardedChildDomainTemplate
      constructor level parent left right child).
Proof.
  intros constructor level parent left right child.
  unfold coqDynamicTruthBooleanGuardedChildAtomicTemplate,
    coqDynamicTruthBooleanGuardedChildDomainTemplate,
    templateAndLeftOrBotLocal, templateAndRightOrBotLocal,
    coqDynamicTruthBooleanDirectChildAdmissibilityCoreConclusionTemplate,
    coqDynamicTruthBooleanDirectChildAdmissibilityCoreInstanceTemplate,
    templateUniversalOpenManyOrBot,
    dynamicTruthBooleanDirectChildAdmissibilityCoreFormula,
    dynamicTruthBooleanDirectChildAdmissibilityCoreBodyFormula.
  cbn [templateUniversalOpenMany embedPAFormula
    templateFormulaOpen templateFormulaSubst templateImpConsequent].
  reflexivity.
Qed.

(** The assembled result is independent of the Boolean constructor.  This
    exact syntactic identity is what permits the already projected local
    exclusivity theorem to be applied without a connective-specific copy. *)
Lemma coqDynamicTruthBooleanGuardedChildAdmissibleTemplate_eq_imp : forall
    constructor level parent left right child assignmentCode assignmentStep,
  coqDynamicTruthBooleanGuardedChildAdmissibleTemplate constructor
      level parent left right child assignmentCode assignmentStep =
  coqDynamicTruthImpGuardedChildAdmissibleTemplate
      level parent left right child assignmentCode assignmentStep.
Proof.
  intros constructor level parent left right child
    assignmentCode assignmentStep.
  destruct constructor;
  unfold coqDynamicTruthBooleanGuardedChildAdmissibleTemplate,
    coqDynamicTruthBooleanGuardedChildAtomicTemplate,
    coqDynamicTruthBooleanGuardedChildDomainTemplate,
    coqDynamicTruthBooleanGuardedChildAssignmentTemplate,
    coqDynamicTruthImpGuardedChildAdmissibleTemplate,
    coqDynamicTruthImpGuardedChildAtomicTemplate,
    coqDynamicTruthImpGuardedChildDomainTemplate,
    coqDynamicTruthImpGuardedChildAssignmentTemplate,
    templateAndLeftOrBotLocal, templateAndRightOrBotLocal,
    coqDynamicTruthBooleanDirectChildAdmissibilityCoreConclusionTemplate,
    coqDynamicTruthBooleanDirectChildAdmissibilityCoreInstanceTemplate,
    coqDynamicTruthImpDirectChildAdmissibilityCoreConclusionTemplate,
    coqDynamicTruthImpDirectChildAdmissibilityCoreInstanceTemplate,
    templateUniversalOpenManyOrBot,
    dynamicTruthBooleanDirectChildAdmissibilityCoreFormula,
    dynamicTruthBooleanDirectChildAdmissibilityCoreBodyFormula,
    dynamicTruthImpDirectChildAdmissibilityCoreFormula,
    dynamicTruthImpDirectChildAdmissibilityCoreBodyFormula;
  cbn [templateUniversalOpenMany embedPAFormula
    templateFormulaOpen templateFormulaSubst templateImpConsequent];
  reflexivity.
Qed.

Theorem
    raw_codedPALocalProofOf_dynamicTruthBooleanGuardedChildAdmissible_of_parent_roots_on_witnessed_extension_under_prefix :
  forall constructor (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall baseWitnessList baseContext prefix
      level parent left right child assignmentCode assignmentStep
      parentAtomicRoot parentDomainRoot,
  RawCodedTemplatePrefixAtomicallyAdequate M translation prefix ->
  RawCodedPAAxiomWitnessContext M baseWitnessList baseContext ->
  In (coqDynamicTruthBooleanGuardedChildShapeTemplate constructor
      level parent left right child) prefix ->
  In (coqDynamicTruthBooleanGuardedChildGuardTemplate constructor
      level parent left right child) prefix ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail translation baseContext prefix)
    (rawTemplateFormula translation
      (coqDynamicTruthBooleanDirectChildAtomicPremiseTemplate
        constructor level parent left right child)) parentAtomicRoot ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail translation baseContext prefix)
    (rawTemplateFormula translation
      (coqDynamicTruthBooleanDirectChildDomainPremiseTemplate
        constructor level parent left right child)) parentDomainRoot ->
  exists targetWitnessList targetContext resultRoot,
    RawCodedPAAxiomWitnessContext M targetWitnessList targetContext /\
    RawContextListIncluded M baseContext targetContext /\
    RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation targetContext prefix)
      (rawTemplateFormula translation
        (coqDynamicTruthBooleanGuardedChildAdmissibleTemplate constructor
          level parent left right child assignmentCode assignmentStep))
      resultRoot.
Proof.
  intros constructor M hPA translation hagreement
    baseWitnessList baseContext prefix level parent left right child
    assignmentCode assignmentStep parentAtomicRoot parentDomainRoot
    hprefix hbase hshapeIn hguardIn hparentAtomic hparentDomain.
  pose proof
    (raw_templateAssumptionOnPAAxiomContext_localProof
      M hPA translation baseWitnessList baseContext prefix
      (coqDynamicTruthBooleanGuardedChildShapeTemplate constructor
        level parent left right child)
      hbase hshapeIn) as hshape.
  pose proof
    (raw_templateAssumptionOnPAAxiomContext_localProof
      M hPA translation baseWitnessList baseContext prefix
      (coqDynamicTruthBooleanGuardedChildGuardTemplate constructor
        level parent left right child)
      hbase hguardIn) as hguard.
  destruct
    (raw_codedPALocalProofOf_dynamicTruthBooleanDirectChildAdmissibilityCore_of_roots_on_witnessed_extension_under_prefix
      constructor M hPA translation hagreement
      baseWitnessList baseContext prefix level parent left right child
      parentAtomicRoot parentDomainRoot
      (rawTemplateProofCodeOnTail translation baseContext
        (trpAss prefix
          (coqDynamicTruthBooleanGuardedChildShapeTemplate constructor
            level parent left right child)))
      (rawTemplateProofCodeOnTail translation baseContext
        (trpAss prefix
          (coqDynamicTruthBooleanGuardedChildGuardTemplate constructor
            level parent left right child)))
      hprefix hbase hparentAtomic hparentDomain hshape hguard)
    as (coreWitnesses & coreRoot & hcoreWitnessed &
      hbaseCoreIncluded & hcore).
  set (coreWitnessList :=
    rawStandardPAAxiomWitnessPrefixWitnessListCode M
      coreWitnesses baseWitnessList).
  set (coreContext :=
    rawStandardPAAxiomWitnessPrefixContextCode M
      coreWitnesses baseContext).
  destruct
    (raw_codedPALocalProofOf_assignmentUniversalDefinedness_instance_on_witnessed_tail_under_prefix
      M hPA translation hagreement coreWitnessList coreContext prefix
      assignmentCode assignmentStep child hprefix hcoreWitnessed)
    as (assignmentWitnesses & assignmentRoot & hfinalWitnessed &
      hassignment).
  set (targetWitnessList :=
    rawStandardPAAxiomWitnessPrefixWitnessListCode M
      assignmentWitnesses coreWitnessList).
  set (targetContext :=
    rawStandardPAAxiomWitnessPrefixContextCode M
      assignmentWitnesses coreContext).
  assert (hcoreFinalIncluded :
      RawContextListIncluded M coreContext targetContext).
  {
    unfold targetContext.
    exact (raw_standardPAAxiomWitnessPrefixContextCode_target_included
      M hPA assignmentWitnesses coreContext).
  }
  destruct
    (raw_codedPALocalProof_sameTemplatePrefix_witnessedTail_transport
      M hPA translation coreWitnessList coreContext
      targetWitnessList targetContext prefix
      (rawTemplateFormula translation
        (coqDynamicTruthBooleanDirectChildAdmissibilityCoreConclusionTemplate
          constructor level parent left right child))
      coreRoot hcoreWitnessed hfinalWitnessed hcoreFinalIncluded hcore)
    as [transportedCoreRoot htransportedCore].
  rewrite
    (coqDynamicTruthBooleanDirectChildAdmissibilityCoreConclusionTemplate_shape
      constructor level parent left right child) in htransportedCore.
  rewrite rawTemplateFormula_and in htransportedCore.
  pose proof (raw_codedPALocalProofOf_andE1 M hPA
    (rawTemplateContextCodeOnTail translation targetContext prefix)
    (rawTemplateFormula translation
      (coqDynamicTruthBooleanGuardedChildAtomicTemplate constructor
        level parent left right child))
    (rawTemplateFormula translation
      (coqDynamicTruthBooleanGuardedChildDomainTemplate constructor
        level parent left right child))
    transportedCoreRoot htransportedCore) as hchildAtomic.
  pose proof (raw_codedPALocalProofOf_andE2 M hPA
    (rawTemplateContextCodeOnTail translation targetContext prefix)
    (rawTemplateFormula translation
      (coqDynamicTruthBooleanGuardedChildAtomicTemplate constructor
        level parent left right child))
    (rawTemplateFormula translation
      (coqDynamicTruthBooleanGuardedChildDomainTemplate constructor
        level parent left right child))
    transportedCoreRoot htransportedCore) as hchildDomain.
  lazymatch type of hchildAtomic with
  | RawCodedPALocalProofOf _ _ _ ?childAtomicRoot =>
      lazymatch type of hchildDomain with
      | RawCodedPALocalProofOf _ _ _ ?childDomainRoot =>
          pose proof (raw_codedPALocalProofOf_andI M hPA
            (rawTemplateContextCodeOnTail translation targetContext prefix)
            (rawTemplateFormula translation
              (coqDynamicTruthBooleanGuardedChildAssignmentTemplate
                assignmentCode assignmentStep child))
            (rawTemplateFormula translation
              (coqDynamicTruthBooleanGuardedChildDomainTemplate constructor
                level parent left right child))
            assignmentRoot childDomainRoot hassignment hchildDomain)
            as hassignmentAndDomain;
          lazymatch type of hassignmentAndDomain with
          | RawCodedPALocalProofOf _ _ _ ?assignmentAndDomainRoot =>
              pose proof (raw_codedPALocalProofOf_andI M hPA
                (rawTemplateContextCodeOnTail translation
                  targetContext prefix)
                (rawTemplateFormula translation
                  (coqDynamicTruthBooleanGuardedChildAtomicTemplate
                    constructor level parent left right child))
                (rawFormulaAndCode M
                  (rawTemplateFormula translation
                    (coqDynamicTruthBooleanGuardedChildAssignmentTemplate
                      assignmentCode assignmentStep child))
                  (rawTemplateFormula translation
                    (coqDynamicTruthBooleanGuardedChildDomainTemplate
                      constructor level parent left right child)))
                childAtomicRoot assignmentAndDomainRoot
                hchildAtomic hassignmentAndDomain) as hresult;
              lazymatch type of hresult with
              | RawCodedPALocalProofOf _ _ _ ?resultRoot =>
                  exists targetWitnessList, targetContext, resultRoot;
                  split; [exact hfinalWitnessed |];
                  split
              end
          end
      end
  end.
  - intros member hmember.
    exact (hcoreFinalIncluded member
      (hbaseCoreIncluded member hmember)).
  - unfold coqDynamicTruthBooleanGuardedChildAdmissibleTemplate in *.
    rewrite !rawTemplateFormula_and in *.
    exact hresult.
Qed.

End
  PABoundedRawCodedDynamicTruthBooleanDirectChildAdmissibilityProofCompilation.
