(**
  Positive fixed-production compilers for the two Sigma implication rows.

  The shared Sigma successor row contains two implication leaves.  A false
  left child selects [ImpFalseLeft]; a true right child selects
  [ImpTrueRight].  The earlier positive compiler constructed the same shared
  row only through the Or leaf.  This file factors the finite proof at the
  point where the selected leaf matters and instantiates it at indices one
  and two of the right-associated Sigma branch disjunction.

  Both public corollaries consume four represented roots in one witnessed
  context: mode zero, the instantiated Sigma domain, the implication-code
  atom, and the appropriate predecessor-state atom.  They return an actual
  represented fixed-production root.  No dynamic-truth Tarski law, global
  lookup result, or semantic validity hypothesis is assumed.
*)

From Stdlib Require Import List.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors
  RawCodedRestrictedPAProof
  RawCodedPAAxiomWitnessPrefix
  RawCodedPALocalProofExistential
  RawCodedPALocalProofComposition
  RawCodedTemplateSyntax
  RawCodedTemplateProjectionSchemas
  RawCodedTemplateDisjunctionCaseSchemas
  RawCodedTemplateProofCompiler
  RawCodedTemplateProofCompilerSelfShiftTail
  RawCodedDynamicTruthUniversalLeafSourceTemplate
  RawCodedFourStateTableAppendRowLtSuccCases
  RawCodedDynamicTruthSuccessorRowsAppendNormalization
  RawCodedDynamicTruthSigmaOrFixedProductionTemplate
  RawCodedDynamicTruthSigmaOrFixedProductionAppendIntegration.

Import ListNotations.

Module PABoundedRawCodedDynamicTruthSigmaImpFixedProductionCompilation.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedPAAxiomWitnessPrefix.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPALocalProofComposition.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateProjectionSchemas.
Import PABoundedRawCodedTemplateDisjunctionCaseSchemas.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedTemplateProofCompilerSelfShiftTail.
Import PABoundedRawCodedDynamicTruthUniversalLeafSourceTemplate.
Import PABoundedRawCodedFourStateTableAppendRowLtSuccCases.
Import PABoundedRawCodedDynamicTruthSuccessorRowsAppendNormalization.
Import PABoundedRawCodedDynamicTruthSigmaOrFixedProductionTemplate.
Import
  PABoundedRawCodedDynamicTruthSigmaOrFixedProductionAppendIntegration.

(** Small constructor-local derived rules avoid unfolding an already
    verified child proof tree while validating its new parent node. *)
Lemma templateRawDerives_andI_local : forall
    context left right leftChild rightChild,
  TemplateRawDerives context left leftChild ->
  TemplateRawDerives context right rightChild ->
  TemplateRawDerives context (tfAnd left right)
    (trpAndI context left right leftChild rightChild).
Proof.
  intros context left right leftChild rightChild
    [hleftValid [hleftContext hleftConclusion]]
    [hrightValid [hrightContext hrightConclusion]].
  unfold TemplateRawDerives.
  cbn [TemplateRawProofValid templateRawContext templateRawConclusion].
  repeat split; assumption.
Qed.

Lemma templateRawDerives_orI1_local : forall
    context left right child,
  TemplateRawDerives context left child ->
  TemplateRawDerives context (tfOr left right)
    (trpOrI1 context left right child).
Proof.
  intros context left right child
    [hvalid [hcontext hconclusion]].
  unfold TemplateRawDerives.
  cbn [TemplateRawProofValid templateRawContext templateRawConclusion].
  repeat split; assumption.
Qed.

(** Decompose an instantiated implication leaf without restating its large
    constructor-code and state-membership atoms. *)
Definition coqDynamicTruthSigmaImpOpenedLeafAt
    (leaf : TemplateFormula)
    witness7 witness6 witness5 witness4
    witness3 witness2 witness1 witness0 : TemplateFormula :=
  coqDynamicTruthSigmaOrInstantiateLeafAt
    witness7 witness6 witness5 witness4
    witness3 witness2 witness1 witness0 leaf.

Definition coqDynamicTruthSigmaImpOpenedCodeAt
    (leaf : TemplateFormula)
    witness7 witness6 witness5 witness4
    witness3 witness2 witness1 witness0 : TemplateFormula :=
  match coqDynamicTruthSigmaImpOpenedLeafAt leaf
      witness7 witness6 witness5 witness4
      witness3 witness2 witness1 witness0 with
  | tfAnd code _ => code
  | _ => tfBot
  end.

Definition coqDynamicTruthSigmaImpOpenedStateAt
    (leaf : TemplateFormula)
    witness7 witness6 witness5 witness4
    witness3 witness2 witness1 witness0 : TemplateFormula :=
  match coqDynamicTruthSigmaImpOpenedLeafAt leaf
      witness7 witness6 witness5 witness4
      witness3 witness2 witness1 witness0 with
  | tfAnd _ (tfAnd state _) => state
  | _ => tfBot
  end.

Definition coqDynamicTruthSigmaImpExpectedOpenedLeafAt
    (leaf : TemplateFormula)
    witness7 witness6 witness5 witness4
    witness3 witness2 witness1 witness0 : TemplateFormula :=
  tfAnd
    (coqDynamicTruthSigmaImpOpenedCodeAt leaf
      witness7 witness6 witness5 witness4
      witness3 witness2 witness1 witness0)
    (tfAnd
      (coqDynamicTruthSigmaImpOpenedStateAt leaf
        witness7 witness6 witness5 witness4
        witness3 witness2 witness1 witness0)
      (tfEq witness0 witness0)).

(** Minimal context for either positive implication leaf.  Its order agrees
    with the established four-root Sigma/Or compiler. *)
Definition coqDynamicTruthSigmaImpFixedProductionContextAt
    (leaf : TemplateFormula)
    witness7 witness6 witness5 witness4
    witness3 witness2 witness1 witness0 : TemplateContext :=
  [coqDynamicTruthSigmaImpOpenedStateAt leaf
      witness7 witness6 witness5 witness4
      witness3 witness2 witness1 witness0;
   coqDynamicTruthSigmaImpOpenedCodeAt leaf
      witness7 witness6 witness5 witness4
      witness3 witness2 witness1 witness0;
   coqDynamicTruthSigmaOrOpenedDomainAt
      witness7 witness6 witness5 witness4
      witness3 witness2 witness1 witness0;
   coqDynamicTruthSigmaOrModeZeroTemplate].

Definition coqDynamicTruthSigmaImpFixedProductionContextOnTailAt
    (leaf : TemplateFormula)
    witness7 witness6 witness5 witness4
    witness3 witness2 witness1 witness0
    (tail : TemplateContext) : TemplateContext :=
  coqDynamicTruthSigmaImpFixedProductionContextAt leaf
    witness7 witness6 witness5 witness4
    witness3 witness2 witness1 witness0 ++ tail.

(** The final equality conjunct is the spare witness equality in both
    implication leaves, hence is proved by Eq-refl rather than assumed. *)
Definition coqDynamicTruthSigmaImpOpenedLeafProofOnTailAt
    (leaf : TemplateFormula)
    witness7 witness6 witness5 witness4
    witness3 witness2 witness1 witness0 tail : TemplateRawProof :=
  let context := coqDynamicTruthSigmaImpFixedProductionContextOnTailAt leaf
    witness7 witness6 witness5 witness4
    witness3 witness2 witness1 witness0 tail in
  let code := coqDynamicTruthSigmaImpOpenedCodeAt leaf
    witness7 witness6 witness5 witness4
    witness3 witness2 witness1 witness0 in
  let state := coqDynamicTruthSigmaImpOpenedStateAt leaf
    witness7 witness6 witness5 witness4
    witness3 witness2 witness1 witness0 in
  trpAndI context code (tfAnd state (tfEq witness0 witness0))
    (trpAss context code)
    (trpAndI context state (tfEq witness0 witness0)
      (trpAss context state)
      (trpEqRefl context witness0)).

Definition coqDynamicTruthSigmaImpOpenedBranchesProofOnTailAt
    (leaf : TemplateFormula) (selectedIndex : nat)
    witness7 witness6 witness5 witness4
    witness3 witness2 witness1 witness0 tail : TemplateRawProof :=
  let context := coqDynamicTruthSigmaImpFixedProductionContextOnTailAt leaf
    witness7 witness6 witness5 witness4
    witness3 witness2 witness1 witness0 tail in
  templateRightDisjunctionIntroductionAt context
    (coqDynamicTruthSigmaOrOpenedBranchPrefixAt
      witness7 witness6 witness5 witness4
      witness3 witness2 witness1 witness0)
    (coqDynamicTruthSigmaOrOpenedUniversalAt
      witness7 witness6 witness5 witness4
      witness3 witness2 witness1 witness0)
    selectedIndex
    (coqDynamicTruthSigmaImpOpenedLeafProofOnTailAt leaf
      witness7 witness6 witness5 witness4
      witness3 witness2 witness1 witness0 tail).

Definition coqDynamicTruthSigmaImpOpenedRowBodyProofOnTailAt
    (leaf : TemplateFormula) (selectedIndex : nat)
    witness7 witness6 witness5 witness4
    witness3 witness2 witness1 witness0 tail : TemplateRawProof :=
  let context := coqDynamicTruthSigmaImpFixedProductionContextOnTailAt leaf
    witness7 witness6 witness5 witness4
    witness3 witness2 witness1 witness0 tail in
  trpAndI context
    (coqDynamicTruthSigmaOrOpenedDomainAt
      witness7 witness6 witness5 witness4
      witness3 witness2 witness1 witness0)
    (coqDynamicTruthSigmaOrOpenedBranchesAt
      witness7 witness6 witness5 witness4
      witness3 witness2 witness1 witness0)
    (trpAss context
      (coqDynamicTruthSigmaOrOpenedDomainAt
        witness7 witness6 witness5 witness4
        witness3 witness2 witness1 witness0))
    (coqDynamicTruthSigmaImpOpenedBranchesProofOnTailAt leaf selectedIndex
      witness7 witness6 witness5 witness4
      witness3 witness2 witness1 witness0 tail).

Definition coqDynamicTruthSigmaImpSuccessorRowProofOnTailAt
    (leaf : TemplateFormula) (selectedIndex : nat)
    witness7 witness6 witness5 witness4
    witness3 witness2 witness1 witness0 tail : TemplateRawProof :=
  let context := coqDynamicTruthSigmaImpFixedProductionContextOnTailAt leaf
    witness7 witness6 witness5 witness4
    witness3 witness2 witness1 witness0 tail in
  templateExistentialWitnessIntroductionFrom context
    (coqDynamicTruthSigmaOrWitnessesAt
      witness7 witness6 witness5 witness4
      witness3 witness2 witness1 witness0)
    coqDynamicTruthSharedSigmaSuccessorRowTemplate
    (coqDynamicTruthSigmaImpOpenedRowBodyProofOnTailAt leaf selectedIndex
      witness7 witness6 witness5 witness4
      witness3 witness2 witness1 witness0 tail).

Definition coqDynamicTruthSigmaImpFixedProductionProofOnTailAt
    (leaf : TemplateFormula) (selectedIndex : nat)
    witness7 witness6 witness5 witness4
    witness3 witness2 witness1 witness0 tail : TemplateRawProof :=
  let context := coqDynamicTruthSigmaImpFixedProductionContextOnTailAt leaf
    witness7 witness6 witness5 witness4
    witness3 witness2 witness1 witness0 tail in
  let sigmaCase := tfAnd coqDynamicTruthSigmaOrModeZeroTemplate
    coqDynamicTruthSharedSigmaSuccessorRowTemplate in
  let piCase := tfAnd coqDynamicTruthSigmaOrModeOneTemplate
    coqDynamicTruthSharedPiSuccessorRowTemplate in
  trpOrI1 context sigmaCase piCase
    (trpAndI context coqDynamicTruthSigmaOrModeZeroTemplate
      coqDynamicTruthSharedSigmaSuccessorRowTemplate
      (trpAss context coqDynamicTruthSigmaOrModeZeroTemplate)
      (coqDynamicTruthSigmaImpSuccessorRowProofOnTailAt leaf selectedIndex
        witness7 witness6 witness5 witness4
        witness3 witness2 witness1 witness0 tail)).

Theorem coqDynamicTruthSigmaImpOpenedLeafProofOnTailAt_derives : forall
    leaf witness7 witness6 witness5 witness4
    witness3 witness2 witness1 witness0 tail,
  coqDynamicTruthSigmaImpOpenedLeafAt leaf
      witness7 witness6 witness5 witness4
      witness3 witness2 witness1 witness0 =
    coqDynamicTruthSigmaImpExpectedOpenedLeafAt leaf
      witness7 witness6 witness5 witness4
      witness3 witness2 witness1 witness0 ->
  TemplateRawDerives
    (coqDynamicTruthSigmaImpFixedProductionContextOnTailAt leaf
      witness7 witness6 witness5 witness4
      witness3 witness2 witness1 witness0 tail)
    (coqDynamicTruthSigmaImpOpenedLeafAt leaf
      witness7 witness6 witness5 witness4
      witness3 witness2 witness1 witness0)
    (coqDynamicTruthSigmaImpOpenedLeafProofOnTailAt leaf
      witness7 witness6 witness5 witness4
      witness3 witness2 witness1 witness0 tail).
Proof.
  intros leaf witness7 witness6 witness5 witness4
    witness3 witness2 witness1 witness0 tail hshape.
  rewrite hshape.
  unfold coqDynamicTruthSigmaImpExpectedOpenedLeafAt,
    coqDynamicTruthSigmaImpOpenedLeafProofOnTailAt,
    TemplateRawDerives.
  cbn [TemplateRawProofValid templateRawContext templateRawConclusion
    coqDynamicTruthSigmaImpFixedProductionContextOnTailAt
    coqDynamicTruthSigmaImpFixedProductionContextAt List.app].
  repeat split; auto.
  right. left. reflexivity.
  left. reflexivity.
Qed.

Theorem coqDynamicTruthSigmaImpOpenedBranchesProofOnTailAt_derives : forall
    leaf selectedIndex witness7 witness6 witness5 witness4
    witness3 witness2 witness1 witness0 tail,
  coqDynamicTruthSigmaImpOpenedLeafAt leaf
      witness7 witness6 witness5 witness4
      witness3 witness2 witness1 witness0 =
    coqDynamicTruthSigmaImpExpectedOpenedLeafAt leaf
      witness7 witness6 witness5 witness4
      witness3 witness2 witness1 witness0 ->
  templateRightDisjunctionBranchAt
    (coqDynamicTruthSigmaOrOpenedBranchPrefixAt
      witness7 witness6 witness5 witness4
      witness3 witness2 witness1 witness0)
    (coqDynamicTruthSigmaOrOpenedUniversalAt
      witness7 witness6 witness5 witness4
      witness3 witness2 witness1 witness0)
    selectedIndex =
    Some (coqDynamicTruthSigmaImpOpenedLeafAt leaf
      witness7 witness6 witness5 witness4
      witness3 witness2 witness1 witness0) ->
  TemplateRawDerives
    (coqDynamicTruthSigmaImpFixedProductionContextOnTailAt leaf
      witness7 witness6 witness5 witness4
      witness3 witness2 witness1 witness0 tail)
    (coqDynamicTruthSigmaOrOpenedBranchesAt
      witness7 witness6 witness5 witness4
      witness3 witness2 witness1 witness0)
    (coqDynamicTruthSigmaImpOpenedBranchesProofOnTailAt leaf selectedIndex
      witness7 witness6 witness5 witness4
      witness3 witness2 witness1 witness0 tail).
Proof.
  intros leaf selectedIndex witness7 witness6 witness5 witness4
    witness3 witness2 witness1 witness0 tail hshape hnth.
  unfold coqDynamicTruthSigmaImpOpenedBranchesProofOnTailAt,
    coqDynamicTruthSigmaOrOpenedBranchesAt.
  eapply templateRightDisjunctionIntroductionAt_derives.
  - exact hnth.
  - exact (coqDynamicTruthSigmaImpOpenedLeafProofOnTailAt_derives
      leaf witness7 witness6 witness5 witness4
      witness3 witness2 witness1 witness0 tail hshape).
Qed.

Theorem coqDynamicTruthSigmaImpOpenedRowBodyProofOnTailAt_derives : forall
    leaf selectedIndex witness7 witness6 witness5 witness4
    witness3 witness2 witness1 witness0 tail,
  coqDynamicTruthSigmaImpOpenedLeafAt leaf
      witness7 witness6 witness5 witness4
      witness3 witness2 witness1 witness0 =
    coqDynamicTruthSigmaImpExpectedOpenedLeafAt leaf
      witness7 witness6 witness5 witness4
      witness3 witness2 witness1 witness0 ->
  templateRightDisjunctionBranchAt
    (coqDynamicTruthSigmaOrOpenedBranchPrefixAt
      witness7 witness6 witness5 witness4
      witness3 witness2 witness1 witness0)
    (coqDynamicTruthSigmaOrOpenedUniversalAt
      witness7 witness6 witness5 witness4
      witness3 witness2 witness1 witness0)
    selectedIndex =
    Some (coqDynamicTruthSigmaImpOpenedLeafAt leaf
      witness7 witness6 witness5 witness4
      witness3 witness2 witness1 witness0) ->
  TemplateRawDerives
    (coqDynamicTruthSigmaImpFixedProductionContextOnTailAt leaf
      witness7 witness6 witness5 witness4
      witness3 witness2 witness1 witness0 tail)
    (coqDynamicTruthSigmaOrOpenedRowBodyAt
      witness7 witness6 witness5 witness4
      witness3 witness2 witness1 witness0)
    (coqDynamicTruthSigmaImpOpenedRowBodyProofOnTailAt leaf selectedIndex
      witness7 witness6 witness5 witness4
      witness3 witness2 witness1 witness0 tail).
Proof.
  intros leaf selectedIndex witness7 witness6 witness5 witness4
    witness3 witness2 witness1 witness0 tail hshape hnth.
  pose proof
    (coqDynamicTruthSigmaImpOpenedBranchesProofOnTailAt_derives
      leaf selectedIndex witness7 witness6 witness5 witness4
      witness3 witness2 witness1 witness0 tail hshape hnth) as hbranches.
  destruct hbranches as [hvalid [hcontext hconclusion]].
  unfold coqDynamicTruthSigmaImpOpenedRowBodyProofOnTailAt,
    coqDynamicTruthSigmaOrOpenedRowBodyAt, TemplateRawDerives.
  cbn [TemplateRawProofValid templateRawContext templateRawConclusion
    coqDynamicTruthSigmaImpFixedProductionContextOnTailAt
    coqDynamicTruthSigmaImpFixedProductionContextAt List.app].
  repeat split; try assumption; auto.
  right. right. left. reflexivity.
Qed.

Theorem coqDynamicTruthSigmaImpSuccessorRowProofOnTailAt_derives : forall
    leaf selectedIndex witness7 witness6 witness5 witness4
    witness3 witness2 witness1 witness0 tail,
  coqDynamicTruthSigmaImpOpenedLeafAt leaf
      witness7 witness6 witness5 witness4
      witness3 witness2 witness1 witness0 =
    coqDynamicTruthSigmaImpExpectedOpenedLeafAt leaf
      witness7 witness6 witness5 witness4
      witness3 witness2 witness1 witness0 ->
  templateRightDisjunctionBranchAt
    (coqDynamicTruthSigmaOrOpenedBranchPrefixAt
      witness7 witness6 witness5 witness4
      witness3 witness2 witness1 witness0)
    (coqDynamicTruthSigmaOrOpenedUniversalAt
      witness7 witness6 witness5 witness4
      witness3 witness2 witness1 witness0)
    selectedIndex =
    Some (coqDynamicTruthSigmaImpOpenedLeafAt leaf
      witness7 witness6 witness5 witness4
      witness3 witness2 witness1 witness0) ->
  TemplateRawDerives
    (coqDynamicTruthSigmaImpFixedProductionContextOnTailAt leaf
      witness7 witness6 witness5 witness4
      witness3 witness2 witness1 witness0 tail)
    coqDynamicTruthSharedSigmaSuccessorRowTemplate
    (coqDynamicTruthSigmaImpSuccessorRowProofOnTailAt leaf selectedIndex
      witness7 witness6 witness5 witness4
      witness3 witness2 witness1 witness0 tail).
Proof.
  intros leaf selectedIndex witness7 witness6 witness5 witness4
    witness3 witness2 witness1 witness0 tail hshape hnth.
  apply templateExistentialWitnessIntroductionFrom_derives.
  rewrite coqDynamicTruthSigmaOrOpenedRowBodyAt_exact.
  exact (coqDynamicTruthSigmaImpOpenedRowBodyProofOnTailAt_derives
    leaf selectedIndex witness7 witness6 witness5 witness4
    witness3 witness2 witness1 witness0 tail hshape hnth).
Qed.

Theorem coqDynamicTruthSigmaImpFixedProductionProofOnTailAt_derives : forall
    leaf selectedIndex witness7 witness6 witness5 witness4
    witness3 witness2 witness1 witness0 tail,
  coqDynamicTruthSigmaImpOpenedLeafAt leaf
      witness7 witness6 witness5 witness4
      witness3 witness2 witness1 witness0 =
    coqDynamicTruthSigmaImpExpectedOpenedLeafAt leaf
      witness7 witness6 witness5 witness4
      witness3 witness2 witness1 witness0 ->
  templateRightDisjunctionBranchAt
    (coqDynamicTruthSigmaOrOpenedBranchPrefixAt
      witness7 witness6 witness5 witness4
      witness3 witness2 witness1 witness0)
    (coqDynamicTruthSigmaOrOpenedUniversalAt
      witness7 witness6 witness5 witness4
      witness3 witness2 witness1 witness0)
    selectedIndex =
    Some (coqDynamicTruthSigmaImpOpenedLeafAt leaf
      witness7 witness6 witness5 witness4
      witness3 witness2 witness1 witness0) ->
  TemplateRawDerives
    (coqDynamicTruthSigmaImpFixedProductionContextOnTailAt leaf
      witness7 witness6 witness5 witness4
      witness3 witness2 witness1 witness0 tail)
    (coqFourStateTableAppendNamedClosedRowProductionTemplate
      coqDynamicTruthSharedSigmaSuccessorRowTemplate
      coqDynamicTruthSharedPiSuccessorRowTemplate)
    (coqDynamicTruthSigmaImpFixedProductionProofOnTailAt leaf selectedIndex
      witness7 witness6 witness5 witness4
      witness3 witness2 witness1 witness0 tail).
Proof.
  intros leaf selectedIndex witness7 witness6 witness5 witness4
    witness3 witness2 witness1 witness0 tail hshape hnth.
  set (context :=
    coqDynamicTruthSigmaImpFixedProductionContextOnTailAt leaf
      witness7 witness6 witness5 witness4
      witness3 witness2 witness1 witness0 tail).
  pose proof
    (coqDynamicTruthSigmaImpSuccessorRowProofOnTailAt_derives
      leaf selectedIndex witness7 witness6 witness5 witness4
      witness3 witness2 witness1 witness0 tail hshape hnth) as hsigma.
  assert (hmode : TemplateRawDerives context
      coqDynamicTruthSigmaOrModeZeroTemplate
      (trpAss context coqDynamicTruthSigmaOrModeZeroTemplate)).
  {
    apply templateRawDerives_assumption.
    unfold context,
      coqDynamicTruthSigmaImpFixedProductionContextOnTailAt,
      coqDynamicTruthSigmaImpFixedProductionContextAt.
    cbn [List.app]. right. right. right. left. reflexivity.
  }
  pose proof (templateRawDerives_andI_local context
    coqDynamicTruthSigmaOrModeZeroTemplate
    coqDynamicTruthSharedSigmaSuccessorRowTemplate
    (trpAss context coqDynamicTruthSigmaOrModeZeroTemplate)
    (coqDynamicTruthSigmaImpSuccessorRowProofOnTailAt leaf selectedIndex
      witness7 witness6 witness5 witness4
      witness3 witness2 witness1 witness0 tail)
    hmode hsigma) as hsigmaCase.
  pose proof (templateRawDerives_orI1_local context
    (tfAnd coqDynamicTruthSigmaOrModeZeroTemplate
      coqDynamicTruthSharedSigmaSuccessorRowTemplate)
    (tfAnd coqDynamicTruthSigmaOrModeOneTemplate
      coqDynamicTruthSharedPiSuccessorRowTemplate)
    (trpAndI context coqDynamicTruthSigmaOrModeZeroTemplate
      coqDynamicTruthSharedSigmaSuccessorRowTemplate
      (trpAss context coqDynamicTruthSigmaOrModeZeroTemplate)
      (coqDynamicTruthSigmaImpSuccessorRowProofOnTailAt leaf selectedIndex
        witness7 witness6 witness5 witness4
        witness3 witness2 witness1 witness0 tail))
    hsigmaCase) as hproduction.
  unfold coqFourStateTableAppendNamedClosedRowProductionTemplate
    in hproduction.
  change (TemplateRawDerives context
    (coqFourStateTableAppendNamedClosedRowProductionTemplate
      coqDynamicTruthSharedSigmaSuccessorRowTemplate
      coqDynamicTruthSharedPiSuccessorRowTemplate)
    (coqDynamicTruthSigmaImpFixedProductionProofOnTailAt leaf selectedIndex
      witness7 witness6 witness5 witness4
      witness3 witness2 witness1 witness0 tail)).
  exact hproduction.
Qed.

(** Curry the four assumptions so independently compiled roots can be
    applied without weakening them into the small source context. *)
Definition coqDynamicTruthSigmaImpFixedProductionCurriedFormulaAt
    (leaf : TemplateFormula)
    witness7 witness6 witness5 witness4
    witness3 witness2 witness1 witness0 : TemplateFormula :=
  tfImp coqDynamicTruthSigmaOrModeZeroTemplate
    (tfImp
      (coqDynamicTruthSigmaOrOpenedDomainAt
        witness7 witness6 witness5 witness4
        witness3 witness2 witness1 witness0)
      (tfImp
        (coqDynamicTruthSigmaImpOpenedCodeAt leaf
          witness7 witness6 witness5 witness4
          witness3 witness2 witness1 witness0)
        (tfImp
          (coqDynamicTruthSigmaImpOpenedStateAt leaf
            witness7 witness6 witness5 witness4
            witness3 witness2 witness1 witness0)
          (coqFourStateTableAppendNamedClosedRowProductionTemplate
            coqDynamicTruthSharedSigmaSuccessorRowTemplate
            coqDynamicTruthSharedPiSuccessorRowTemplate)))).

Definition coqDynamicTruthSigmaImpFixedProductionCurriedProofAt
    (leaf : TemplateFormula) (selectedIndex : nat)
    witness7 witness6 witness5 witness4
    witness3 witness2 witness1 witness0
    (tail : TemplateContext) : TemplateRawProof :=
  let mode := coqDynamicTruthSigmaOrModeZeroTemplate in
  let domain := coqDynamicTruthSigmaOrOpenedDomainAt
    witness7 witness6 witness5 witness4
    witness3 witness2 witness1 witness0 in
  let code := coqDynamicTruthSigmaImpOpenedCodeAt leaf
    witness7 witness6 witness5 witness4
    witness3 witness2 witness1 witness0 in
  let state := coqDynamicTruthSigmaImpOpenedStateAt leaf
    witness7 witness6 witness5 witness4
    witness3 witness2 witness1 witness0 in
  let conclusion := coqFourStateTableAppendNamedClosedRowProductionTemplate
    coqDynamicTruthSharedSigmaSuccessorRowTemplate
    coqDynamicTruthSharedPiSuccessorRowTemplate in
  trpImpI tail mode
    (tfImp domain (tfImp code (tfImp state conclusion)))
    (trpImpI (mode :: tail) domain
      (tfImp code (tfImp state conclusion))
      (trpImpI (domain :: mode :: tail) code
        (tfImp state conclusion)
        (trpImpI (code :: domain :: mode :: tail) state conclusion
          (coqDynamicTruthSigmaImpFixedProductionProofOnTailAt
            leaf selectedIndex
            witness7 witness6 witness5 witness4
            witness3 witness2 witness1 witness0 tail)))).

Theorem coqDynamicTruthSigmaImpFixedProductionCurriedProofAt_derives :
  forall leaf selectedIndex witness7 witness6 witness5 witness4
    witness3 witness2 witness1 witness0 tail,
  coqDynamicTruthSigmaImpOpenedLeafAt leaf
      witness7 witness6 witness5 witness4
      witness3 witness2 witness1 witness0 =
    coqDynamicTruthSigmaImpExpectedOpenedLeafAt leaf
      witness7 witness6 witness5 witness4
      witness3 witness2 witness1 witness0 ->
  templateRightDisjunctionBranchAt
    (coqDynamicTruthSigmaOrOpenedBranchPrefixAt
      witness7 witness6 witness5 witness4
      witness3 witness2 witness1 witness0)
    (coqDynamicTruthSigmaOrOpenedUniversalAt
      witness7 witness6 witness5 witness4
      witness3 witness2 witness1 witness0)
    selectedIndex =
    Some (coqDynamicTruthSigmaImpOpenedLeafAt leaf
      witness7 witness6 witness5 witness4
      witness3 witness2 witness1 witness0) ->
  TemplateRawDerives tail
    (coqDynamicTruthSigmaImpFixedProductionCurriedFormulaAt leaf
      witness7 witness6 witness5 witness4
      witness3 witness2 witness1 witness0)
    (coqDynamicTruthSigmaImpFixedProductionCurriedProofAt leaf selectedIndex
      witness7 witness6 witness5 witness4
      witness3 witness2 witness1 witness0 tail).
Proof.
  intros leaf selectedIndex witness7 witness6 witness5 witness4
    witness3 witness2 witness1 witness0 tail hshape hnth.
  unfold coqDynamicTruthSigmaImpFixedProductionCurriedProofAt,
    coqDynamicTruthSigmaImpFixedProductionCurriedFormulaAt.
  apply templateRawDerives_impI_local.
  apply templateRawDerives_impI_local.
  apply templateRawDerives_impI_local.
  apply templateRawDerives_impI_local.
  change (TemplateRawDerives
    (coqDynamicTruthSigmaImpFixedProductionContextOnTailAt leaf
      witness7 witness6 witness5 witness4
      witness3 witness2 witness1 witness0 tail)
    (coqFourStateTableAppendNamedClosedRowProductionTemplate
      coqDynamicTruthSharedSigmaSuccessorRowTemplate
      coqDynamicTruthSharedPiSuccessorRowTemplate)
    (coqDynamicTruthSigmaImpFixedProductionProofOnTailAt leaf selectedIndex
      witness7 witness6 witness5 witness4
      witness3 witness2 witness1 witness0 tail)).
  exact (coqDynamicTruthSigmaImpFixedProductionProofOnTailAt_derives
    leaf selectedIndex witness7 witness6 witness5 witness4
    witness3 witness2 witness1 witness0 tail hshape hnth).
Qed.

Theorem
    raw_codedPALocalProofOf_dynamic_truth_sigma_imp_fixed_production_of_four_roots :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M)
    witnessList baseContext tail leaf selectedIndex
    witness7 witness6 witness5 witness4
    witness3 witness2 witness1 witness0
    modeRoot domainRoot codeRoot stateRoot,
  coqDynamicTruthSigmaImpOpenedLeafAt leaf
      witness7 witness6 witness5 witness4
      witness3 witness2 witness1 witness0 =
    coqDynamicTruthSigmaImpExpectedOpenedLeafAt leaf
      witness7 witness6 witness5 witness4
      witness3 witness2 witness1 witness0 ->
  templateRightDisjunctionBranchAt
    (coqDynamicTruthSigmaOrOpenedBranchPrefixAt
      witness7 witness6 witness5 witness4
      witness3 witness2 witness1 witness0)
    (coqDynamicTruthSigmaOrOpenedUniversalAt
      witness7 witness6 witness5 witness4
      witness3 witness2 witness1 witness0)
    selectedIndex =
    Some (coqDynamicTruthSigmaImpOpenedLeafAt leaf
      witness7 witness6 witness5 witness4
      witness3 witness2 witness1 witness0) ->
  RawCodedPAAxiomWitnessContext M witnessList baseContext ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail translation baseContext tail)
    (rawTemplateFormula translation
      coqDynamicTruthSigmaOrModeZeroTemplate) modeRoot ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail translation baseContext tail)
    (rawTemplateFormula translation
      (coqDynamicTruthSigmaOrOpenedDomainAt
        witness7 witness6 witness5 witness4
        witness3 witness2 witness1 witness0)) domainRoot ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail translation baseContext tail)
    (rawTemplateFormula translation
      (coqDynamicTruthSigmaImpOpenedCodeAt leaf
        witness7 witness6 witness5 witness4
        witness3 witness2 witness1 witness0)) codeRoot ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail translation baseContext tail)
    (rawTemplateFormula translation
      (coqDynamicTruthSigmaImpOpenedStateAt leaf
        witness7 witness6 witness5 witness4
        witness3 witness2 witness1 witness0)) stateRoot ->
  exists fixedProductionRoot,
    RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation baseContext tail)
      (rawTemplateFormula translation
        (coqFourStateTableAppendNamedClosedRowProductionTemplate
          coqDynamicTruthSharedSigmaSuccessorRowTemplate
          coqDynamicTruthSharedPiSuccessorRowTemplate))
      fixedProductionRoot.
Proof.
  intros M hPA translation witnessList baseContext tail leaf selectedIndex
    witness7 witness6 witness5 witness4
    witness3 witness2 witness1 witness0
    modeRoot domainRoot codeRoot stateRoot hshape hnth
    hbase hmode hdomain hcode hstate.
  set (curriedProof :=
    coqDynamicTruthSigmaImpFixedProductionCurriedProofAt leaf selectedIndex
      witness7 witness6 witness5 witness4
      witness3 witness2 witness1 witness0 tail).
  pose proof
    (raw_templateProofOnPAAxiomContext_localProof
      M hPA translation witnessList baseContext curriedProof hbase
      (proj1
        (coqDynamicTruthSigmaImpFixedProductionCurriedProofAt_derives
          leaf selectedIndex witness7 witness6 witness5 witness4
          witness3 witness2 witness1 witness0 tail hshape hnth)))
    as hcurried.
  unfold curriedProof in hcurried.
  lazymatch type of hcurried with
  | RawCodedPALocalProofOf _ _ _ ?curriedRoot =>
      change (RawCodedPALocalProofOf M
        (rawTemplateContextCodeOnTail translation baseContext tail)
        (rawTemplateFormula translation
          (coqDynamicTruthSigmaImpFixedProductionCurriedFormulaAt leaf
            witness7 witness6 witness5 witness4
            witness3 witness2 witness1 witness0)) curriedRoot)
        in hcurried
  end.
  unfold coqDynamicTruthSigmaImpFixedProductionCurriedFormulaAt in hcurried.
  rewrite !rawTemplateFormula_imp in hcurried.
  pose proof
    (raw_codedPALocalProofOf_impE M hPA
      (rawTemplateContextCodeOnTail translation baseContext tail)
      (rawTemplateFormula translation
        coqDynamicTruthSigmaOrModeZeroTemplate)
      (rawFormulaImpCode M
        (rawTemplateFormula translation
          (coqDynamicTruthSigmaOrOpenedDomainAt
            witness7 witness6 witness5 witness4
            witness3 witness2 witness1 witness0))
        (rawFormulaImpCode M
          (rawTemplateFormula translation
            (coqDynamicTruthSigmaImpOpenedCodeAt leaf
              witness7 witness6 witness5 witness4
              witness3 witness2 witness1 witness0))
          (rawFormulaImpCode M
            (rawTemplateFormula translation
              (coqDynamicTruthSigmaImpOpenedStateAt leaf
                witness7 witness6 witness5 witness4
                witness3 witness2 witness1 witness0))
            (rawTemplateFormula translation
              (coqFourStateTableAppendNamedClosedRowProductionTemplate
                coqDynamicTruthSharedSigmaSuccessorRowTemplate
                coqDynamicTruthSharedPiSuccessorRowTemplate)))))
      _ modeRoot hcurried hmode) as hafterMode.
  lazymatch type of hafterMode with
  | RawCodedPALocalProofOf _ _ _ ?afterModeRoot =>
      destruct
        (raw_codedPALocalProofOf_impE3 M hPA
          (rawTemplateContextCodeOnTail translation baseContext tail)
          (rawTemplateFormula translation
            (coqDynamicTruthSigmaOrOpenedDomainAt
              witness7 witness6 witness5 witness4
              witness3 witness2 witness1 witness0))
          (rawTemplateFormula translation
            (coqDynamicTruthSigmaImpOpenedCodeAt leaf
              witness7 witness6 witness5 witness4
              witness3 witness2 witness1 witness0))
          (rawTemplateFormula translation
            (coqDynamicTruthSigmaImpOpenedStateAt leaf
              witness7 witness6 witness5 witness4
              witness3 witness2 witness1 witness0))
          (rawTemplateFormula translation
            (coqFourStateTableAppendNamedClosedRowProductionTemplate
              coqDynamicTruthSharedSigmaSuccessorRowTemplate
              coqDynamicTruthSharedPiSuccessorRowTemplate))
          afterModeRoot domainRoot codeRoot stateRoot
          hafterMode hdomain hcode hstate) as
        [fixedProductionRoot hfixed]
  end.
  exists fixedProductionRoot. exact hfixed.
Qed.

(** The two concrete leaves and their literal positions in the shared Sigma
    branch prefix. *)
Lemma coqDynamicTruthSigmaImpFalseLeftOpenedLeafAt_shape : forall
    witness7 witness6 witness5 witness4
    witness3 witness2 witness1 witness0,
  coqDynamicTruthSigmaImpOpenedLeafAt
      coqDynamicTruthSigmaImpFalseLeftLeafTemplate
      witness7 witness6 witness5 witness4
      witness3 witness2 witness1 witness0 =
    coqDynamicTruthSigmaImpExpectedOpenedLeafAt
      coqDynamicTruthSigmaImpFalseLeftLeafTemplate
      witness7 witness6 witness5 witness4
      witness3 witness2 witness1 witness0.
Proof. intros. reflexivity. Qed.

Lemma coqDynamicTruthSigmaImpFalseLeftOpenedLeafAt_nth : forall
    witness7 witness6 witness5 witness4
    witness3 witness2 witness1 witness0,
  templateRightDisjunctionBranchAt
    (coqDynamicTruthSigmaOrOpenedBranchPrefixAt
      witness7 witness6 witness5 witness4
      witness3 witness2 witness1 witness0)
    (coqDynamicTruthSigmaOrOpenedUniversalAt
      witness7 witness6 witness5 witness4
      witness3 witness2 witness1 witness0) 1 =
    Some (coqDynamicTruthSigmaImpOpenedLeafAt
      coqDynamicTruthSigmaImpFalseLeftLeafTemplate
      witness7 witness6 witness5 witness4
      witness3 witness2 witness1 witness0).
Proof. intros. reflexivity. Qed.

Lemma coqDynamicTruthSigmaImpTrueRightOpenedLeafAt_shape : forall
    witness7 witness6 witness5 witness4
    witness3 witness2 witness1 witness0,
  coqDynamicTruthSigmaImpOpenedLeafAt
      coqDynamicTruthSigmaImpTrueRightLeafTemplate
      witness7 witness6 witness5 witness4
      witness3 witness2 witness1 witness0 =
    coqDynamicTruthSigmaImpExpectedOpenedLeafAt
      coqDynamicTruthSigmaImpTrueRightLeafTemplate
      witness7 witness6 witness5 witness4
      witness3 witness2 witness1 witness0.
Proof. intros. reflexivity. Qed.

Lemma coqDynamicTruthSigmaImpTrueRightOpenedLeafAt_nth : forall
    witness7 witness6 witness5 witness4
    witness3 witness2 witness1 witness0,
  templateRightDisjunctionBranchAt
    (coqDynamicTruthSigmaOrOpenedBranchPrefixAt
      witness7 witness6 witness5 witness4
      witness3 witness2 witness1 witness0)
    (coqDynamicTruthSigmaOrOpenedUniversalAt
      witness7 witness6 witness5 witness4
      witness3 witness2 witness1 witness0) 2 =
    Some (coqDynamicTruthSigmaImpOpenedLeafAt
      coqDynamicTruthSigmaImpTrueRightLeafTemplate
      witness7 witness6 witness5 witness4
      witness3 witness2 witness1 witness0).
Proof. intros. reflexivity. Qed.

Corollary
    raw_codedPALocalProofOf_dynamic_truth_sigma_imp_false_left_fixed_production_of_four_roots :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M)
    witnessList baseContext tail
    witness7 witness6 witness5 witness4
    witness3 witness2 witness1 witness0
    modeRoot domainRoot codeRoot stateRoot,
  RawCodedPAAxiomWitnessContext M witnessList baseContext ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail translation baseContext tail)
    (rawTemplateFormula translation
      coqDynamicTruthSigmaOrModeZeroTemplate) modeRoot ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail translation baseContext tail)
    (rawTemplateFormula translation
      (coqDynamicTruthSigmaOrOpenedDomainAt
        witness7 witness6 witness5 witness4
        witness3 witness2 witness1 witness0)) domainRoot ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail translation baseContext tail)
    (rawTemplateFormula translation
      (coqDynamicTruthSigmaImpOpenedCodeAt
        coqDynamicTruthSigmaImpFalseLeftLeafTemplate
        witness7 witness6 witness5 witness4
        witness3 witness2 witness1 witness0)) codeRoot ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail translation baseContext tail)
    (rawTemplateFormula translation
      (coqDynamicTruthSigmaImpOpenedStateAt
        coqDynamicTruthSigmaImpFalseLeftLeafTemplate
        witness7 witness6 witness5 witness4
        witness3 witness2 witness1 witness0)) stateRoot ->
  exists fixedProductionRoot,
    RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation baseContext tail)
      (rawTemplateFormula translation
        (coqFourStateTableAppendNamedClosedRowProductionTemplate
          coqDynamicTruthSharedSigmaSuccessorRowTemplate
          coqDynamicTruthSharedPiSuccessorRowTemplate))
      fixedProductionRoot.
Proof.
  intros M hPA translation witnessList baseContext tail
    witness7 witness6 witness5 witness4
    witness3 witness2 witness1 witness0
    modeRoot domainRoot codeRoot stateRoot
    hbase hmode hdomain hcode hstate.
  exact
    (raw_codedPALocalProofOf_dynamic_truth_sigma_imp_fixed_production_of_four_roots
      M hPA translation witnessList baseContext tail
      coqDynamicTruthSigmaImpFalseLeftLeafTemplate 1
      witness7 witness6 witness5 witness4
      witness3 witness2 witness1 witness0
      modeRoot domainRoot codeRoot stateRoot
      (coqDynamicTruthSigmaImpFalseLeftOpenedLeafAt_shape
        witness7 witness6 witness5 witness4
        witness3 witness2 witness1 witness0)
      (coqDynamicTruthSigmaImpFalseLeftOpenedLeafAt_nth
        witness7 witness6 witness5 witness4
        witness3 witness2 witness1 witness0)
      hbase hmode hdomain hcode hstate).
Qed.

Corollary
    raw_codedPALocalProofOf_dynamic_truth_sigma_imp_true_right_fixed_production_of_four_roots :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M)
    witnessList baseContext tail
    witness7 witness6 witness5 witness4
    witness3 witness2 witness1 witness0
    modeRoot domainRoot codeRoot stateRoot,
  RawCodedPAAxiomWitnessContext M witnessList baseContext ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail translation baseContext tail)
    (rawTemplateFormula translation
      coqDynamicTruthSigmaOrModeZeroTemplate) modeRoot ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail translation baseContext tail)
    (rawTemplateFormula translation
      (coqDynamicTruthSigmaOrOpenedDomainAt
        witness7 witness6 witness5 witness4
        witness3 witness2 witness1 witness0)) domainRoot ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail translation baseContext tail)
    (rawTemplateFormula translation
      (coqDynamicTruthSigmaImpOpenedCodeAt
        coqDynamicTruthSigmaImpTrueRightLeafTemplate
        witness7 witness6 witness5 witness4
        witness3 witness2 witness1 witness0)) codeRoot ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail translation baseContext tail)
    (rawTemplateFormula translation
      (coqDynamicTruthSigmaImpOpenedStateAt
        coqDynamicTruthSigmaImpTrueRightLeafTemplate
        witness7 witness6 witness5 witness4
        witness3 witness2 witness1 witness0)) stateRoot ->
  exists fixedProductionRoot,
    RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation baseContext tail)
      (rawTemplateFormula translation
        (coqFourStateTableAppendNamedClosedRowProductionTemplate
          coqDynamicTruthSharedSigmaSuccessorRowTemplate
          coqDynamicTruthSharedPiSuccessorRowTemplate))
      fixedProductionRoot.
Proof.
  intros M hPA translation witnessList baseContext tail
    witness7 witness6 witness5 witness4
    witness3 witness2 witness1 witness0
    modeRoot domainRoot codeRoot stateRoot
    hbase hmode hdomain hcode hstate.
  exact
    (raw_codedPALocalProofOf_dynamic_truth_sigma_imp_fixed_production_of_four_roots
      M hPA translation witnessList baseContext tail
      coqDynamicTruthSigmaImpTrueRightLeafTemplate 2
      witness7 witness6 witness5 witness4
      witness3 witness2 witness1 witness0
      modeRoot domainRoot codeRoot stateRoot
      (coqDynamicTruthSigmaImpTrueRightOpenedLeafAt_shape
        witness7 witness6 witness5 witness4
        witness3 witness2 witness1 witness0)
      (coqDynamicTruthSigmaImpTrueRightOpenedLeafAt_nth
        witness7 witness6 witness5 witness4
        witness3 witness2 witness1 witness0)
      hbase hmode hdomain hcode hstate).
Qed.

End PABoundedRawCodedDynamicTruthSigmaImpFixedProductionCompilation.
