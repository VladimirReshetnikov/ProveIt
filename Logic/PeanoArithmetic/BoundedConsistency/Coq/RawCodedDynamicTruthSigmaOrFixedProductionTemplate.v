(**
  A pure proof template for the mode-zero Sigma/Or append production.

  The global-table append compiler eventually asks for the closed-row
  alternative

      (mode = 0 /\ SigmaRow) \/ (mode = 1 /\ PiRow).

  For an Or node, the Sigma row is obtained by choosing its eight local-row
  witnesses and selecting the fifth branch of the right-associated Sigma
  disjunction.  This file isolates that entirely logical construction.  In
  particular, it does not assume a pre-built fixed-production proof: its
  context contains only the mode-zero equality, the instantiated Sigma
  domain, the parent Or-code atom, and the selected left-child state atom.

  Witness opening is kept explicit.  That matters because the local-row
  formulas use all thirteen fields of the surrounding global-row
  environment, while their eight existential witnesses occupy de Bruijn
  slots seven through zero.
*)

From Stdlib Require Import List.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedTemplateSyntax
  RawCodedTemplateProjectionSchemas
  RawCodedTemplateDisjunctionCaseSchemas
  RawCodedTemplateProofCompiler
  RawCodedPALocalProofExistential
  RawCodedDynamicTruthUniversalLeafSourceTemplate
  RawCodedRestrictedPADerivationSoundnessExtendedDirectInputs
  RawCodedFourStateTableAppendRowLtSuccCases
  RawCodedDynamicTruthSuccessorRowsAppendNormalization.

Module PABoundedRawCodedDynamicTruthSigmaOrFixedProductionTemplate.

Import ListNotations.
Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateProjectionSchemas.
Import PABoundedRawCodedTemplateDisjunctionCaseSchemas.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedDynamicTruthUniversalLeafSourceTemplate.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessExtendedDirectInputs.
Import PABoundedRawCodedDynamicTruthSuccessorRowsAppendNormalization.
Import PABoundedRawCodedFourStateTableAppendRowLtSuccCases.

(** Open as many leading existential binders as the witness list permits.
    A non-existential target is left unchanged; this total spelling keeps the
    accompanying proof constructor useful as a small general schema. *)
Fixpoint templateExistentialWitnessOpeningMany
    (witnesses : list TemplateTerm) (target : TemplateFormula)
    : TemplateFormula :=
  match witnesses with
  | [] => target
  | witness :: remaining =>
      match target with
      | tfEx body =>
          templateExistentialWitnessOpeningMany remaining
            (templateFormulaOpen witness body)
      | _ => target
      end
  end.

(** Reintroduce the witnesses in the same outer-to-inner order used by
    [templateExistentialWitnessOpeningMany].  The source proof is the proof
    of the fully opened body and therefore appears only at the unique leaf. *)
Fixpoint templateExistentialWitnessIntroductionFrom
    (context : TemplateContext) (witnesses : list TemplateTerm)
    (target : TemplateFormula) (sourceProof : TemplateRawProof)
    : TemplateRawProof :=
  match witnesses with
  | [] => sourceProof
  | witness :: remaining =>
      match target with
      | tfEx body =>
          trpExI context body witness
            (templateExistentialWitnessIntroductionFrom context remaining
              (templateFormulaOpen witness body) sourceProof)
      | _ => sourceProof
      end
  end.

Theorem templateExistentialWitnessIntroductionFrom_derives : forall
    context witnesses target sourceProof,
  TemplateRawDerives context
    (templateExistentialWitnessOpeningMany witnesses target) sourceProof ->
  TemplateRawDerives context target
    (templateExistentialWitnessIntroductionFrom
      context witnesses target sourceProof).
Proof.
  intros context witnesses.
  revert context.
  induction witnesses as [|witness remaining ih];
    intros context target sourceProof hsource.
  - exact hsource.
  - destruct target;
      cbn [templateExistentialWitnessOpeningMany
        templateExistentialWitnessIntroductionFrom] in *;
      try exact hsource.
    pose proof (ih context _ sourceProof hsource) as hchild.
    destruct hchild as [hvalid [hcontext hconclusion]].
    unfold TemplateRawDerives.
    cbn [TemplateRawProofValid templateRawContext templateRawConclusion].
    repeat split; try assumption; reflexivity.
Qed.

(** The eight terms are named by their final slots in the opened local-row
    body.  Thus [witness7] chooses the left state index, [witness6] its
    formula, [witness5]/[witness4] choose the unused right state for this
    left-introduction proof, and slots three through zero are padding for the
    other Sigma constructors. *)
Definition coqDynamicTruthSigmaOrWitnessesAt
    (witness7 witness6 witness5 witness4
      witness3 witness2 witness1 witness0 : TemplateTerm)
    : list TemplateTerm :=
  [witness7; witness6; witness5; witness4;
   witness3; witness2; witness1; witness0].

(** Apply the same eight substitutions to an unquantified Sigma-row leaf.
    Wrapping the leaf in eight binders before opening makes the de Bruijn
    action literally identical to opening the complete successor row. *)
Definition coqDynamicTruthSigmaOrInstantiateLeafAt
    (witness7 witness6 witness5 witness4
      witness3 witness2 witness1 witness0 : TemplateTerm)
    (leaf : TemplateFormula) : TemplateFormula :=
  templateExistentialWitnessOpeningMany
    (coqDynamicTruthSigmaOrWitnessesAt
      witness7 witness6 witness5 witness4
      witness3 witness2 witness1 witness0)
    (templateRepeatedExists 8 leaf).

(** The three proper subformulas of the Sigma Or leaf.  Pattern matching is
    preferable to restating their large table-membership atoms, and the
    following shape theorem audits that no fallback branch is used. *)
Definition coqDynamicTruthSigmaOrCodeLeafTemplate : TemplateFormula :=
  match coqDynamicTruthSigmaOrLeafTemplate with
  | tfAnd formulaCode _ => formulaCode
  | _ => tfBot
  end.

Definition coqDynamicTruthSigmaOrLeftStateLeafTemplate : TemplateFormula :=
  match coqDynamicTruthSigmaOrLeafTemplate with
  | tfAnd _ (tfOr leftState _) => leftState
  | _ => tfBot
  end.

Definition coqDynamicTruthSigmaOrRightStateLeafTemplate : TemplateFormula :=
  match coqDynamicTruthSigmaOrLeafTemplate with
  | tfAnd _ (tfOr _ rightState) => rightState
  | _ => tfBot
  end.

Lemma coqDynamicTruthSigmaOrLeafTemplate_shape :
  coqDynamicTruthSigmaOrLeafTemplate =
    tfAnd coqDynamicTruthSigmaOrCodeLeafTemplate
      (tfOr coqDynamicTruthSigmaOrLeftStateLeafTemplate
        coqDynamicTruthSigmaOrRightStateLeafTemplate).
Proof. reflexivity. Qed.

(** Instantiated leaves used by the source context and proof tree. *)
Definition coqDynamicTruthSigmaOrOpenedDomainAt
    witness7 witness6 witness5 witness4
    witness3 witness2 witness1 witness0 : TemplateFormula :=
  coqDynamicTruthSigmaOrInstantiateLeafAt
    witness7 witness6 witness5 witness4
    witness3 witness2 witness1 witness0
    coqDynamicTruthSigmaDomainLeafTemplate.

Definition coqDynamicTruthSigmaOrOpenedCodeAt
    witness7 witness6 witness5 witness4
    witness3 witness2 witness1 witness0 : TemplateFormula :=
  coqDynamicTruthSigmaOrInstantiateLeafAt
    witness7 witness6 witness5 witness4
    witness3 witness2 witness1 witness0
    coqDynamicTruthSigmaOrCodeLeafTemplate.

Definition coqDynamicTruthSigmaOrOpenedLeftStateAt
    witness7 witness6 witness5 witness4
    witness3 witness2 witness1 witness0 : TemplateFormula :=
  coqDynamicTruthSigmaOrInstantiateLeafAt
    witness7 witness6 witness5 witness4
    witness3 witness2 witness1 witness0
    coqDynamicTruthSigmaOrLeftStateLeafTemplate.

Definition coqDynamicTruthSigmaOrOpenedRightStateAt
    witness7 witness6 witness5 witness4
    witness3 witness2 witness1 witness0 : TemplateFormula :=
  coqDynamicTruthSigmaOrInstantiateLeafAt
    witness7 witness6 witness5 witness4
    witness3 witness2 witness1 witness0
    coqDynamicTruthSigmaOrRightStateLeafTemplate.

Definition coqDynamicTruthSigmaOrOpenedLeafAt
    witness7 witness6 witness5 witness4
    witness3 witness2 witness1 witness0 : TemplateFormula :=
  coqDynamicTruthSigmaOrInstantiateLeafAt
    witness7 witness6 witness5 witness4
    witness3 witness2 witness1 witness0
    coqDynamicTruthSigmaOrLeafTemplate.

(** The Sigma branch disjunction is represented by the generic
    right-associated schema.  The Or leaf has zero-based index four. *)
Definition coqDynamicTruthSigmaBranchPrefixTemplates
    : list TemplateFormula :=
  [coqDynamicTruthSigmaQfLeafTemplate;
   coqDynamicTruthSigmaImpFalseLeftLeafTemplate;
   coqDynamicTruthSigmaImpTrueRightLeafTemplate;
   coqDynamicTruthSigmaAndLeafTemplate;
   coqDynamicTruthSigmaOrLeafTemplate;
   coqDynamicTruthSigmaExLeafTemplate].

Definition coqDynamicTruthSigmaOrOpenedBranchPrefixAt
    witness7 witness6 witness5 witness4
    witness3 witness2 witness1 witness0 : list TemplateFormula :=
  map
    (coqDynamicTruthSigmaOrInstantiateLeafAt
      witness7 witness6 witness5 witness4
      witness3 witness2 witness1 witness0)
    coqDynamicTruthSigmaBranchPrefixTemplates.

Definition coqDynamicTruthSigmaOrOpenedUniversalAt
    witness7 witness6 witness5 witness4
    witness3 witness2 witness1 witness0 : TemplateFormula :=
  coqDynamicTruthSigmaOrInstantiateLeafAt
    witness7 witness6 witness5 witness4
    witness3 witness2 witness1 witness0
    (coqDynamicTruthSigmaUniversalLeafTemplateAt
      coqRestrictedPALowerPiTruthPredicateName).

Definition coqDynamicTruthSigmaOrOpenedBranchesAt
    witness7 witness6 witness5 witness4
    witness3 witness2 witness1 witness0 : TemplateFormula :=
  templateRightDisjunction
    (coqDynamicTruthSigmaOrOpenedBranchPrefixAt
      witness7 witness6 witness5 witness4
      witness3 witness2 witness1 witness0)
    (coqDynamicTruthSigmaOrOpenedUniversalAt
      witness7 witness6 witness5 witness4
      witness3 witness2 witness1 witness0).

Definition coqDynamicTruthSigmaOrOpenedRowBodyAt
    witness7 witness6 witness5 witness4
    witness3 witness2 witness1 witness0 : TemplateFormula :=
  tfAnd
    (coqDynamicTruthSigmaOrOpenedDomainAt
      witness7 witness6 witness5 witness4
      witness3 witness2 witness1 witness0)
    (coqDynamicTruthSigmaOrOpenedBranchesAt
      witness7 witness6 witness5 witness4
      witness3 witness2 witness1 witness0).

(** Computational audits tying the decomposed leaves back to the exact
    shared Sigma row consumed by append normalization. *)
Lemma coqDynamicTruthSigmaOrOpenedLeafAt_shape : forall
    witness7 witness6 witness5 witness4
    witness3 witness2 witness1 witness0,
  coqDynamicTruthSigmaOrOpenedLeafAt
      witness7 witness6 witness5 witness4
      witness3 witness2 witness1 witness0 =
    tfAnd
      (coqDynamicTruthSigmaOrOpenedCodeAt
        witness7 witness6 witness5 witness4
        witness3 witness2 witness1 witness0)
      (tfOr
        (coqDynamicTruthSigmaOrOpenedLeftStateAt
          witness7 witness6 witness5 witness4
          witness3 witness2 witness1 witness0)
        (coqDynamicTruthSigmaOrOpenedRightStateAt
          witness7 witness6 witness5 witness4
          witness3 witness2 witness1 witness0)).
Proof. intros. reflexivity. Qed.

Lemma coqDynamicTruthSigmaOrOpenedBranchesAt_exact : forall
    witness7 witness6 witness5 witness4
    witness3 witness2 witness1 witness0,
  coqDynamicTruthSigmaOrInstantiateLeafAt
      witness7 witness6 witness5 witness4
      witness3 witness2 witness1 witness0
      (coqDynamicTruthSigmaBranchesTemplateAt
        coqRestrictedPALowerPiTruthPredicateName) =
    coqDynamicTruthSigmaOrOpenedBranchesAt
      witness7 witness6 witness5 witness4
      witness3 witness2 witness1 witness0.
Proof. intros. reflexivity. Qed.

Lemma coqDynamicTruthSigmaOrOpenedRowBodyAt_exact : forall
    witness7 witness6 witness5 witness4
    witness3 witness2 witness1 witness0,
  templateExistentialWitnessOpeningMany
      (coqDynamicTruthSigmaOrWitnessesAt
        witness7 witness6 witness5 witness4
        witness3 witness2 witness1 witness0)
      coqDynamicTruthSharedSigmaSuccessorRowTemplate =
    coqDynamicTruthSigmaOrOpenedRowBodyAt
      witness7 witness6 witness5 witness4
      witness3 witness2 witness1 witness0.
Proof. intros. reflexivity. Qed.

Definition coqDynamicTruthSigmaOrModeZeroTemplate : TemplateFormula :=
  tfEq
    (ttParameter coqFourStateTableAppendRowModeParameterName) ttZero.

Definition coqDynamicTruthSigmaOrModeOneTemplate : TemplateFormula :=
  tfEq
    (ttParameter coqFourStateTableAppendRowModeParameterName)
    (ttSucc ttZero).

(** Minimal assumption context for the positive left-child construction. *)
Definition coqDynamicTruthSigmaOrFixedProductionContextAt
    witness7 witness6 witness5 witness4
    witness3 witness2 witness1 witness0 : TemplateContext :=
  [coqDynamicTruthSigmaOrOpenedLeftStateAt
      witness7 witness6 witness5 witness4
      witness3 witness2 witness1 witness0;
   coqDynamicTruthSigmaOrOpenedCodeAt
      witness7 witness6 witness5 witness4
      witness3 witness2 witness1 witness0;
   coqDynamicTruthSigmaOrOpenedDomainAt
      witness7 witness6 witness5 witness4
      witness3 witness2 witness1 witness0;
   coqDynamicTruthSigmaOrModeZeroTemplate].

Definition coqDynamicTruthSigmaOrOpenedLeafProofAt
    witness7 witness6 witness5 witness4
    witness3 witness2 witness1 witness0 : TemplateRawProof :=
  let context := coqDynamicTruthSigmaOrFixedProductionContextAt
    witness7 witness6 witness5 witness4
    witness3 witness2 witness1 witness0 in
  let formulaCode := coqDynamicTruthSigmaOrOpenedCodeAt
    witness7 witness6 witness5 witness4
    witness3 witness2 witness1 witness0 in
  let leftState := coqDynamicTruthSigmaOrOpenedLeftStateAt
    witness7 witness6 witness5 witness4
    witness3 witness2 witness1 witness0 in
  let rightState := coqDynamicTruthSigmaOrOpenedRightStateAt
    witness7 witness6 witness5 witness4
    witness3 witness2 witness1 witness0 in
  trpAndI context formulaCode (tfOr leftState rightState)
    (trpAss context formulaCode)
    (trpOrI1 context leftState rightState
      (trpAss context leftState)).

Definition coqDynamicTruthSigmaOrOpenedBranchesProofAt
    witness7 witness6 witness5 witness4
    witness3 witness2 witness1 witness0 : TemplateRawProof :=
  let context := coqDynamicTruthSigmaOrFixedProductionContextAt
    witness7 witness6 witness5 witness4
    witness3 witness2 witness1 witness0 in
  templateRightDisjunctionIntroductionAt context
    (coqDynamicTruthSigmaOrOpenedBranchPrefixAt
      witness7 witness6 witness5 witness4
      witness3 witness2 witness1 witness0)
    (coqDynamicTruthSigmaOrOpenedUniversalAt
      witness7 witness6 witness5 witness4
      witness3 witness2 witness1 witness0)
    4
    (coqDynamicTruthSigmaOrOpenedLeafProofAt
      witness7 witness6 witness5 witness4
      witness3 witness2 witness1 witness0).

Definition coqDynamicTruthSigmaOrOpenedRowBodyProofAt
    witness7 witness6 witness5 witness4
    witness3 witness2 witness1 witness0 : TemplateRawProof :=
  let context := coqDynamicTruthSigmaOrFixedProductionContextAt
    witness7 witness6 witness5 witness4
    witness3 witness2 witness1 witness0 in
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
    (coqDynamicTruthSigmaOrOpenedBranchesProofAt
      witness7 witness6 witness5 witness4
      witness3 witness2 witness1 witness0).

Definition coqDynamicTruthSigmaOrSuccessorRowProofAt
    witness7 witness6 witness5 witness4
    witness3 witness2 witness1 witness0 : TemplateRawProof :=
  let context := coqDynamicTruthSigmaOrFixedProductionContextAt
    witness7 witness6 witness5 witness4
    witness3 witness2 witness1 witness0 in
  templateExistentialWitnessIntroductionFrom context
    (coqDynamicTruthSigmaOrWitnessesAt
      witness7 witness6 witness5 witness4
      witness3 witness2 witness1 witness0)
    coqDynamicTruthSharedSigmaSuccessorRowTemplate
    (coqDynamicTruthSigmaOrOpenedRowBodyProofAt
      witness7 witness6 witness5 witness4
      witness3 witness2 witness1 witness0).

(** Final mode-zero injection into the exact append production. *)
Definition coqDynamicTruthSigmaOrFixedProductionProofAt
    witness7 witness6 witness5 witness4
    witness3 witness2 witness1 witness0 : TemplateRawProof :=
  let context := coqDynamicTruthSigmaOrFixedProductionContextAt
    witness7 witness6 witness5 witness4
    witness3 witness2 witness1 witness0 in
  let sigmaCase := tfAnd coqDynamicTruthSigmaOrModeZeroTemplate
    coqDynamicTruthSharedSigmaSuccessorRowTemplate in
  let piCase := tfAnd coqDynamicTruthSigmaOrModeOneTemplate
    coqDynamicTruthSharedPiSuccessorRowTemplate in
  trpOrI1 context sigmaCase piCase
    (trpAndI context coqDynamicTruthSigmaOrModeZeroTemplate
      coqDynamicTruthSharedSigmaSuccessorRowTemplate
      (trpAss context coqDynamicTruthSigmaOrModeZeroTemplate)
      (coqDynamicTruthSigmaOrSuccessorRowProofAt
        witness7 witness6 witness5 witness4
        witness3 witness2 witness1 witness0)).

Theorem coqDynamicTruthSigmaOrOpenedLeafProofAt_derives : forall
    witness7 witness6 witness5 witness4
    witness3 witness2 witness1 witness0,
  TemplateRawDerives
    (coqDynamicTruthSigmaOrFixedProductionContextAt
      witness7 witness6 witness5 witness4
      witness3 witness2 witness1 witness0)
    (coqDynamicTruthSigmaOrOpenedLeafAt
      witness7 witness6 witness5 witness4
      witness3 witness2 witness1 witness0)
    (coqDynamicTruthSigmaOrOpenedLeafProofAt
      witness7 witness6 witness5 witness4
      witness3 witness2 witness1 witness0).
Proof.
  intros.
  rewrite coqDynamicTruthSigmaOrOpenedLeafAt_shape.
  unfold coqDynamicTruthSigmaOrOpenedLeafProofAt, TemplateRawDerives.
  cbn [TemplateRawProofValid templateRawContext templateRawConclusion
    coqDynamicTruthSigmaOrFixedProductionContextAt].
  repeat split; auto.
Qed.

Theorem coqDynamicTruthSigmaOrOpenedBranchesProofAt_derives : forall
    witness7 witness6 witness5 witness4
    witness3 witness2 witness1 witness0,
  TemplateRawDerives
    (coqDynamicTruthSigmaOrFixedProductionContextAt
      witness7 witness6 witness5 witness4
      witness3 witness2 witness1 witness0)
    (coqDynamicTruthSigmaOrOpenedBranchesAt
      witness7 witness6 witness5 witness4
      witness3 witness2 witness1 witness0)
    (coqDynamicTruthSigmaOrOpenedBranchesProofAt
      witness7 witness6 witness5 witness4
      witness3 witness2 witness1 witness0).
Proof.
  intros.
  unfold coqDynamicTruthSigmaOrOpenedBranchesProofAt,
    coqDynamicTruthSigmaOrOpenedBranchesAt.
  eapply templateRightDisjunctionIntroductionAt_derives.
  - reflexivity.
  - apply coqDynamicTruthSigmaOrOpenedLeafProofAt_derives.
Qed.

Theorem coqDynamicTruthSigmaOrOpenedRowBodyProofAt_derives : forall
    witness7 witness6 witness5 witness4
    witness3 witness2 witness1 witness0,
  TemplateRawDerives
    (coqDynamicTruthSigmaOrFixedProductionContextAt
      witness7 witness6 witness5 witness4
      witness3 witness2 witness1 witness0)
    (coqDynamicTruthSigmaOrOpenedRowBodyAt
      witness7 witness6 witness5 witness4
      witness3 witness2 witness1 witness0)
    (coqDynamicTruthSigmaOrOpenedRowBodyProofAt
      witness7 witness6 witness5 witness4
      witness3 witness2 witness1 witness0).
Proof.
  intros.
  pose proof
    (coqDynamicTruthSigmaOrOpenedBranchesProofAt_derives
      witness7 witness6 witness5 witness4
      witness3 witness2 witness1 witness0) as hbranches.
  destruct hbranches as [hvalid [hcontext hconclusion]].
  unfold coqDynamicTruthSigmaOrOpenedRowBodyProofAt,
    coqDynamicTruthSigmaOrOpenedRowBodyAt, TemplateRawDerives.
  cbn [TemplateRawProofValid templateRawContext templateRawConclusion
    coqDynamicTruthSigmaOrFixedProductionContextAt].
  repeat split; try assumption; auto.
Qed.

Theorem coqDynamicTruthSigmaOrSuccessorRowProofAt_derives : forall
    witness7 witness6 witness5 witness4
    witness3 witness2 witness1 witness0,
  TemplateRawDerives
    (coqDynamicTruthSigmaOrFixedProductionContextAt
      witness7 witness6 witness5 witness4
      witness3 witness2 witness1 witness0)
    coqDynamicTruthSharedSigmaSuccessorRowTemplate
    (coqDynamicTruthSigmaOrSuccessorRowProofAt
      witness7 witness6 witness5 witness4
      witness3 witness2 witness1 witness0).
Proof.
  intros.
  apply templateExistentialWitnessIntroductionFrom_derives.
  rewrite coqDynamicTruthSigmaOrOpenedRowBodyAt_exact.
  apply coqDynamicTruthSigmaOrOpenedRowBodyProofAt_derives.
Qed.

Theorem coqDynamicTruthSigmaOrFixedProductionProofAt_derives : forall
    witness7 witness6 witness5 witness4
    witness3 witness2 witness1 witness0,
  TemplateRawDerives
    (coqDynamicTruthSigmaOrFixedProductionContextAt
      witness7 witness6 witness5 witness4
      witness3 witness2 witness1 witness0)
    (coqFourStateTableAppendNamedClosedRowProductionTemplate
      coqDynamicTruthSharedSigmaSuccessorRowTemplate
      coqDynamicTruthSharedPiSuccessorRowTemplate)
    (coqDynamicTruthSigmaOrFixedProductionProofAt
      witness7 witness6 witness5 witness4
      witness3 witness2 witness1 witness0).
Proof.
  intros.
  pose proof
    (coqDynamicTruthSigmaOrSuccessorRowProofAt_derives
      witness7 witness6 witness5 witness4
      witness3 witness2 witness1 witness0) as hsigma.
  destruct hsigma as [hvalid [hcontext hconclusion]].
  unfold coqDynamicTruthSigmaOrFixedProductionProofAt,
    coqFourStateTableAppendNamedClosedRowProductionTemplate,
    coqDynamicTruthSigmaOrModeZeroTemplate,
    coqDynamicTruthSigmaOrModeOneTemplate,
    TemplateRawDerives.
  cbn [TemplateRawProofValid templateRawContext templateRawConclusion
    coqDynamicTruthSigmaOrFixedProductionContextAt].
  repeat split; try assumption; auto.
Qed.

(** Coverage-certified compilation of the fixed finite proof tree. *)
Theorem raw_codedPALocalProofOf_dynamic_truth_sigma_or_fixed_production :
    forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M)
    witness7 witness6 witness5 witness4
    witness3 witness2 witness1 witness0,
  RawCodedPALocalProofOf M
    (rawTemplateContextCode translation
      (coqDynamicTruthSigmaOrFixedProductionContextAt
        witness7 witness6 witness5 witness4
        witness3 witness2 witness1 witness0))
    (rawTemplateFormula translation
      (coqFourStateTableAppendNamedClosedRowProductionTemplate
        coqDynamicTruthSharedSigmaSuccessorRowTemplate
        coqDynamicTruthSharedPiSuccessorRowTemplate))
    (rawTemplateProofCode translation
      (coqDynamicTruthSigmaOrFixedProductionProofAt
        witness7 witness6 witness5 witness4
        witness3 witness2 witness1 witness0)).
Proof.
  intros M hPA translation
    witness7 witness6 witness5 witness4
    witness3 witness2 witness1 witness0.
  apply raw_templateProof_localProof.
  exact (proj1
    (coqDynamicTruthSigmaOrFixedProductionProofAt_derives
      witness7 witness6 witness5 witness4
      witness3 witness2 witness1 witness0)).
Qed.

End PABoundedRawCodedDynamicTruthSigmaOrFixedProductionTemplate.
