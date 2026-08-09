(**
  Consume the Sigma/Or constructor case without identifying witnesses.

  The historical append-side consumer combined a domain atom opened with
  one tuple of eight variables with a constructor code atom obtained after
  opening a fresh existential tuple.  Those tuples are not definitionally
  interchangeable: in the honest constructor body the parent code occurs at
  [#10], while the historical pre-opened alias has parent [#2].

  This module keeps the data which must share witnesses in one source:

      Ex^8 (SigmaDomain /\ SigmaOrLeaf).

  After the eight eliminations, both conjuncts mention the same fresh
  eigenvariables.  The Or leaf can therefore be injected into the fifth
  branch of the Sigma disjunction, conjoined with the correlated domain, and
  closed again with exactly those eight witnesses.  No equality or transport
  between the honest [#10] code and the old [#2] code is used.
*)

From Stdlib Require Import List.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedProofBinaryConstructors
  RawCodedRestrictedPAProof
  RawCodedPALocalProofExistential
  RawCodedPALocalProofComposition
  RawCodedPAAxiomWitnessPrefix
  RawCodedTemplateSyntax
  RawCodedTemplateRenamingSubstitution
  RawCodedTemplateProjectionSchemas
  RawCodedTemplateProofCompiler
  RawCodedTemplateProofCompilerSelfShiftTail
  RawCodedTemplateDisjunctionCaseSchemas
  RawCodedRestrictedPADerivationSoundnessDirectRuleDispatchFrontier
  RawCodedRestrictedPADerivationSoundnessExtendedDirectInputs
  RawCodedTemplateNestedExistentialElimination
  RawCodedDynamicTruthUniversalLeafSourceTemplate
  RawCodedDynamicTruthSuccessorRowsAppendNormalization
  RawCodedDynamicTruthSigmaOrFixedProductionTemplate
  RawCodedDynamicTruthSigmaOrOpenedConstructorCodeProjection.

Module
  PABoundedRawCodedDynamicTruthSigmaOrCorrelatedConstructorConsumer.

Import ListNotations.
Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedProofBinaryConstructors.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPALocalProofComposition.
Import PABoundedRawCodedPAAxiomWitnessPrefix.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateRenamingSubstitution.
Import PABoundedRawCodedTemplateProjectionSchemas.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedTemplateProofCompilerSelfShiftTail.
Import PABoundedRawCodedTemplateDisjunctionCaseSchemas.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectRuleDispatchFrontier.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessExtendedDirectInputs.
Import PABoundedRawCodedTemplateNestedExistentialElimination.
Import PABoundedRawCodedDynamicTruthUniversalLeafSourceTemplate.
Import PABoundedRawCodedDynamicTruthSuccessorRowsAppendNormalization.
Import PABoundedRawCodedDynamicTruthSigmaOrFixedProductionTemplate.
Import
  PABoundedRawCodedDynamicTruthSigmaOrOpenedConstructorCodeProjection.

(** The constructor branch and its domain are deliberately placed beneath
    the same eight binders.  Splitting this into two unrelated existential
    sources would lose the witness correlation needed by the row proof. *)
Definition coqDynamicTruthSigmaOrCorrelatedConstructorBodyTemplate
    : TemplateFormula :=
  tfAnd coqDynamicTruthSigmaDomainLeafTemplate
    coqDynamicTruthSigmaOrLeafTemplate.

Definition coqDynamicTruthSigmaOrCorrelatedConstructorSourceTemplate
    : TemplateFormula :=
  rawCoqTemplateExN 8
    coqDynamicTruthSigmaOrCorrelatedConstructorBodyTemplate.

Lemma coqDynamicTruthSigmaOrCorrelatedConstructorSourceTemplate_exact :
  coqDynamicTruthSigmaOrCorrelatedConstructorSourceTemplate =
  templateRepeatedExists 8
    (tfAnd coqDynamicTruthSigmaDomainLeafTemplate
      coqDynamicTruthSigmaOrLeafTemplate).
Proof. reflexivity. Qed.

(** At the deepest constructor scope the code field is the honest [#10]
    atom exposed by the projection module. *)
Lemma coqDynamicTruthSigmaOrCorrelatedConstructorBody_code_shape :
  coqDynamicTruthSigmaOrCorrelatedConstructorBodyTemplate =
  tfAnd coqDynamicTruthSigmaDomainLeafTemplate
    (tfAnd coqDynamicTruthSigmaOrOpenedConstructorCodeRootTemplate
      (tfOr coqDynamicTruthSigmaOrLeftStateLeafTemplate
        coqDynamicTruthSigmaOrRightStateLeafTemplate)).
Proof.
  unfold coqDynamicTruthSigmaOrCorrelatedConstructorBodyTemplate,
    coqDynamicTruthSigmaOrOpenedConstructorCodeRootTemplate.
  now rewrite coqDynamicTruthSigmaOrLeafTemplate_shape.
Qed.

(** The eigenvariables are named by their actual de Bruijn slots in the
    deepest context. *)
Definition coqDynamicTruthSigmaOrHonestConstructorWitnesses
    : list TemplateTerm :=
  coqDynamicTruthSigmaOrWitnessesAt
    (ttVar 7) (ttVar 6) (ttVar 5) (ttVar 4)
    (ttVar 3) (ttVar 2) (ttVar 1) (ttVar 0).

(** The shared Sigma row uses the restricted lower-Pi opaque predicate in
    its universal branch; it is not the older default branch template. *)
Definition coqDynamicTruthSigmaOrSharedBranchesTemplate : TemplateFormula :=
  coqDynamicTruthSigmaBranchesTemplateAt
    coqRestrictedPALowerPiTruthPredicateName.

Lemma coqDynamicTruthSharedSigmaSuccessorRowTemplate_ex8_shape :
  coqDynamicTruthSharedSigmaSuccessorRowTemplate =
  rawCoqTemplateExN 8
    (tfAnd coqDynamicTruthSigmaDomainLeafTemplate
      coqDynamicTruthSigmaOrSharedBranchesTemplate).
Proof. reflexivity. Qed.

(** A syntax-generic cancellation lemma keeps the following audit small.
    Reducing the concrete Sigma formula here would create an enormous proof
    term; composing renamings and substitutions first shows pointwise that
    the eight shifts and the eight fresh openings cancel for every body. *)
Lemma coqDynamicTruthSigmaOr_open_fresh_after_rename8_ex8 :
  forall body,
  templateExistentialWitnessOpeningMany
    coqDynamicTruthSigmaOrHonestConstructorWitnesses
    (rawCoqTemplateRenameN 8 (rawCoqTemplateExN 8 body)) = body.
Proof.
  intro body.
  cbn [coqDynamicTruthSigmaOrHonestConstructorWitnesses
    coqDynamicTruthSigmaOrWitnessesAt rawCoqTemplateRenameN
    rawCoqTemplateExN templateExistentialWitnessOpeningMany
    templateFormulaOpen templateFormulaRename templateUpRenaming
    templateFormulaSubst templateTermUpSubst templateInstTerm].
  repeat rewrite templateFormulaRename_comp.
  repeat rewrite templateFormulaSubst_comp.
  rewrite templateFormulaSubst_rename.
  transitivity
    (templateFormulaSubst (fun index => ttVar index) body).
  - apply templateFormulaSubst_ext.
    intro index.
    do 8 (destruct index as [|index]; [reflexivity |]).
    reflexivity.
  - apply templateFormulaSubst_id.
Qed.

(** Eight Ex-E steps rename the eventual conclusion eight times.  Opening
    that renamed row with the fresh variables computes back to the literal
    unquantified Sigma body; ambient row variables remain correctly shifted. *)
Lemma coqDynamicTruthSigmaOrHonestConstructor_opened_renamed_row :
  templateExistentialWitnessOpeningMany
    coqDynamicTruthSigmaOrHonestConstructorWitnesses
    (rawCoqTemplateRenameN 8
      coqDynamicTruthSharedSigmaSuccessorRowTemplate) =
  tfAnd coqDynamicTruthSigmaDomainLeafTemplate
    coqDynamicTruthSigmaOrSharedBranchesTemplate.
Proof.
  rewrite coqDynamicTruthSharedSigmaSuccessorRowTemplate_ex8_shape.
  apply coqDynamicTruthSigmaOr_open_fresh_after_rename8_ex8.
Qed.

(** Exact deepest context produced by eliminating the correlated source.
    [tail] is arbitrary, so this proof can later sit inside the global Ex10
    eigencontext or any append-side temporary prefix. *)
Definition coqDynamicTruthSigmaOrCorrelatedConstructorDeepContextOn
    (tail : TemplateContext) : TemplateContext :=
  rawCoqTemplateNestedExContext 8
    coqDynamicTruthSigmaOrCorrelatedConstructorBodyTemplate tail.

Lemma coqDynamicTruthSigmaOrCorrelatedConstructorDeepContextOn_head :
  forall tail,
  exists rest,
    coqDynamicTruthSigmaOrCorrelatedConstructorDeepContextOn tail =
    coqDynamicTruthSigmaOrCorrelatedConstructorBodyTemplate :: rest.
Proof. intros. eexists. reflexivity. Qed.

(** Projection roots from the literal head assumption. *)
Definition coqDynamicTruthSigmaOrCorrelatedConstructorBodyAssumption
    (tail : TemplateContext) : TemplateRawProof :=
  trpAss (coqDynamicTruthSigmaOrCorrelatedConstructorDeepContextOn tail)
    coqDynamicTruthSigmaOrCorrelatedConstructorBodyTemplate.

Definition coqDynamicTruthSigmaOrCorrelatedDomainProof
    (tail : TemplateContext) : TemplateRawProof :=
  trpAndE1 (coqDynamicTruthSigmaOrCorrelatedConstructorDeepContextOn tail)
    coqDynamicTruthSigmaDomainLeafTemplate
    coqDynamicTruthSigmaOrLeafTemplate
    (coqDynamicTruthSigmaOrCorrelatedConstructorBodyAssumption tail).

Definition coqDynamicTruthSigmaOrCorrelatedLeafProof
    (tail : TemplateContext) : TemplateRawProof :=
  trpAndE2 (coqDynamicTruthSigmaOrCorrelatedConstructorDeepContextOn tail)
    coqDynamicTruthSigmaDomainLeafTemplate
    coqDynamicTruthSigmaOrLeafTemplate
    (coqDynamicTruthSigmaOrCorrelatedConstructorBodyAssumption tail).

Definition coqDynamicTruthSigmaOrCorrelatedBranchesProof
    (tail : TemplateContext) : TemplateRawProof :=
  templateRightDisjunctionIntroductionAt
    (coqDynamicTruthSigmaOrCorrelatedConstructorDeepContextOn tail)
    coqDynamicTruthSigmaBranchPrefixTemplates
    (coqDynamicTruthSigmaUniversalLeafTemplateAt
      coqRestrictedPALowerPiTruthPredicateName)
    4 (coqDynamicTruthSigmaOrCorrelatedLeafProof tail).

Definition coqDynamicTruthSigmaOrCorrelatedRowBodyProof
    (tail : TemplateContext) : TemplateRawProof :=
  trpAndI (coqDynamicTruthSigmaOrCorrelatedConstructorDeepContextOn tail)
    coqDynamicTruthSigmaDomainLeafTemplate
    coqDynamicTruthSigmaOrSharedBranchesTemplate
    (coqDynamicTruthSigmaOrCorrelatedDomainProof tail)
    (coqDynamicTruthSigmaOrCorrelatedBranchesProof tail).

Definition coqDynamicTruthSigmaOrCorrelatedRenamedRowProof
    (tail : TemplateContext) : TemplateRawProof :=
  templateExistentialWitnessIntroductionFrom
    (coqDynamicTruthSigmaOrCorrelatedConstructorDeepContextOn tail)
    coqDynamicTruthSigmaOrHonestConstructorWitnesses
    (rawCoqTemplateRenameN 8
      coqDynamicTruthSharedSigmaSuccessorRowTemplate)
    (coqDynamicTruthSigmaOrCorrelatedRowBodyProof tail).

Lemma coqDynamicTruthSigmaOrCorrelatedConstructorBodyAssumption_derives :
  forall tail,
  TemplateRawDerives
    (coqDynamicTruthSigmaOrCorrelatedConstructorDeepContextOn tail)
    coqDynamicTruthSigmaOrCorrelatedConstructorBodyTemplate
    (coqDynamicTruthSigmaOrCorrelatedConstructorBodyAssumption tail).
Proof.
  intro tail. apply templateRawDerives_assumption.
  destruct
    (coqDynamicTruthSigmaOrCorrelatedConstructorDeepContextOn_head tail)
    as [rest ->]. left. reflexivity.
Qed.

Lemma coqDynamicTruthSigmaOrCorrelatedDomainProof_derives : forall tail,
  TemplateRawDerives
    (coqDynamicTruthSigmaOrCorrelatedConstructorDeepContextOn tail)
    coqDynamicTruthSigmaDomainLeafTemplate
    (coqDynamicTruthSigmaOrCorrelatedDomainProof tail).
Proof.
  intro tail.
  destruct
    (coqDynamicTruthSigmaOrCorrelatedConstructorBodyAssumption_derives tail)
    as [hvalid [hcontext hconclusion]].
  unfold coqDynamicTruthSigmaOrCorrelatedDomainProof, TemplateRawDerives.
  cbn [TemplateRawProofValid templateRawContext templateRawConclusion].
  repeat split; assumption || reflexivity.
Qed.

Lemma coqDynamicTruthSigmaOrCorrelatedLeafProof_derives : forall tail,
  TemplateRawDerives
    (coqDynamicTruthSigmaOrCorrelatedConstructorDeepContextOn tail)
    coqDynamicTruthSigmaOrLeafTemplate
    (coqDynamicTruthSigmaOrCorrelatedLeafProof tail).
Proof.
  intro tail.
  destruct
    (coqDynamicTruthSigmaOrCorrelatedConstructorBodyAssumption_derives tail)
    as [hvalid [hcontext hconclusion]].
  unfold coqDynamicTruthSigmaOrCorrelatedLeafProof, TemplateRawDerives.
  cbn [TemplateRawProofValid templateRawContext templateRawConclusion].
  repeat split; assumption || reflexivity.
Qed.

Lemma coqDynamicTruthSigmaOrCorrelatedBranchesProof_derives : forall tail,
  TemplateRawDerives
    (coqDynamicTruthSigmaOrCorrelatedConstructorDeepContextOn tail)
    coqDynamicTruthSigmaOrSharedBranchesTemplate
    (coqDynamicTruthSigmaOrCorrelatedBranchesProof tail).
Proof.
  intro tail.
  unfold coqDynamicTruthSigmaOrCorrelatedBranchesProof,
    coqDynamicTruthSigmaOrSharedBranchesTemplate,
    coqDynamicTruthSigmaBranchesTemplateAt,
    coqDynamicTruthSigmaBranchPrefixTemplates.
  eapply templateRightDisjunctionIntroductionAt_derives.
  - reflexivity.
  - apply coqDynamicTruthSigmaOrCorrelatedLeafProof_derives.
Qed.

Lemma coqDynamicTruthSigmaOr_templateRawDerives_andI : forall
    context left right leftProof rightProof,
  TemplateRawDerives context left leftProof ->
  TemplateRawDerives context right rightProof ->
  TemplateRawDerives context (tfAnd left right)
    (trpAndI context left right leftProof rightProof).
Proof.
  intros context left right leftProof rightProof
    [hleftValid [hleftContext hleftConclusion]]
    [hrightValid [hrightContext hrightConclusion]].
  unfold TemplateRawDerives.
  cbn [TemplateRawProofValid templateRawContext templateRawConclusion].
  repeat split; assumption.
Qed.

Lemma coqDynamicTruthSigmaOrCorrelatedRowBodyProof_derives : forall tail,
  TemplateRawDerives
    (coqDynamicTruthSigmaOrCorrelatedConstructorDeepContextOn tail)
    (tfAnd coqDynamicTruthSigmaDomainLeafTemplate
      coqDynamicTruthSigmaOrSharedBranchesTemplate)
    (coqDynamicTruthSigmaOrCorrelatedRowBodyProof tail).
Proof.
  intro tail.
  unfold coqDynamicTruthSigmaOrCorrelatedRowBodyProof.
  apply coqDynamicTruthSigmaOr_templateRawDerives_andI.
  - apply coqDynamicTruthSigmaOrCorrelatedDomainProof_derives.
  - apply coqDynamicTruthSigmaOrCorrelatedBranchesProof_derives.
Qed.

Theorem coqDynamicTruthSigmaOrCorrelatedRenamedRowProof_derives :
  forall tail,
  TemplateRawDerives
    (coqDynamicTruthSigmaOrCorrelatedConstructorDeepContextOn tail)
    (rawCoqTemplateRenameN 8
      coqDynamicTruthSharedSigmaSuccessorRowTemplate)
    (coqDynamicTruthSigmaOrCorrelatedRenamedRowProof tail).
Proof.
  intro tail.
  apply templateExistentialWitnessIntroductionFrom_derives.
  rewrite coqDynamicTruthSigmaOrHonestConstructor_opened_renamed_row.
  apply coqDynamicTruthSigmaOrCorrelatedRowBodyProof_derives.
Qed.

(** Close the eight Ex-E nodes.  This theorem is the corrected pure
    consumer: its only source is the correlated constructor package. *)
Definition coqDynamicTruthSigmaOrCorrelatedConstructorRowProofOn
    (tail : TemplateContext) : TemplateRawProof :=
  rawCoqTemplateNestedExEliminationRoot 8
    coqDynamicTruthSigmaOrCorrelatedConstructorBodyTemplate
    coqDynamicTruthSharedSigmaSuccessorRowTemplate tail
    (coqDynamicTruthSigmaOrCorrelatedRenamedRowProof tail).

Theorem coqDynamicTruthSigmaOrCorrelatedConstructorRowProofOn_derives :
  forall tail,
  TemplateRawDerives
    (coqDynamicTruthSigmaOrCorrelatedConstructorSourceTemplate :: tail)
    coqDynamicTruthSharedSigmaSuccessorRowTemplate
    (coqDynamicTruthSigmaOrCorrelatedConstructorRowProofOn tail).
Proof.
  intro tail.
  unfold coqDynamicTruthSigmaOrCorrelatedConstructorSourceTemplate,
    coqDynamicTruthSigmaOrCorrelatedConstructorRowProofOn.
  apply rawCoqTemplateNestedExEliminationRoot_derives.
  apply coqDynamicTruthSigmaOrCorrelatedRenamedRowProof_derives.
Qed.

(** Curry the corrected source so an independently represented root can be
    consumed without making it a literal prefix member. *)
Definition coqDynamicTruthSigmaOrCorrelatedConstructorRowConsumerFormula
    : TemplateFormula :=
  tfImp coqDynamicTruthSigmaOrCorrelatedConstructorSourceTemplate
    coqDynamicTruthSharedSigmaSuccessorRowTemplate.

Definition coqDynamicTruthSigmaOrCorrelatedConstructorRowConsumerProof
    (tail : TemplateContext) : TemplateRawProof :=
  trpImpI tail coqDynamicTruthSigmaOrCorrelatedConstructorSourceTemplate
    coqDynamicTruthSharedSigmaSuccessorRowTemplate
    (coqDynamicTruthSigmaOrCorrelatedConstructorRowProofOn tail).

Lemma coqDynamicTruthSigmaOr_templateRawDerives_impI : forall
    context antecedent consequent child,
  TemplateRawDerives (antecedent :: context) consequent child ->
  TemplateRawDerives context (tfImp antecedent consequent)
    (trpImpI context antecedent consequent child).
Proof.
  intros context antecedent consequent child
    [hvalid [hcontext hconclusion]].
  unfold TemplateRawDerives.
  cbn [TemplateRawProofValid templateRawContext templateRawConclusion].
  repeat split; assumption || reflexivity.
Qed.

Theorem
    coqDynamicTruthSigmaOrCorrelatedConstructorRowConsumerProof_derives :
  forall tail,
  TemplateRawDerives tail
    coqDynamicTruthSigmaOrCorrelatedConstructorRowConsumerFormula
    (coqDynamicTruthSigmaOrCorrelatedConstructorRowConsumerProof tail).
Proof.
  intro tail.
  unfold coqDynamicTruthSigmaOrCorrelatedConstructorRowConsumerFormula,
    coqDynamicTruthSigmaOrCorrelatedConstructorRowConsumerProof.
  apply coqDynamicTruthSigmaOr_templateRawDerives_impI.
  apply coqDynamicTruthSigmaOrCorrelatedConstructorRowProofOn_derives.
Qed.

(** Represented handoff in an arbitrary template tail.  In particular,
    [tail] may be the deepest context obtained by opening the global Ex10
    traversal source; no formula-specific transport is required here. *)
Theorem
    raw_codedPALocalProofOf_dynamicTruthSigmaOr_correlatedConstructorRow_of_root :
  forall (M : RawPAModel) (hPA : RawPASatisfies M)
    (translation : RawCodedTemplateTranslation M)
    sourceWitnessList sourceContext tail sourceRoot,
  RawCodedPAAxiomWitnessContext M sourceWitnessList sourceContext ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail translation sourceContext tail)
    (rawTemplateFormula translation
      coqDynamicTruthSigmaOrCorrelatedConstructorSourceTemplate)
    sourceRoot ->
  exists rowRoot,
    RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation sourceContext tail)
      (rawTemplateFormula translation
        coqDynamicTruthSharedSigmaSuccessorRowTemplate) rowRoot.
Proof.
  intros M hPA translation sourceWitnessList sourceContext tail
    sourceRoot hwitnessed hsource.
  set (consumerProof :=
    coqDynamicTruthSigmaOrCorrelatedConstructorRowConsumerProof tail).
  pose proof
    (raw_templateProofOnPAAxiomContext_localProof
      M hPA translation sourceWitnessList sourceContext consumerProof
      hwitnessed
      (proj1
        (coqDynamicTruthSigmaOrCorrelatedConstructorRowConsumerProof_derives
          tail))) as hconsumer.
  unfold consumerProof in hconsumer.
  lazymatch type of hconsumer with
  | RawCodedPALocalProofOf _ _ _ ?consumerRoot =>
      change (RawCodedPALocalProofOf M
        (rawTemplateContextCodeOnTail translation sourceContext tail)
        (rawTemplateFormula translation
          coqDynamicTruthSigmaOrCorrelatedConstructorRowConsumerFormula)
        consumerRoot) in hconsumer
  end.
  unfold coqDynamicTruthSigmaOrCorrelatedConstructorRowConsumerFormula
    in hconsumer.
  rewrite rawTemplateFormula_imp in hconsumer.
  lazymatch type of hconsumer with
  | RawCodedPALocalProofOf _ _ _ ?consumerRoot =>
      exists
        (rawProofImpERoot M
          (rawTemplateContextCodeOnTail translation sourceContext tail)
          (rawTemplateFormula translation
            coqDynamicTruthSigmaOrCorrelatedConstructorSourceTemplate)
          (rawTemplateFormula translation
            coqDynamicTruthSharedSigmaSuccessorRowTemplate)
          consumerRoot sourceRoot);
      exact
        (raw_codedPALocalProofOf_impE M hPA
          (rawTemplateContextCodeOnTail translation sourceContext tail)
          (rawTemplateFormula translation
            coqDynamicTruthSigmaOrCorrelatedConstructorSourceTemplate)
          (rawTemplateFormula translation
            coqDynamicTruthSharedSigmaSuccessorRowTemplate)
          consumerRoot sourceRoot hconsumer hsource)
  end.
Qed.

End
  PABoundedRawCodedDynamicTruthSigmaOrCorrelatedConstructorConsumer.
