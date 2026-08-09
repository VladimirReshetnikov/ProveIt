(**
  Project the parent-code field from the honest Sigma/Or constructor branch.

  The constructor case does not directly provide an arbitrary opened code
  atom.  Its actual source is the eight-existential branch

      Ex^8 (FormulaOrCode(parent,left,right) /\ (leftState \/ rightState)).

  This module records both useful forms of its projection.  First, a fixed
  represented proof maps the branch source to [Ex^8 FormulaOrCode] without
  changing the mode-zero append context.  Second, after the same eight
  existential eliminations have introduced fresh eigenvariables, the branch
  body is the literal head assumption and [And-E1] produces its opened code
  atom.

  The latter atom uses parent slot [#10]: the five row variables and the
  pre-existing append witnesses have moved under eight *new* constructor
  witnesses.  This is intentionally contrasted with the historical guarded
  alias, which reuses the append witnesses and therefore has parent slot
  [#2].  The inequality theorem below is the precise integration boundary;
  no variable-identification assumption is smuggled into the projection.
*)

From Stdlib Require Import List.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors
  RawCodedContextLists
  RawCodedProofAssumptionLeaf
  RawCodedProofBinaryConstructors
  RawCodedRestrictedPAProof
  RawCodedPAAxiomWitnessPrefix
  RawCodedPALocalProofExistential
  RawCodedPALocalProofComposition
  RawCodedPALocalProofConjunction
  RawCodedPALocalProofExistentialEliminationChain
  RawCodedPALocalProofWitnessedContextMerge
  RawCodedTemplateSyntax
  RawCodedTemplateProjectionSchemas
  RawCodedTemplateProofCompiler
  RawCodedTemplateProofCompilerSelfShiftTail
  RawCodedTemplateLocalProofWitnessedTailTransport
  RawCodedTemplateDirectStructuralTranslation
  RawCodedFormulaBoundAllCarrierBoundary
  RawCodedDynamicTruthBooleanBranchExclusivity
  RawCodedDynamicTruthSigmaSuccessorRowGraph
  RawCodedDynamicTruthUniversalLeafSourceTemplate
  RawCodedDynamicTruthSigmaOrFixedProductionTemplate
  RawCodedDynamicTruthSigmaOrGuardedCanonicalConsumerIntegration
  RawCodedDynamicTruthSigmaOrGuardedCanonicalThreeRootCompilation.

Module
  PABoundedRawCodedDynamicTruthSigmaOrOpenedConstructorCodeProjection.

Import ListNotations.
Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedContextLists.
Import PABoundedRawCodedProofAssumptionLeaf.
Import PABoundedRawCodedProofBinaryConstructors.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedPAAxiomWitnessPrefix.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPALocalProofComposition.
Import PABoundedRawCodedPALocalProofConjunction.
Import PABoundedRawCodedPALocalProofExistentialEliminationChain.
Import PABoundedRawCodedPALocalProofWitnessedContextMerge.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateProjectionSchemas.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedTemplateProofCompilerSelfShiftTail.
Import PABoundedRawCodedTemplateLocalProofWitnessedTailTransport.
Import PABoundedRawCodedTemplateDirectStructuralTranslation.
Import PABoundedRawCodedFormulaBoundAllCarrierBoundary.
Import PABoundedRawCodedDynamicTruthBooleanBranchExclusivity.
Import PABoundedRawCodedDynamicTruthSigmaSuccessorRowGraph.
Import PABoundedRawCodedDynamicTruthUniversalLeafSourceTemplate.
Import PABoundedRawCodedDynamicTruthSigmaOrFixedProductionTemplate.
Import
  PABoundedRawCodedDynamicTruthSigmaOrGuardedCanonicalConsumerIntegration.
Import
  PABoundedRawCodedDynamicTruthSigmaOrGuardedCanonicalThreeRootCompilation.

(** Literal constructor source and its existentially retained code field. *)
Definition coqDynamicTruthSigmaOrConstructorBranchSourceTemplate
    : TemplateFormula :=
  templateRepeatedExists 8 coqDynamicTruthSigmaOrLeafTemplate.

Definition coqDynamicTruthSigmaOrConstructorCodeExistentialTemplate
    : TemplateFormula :=
  templateRepeatedExists 8 coqDynamicTruthSigmaOrCodeLeafTemplate.

Lemma coqDynamicTruthSigmaOrConstructorBranchSourceTemplate_exact :
  coqDynamicTruthSigmaOrConstructorBranchSourceTemplate =
  embedPAFormula dynamicTruthSigmaOrEx8BranchFormula.
Proof. reflexivity. Qed.

(** The pure logical projection retains all eight existential witnesses. *)
Definition coqDynamicTruthSigmaOrConstructorCodeProjectionFormula
    : TemplateFormula :=
  tfImp coqDynamicTruthSigmaOrConstructorBranchSourceTemplate
    coqDynamicTruthSigmaOrConstructorCodeExistentialTemplate.

Definition coqDynamicTruthSigmaOrConstructorCodeProjectionProof
    : TemplateRawProof :=
  templateRepeatedExistsSelectionProof 8
    [coqDynamicTruthSigmaOrCodeLeafTemplate]
    (tfOr coqDynamicTruthSigmaOrLeftStateLeafTemplate
      coqDynamicTruthSigmaOrRightStateLeafTemplate)
    [] 0.

Theorem coqDynamicTruthSigmaOrConstructorCodeProjectionProof_derives :
  TemplateRawDerives []
    coqDynamicTruthSigmaOrConstructorCodeProjectionFormula
    coqDynamicTruthSigmaOrConstructorCodeProjectionProof.
Proof.
  unfold coqDynamicTruthSigmaOrConstructorCodeProjectionFormula,
    coqDynamicTruthSigmaOrConstructorBranchSourceTemplate,
    coqDynamicTruthSigmaOrConstructorCodeExistentialTemplate,
    coqDynamicTruthSigmaOrConstructorCodeProjectionProof.
  rewrite coqDynamicTruthSigmaOrLeafTemplate_shape.
  apply templateRepeatedExistsSelectionProof_derives.
Qed.

(** Compile the fixed implication once, weaken it under the exact mode-zero
    prefix, and apply it to a represented constructor-branch source.  The
    output remains in the original prefix because all eigenvariables are
    kept existentially bound. *)
Theorem
    raw_codedPALocalProofOf_dynamicTruthSigmaOr_constructorCodeExistential_under_modeZeroRowPrefix :
  forall (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    sourceWitnessList sourceContext outerPrefix sourceRoot,
  RawCodedPAAxiomWitnessContext M sourceWitnessList sourceContext ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail
      (rawDirectStructuralTemplateTranslation M hPA inputs)
      sourceContext
      (coqDynamicTruthSigmaOrGuardedCanonicalModeZeroRowPrefix
        outerPrefix))
    (rawTemplateFormula
      (rawDirectStructuralTemplateTranslation M hPA inputs)
      coqDynamicTruthSigmaOrConstructorBranchSourceTemplate) sourceRoot ->
  exists codeRoot,
    RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        sourceContext
        (coqDynamicTruthSigmaOrGuardedCanonicalModeZeroRowPrefix
          outerPrefix))
      (rawTemplateFormula
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        coqDynamicTruthSigmaOrConstructorCodeExistentialTemplate) codeRoot.
Proof.
  intros M hPA inputs sourceWitnessList sourceContext outerPrefix
    sourceRoot hwitnessed hsource.
  set (translation :=
    rawDirectStructuralTemplateTranslation M hPA inputs).
  set (prefix :=
    coqDynamicTruthSigmaOrGuardedCanonicalModeZeroRowPrefix outerPrefix).

  destruct coqDynamicTruthSigmaOrConstructorCodeProjectionProof_derives as
    [hprojectionValid _].
  pose proof
    (raw_templateProofOnPAAxiomContext_localProof
      M hPA translation sourceWitnessList sourceContext
      coqDynamicTruthSigmaOrConstructorCodeProjectionProof
      hwitnessed hprojectionValid) as hprojectionBase.
  cbn [rawTemplateContextCodeOnTail] in hprojectionBase.

  destruct
    (raw_codedPALocalProof_templatePrefix
      M hPA translation sourceContext prefix
      (rawTemplateFormula translation
        coqDynamicTruthSigmaOrConstructorCodeProjectionFormula)
      (rawTemplateProofCodeOnTail translation sourceContext
        coqDynamicTruthSigmaOrConstructorCodeProjectionProof)
      (raw_codedPAAxiomWitnessContext_context_realizable
        M sourceWitnessList sourceContext hwitnessed)
      (fun formula _ =>
        rawDirectTemplateFormula_atomically_adequate
          M hPA inputs formula)
      hprojectionBase) as [projectionRoot hprojection].

  unfold coqDynamicTruthSigmaOrConstructorCodeProjectionFormula
    in hprojection.
  rewrite rawTemplateFormula_imp in hprojection.
  exists
    (rawProofImpERoot M
      (rawTemplateContextCodeOnTail translation sourceContext prefix)
      (rawTemplateFormula translation
        coqDynamicTruthSigmaOrConstructorBranchSourceTemplate)
      (rawTemplateFormula translation
        coqDynamicTruthSigmaOrConstructorCodeExistentialTemplate)
      projectionRoot sourceRoot).
  exact
    (raw_codedPALocalProofOf_impE M hPA
      (rawTemplateContextCodeOnTail translation sourceContext prefix)
      (rawTemplateFormula translation
        coqDynamicTruthSigmaOrConstructorBranchSourceTemplate)
      (rawTemplateFormula translation
        coqDynamicTruthSigmaOrConstructorCodeExistentialTemplate)
      projectionRoot sourceRoot hprojection hsource).
Qed.

(** Exact context after eliminating the constructor source's eight leading
    existential binders on top of the mode-zero append prefix. *)
Definition coqDynamicTruthSigmaOrOpenedConstructorContextUnderModeZeroAt
    (outerPrefix : TemplateContext) : TemplateContext :=
  match templateExistentialEliminationContext 8
    coqDynamicTruthSigmaOrConstructorBranchSourceTemplate
    (coqDynamicTruthSigmaOrGuardedCanonicalModeZeroRowPrefix outerPrefix)
  with
  | Some context => context
  | None => []
  end.

Lemma coqDynamicTruthSigmaOrOpenedConstructorContextUnderModeZeroAt_success :
  forall outerPrefix,
  templateExistentialEliminationContext 8
    coqDynamicTruthSigmaOrConstructorBranchSourceTemplate
    (coqDynamicTruthSigmaOrGuardedCanonicalModeZeroRowPrefix outerPrefix) =
  Some
    (coqDynamicTruthSigmaOrOpenedConstructorContextUnderModeZeroAt
      outerPrefix).
Proof. intros. reflexivity. Qed.

Lemma coqDynamicTruthSigmaOrOpenedConstructorContextUnderModeZeroAt_head :
  forall outerPrefix,
  exists tail,
  coqDynamicTruthSigmaOrOpenedConstructorContextUnderModeZeroAt outerPrefix =
  coqDynamicTruthSigmaOrLeafTemplate :: tail.
Proof. intros. eexists. reflexivity. Qed.

(** The honest opened code field refers to the shifted parent row variable
    [#10] and to the fresh constructor witnesses [#6] and [#4]. *)
Definition coqDynamicTruthSigmaOrOpenedConstructorCodeRootTemplate
    : TemplateFormula :=
  coqDynamicTruthSigmaOrCodeLeafTemplate.

Lemma coqDynamicTruthSigmaOrOpenedConstructorCodeRootTemplate_shape :
  coqDynamicTruthSigmaOrOpenedConstructorCodeRootTemplate =
  embedPAFormula
    (formulaOrCodeTermAt (tVar 10) (tVar 6) (tVar 4)).
Proof. reflexivity. Qed.

(** This syntactic inequality is the key scope audit.  The current guarded
    alias has parent [#2], whereas honest existential elimination places the
    same pre-existing parent under eight fresh variables at [#10]. *)
Lemma coqDynamicTruthSigmaOrOpenedConstructorCodeRootTemplate_neq_guarded :
  coqDynamicTruthSigmaOrOpenedConstructorCodeRootTemplate <>
  coqDynamicTruthSigmaOrGuardedCanonicalCodeRootTemplate.
Proof.
  rewrite coqDynamicTruthSigmaOrOpenedConstructorCodeRootTemplate_shape.
  unfold coqDynamicTruthSigmaOrGuardedCanonicalCodeRootTemplate,
    coqDynamicTruthSigmaOrOpenedCodeAt,
    coqDynamicTruthSigmaOrInstantiateLeafAt,
    coqDynamicTruthSigmaOrWitnessesAt,
    coqDynamicTruthSigmaOrCodeLeafTemplate,
    coqDynamicTruthSigmaOrLeafTemplate,
    dynamicTruthSigmaRowOrFormula,
    formulaOrCodeTermAt, codeList3TermAt.
  discriminate.
Qed.

(** Inside the exact opened context, the source body is a head assumption;
    one represented conjunction elimination yields its first field. *)
Theorem
    raw_codedPALocalProofOf_dynamicTruthSigmaOr_openedConstructorCode_under_modeZeroRowPrefix :
  forall (M : RawPAModel) (hPA : RawPASatisfies M)
    (translation : RawCodedTemplateTranslation M)
    sourceWitnessList sourceContext outerPrefix,
  RawCodedPAAxiomWitnessContext M sourceWitnessList sourceContext ->
  exists codeRoot,
    RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation sourceContext
        (coqDynamicTruthSigmaOrOpenedConstructorContextUnderModeZeroAt
          outerPrefix))
      (rawTemplateFormula translation
        coqDynamicTruthSigmaOrOpenedConstructorCodeRootTemplate) codeRoot.
Proof.
  intros M hPA translation sourceWitnessList sourceContext outerPrefix
    hwitnessed.
  destruct
    (coqDynamicTruthSigmaOrOpenedConstructorContextUnderModeZeroAt_head
      outerPrefix) as [tail hhead].
  assert (htail : RawContextListRealizable M
      (rawTemplateContextCodeOnTail translation sourceContext tail)).
  {
    apply (raw_templateContextOnTail_realizable M hPA).
    exact (raw_codedPAAxiomWitnessContext_context_realizable
      M sourceWitnessList sourceContext hwitnessed).
  }
  assert (hbody : RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation sourceContext
        (coqDynamicTruthSigmaOrOpenedConstructorContextUnderModeZeroAt
          outerPrefix))
      (rawTemplateFormula translation coqDynamicTruthSigmaOrLeafTemplate)
      (rawProofAssumptionRoot M
        (rawTemplateContextCodeOnTail translation sourceContext
          (coqDynamicTruthSigmaOrOpenedConstructorContextUnderModeZeroAt
            outerPrefix))
        (rawTemplateFormula translation
          coqDynamicTruthSigmaOrLeafTemplate))).
  {
    rewrite hhead. cbn [rawTemplateContextCodeOnTail].
    exact (raw_codedPALocalProofOf_assumption M hPA
      (rawTemplateContextCodeOnTail translation sourceContext tail)
      (rawTemplateFormula translation
        coqDynamicTruthSigmaOrLeafTemplate) htail).
  }
  rewrite coqDynamicTruthSigmaOrLeafTemplate_shape in hbody.
  rewrite rawTemplateFormula_and in hbody.
  lazymatch type of hbody with
  | RawCodedPALocalProofOf _ _ _ ?bodyRoot =>
      eexists;
      exact (raw_codedPALocalProofOf_andE1 M hPA
        (rawTemplateContextCodeOnTail translation sourceContext
          (coqDynamicTruthSigmaOrOpenedConstructorContextUnderModeZeroAt
            outerPrefix))
        (rawTemplateFormula translation
          coqDynamicTruthSigmaOrCodeLeafTemplate)
        (rawTemplateFormula translation
          (tfOr coqDynamicTruthSigmaOrLeftStateLeafTemplate
            coqDynamicTruthSigmaOrRightStateLeafTemplate))
        bodyRoot hbody)
  end.
Qed.

(** Empty-witness growing packaging of the opened-head projection. *)
Theorem
    raw_dynamicTruthSigmaOr_openedConstructorCodeGrowingCompilerUnderModeZeroRowPrefix :
  forall (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M) outerPrefix,
  RawCodedPAStandardWitnessGrowingTemplateFormulaCompilerAt M
    (rawDirectStructuralTemplateTranslation M hPA inputs)
    (coqDynamicTruthSigmaOrOpenedConstructorContextUnderModeZeroAt
      outerPrefix)
    coqDynamicTruthSigmaOrOpenedConstructorCodeRootTemplate.
Proof.
  intros M hPA inputs outerPrefix
    sourceWitnessList sourceContext hwitnessed.
  destruct
    (raw_codedPALocalProofOf_dynamicTruthSigmaOr_openedConstructorCode_under_modeZeroRowPrefix
      M hPA (rawDirectStructuralTemplateTranslation M hPA inputs)
      sourceWitnessList sourceContext outerPrefix hwitnessed) as
    [codeRoot hcode].
  exists [], codeRoot.
  cbn [rawStandardPAAxiomWitnessPrefixWitnessListCode
    rawStandardPAAxiomWitnessPrefixContextCode].
  split; assumption.
Qed.

End PABoundedRawCodedDynamicTruthSigmaOrOpenedConstructorCodeProjection.
