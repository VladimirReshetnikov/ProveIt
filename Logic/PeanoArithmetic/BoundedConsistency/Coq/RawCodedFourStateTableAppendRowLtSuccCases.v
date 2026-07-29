(**
  Specialize the represented successor-bound split to an appended table row.

  The generic arithmetic compiler keeps a finite temporary template prefix
  above a witnessed PA tail.  The append compiler describes the same context
  operationally, by eliminating eight table witnesses and then introducing
  five row variables.  This module proves that their carrier context codes
  coincide and exposes the case disjunction in the latter, client-facing
  form.  No carrier-coded context or witness list is decoded.
*)

From Stdlib Require Import List Arith.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  CodedProof
  RawCodedSyntaxConstructors
  RawCodedContextLists
  RawCodedContextShift
  RawCodedRestrictedPAProof
  RawCodedPAAxiomContextSelfShift
  RawCodedFixedLevelTruth
  RawCodedFixedLevelTruthTotality
  RawCodedPAAxiomWitnessPrefix
  RawCodedProofAssumptionLeaf
  RawCodedProofImpIConstructor
  RawCodedProofAllIConstructor
  RawCodedProofExEConstructor
  RawCodedPALocalProofExistential
  RawCodedPALocalProofPropositionalRules
  RawCodedPALocalProofComposition
  RawCodedPALocalProofContextInsertUnconditional
  RawCodedPALocalProofWitnessedContextMerge
  RawCodedPALocalProofEquality
  RawCodedPALocalProofUniversalEliminationChain
  RawCodedPALocalProofExistentialEliminationChain
  RawCodedTemplateSyntax
  RawCodedTemplateStructuralTranslation
  RawCodedTemplateRenamingSubstitution
  RawCodedTemplateParameterAbstraction
  RawCodedTemplateProofCompiler
  RawCodedTemplateProofCompilerSelfShiftTail
  RawCodedTemplatePAEmbedding
  RawCodedTemplatePAEmbeddingSelfShiftTail
  RawCodedTemplateLocalProofWitnessedTailTransport
  RawCodedTemplateLocalProofStandardWitnessTailTransport
  RawCodedPALocalProofUniversalIntroductionChain
  RawCodedLtSuccCasesProofCompilation
  RawCodedBetaLookupFunctionalitySource
  RawCodedBetaLookupFunctionalityProofCompilation
  RawCodedFourStateTableAppendSource
  RawCodedFourStateTableAppendProofCompilation
  RawCodedFourStateTableAppendExistentialElimination.

Import ListNotations.

Module PABoundedRawCodedFourStateTableAppendRowLtSuccCases.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedCodedProof.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedContextLists.
Import PABoundedRawCodedContextShift.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedPAAxiomContextSelfShift.
Import PABoundedRawCodedFixedLevelTruth.
Import PABoundedRawCodedFixedLevelTruthTotality.
Import PABoundedRawCodedPAAxiomWitnessPrefix.
Import PABoundedRawCodedProofAssumptionLeaf.
Import PABoundedRawCodedProofImpIConstructor.
Import PABoundedRawCodedProofAllIConstructor.
Import PABoundedRawCodedProofExEConstructor.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPALocalProofPropositionalRules.
Import PABoundedRawCodedPALocalProofComposition.
Import PABoundedRawCodedPALocalProofContextInsertUnconditional.
Import PABoundedRawCodedPALocalProofWitnessedContextMerge.
Import PABoundedRawCodedPALocalProofEquality.
Import PABoundedRawCodedPALocalProofUniversalEliminationChain.
Import PABoundedRawCodedPALocalProofExistentialEliminationChain.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateStructuralTranslation.
Import PABoundedRawCodedTemplateRenamingSubstitution.
Import PABoundedRawCodedTemplateParameterAbstraction.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedTemplateProofCompilerSelfShiftTail.
Import PABoundedRawCodedTemplatePAEmbedding.
Import PABoundedRawCodedTemplatePAEmbeddingSelfShiftTail.
Import PABoundedRawCodedTemplateLocalProofWitnessedTailTransport.
Import PABoundedRawCodedTemplateLocalProofStandardWitnessTailTransport.
Import PABoundedRawCodedPALocalProofUniversalIntroductionChain.
Import PABoundedRawCodedLtSuccCasesProofCompilation.
Import PABoundedRawCodedBetaLookupFunctionalitySource.
Import PABoundedRawCodedBetaLookupFunctionalityProofCompilation.
Import PABoundedRawCodedFourStateTableAppendSource.
Import PABoundedRawCodedFourStateTableAppendProofCompilation.
Import PABoundedRawCodedFourStateTableAppendExistentialElimination.

(** Use an equality appearing as a freshly consed assumption in the reverse
    direction.  This is the characteristic shape of the append equality
    branch: the base context proves the motive at [target], while the branch
    head says [source = target].  Symmetry and equality elimination are both
    derived inside the represented proof calculus; the base proof is moved
    below the branch head only by the guarded context-transplant theorem. *)
Theorem raw_codedPALocalProofOf_templateEqTransport_reverse_head : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M)
    context source target motive motiveRoot,
  let equalityHead :=
    rawTemplateFormula translation (tfEq source target) in
  RawCodedFormulaAtomicallyAdequate M equalityHead ->
  RawContextListRealizable M context ->
  RawCodedPALocalProofOf M context
    (rawTemplateFormula translation
      (templateFormulaOpen target motive)) motiveRoot ->
  exists root,
    RawCodedPALocalProofOf M
      (rawListNode M equalityHead context)
      (rawTemplateFormula translation
        (templateFormulaOpen source motive)) root.
Proof.
  intros M hPA translation context source target motive motiveRoot
    equalityHead hhead hcontext hmotive.
  cbn zeta in *.
  pose proof (raw_codedPALocalProofOf_assumption M hPA context
    (rawTemplateFormula translation (tfEq source target)) hcontext)
    as hequality.
  destruct (raw_codedPALocalProofOf_templateEqSymmetry M hPA translation
    (rawListNode M
      (rawTemplateFormula translation (tfEq source target)) context)
    source target
    (rawProofAssumptionRoot M
      (rawListNode M
        (rawTemplateFormula translation (tfEq source target)) context)
      (rawTemplateFormula translation (tfEq source target)))
    hequality) as [symmetryRoot hsymmetry].
  destruct (raw_codedPALocalProof_adequateConsTransplant M hPA
    context
    (rawTemplateFormula translation (tfEq source target))
    (rawTemplateFormula translation
      (templateFormulaOpen target motive))
    motiveRoot hhead hcontext hmotive)
    as [transplantedMotiveRoot htransplantedMotive].
  eexists.
  exact (raw_codedPALocalProofOf_templateEqElim M hPA translation
    (rawListNode M
      (rawTemplateFormula translation (tfEq source target)) context)
    target source motive symmetryRoot transplantedMotiveRoot
    hsymmetry htransplantedMotive).
Qed.

(** Capture-avoiding specialization for the carrier parameters used by the
    outer successor compiler.  Abstracting [name] inserts one ordinary PA
    variable; the parameter-abstraction round trip identifies its opening at
    the original parameter with [input] literally.  Opening at [source]
    therefore gives the exact transported branch target. *)
Theorem
    raw_codedPALocalProofOf_templateEqTransport_reverse_head_parameter :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M)
    context name source input inputRoot,
  let equalityHead := rawTemplateFormula translation
    (tfEq source (ttParameter name)) in
  RawCodedFormulaAtomicallyAdequate M equalityHead ->
  RawContextListRealizable M context ->
  RawCodedPALocalProofOf M context
    (rawTemplateFormula translation input) inputRoot ->
  exists root,
    RawCodedPALocalProofOf M
      (rawListNode M equalityHead context)
      (rawTemplateFormula translation
        (templateFormulaOpen source
          (templateFormulaAbstractParameter name input))) root.
Proof.
  intros M hPA translation context name source input inputRoot
    equalityHead hhead hcontext hinput.
  cbn zeta in *.
  eapply (raw_codedPALocalProofOf_templateEqTransport_reverse_head
    M hPA translation context source (ttParameter name)
    (templateFormulaAbstractParameter name input) inputRoot).
  - exact hhead.
  - exact hcontext.
  - rewrite templateFormulaAbstractParameter_open.
    exact hinput.
Qed.

(** The four appended-entry fields with their shared bound parameter
    abstracted and reopened at the traversal row index.  Keeping this as a
    named template makes the capture-avoiding transport target transparent
    to the later lookup-functionality comparison. *)
Definition coqFourStateTableAppendEqualityTransportedNewStateLookupTemplate
    (boundName : TemplateParameterName) (index : TemplateTerm)
    (modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      mode formula assignmentCode assignmentStep : TemplateTerm)
    : TemplateFormula :=
  templateFormulaOpen index
    (templateFormulaAbstractParameter boundName
      (templateFormulaShiftMany 5
        (coqFourStateTableAppendNewStateLookupTemplate
          modeCode modeStep formulaCode formulaStep
          assignmentCodeCode assignmentCodeStep
          assignmentStepCode assignmentStepStep
          (ttParameter boundName)
          mode formula assignmentCode assignmentStep))).

(** The four beta-functionality instances used to compare the transported
    appended entry with the independently bound traversal row.  After eight
    append witnesses and five row variables, the new code/step pairs occupy
    variables 12/11, 10/9, 8/7, and 6/5. *)
Definition coqFourStateTableAppendEqualityModeFunctionalityArguments
    (modeName : TemplateParameterName)
    (index rowMode : TemplateTerm)
    : CoqBetaLookupFunctionalityArguments :=
  {| coqBetaLookupFunctionalityOut1 := ttParameter modeName;
     coqBetaLookupFunctionalityOut2 := rowMode;
     coqBetaLookupFunctionalityCode := ttVar 12;
     coqBetaLookupFunctionalityStep := ttVar 11;
     coqBetaLookupFunctionalityIndex := index |}.

Definition coqFourStateTableAppendEqualityFormulaFunctionalityArguments
    (formulaName : TemplateParameterName)
    (index rowFormula : TemplateTerm)
    : CoqBetaLookupFunctionalityArguments :=
  {| coqBetaLookupFunctionalityOut1 := ttParameter formulaName;
     coqBetaLookupFunctionalityOut2 := rowFormula;
     coqBetaLookupFunctionalityCode := ttVar 10;
     coqBetaLookupFunctionalityStep := ttVar 9;
     coqBetaLookupFunctionalityIndex := index |}.

Definition
    coqFourStateTableAppendEqualityAssignmentCodeFunctionalityArguments
    (assignmentCodeName : TemplateParameterName)
    (index rowAssignmentCode : TemplateTerm)
    : CoqBetaLookupFunctionalityArguments :=
  {| coqBetaLookupFunctionalityOut1 := ttParameter assignmentCodeName;
     coqBetaLookupFunctionalityOut2 := rowAssignmentCode;
     coqBetaLookupFunctionalityCode := ttVar 8;
     coqBetaLookupFunctionalityStep := ttVar 7;
     coqBetaLookupFunctionalityIndex := index |}.

Definition
    coqFourStateTableAppendEqualityAssignmentStepFunctionalityArguments
    (assignmentStepName : TemplateParameterName)
    (index rowAssignmentStep : TemplateTerm)
    : CoqBetaLookupFunctionalityArguments :=
  {| coqBetaLookupFunctionalityOut1 := ttParameter assignmentStepName;
     coqBetaLookupFunctionalityOut2 := rowAssignmentStep;
     coqBetaLookupFunctionalityCode := ttVar 6;
     coqBetaLookupFunctionalityStep := ttVar 5;
     coqBetaLookupFunctionalityIndex := index |}.

Definition coqFourStateTableAppendEqualityRowLookupTemplate
    (modeName formulaName assignmentCodeName assignmentStepName
      : TemplateParameterName)
    (index rowMode rowFormula rowAssignmentCode rowAssignmentStep
      : TemplateTerm) : TemplateFormula :=
  let modeArguments :=
    coqFourStateTableAppendEqualityModeFunctionalityArguments
      modeName index rowMode in
  let formulaArguments :=
    coqFourStateTableAppendEqualityFormulaFunctionalityArguments
      formulaName index rowFormula in
  let assignmentCodeArguments :=
    coqFourStateTableAppendEqualityAssignmentCodeFunctionalityArguments
      assignmentCodeName index rowAssignmentCode in
  let assignmentStepArguments :=
    coqFourStateTableAppendEqualityAssignmentStepFunctionalityArguments
      assignmentStepName index rowAssignmentStep in
  tfAnd (coqBetaLookupFunctionalitySecondLookupOf modeArguments)
    (tfAnd (coqBetaLookupFunctionalitySecondLookupOf formulaArguments)
      (tfAnd
        (coqBetaLookupFunctionalitySecondLookupOf assignmentCodeArguments)
        (coqBetaLookupFunctionalitySecondLookupOf
          assignmentStepArguments))).

Lemma coqFourStateTableAppendEqualityRowLookupTemplate_matches_second :
  forall modeName formulaName assignmentCodeName assignmentStepName
    index rowMode rowFormula rowAssignmentCode rowAssignmentStep,
  TemplateAnd4MatchesBetaFunctionalitySide
    coqBetaLookupFunctionalitySecondLookupOf
    (coqFourStateTableAppendEqualityRowLookupTemplate
      modeName formulaName assignmentCodeName assignmentStepName
      index rowMode rowFormula rowAssignmentCode rowAssignmentStep)
    (coqFourStateTableAppendEqualityModeFunctionalityArguments
      modeName index rowMode)
    (coqFourStateTableAppendEqualityFormulaFunctionalityArguments
      formulaName index rowFormula)
    (coqFourStateTableAppendEqualityAssignmentCodeFunctionalityArguments
      assignmentCodeName index rowAssignmentCode)
    (coqFourStateTableAppendEqualityAssignmentStepFunctionalityArguments
      assignmentStepName index rowAssignmentStep).
Proof.
  intros.
  unfold TemplateAnd4MatchesBetaFunctionalitySide,
    coqFourStateTableAppendEqualityRowLookupTemplate,
    templateAnd4First, templateAnd4Second,
    templateAnd4Third, templateAnd4Fourth.
  repeat split; reflexivity.
Qed.

(** Before the five row binders are introduced, the mode lookup projected
    from the eight-witness append body is literally one beta-functionality
    first premise.  This small normalization lemma is the base case for the
    shifted and parameter-abstracted four-column contract. *)
Lemma coqFourStateTableAppendModeLookupTemplate_beta_first : forall
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    boundName modeName formulaName assignmentCodeName assignmentStepName
    rowMode,
  coqFourStateTableAppendModeLookupTemplate
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    (ttParameter boundName) (ttParameter modeName)
    (ttParameter formulaName) (ttParameter assignmentCodeName)
    (ttParameter assignmentStepName) =
  coqBetaLookupFunctionalityFirstLookupOf
    {| coqBetaLookupFunctionalityOut1 := ttParameter modeName;
       coqBetaLookupFunctionalityOut2 := rowMode;
       coqBetaLookupFunctionalityCode := ttVar 7;
       coqBetaLookupFunctionalityStep := ttVar 6;
       coqBetaLookupFunctionalityIndex := ttParameter boundName |}.
Proof.
  intros.
  unfold coqFourStateTableAppendModeLookupTemplate,
    coqFourStateTableAppendExtensionBodyTemplate,
    coqFourStateTableAppendExistsTemplate,
    coqFourStateTableAppendInstanceTemplate,
    codedFourStateTableAppendFormula,
    fourStateTableAppendRepeatedAll,
    fourStateTableAppendExtensionBody,
    fixedLevelEx8, fixedLevelAnd4,
    codedAssignmentAppendAtTermAt,
    coqBetaLookupFunctionalityFirstLookupOf,
    coqBetaLookupFunctionalityInstanceOf,
    coqBetaLookupFunctionalityInstanceTemplate,
    codedBetaLookupFunctionalityFormula,
    templateImpAntecedent,
    templateAndFirst, templateAndSecond,
    templateAnd4First,
    templateUniversalOpenManyOrBot.
  cbn [templateUniversalOpenMany embedPAFormula
    templateFormulaOpen templateExistentialBodyMany].
  repeat rewrite templateFormulaSubst_comp.
  cbn [templateFormulaSubst templateTermSubst
    templateTermUpSubst templateInstTerm].
  reflexivity.
Qed.

(** The remaining three projections obey the same normalization.  Their
    de Bruijn pairs descend by two because the append body binds the four
    code/step pairs in mode, formula, assignment-code, assignment-step
    order.  Keeping the equalities separate makes later projection rewrites
    local and documents the exact witness layout. *)
Lemma coqFourStateTableAppendFormulaLookupTemplate_beta_first : forall
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    boundName modeName formulaName assignmentCodeName assignmentStepName
    rowFormula,
  coqFourStateTableAppendFormulaLookupTemplate
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    (ttParameter boundName) (ttParameter modeName)
    (ttParameter formulaName) (ttParameter assignmentCodeName)
    (ttParameter assignmentStepName) =
  coqBetaLookupFunctionalityFirstLookupOf
    {| coqBetaLookupFunctionalityOut1 := ttParameter formulaName;
       coqBetaLookupFunctionalityOut2 := rowFormula;
       coqBetaLookupFunctionalityCode := ttVar 5;
       coqBetaLookupFunctionalityStep := ttVar 4;
       coqBetaLookupFunctionalityIndex := ttParameter boundName |}.
Proof.
  intros.
  unfold coqFourStateTableAppendFormulaLookupTemplate,
    coqFourStateTableAppendExtensionBodyTemplate,
    coqFourStateTableAppendExistsTemplate,
    coqFourStateTableAppendInstanceTemplate,
    codedFourStateTableAppendFormula,
    fourStateTableAppendRepeatedAll,
    fourStateTableAppendExtensionBody,
    fixedLevelEx8, fixedLevelAnd4,
    codedAssignmentAppendAtTermAt,
    coqBetaLookupFunctionalityFirstLookupOf,
    coqBetaLookupFunctionalityInstanceOf,
    coqBetaLookupFunctionalityInstanceTemplate,
    codedBetaLookupFunctionalityFormula,
    templateImpAntecedent,
    templateAndFirst, templateAndSecond,
    templateAnd4Second,
    templateUniversalOpenManyOrBot.
  cbn [templateUniversalOpenMany embedPAFormula
    templateFormulaOpen templateExistentialBodyMany].
  repeat rewrite templateFormulaSubst_comp.
  cbn [templateFormulaSubst templateTermSubst
    templateTermUpSubst templateInstTerm].
  reflexivity.
Qed.

Lemma coqFourStateTableAppendAssignmentCodeLookupTemplate_beta_first : forall
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    boundName modeName formulaName assignmentCodeName assignmentStepName
    rowAssignmentCode,
  coqFourStateTableAppendAssignmentCodeLookupTemplate
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    (ttParameter boundName) (ttParameter modeName)
    (ttParameter formulaName) (ttParameter assignmentCodeName)
    (ttParameter assignmentStepName) =
  coqBetaLookupFunctionalityFirstLookupOf
    {| coqBetaLookupFunctionalityOut1 := ttParameter assignmentCodeName;
       coqBetaLookupFunctionalityOut2 := rowAssignmentCode;
       coqBetaLookupFunctionalityCode := ttVar 3;
       coqBetaLookupFunctionalityStep := ttVar 2;
       coqBetaLookupFunctionalityIndex := ttParameter boundName |}.
Proof.
  intros.
  unfold coqFourStateTableAppendAssignmentCodeLookupTemplate,
    coqFourStateTableAppendExtensionBodyTemplate,
    coqFourStateTableAppendExistsTemplate,
    coqFourStateTableAppendInstanceTemplate,
    codedFourStateTableAppendFormula,
    fourStateTableAppendRepeatedAll,
    fourStateTableAppendExtensionBody,
    fixedLevelEx8, fixedLevelAnd4,
    codedAssignmentAppendAtTermAt,
    coqBetaLookupFunctionalityFirstLookupOf,
    coqBetaLookupFunctionalityInstanceOf,
    coqBetaLookupFunctionalityInstanceTemplate,
    codedBetaLookupFunctionalityFormula,
    templateImpAntecedent,
    templateAndFirst, templateAndSecond,
    templateAnd4Third,
    templateUniversalOpenManyOrBot.
  cbn [templateUniversalOpenMany embedPAFormula
    templateFormulaOpen templateExistentialBodyMany].
  repeat rewrite templateFormulaSubst_comp.
  cbn [templateFormulaSubst templateTermSubst
    templateTermUpSubst templateInstTerm].
  reflexivity.
Qed.

Lemma coqFourStateTableAppendAssignmentStepLookupTemplate_beta_first : forall
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    boundName modeName formulaName assignmentCodeName assignmentStepName
    rowAssignmentStep,
  coqFourStateTableAppendAssignmentStepLookupTemplate
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    (ttParameter boundName) (ttParameter modeName)
    (ttParameter formulaName) (ttParameter assignmentCodeName)
    (ttParameter assignmentStepName) =
  coqBetaLookupFunctionalityFirstLookupOf
    {| coqBetaLookupFunctionalityOut1 := ttParameter assignmentStepName;
       coqBetaLookupFunctionalityOut2 := rowAssignmentStep;
       coqBetaLookupFunctionalityCode := ttVar 1;
       coqBetaLookupFunctionalityStep := ttVar 0;
       coqBetaLookupFunctionalityIndex := ttParameter boundName |}.
Proof.
  intros.
  unfold coqFourStateTableAppendAssignmentStepLookupTemplate,
    coqFourStateTableAppendExtensionBodyTemplate,
    coqFourStateTableAppendExistsTemplate,
    coqFourStateTableAppendInstanceTemplate,
    codedFourStateTableAppendFormula,
    fourStateTableAppendRepeatedAll,
    fourStateTableAppendExtensionBody,
    fixedLevelEx8, fixedLevelAnd4,
    codedAssignmentAppendAtTermAt,
    coqBetaLookupFunctionalityFirstLookupOf,
    coqBetaLookupFunctionalityInstanceOf,
    coqBetaLookupFunctionalityInstanceTemplate,
    codedBetaLookupFunctionalityFormula,
    templateImpAntecedent,
    templateAndFirst, templateAndSecond,
    templateAnd4Fourth,
    templateUniversalOpenManyOrBot.
  cbn [templateUniversalOpenMany embedPAFormula
    templateFormulaOpen templateExistentialBodyMany].
  repeat rewrite templateFormulaSubst_comp.
  cbn [templateFormulaSubst templateTermSubst
    templateTermUpSubst templateInstTerm].
  reflexivity.
Qed.

(** Shift one beta first-premise beneath the five row binders, then replace
    its named append bound by the traversal index.  The result records the
    whole binder calculation once: ordinary code/step variables rise by
    five, field parameters remain fixed, and the selected bound parameter
    is opened capture-avoidantly at [index]. *)
Lemma coqBetaLookupFunctionalityFirstLookup_shift5_abstract_open : forall
    boundName valueName index rowValue codeVariable stepVariable,
  valueName <> boundName ->
  templateFormulaOpen index
    (templateFormulaAbstractParameter boundName
      (templateFormulaShiftMany 5
        (coqBetaLookupFunctionalityFirstLookupOf
          {| coqBetaLookupFunctionalityOut1 := ttParameter valueName;
             coqBetaLookupFunctionalityOut2 := rowValue;
             coqBetaLookupFunctionalityCode := ttVar codeVariable;
             coqBetaLookupFunctionalityStep := ttVar stepVariable;
             coqBetaLookupFunctionalityIndex :=
               ttParameter boundName |}))) =
  coqBetaLookupFunctionalityFirstLookupOf
    {| coqBetaLookupFunctionalityOut1 := ttParameter valueName;
       coqBetaLookupFunctionalityOut2 := rowValue;
       coqBetaLookupFunctionalityCode := ttVar (5 + codeVariable);
       coqBetaLookupFunctionalityStep := ttVar (5 + stepVariable);
       coqBetaLookupFunctionalityIndex := index |}.
Proof.
  intros boundName valueName index rowValue codeVariable stepVariable
    hfresh.
  assert (hfreshEqb : Nat.eqb valueName boundName = false) by
    (apply Nat.eqb_neq; exact hfresh).
  unfold coqBetaLookupFunctionalityFirstLookupOf,
    coqBetaLookupFunctionalityInstanceOf,
    coqBetaLookupFunctionalityInstanceTemplate,
    codedBetaLookupFunctionalityFormula,
    templateImpAntecedent,
    templateAndFirst, templateAndSecond,
    templateUniversalOpenManyOrBot,
    templateFormulaAbstractParameter,
    templateFormulaOpen.
  cbv [templateFormulaShiftMany templateFormulaRename
    templateTermRename templateTermsRename
    templateFormulaAbstractParameterAt
    templateTermAbstractParameterAt templateTermsAbstractParameterAt
    templateFormulaSubst templateTermSubst templateTermsSubst
    templateTermUpSubst templateUpRenaming templateInstTerm
    templateShiftRenamingAt
    templateUniversalOpenMany templateFormulaOpen
    embedPAFormula embedPATerm
    coqBetaLookupFunctionalityOut1
    coqBetaLookupFunctionalityOut2
    coqBetaLookupFunctionalityCode
    coqBetaLookupFunctionalityStep
    coqBetaLookupFunctionalityIndex
    Formula.betaTermTermAt Formula.betaModTermTerm
    Formula.remTermTermAt Formula.ltTermAt
    Term.rename].
  rewrite hfreshEqb.
  rewrite Nat.eqb_refl.
  cbn [templateTermSubst templateTermRename
    templateTermUpSubst templateInstTerm].
  reflexivity.
Qed.

(** The transformed append lookup supplies the first premise of all four
    functionality instances.  The four freshness hypotheses are necessary:
    [templateFormulaAbstractParameter] intentionally abstracts every
    occurrence of [boundName], so a field parameter bearing that same name
    would no longer denote the independently fixed row value. *)
Lemma
    coqFourStateTableAppendEqualityTransportedNewStateLookupTemplate_matches_first :
  forall modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    boundName modeName formulaName assignmentCodeName assignmentStepName
    index rowMode rowFormula rowAssignmentCode rowAssignmentStep,
  modeName <> boundName ->
  formulaName <> boundName ->
  assignmentCodeName <> boundName ->
  assignmentStepName <> boundName ->
  TemplateAnd4MatchesBetaFunctionalitySide
    coqBetaLookupFunctionalityFirstLookupOf
    (coqFourStateTableAppendEqualityTransportedNewStateLookupTemplate
      boundName index
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      (ttParameter modeName) (ttParameter formulaName)
      (ttParameter assignmentCodeName) (ttParameter assignmentStepName))
    (coqFourStateTableAppendEqualityModeFunctionalityArguments
      modeName index rowMode)
    (coqFourStateTableAppendEqualityFormulaFunctionalityArguments
      formulaName index rowFormula)
    (coqFourStateTableAppendEqualityAssignmentCodeFunctionalityArguments
      assignmentCodeName index rowAssignmentCode)
    (coqFourStateTableAppendEqualityAssignmentStepFunctionalityArguments
      assignmentStepName index rowAssignmentStep).
Proof.
  intros modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    boundName modeName formulaName assignmentCodeName assignmentStepName
    index rowMode rowFormula rowAssignmentCode rowAssignmentStep
    hmode hformula hassignmentCode hassignmentStep.
  unfold TemplateAnd4MatchesBetaFunctionalitySide,
    coqFourStateTableAppendEqualityTransportedNewStateLookupTemplate,
    coqFourStateTableAppendNewStateLookupTemplate.
  rewrite !templateFormulaShiftMany_and.
  cbn [templateFormulaAbstractParameter
    templateFormulaAbstractParameterAt
    templateFormulaOpen templateFormulaSubst
    templateAnd4First templateAnd4Second
    templateAnd4Third templateAnd4Fourth].
  repeat split.
  - rewrite (coqFourStateTableAppendModeLookupTemplate_beta_first
      _ _ _ _ _ _ _ _ _ _ _ _ _ rowMode).
    unfold coqFourStateTableAppendEqualityModeFunctionalityArguments.
    exact
      (coqBetaLookupFunctionalityFirstLookup_shift5_abstract_open
        boundName modeName index rowMode 7 6 hmode).
  - rewrite (coqFourStateTableAppendFormulaLookupTemplate_beta_first
      _ _ _ _ _ _ _ _ _ _ _ _ _ rowFormula).
    unfold coqFourStateTableAppendEqualityFormulaFunctionalityArguments.
    exact
      (coqBetaLookupFunctionalityFirstLookup_shift5_abstract_open
        boundName formulaName index rowFormula 5 4 hformula).
  - rewrite
      (coqFourStateTableAppendAssignmentCodeLookupTemplate_beta_first
        _ _ _ _ _ _ _ _ _ _ _ _ _ rowAssignmentCode).
    unfold
      coqFourStateTableAppendEqualityAssignmentCodeFunctionalityArguments.
    exact
      (coqBetaLookupFunctionalityFirstLookup_shift5_abstract_open
        boundName assignmentCodeName index rowAssignmentCode 3 2
        hassignmentCode).
  - rewrite
      (coqFourStateTableAppendAssignmentStepLookupTemplate_beta_first
        _ _ _ _ _ _ _ _ _ _ _ _ _ rowAssignmentStep).
    unfold
      coqFourStateTableAppendEqualityAssignmentStepFunctionalityArguments.
    exact
      (coqBetaLookupFunctionalityFirstLookup_shift5_abstract_open
        boundName assignmentStepName index rowAssignmentStep 1 0
        hassignmentStep).
Qed.

(** Equality callback for the appended row.  The shifted lookup at the
    appended bound is projected from the append witnesses themselves; the
    literal branch assumption [index = bound] then transports all four
    fields together to [index]. *)
Theorem
    raw_codedPALocalProofOf_four_state_table_append_equality_branch_lookup_parameter :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M)
    context
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    boundName mode formula assignmentCode assignmentStep
    index rowBound,
  let shiftedWitnessContext := templateContextShiftMany 5
    (coqFourStateTableAppendWitnessContext
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      (ttParameter boundName) mode formula assignmentCode assignmentStep
      context) in
  let shiftedWitnessContextCode :=
    rawTemplateContextCode translation shiftedWitnessContext in
  let branchHead := rawTemplateFormula translation
    (coqLtSuccCasesEqualTemplate index rowBound) in
  coqLtSuccCasesEqualTemplate index rowBound =
    tfEq index (ttParameter boundName) ->
  RawCodedFormulaAtomicallyAdequate M branchHead ->
  exists root,
    RawCodedPALocalProofOf M
      (rawListNode M branchHead shiftedWitnessContextCode)
      (rawTemplateFormula translation
        (coqFourStateTableAppendEqualityTransportedNewStateLookupTemplate
          boundName index
          modeCode modeStep formulaCode formulaStep
          assignmentCodeCode assignmentCodeStep
          assignmentStepCode assignmentStepStep
          mode formula assignmentCode assignmentStep)) root.
Proof.
  intros M hPA translation context
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    boundName mode formula assignmentCode assignmentStep
    index rowBound
    shiftedWitnessContext shiftedWitnessContextCode branchHead
    hequalHead hhead.
  cbn zeta in *.
  destruct
    (raw_codedPALocalProofOf_four_state_table_append_new_state_lookup_shift_many
      M hPA translation 5 context
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      (ttParameter boundName) mode formula assignmentCode assignmentStep)
    as [lookupRoot hlookup].
  pose proof (raw_templateContext_realizable M hPA translation
    (templateContextShiftMany 5
      (coqFourStateTableAppendWitnessContext
        modeCode modeStep formulaCode formulaStep
        assignmentCodeCode assignmentCodeStep
        assignmentStepCode assignmentStepStep
        (ttParameter boundName) mode formula assignmentCode assignmentStep
        context))) as hcontext.
  assert (hbranchHead :
      rawTemplateFormula translation
        (coqLtSuccCasesEqualTemplate index rowBound) =
      rawTemplateFormula translation
        (tfEq index (ttParameter boundName))).
  {
    now rewrite hequalHead.
  }
  change (RawCodedFormulaAtomicallyAdequate M
    (rawTemplateFormula translation
      (coqLtSuccCasesEqualTemplate index rowBound))) in hhead.
  rewrite hbranchHead in hhead.
  destruct
    (raw_codedPALocalProofOf_templateEqTransport_reverse_head_parameter
      M hPA translation
      (rawTemplateContextCode translation
        (templateContextShiftMany 5
          (coqFourStateTableAppendWitnessContext
            modeCode modeStep formulaCode formulaStep
            assignmentCodeCode assignmentCodeStep
            assignmentStepCode assignmentStepStep
            (ttParameter boundName) mode formula assignmentCode assignmentStep
            context)))
      boundName index
      (templateFormulaShiftMany 5
        (coqFourStateTableAppendNewStateLookupTemplate
          modeCode modeStep formulaCode formulaStep
          assignmentCodeCode assignmentCodeStep
          assignmentStepCode assignmentStepStep
          (ttParameter boundName) mode formula assignmentCode assignmentStep))
      lookupRoot hhead hcontext hlookup)
    as [root hroot].
  exists root.
  unfold coqFourStateTableAppendEqualityTransportedNewStateLookupTemplate.
  change (RawCodedPALocalProofOf M
    (rawListNode M
      (rawTemplateFormula translation
        (coqLtSuccCasesEqualTemplate index rowBound))
      (rawTemplateContextCode translation
        (templateContextShiftMany 5
          (coqFourStateTableAppendWitnessContext
            modeCode modeStep formulaCode formulaStep
            assignmentCodeCode assignmentCodeStep
            assignmentStepCode assignmentStepStep
            (ttParameter boundName) mode formula assignmentCode assignmentStep
            context))))
    (rawTemplateFormula translation
      (templateFormulaOpen index
        (templateFormulaAbstractParameter boundName
          (templateFormulaShiftMany 5
            (coqFourStateTableAppendNewStateLookupTemplate
              modeCode modeStep formulaCode formulaStep
              assignmentCodeCode assignmentCodeStep
              assignmentStepCode assignmentStepStep
              (ttParameter boundName) mode formula assignmentCode
              assignmentStep))))) root).
  rewrite hbranchHead.
  exact hroot.
Qed.

(** Prefix-general equality callback.  Later row clients place the lookup
    and bound assumptions between the equality branch head and the shifted
    append-witness context.  Build the fixed appended lookup first, weaken it
    beneath that finite adequate prefix, and only then consume [index = b]. *)
Theorem
    raw_codedPALocalProofOf_four_state_table_append_equality_branch_lookup_parameter_under_prefix :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M)
    context extraPrefix
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    boundName mode formula assignmentCode assignmentStep
    index rowBound,
  let shiftedWitnessContext := templateContextShiftMany 5
    (coqFourStateTableAppendWitnessContext
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      (ttParameter boundName) mode formula assignmentCode assignmentStep
      context) in
  let shiftedWitnessContextCode :=
    rawTemplateContextCode translation shiftedWitnessContext in
  let branchHead := rawTemplateFormula translation
    (coqLtSuccCasesEqualTemplate index rowBound) in
  RawCodedTemplatePrefixAtomicallyAdequate M translation extraPrefix ->
  coqLtSuccCasesEqualTemplate index rowBound =
    tfEq index (ttParameter boundName) ->
  RawCodedFormulaAtomicallyAdequate M branchHead ->
  exists root,
    RawCodedPALocalProofOf M
      (rawListNode M branchHead
        (rawTemplateContextCodeOnTail translation
          shiftedWitnessContextCode extraPrefix))
      (rawTemplateFormula translation
        (coqFourStateTableAppendEqualityTransportedNewStateLookupTemplate
          boundName index
          modeCode modeStep formulaCode formulaStep
          assignmentCodeCode assignmentCodeStep
          assignmentStepCode assignmentStepStep
          mode formula assignmentCode assignmentStep)) root.
Proof.
  intros M hPA translation context extraPrefix
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    boundName mode formula assignmentCode assignmentStep
    index rowBound
    shiftedWitnessContext shiftedWitnessContextCode branchHead
    hprefix hequalHead hhead.
  cbn zeta in *.
  destruct
    (raw_codedPALocalProofOf_four_state_table_append_new_state_lookup_shift_many
      M hPA translation 5 context
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      (ttParameter boundName) mode formula assignmentCode assignmentStep)
    as [lookupRoot hlookup].
  pose proof (raw_templateContext_realizable M hPA translation
    (templateContextShiftMany 5
      (coqFourStateTableAppendWitnessContext
        modeCode modeStep formulaCode formulaStep
        assignmentCodeCode assignmentCodeStep
        assignmentStepCode assignmentStepStep
        (ttParameter boundName) mode formula assignmentCode assignmentStep
        context))) as hcontext.
  destruct
    (raw_codedPALocalProof_templatePrefix
      M hPA translation
      (rawTemplateContextCode translation
        (templateContextShiftMany 5
          (coqFourStateTableAppendWitnessContext
            modeCode modeStep formulaCode formulaStep
            assignmentCodeCode assignmentCodeStep
            assignmentStepCode assignmentStepStep
            (ttParameter boundName) mode formula assignmentCode assignmentStep
            context)))
      extraPrefix
      (rawTemplateFormula translation
        (templateFormulaShiftMany 5
          (coqFourStateTableAppendNewStateLookupTemplate
            modeCode modeStep formulaCode formulaStep
            assignmentCodeCode assignmentCodeStep
            assignmentStepCode assignmentStepStep
            (ttParameter boundName) mode formula assignmentCode
            assignmentStep)))
      lookupRoot hcontext hprefix hlookup)
    as [prefixedLookupRoot hprefixedLookup].
  assert (hprefixedContext : RawContextListRealizable M
      (rawTemplateContextCodeOnTail translation
        (rawTemplateContextCode translation
          (templateContextShiftMany 5
            (coqFourStateTableAppendWitnessContext
              modeCode modeStep formulaCode formulaStep
              assignmentCodeCode assignmentCodeStep
              assignmentStepCode assignmentStepStep
              (ttParameter boundName) mode formula assignmentCode
              assignmentStep context))) extraPrefix)).
  {
    apply (raw_templateContextOnTail_realizable M hPA).
    exact hcontext.
  }
  assert (hbranchHead :
      rawTemplateFormula translation
        (coqLtSuccCasesEqualTemplate index rowBound) =
      rawTemplateFormula translation
        (tfEq index (ttParameter boundName))).
  { now rewrite hequalHead. }
  change (RawCodedFormulaAtomicallyAdequate M
    (rawTemplateFormula translation
      (coqLtSuccCasesEqualTemplate index rowBound))) in hhead.
  rewrite hbranchHead in hhead.
  destruct
    (raw_codedPALocalProofOf_templateEqTransport_reverse_head_parameter
      M hPA translation
      (rawTemplateContextCodeOnTail translation
        (rawTemplateContextCode translation
          (templateContextShiftMany 5
            (coqFourStateTableAppendWitnessContext
              modeCode modeStep formulaCode formulaStep
              assignmentCodeCode assignmentCodeStep
              assignmentStepCode assignmentStepStep
              (ttParameter boundName) mode formula assignmentCode
              assignmentStep context))) extraPrefix)
      boundName index
      (templateFormulaShiftMany 5
        (coqFourStateTableAppendNewStateLookupTemplate
          modeCode modeStep formulaCode formulaStep
          assignmentCodeCode assignmentCodeStep
          assignmentStepCode assignmentStepStep
          (ttParameter boundName) mode formula assignmentCode assignmentStep))
      prefixedLookupRoot hhead hprefixedContext hprefixedLookup)
    as [root hroot].
  exists root.
  unfold coqFourStateTableAppendEqualityTransportedNewStateLookupTemplate.
  change (RawCodedPALocalProofOf M
    (rawListNode M
      (rawTemplateFormula translation
        (coqLtSuccCasesEqualTemplate index rowBound))
      (rawTemplateContextCodeOnTail translation
        (rawTemplateContextCode translation
          (templateContextShiftMany 5
            (coqFourStateTableAppendWitnessContext
              modeCode modeStep formulaCode formulaStep
              assignmentCodeCode assignmentCodeStep
              assignmentStepCode assignmentStepStep
              (ttParameter boundName) mode formula assignmentCode
              assignmentStep context))) extraPrefix))
    (rawTemplateFormula translation
      (templateFormulaOpen index
        (templateFormulaAbstractParameter boundName
          (templateFormulaShiftMany 5
            (coqFourStateTableAppendNewStateLookupTemplate
              modeCode modeStep formulaCode formulaStep
              assignmentCodeCode assignmentCodeStep
              assignmentStepCode assignmentStepStep
              (ttParameter boundName) mode formula assignmentCode
              assignmentStep))))) root).
  rewrite hbranchHead.
  exact hroot.
Qed.

(** Compare the transported appended entry with a row lookup under one
    witnessed temporary context.  Both four-component contracts are now
    discharged internally: the row side is definitional, while the append
    side uses the shift/abstraction calculation above. *)
Theorem
    raw_codedPALocalProofOf_four_state_table_append_equality_lookup_functionality_on_witnessed_tail_under_prefix :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall baseWitnessList baseContext prefix
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    boundName modeName formulaName assignmentCodeName assignmentStepName
    index rowMode rowFormula rowAssignmentCode rowAssignmentStep
    fixedLookupRoot rowLookupRoot,
  let modeArguments :=
    coqFourStateTableAppendEqualityModeFunctionalityArguments
      modeName index rowMode in
  let formulaArguments :=
    coqFourStateTableAppendEqualityFormulaFunctionalityArguments
      formulaName index rowFormula in
  let assignmentCodeArguments :=
    coqFourStateTableAppendEqualityAssignmentCodeFunctionalityArguments
      assignmentCodeName index rowAssignmentCode in
  let assignmentStepArguments :=
    coqFourStateTableAppendEqualityAssignmentStepFunctionalityArguments
      assignmentStepName index rowAssignmentStep in
  let fixedLookup :=
    coqFourStateTableAppendEqualityTransportedNewStateLookupTemplate
      boundName index
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      (ttParameter modeName) (ttParameter formulaName)
      (ttParameter assignmentCodeName) (ttParameter assignmentStepName) in
  let rowLookup := coqFourStateTableAppendEqualityRowLookupTemplate
    modeName formulaName assignmentCodeName assignmentStepName
    index rowMode rowFormula rowAssignmentCode rowAssignmentStep in
  RawCodedTemplatePrefixAtomicallyAdequate M translation prefix ->
  RawCodedPAAxiomWitnessContext M baseWitnessList baseContext ->
  modeName <> boundName ->
  formulaName <> boundName ->
  assignmentCodeName <> boundName ->
  assignmentStepName <> boundName ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail translation baseContext prefix)
    (rawTemplateFormula translation fixedLookup) fixedLookupRoot ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail translation baseContext prefix)
    (rawTemplateFormula translation rowLookup) rowLookupRoot ->
  exists (witnesses : StandardPAAxiomWitnessPrefix) equalityRoots,
    RawCodedPAAxiomWitnessContext M
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        witnesses baseWitnessList)
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses baseContext) /\
    Forall2
      (fun argument root =>
        RawCodedPALocalProofOf M
          (rawTemplateContextCodeOnTail translation
            (rawStandardPAAxiomWitnessPrefixContextCode M
              witnesses baseContext) prefix)
          (rawTemplateFormula translation
            (coqBetaLookupFunctionalityEqualityOf argument)) root)
      [modeArguments; formulaArguments;
       assignmentCodeArguments; assignmentStepArguments]
      equalityRoots.
Proof.
  intros M hPA translation hagreement
    baseWitnessList baseContext prefix
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    boundName modeName formulaName assignmentCodeName assignmentStepName
    index rowMode rowFormula rowAssignmentCode rowAssignmentStep
    fixedLookupRoot rowLookupRoot
    modeArguments formulaArguments assignmentCodeArguments
    assignmentStepArguments fixedLookup rowLookup
    hprefix hbase hmodeFresh hformulaFresh
    hassignmentCodeFresh hassignmentStepFresh
    hfixedLookup hrowLookup.
  cbn zeta in *.
  exact
    (raw_codedPALocalProofOf_beta_lookup_functionality_and4_on_witnessed_tail_under_prefix
      M hPA translation hagreement baseWitnessList baseContext prefix
      (coqFourStateTableAppendEqualityModeFunctionalityArguments
        modeName index rowMode)
      (coqFourStateTableAppendEqualityFormulaFunctionalityArguments
        formulaName index rowFormula)
      (coqFourStateTableAppendEqualityAssignmentCodeFunctionalityArguments
        assignmentCodeName index rowAssignmentCode)
      (coqFourStateTableAppendEqualityAssignmentStepFunctionalityArguments
        assignmentStepName index rowAssignmentStep)
      (coqFourStateTableAppendEqualityTransportedNewStateLookupTemplate
        boundName index
        modeCode modeStep formulaCode formulaStep
        assignmentCodeCode assignmentCodeStep
        assignmentStepCode assignmentStepStep
        (ttParameter modeName) (ttParameter formulaName)
        (ttParameter assignmentCodeName) (ttParameter assignmentStepName))
      (coqFourStateTableAppendEqualityRowLookupTemplate
        modeName formulaName assignmentCodeName assignmentStepName
        index rowMode rowFormula rowAssignmentCode rowAssignmentStep)
      fixedLookupRoot rowLookupRoot hprefix hbase
      (coqFourStateTableAppendEqualityTransportedNewStateLookupTemplate_matches_first
        modeCode modeStep formulaCode formulaStep
        assignmentCodeCode assignmentCodeStep
        assignmentStepCode assignmentStepStep
        boundName modeName formulaName assignmentCodeName assignmentStepName
        index rowMode rowFormula rowAssignmentCode rowAssignmentStep
        hmodeFresh hformulaFresh
        hassignmentCodeFresh hassignmentStepFresh)
      (coqFourStateTableAppendEqualityRowLookupTemplate_matches_second
        modeName formulaName assignmentCodeName assignmentStepName
        index rowMode rowFormula rowAssignmentCode rowAssignmentStep)
      hfixedLookup hrowLookup).
Qed.

(** Name the four roots returned by the family compiler and expose their
    conclusions as literal equalities.  This is the client-facing form used
    by the successor-row equality branch: every comparison inhabits the same
    newly extended witnessed tail, so subsequent conjunction and equality
    transport can be performed without another context reconciliation. *)
Theorem
    raw_codedPALocalProofOf_four_state_table_append_equality_four_equalities_on_witnessed_tail_under_prefix :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall baseWitnessList baseContext prefix
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    boundName modeName formulaName assignmentCodeName assignmentStepName
    index rowMode rowFormula rowAssignmentCode rowAssignmentStep
    fixedLookupRoot rowLookupRoot,
  RawCodedTemplatePrefixAtomicallyAdequate M translation prefix ->
  RawCodedPAAxiomWitnessContext M baseWitnessList baseContext ->
  modeName <> boundName ->
  formulaName <> boundName ->
  assignmentCodeName <> boundName ->
  assignmentStepName <> boundName ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail translation baseContext prefix)
    (rawTemplateFormula translation
      (coqFourStateTableAppendEqualityTransportedNewStateLookupTemplate
        boundName index
        modeCode modeStep formulaCode formulaStep
        assignmentCodeCode assignmentCodeStep
        assignmentStepCode assignmentStepStep
        (ttParameter modeName) (ttParameter formulaName)
        (ttParameter assignmentCodeName) (ttParameter assignmentStepName)))
    fixedLookupRoot ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail translation baseContext prefix)
    (rawTemplateFormula translation
      (coqFourStateTableAppendEqualityRowLookupTemplate
        modeName formulaName assignmentCodeName assignmentStepName
        index rowMode rowFormula rowAssignmentCode rowAssignmentStep))
    rowLookupRoot ->
  exists (witnesses : StandardPAAxiomWitnessPrefix)
    modeEqualityRoot formulaEqualityRoot
    assignmentCodeEqualityRoot assignmentStepEqualityRoot,
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
        (tfEq rowMode (ttParameter modeName))) modeEqualityRoot /\
    RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation
        (rawStandardPAAxiomWitnessPrefixContextCode M
          witnesses baseContext) prefix)
      (rawTemplateFormula translation
        (tfEq rowFormula (ttParameter formulaName))) formulaEqualityRoot /\
    RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation
        (rawStandardPAAxiomWitnessPrefixContextCode M
          witnesses baseContext) prefix)
      (rawTemplateFormula translation
        (tfEq rowAssignmentCode (ttParameter assignmentCodeName)))
      assignmentCodeEqualityRoot /\
    RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation
        (rawStandardPAAxiomWitnessPrefixContextCode M
          witnesses baseContext) prefix)
      (rawTemplateFormula translation
        (tfEq rowAssignmentStep (ttParameter assignmentStepName)))
      assignmentStepEqualityRoot.
Proof.
  intros M hPA translation hagreement
    baseWitnessList baseContext prefix
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    boundName modeName formulaName assignmentCodeName assignmentStepName
    index rowMode rowFormula rowAssignmentCode rowAssignmentStep
    fixedLookupRoot rowLookupRoot
    hprefix hbase hmodeFresh hformulaFresh
    hassignmentCodeFresh hassignmentStepFresh
    hfixedLookup hrowLookup.
  destruct
    (raw_codedPALocalProofOf_four_state_table_append_equality_lookup_functionality_on_witnessed_tail_under_prefix
      M hPA translation hagreement
      baseWitnessList baseContext prefix
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      boundName modeName formulaName assignmentCodeName assignmentStepName
      index rowMode rowFormula rowAssignmentCode rowAssignmentStep
      fixedLookupRoot rowLookupRoot
      hprefix hbase hmodeFresh hformulaFresh
      hassignmentCodeFresh hassignmentStepFresh
      hfixedLookup hrowLookup)
    as (witnesses & equalityRoots & hextended & hequalities).
  inversion hequalities as
      [|modeArguments modeEqualityRoot remainingArguments1 remainingRoots1
        hmodeEquality hequalities1]; subst.
  inversion hequalities1 as
      [|formulaArguments formulaEqualityRoot
        remainingArguments2 remainingRoots2
        hformulaEquality hequalities2]; subst.
  inversion hequalities2 as
      [|assignmentCodeArguments assignmentCodeEqualityRoot
        remainingArguments3 remainingRoots3
        hassignmentCodeEquality hequalities3]; subst.
  inversion hequalities3 as
      [|assignmentStepArguments assignmentStepEqualityRoot
        remainingArguments4 remainingRoots4
        hassignmentStepEquality hequalities4]; subst.
  inversion hequalities4; subst.
  rewrite coqBetaLookupFunctionalityEqualityOf_eq in
    hmodeEquality, hformulaEquality,
    hassignmentCodeEquality, hassignmentStepEquality.
  cbn [coqFourStateTableAppendEqualityModeFunctionalityArguments
    coqFourStateTableAppendEqualityFormulaFunctionalityArguments
    coqFourStateTableAppendEqualityAssignmentCodeFunctionalityArguments
    coqFourStateTableAppendEqualityAssignmentStepFunctionalityArguments]
    in hmodeEquality, hformulaEquality,
      hassignmentCodeEquality, hassignmentStepEquality.
  exists witnesses, modeEqualityRoot, formulaEqualityRoot,
    assignmentCodeEqualityRoot, assignmentStepEqualityRoot.
  split; [exact hextended |].
  split; [exact hmodeEquality |].
  split; [exact hformulaEquality |].
  split; [exact hassignmentCodeEquality |].
  exact hassignmentStepEquality.
Qed.

(** The ordered parameter bindings changed by an equality-branch row. *)
Definition coqFourStateTableAppendEqualityFieldBindings
    (modeName formulaName assignmentCodeName assignmentStepName
      : TemplateParameterName)
    (rowMode rowFormula rowAssignmentCode rowAssignmentStep : TemplateTerm)
    : list (TemplateParameterName * TemplateTerm) :=
  [(modeName, rowMode); (formulaName, rowFormula);
   (assignmentCodeName, rowAssignmentCode);
   (assignmentStepName, rowAssignmentStep)].

(** ------------------------------------------------------------------
    Concrete closed-row production under the five traversal binders.

    Parameter names [2..5] are disjoint from the two level parameters used
    by the native Sigma/Pi row sources.  After the row index [#4] has been
    introduced, the four exposed state fields are literally [#3..#0]. *)

Definition coqFourStateTableAppendRowModeParameterName
    : TemplateParameterName := 2.
Definition coqFourStateTableAppendRowFormulaParameterName
    : TemplateParameterName := 3.
Definition coqFourStateTableAppendRowAssignmentCodeParameterName
    : TemplateParameterName := 4.
Definition coqFourStateTableAppendRowAssignmentStepParameterName
    : TemplateParameterName := 5.

Definition coqFourStateTableAppendConcreteRowFieldBindings
    : list (TemplateParameterName * TemplateTerm) :=
  coqFourStateTableAppendEqualityFieldBindings
    coqFourStateTableAppendRowModeParameterName
    coqFourStateTableAppendRowFormulaParameterName
    coqFourStateTableAppendRowAssignmentCodeParameterName
    coqFourStateTableAppendRowAssignmentStepParameterName
    (ttVar 3) (ttVar 2) (ttVar 1) (ttVar 0).

(** The mode split of [fixedLevelClosedSuccessorRowTermAt], with its two
    polarity bodies left abstract.  Those bodies may mention all four named
    row fields; finite replacement below traverses them as well. *)
Definition coqFourStateTableAppendNamedClosedRowProductionTemplate
    (sigmaProduction piProduction : TemplateFormula) : TemplateFormula :=
  tfOr
    (tfAnd
      (tfEq
        (ttParameter coqFourStateTableAppendRowModeParameterName) ttZero)
      sigmaProduction)
    (tfAnd
      (tfEq
        (ttParameter coqFourStateTableAppendRowModeParameterName)
        (ttSucc ttZero))
      piProduction).

Definition coqFourStateTableAppendConcreteClosedRowProductionTemplate
    (sigmaProduction piProduction : TemplateFormula) : TemplateFormula :=
  tfOr
    (tfAnd (tfEq (ttVar 3) ttZero)
      (templateFormulaReplaceParametersDirect
        coqFourStateTableAppendConcreteRowFieldBindings sigmaProduction))
    (tfAnd (tfEq (ttVar 3) (ttSucc ttZero))
      (templateFormulaReplaceParametersDirect
        coqFourStateTableAppendConcreteRowFieldBindings piProduction)).

(** The exact syntax identity required by the equality branch of the global
    successor traversal.  It is a computation over the fixed four-name
    namespace; the arbitrary polarity bodies need not be unfolded. *)
Theorem
    coqFourStateTableAppendNamedClosedRowProductionTemplate_replace_fields :
  forall sigmaProduction piProduction,
  templateFormulaReplaceParameters
    coqFourStateTableAppendConcreteRowFieldBindings
    (coqFourStateTableAppendNamedClosedRowProductionTemplate
      sigmaProduction piProduction) =
  coqFourStateTableAppendConcreteClosedRowProductionTemplate
    sigmaProduction piProduction.
Proof.
  intros sigmaProduction piProduction.
  rewrite templateFormulaReplaceParameters_eq_direct.
  reflexivity.
Qed.

(** The inherited traversal is universally quantified in the literal row
    order index, mode, formula, assignment code, assignment step. *)
Definition coqFourStateTableAppendConcreteRowVariables
    : list TemplateTerm :=
  [ttVar 4; ttVar 3; ttVar 2; ttVar 1; ttVar 0].

(** Compile the predecessor production from an inherited traversal root.
    The exact opening equation remains visible because the traversal body is
    supplied by the outer global-code client; all proof-root assembly is
    independent of that syntax. *)
Theorem
    raw_codedPALocalProofOf_four_state_table_append_inherited_row_production :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M)
    context inheritedTraversal below oldLookup result
    traversalRoot belowRoot oldLookupRoot,
  templateUniversalOpenMany inheritedTraversal
    coqFourStateTableAppendConcreteRowVariables =
    Some (tfImp below (tfImp oldLookup result)) ->
  RawCodedPALocalProofOf M context
    (rawTemplateFormula translation inheritedTraversal) traversalRoot ->
  RawCodedPALocalProofOf M context
    (rawTemplateFormula translation below) belowRoot ->
  RawCodedPALocalProofOf M context
    (rawTemplateFormula translation oldLookup) oldLookupRoot ->
  exists resultRoot,
    RawCodedPALocalProofOf M context
      (rawTemplateFormula translation result) resultRoot.
Proof.
  intros M hPA translation context inheritedTraversal
    below oldLookup result traversalRoot belowRoot oldLookupRoot
    hopen htraversal hbelow holdLookup.
  exact
    (raw_codedPALocalProofOf_templateUniversalOpenMany_impE2
      M hPA translation context inheritedTraversal
      coqFourStateTableAppendConcreteRowVariables
      below oldLookup result traversalRoot belowRoot oldLookupRoot
      hopen htraversal hbelow holdLookup).
Qed.

(** Proof roots consumed by the inherited predecessor production in one
    literal branch context. *)
Definition RawFourStateTableAppendInheritedProductionInputsAt
    (M : RawPAModel) (translation : RawCodedTemplateTranslation M)
    (context : M) (prefix : TemplateContext)
    (inheritedTraversal below oldLookup : TemplateFormula) : Prop :=
  exists traversalRoot belowRoot oldLookupRoot,
    RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation context prefix)
      (rawTemplateFormula translation inheritedTraversal) traversalRoot /\
    RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation context prefix)
      (rawTemplateFormula translation below) belowRoot /\
    RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation context prefix)
      (rawTemplateFormula translation oldLookup) oldLookupRoot.

Arguments RawFourStateTableAppendInheritedProductionInputsAt
  M translation context prefix inheritedTraversal below oldLookup
  : clear implicits.

(** The two predecessor proofs that genuinely exist before the arithmetic
    branch is chosen. *)
Definition RawFourStateTableAppendInheritedLocalRootsAt
    (M : RawPAModel) (translation : RawCodedTemplateTranslation M)
    (context : M) (prefix : TemplateContext)
    (inheritedTraversal oldLookup : TemplateFormula) : Prop :=
  exists traversalRoot oldLookupRoot,
    RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation context prefix)
      (rawTemplateFormula translation inheritedTraversal) traversalRoot /\
    RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation context prefix)
      (rawTemplateFormula translation oldLookup) oldLookupRoot.

Arguments RawFourStateTableAppendInheritedLocalRootsAt
  M translation context prefix inheritedTraversal oldLookup
  : clear implicits.

(** Transport the two roots chosen before the arithmetic case split to the
    current dependency-ordered witnessed-tail extension. *)
Theorem raw_fourStateTableAppendInheritedLocalRootsAt_transport :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M)
    baseWitnessList baseContext sourceWitnessList sourceContext prefix
    inheritedTraversal oldLookup,
  RawCodedPAAxiomWitnessContext M baseWitnessList baseContext ->
  RawCodedPAAxiomWitnessContext M sourceWitnessList sourceContext ->
  RawContextListIncluded M baseContext sourceContext ->
  RawFourStateTableAppendInheritedLocalRootsAt M translation
    baseContext prefix inheritedTraversal oldLookup ->
  RawFourStateTableAppendInheritedLocalRootsAt M translation
    sourceContext prefix inheritedTraversal oldLookup.
Proof.
  intros M hPA translation
    baseWitnessList baseContext sourceWitnessList sourceContext prefix
    inheritedTraversal oldLookup hbase hsource hincluded
    (traversalRoot & oldLookupRoot & htraversal & holdLookup).
  destruct
    (raw_codedPALocalProof_sameTemplatePrefix_witnessedTail_transport
      M hPA translation
      baseWitnessList baseContext sourceWitnessList sourceContext prefix
      (rawTemplateFormula translation inheritedTraversal)
      traversalRoot hbase hsource hincluded htraversal)
    as [transportedTraversalRoot htransportedTraversal].
  destruct
    (raw_codedPALocalProof_sameTemplatePrefix_witnessedTail_transport
      M hPA translation
      baseWitnessList baseContext sourceWitnessList sourceContext prefix
      (rawTemplateFormula translation oldLookup)
      oldLookupRoot hbase hsource hincluded holdLookup)
    as [transportedOldLookupRoot htransportedOldLookup].
  exists transportedTraversalRoot, transportedOldLookupRoot.
  split; assumption.
Qed.

(** Construct the predecessor package from proofs available before the case
    split.  The adequate [below] formula is inserted once above the shared
    prefix; inherited traversal and lookup roots are rebuilt beneath it, and
    the bound premise is the literal represented assumption leaf. *)
Theorem
    raw_fourStateTableAppendInheritedProductionInputsAt_of_local_roots :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M)
    sourceWitnessList sourceContext prefix inheritedTraversal below oldLookup
    traversalRoot oldLookupRoot,
  RawCodedPAAxiomWitnessContext M sourceWitnessList sourceContext ->
  RawCodedFormulaAtomicallyAdequate M
    (rawTemplateFormula translation below) ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail translation sourceContext prefix)
    (rawTemplateFormula translation inheritedTraversal) traversalRoot ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail translation sourceContext prefix)
    (rawTemplateFormula translation oldLookup) oldLookupRoot ->
  RawFourStateTableAppendInheritedProductionInputsAt M translation
    sourceContext (below :: prefix)
    inheritedTraversal below oldLookup.
Proof.
  intros M hPA translation sourceWitnessList sourceContext prefix
    inheritedTraversal below oldLookup traversalRoot oldLookupRoot
    hsource hbelowAdequate htraversal holdLookup.
  set (fullContext :=
    rawTemplateContextCodeOnTail translation sourceContext prefix).
  assert (hfullContext : RawContextListRealizable M fullContext).
  {
    unfold fullContext.
    apply (raw_templateContextOnTail_realizable M hPA).
    exact (raw_codedPAAxiomWitnessContext_context_realizable M
      sourceWitnessList sourceContext hsource).
  }
  assert (hbelowPrefix :
      RawCodedTemplatePrefixAtomicallyAdequate M translation [below]).
  {
    intros formula [hformula | hformula].
    - subst formula. exact hbelowAdequate.
    - contradiction.
  }
  destruct (raw_codedPALocalProof_templatePrefix
    M hPA translation fullContext [below]
    (rawTemplateFormula translation inheritedTraversal)
    traversalRoot hfullContext hbelowPrefix htraversal)
    as [shiftedTraversalRoot hshiftedTraversal].
  destruct (raw_codedPALocalProof_templatePrefix
    M hPA translation fullContext [below]
    (rawTemplateFormula translation oldLookup)
    oldLookupRoot hfullContext hbelowPrefix holdLookup)
    as [shiftedLookupRoot hshiftedLookup].
  pose proof (raw_codedPALocalProofOf_assumption M hPA
    fullContext (rawTemplateFormula translation below) hfullContext)
    as hbelowAssumption.
  exists shiftedTraversalRoot,
    (rawProofAssumptionRoot M
      (rawListNode M (rawTemplateFormula translation below) fullContext)
      (rawTemplateFormula translation below)),
    shiftedLookupRoot.
  cbn in hshiftedTraversal, hshiftedLookup |- *.
  split; [exact hshiftedTraversal |].
  split; [exact hbelowAssumption | exact hshiftedLookup].
Qed.

Corollary
    raw_fourStateTableAppendInheritedProductionInputsAt_of_local_root_package :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M)
    sourceWitnessList sourceContext prefix inheritedTraversal below oldLookup,
  RawCodedPAAxiomWitnessContext M sourceWitnessList sourceContext ->
  RawCodedFormulaAtomicallyAdequate M
    (rawTemplateFormula translation below) ->
  RawFourStateTableAppendInheritedLocalRootsAt M translation
    sourceContext prefix inheritedTraversal oldLookup ->
  RawFourStateTableAppendInheritedProductionInputsAt M translation
    sourceContext (below :: prefix)
    inheritedTraversal below oldLookup.
Proof.
  intros M hPA translation sourceWitnessList sourceContext prefix
    inheritedTraversal below oldLookup hsource hbelow
    (traversalRoot & oldLookupRoot & htraversal & holdLookup).
  exact
    (raw_fourStateTableAppendInheritedProductionInputsAt_of_local_roots
      M hPA translation sourceWitnessList sourceContext prefix
      inheritedTraversal below oldLookup traversalRoot oldLookupRoot
      hsource hbelow htraversal holdLookup).
Qed.

(** Package the five-open/two-application result as a no-growth callback.
    This is the exact predecessor dual of the growing equality assembler. *)
Theorem
    raw_codedPALocalProofOf_four_state_table_append_inherited_row_production_growing_tail :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M)
    sourceWitnessList sourceContext prefix
    inheritedTraversal below oldLookup result,
  RawCodedPAAxiomWitnessContext M sourceWitnessList sourceContext ->
  templateUniversalOpenMany inheritedTraversal
    coqFourStateTableAppendConcreteRowVariables =
    Some (tfImp below (tfImp oldLookup result)) ->
  RawFourStateTableAppendInheritedProductionInputsAt M translation
    sourceContext prefix inheritedTraversal below oldLookup ->
  RawCodedPAGrowingTemplateLocalProofAt M translation
    sourceWitnessList sourceContext prefix
    (rawTemplateFormula translation result).
Proof.
  intros M hPA translation sourceWitnessList sourceContext prefix
    inheritedTraversal below oldLookup result hsource hopen
    (traversalRoot & belowRoot & oldLookupRoot &
      htraversal & hbelow & holdLookup).
  destruct
    (raw_codedPALocalProofOf_four_state_table_append_inherited_row_production
      M hPA translation
      (rawTemplateContextCodeOnTail translation sourceContext prefix)
      inheritedTraversal below oldLookup result
      traversalRoot belowRoot oldLookupRoot
      hopen htraversal hbelow holdLookup)
    as [resultRoot hresult].
  unfold RawCodedPAGrowingTemplateLocalProofAt.
  exists sourceWitnessList, sourceContext, resultRoot.
  split; [exact hsource |].
  split; [apply raw_contextListIncluded_refl | exact hresult].
Qed.

(** Assemble the equality branch for an arbitrary production over the four
    fixed appended fields.  The production root is first weakened across the
    single witness extension chosen by beta functionality.  The four literal
    field equalities are then consumed in order by the generic represented
    parameter-transport compiler. *)
Theorem
    raw_codedPALocalProofOf_four_state_table_append_equality_transport_result_on_witnessed_tail_under_prefix :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall baseWitnessList baseContext prefix
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    boundName modeName formulaName assignmentCodeName assignmentStepName
    index rowMode rowFormula rowAssignmentCode rowAssignmentStep
    fixedLookupRoot rowLookupRoot fixedResult fixedResultRoot,
  RawCodedTemplatePrefixAtomicallyAdequate M translation prefix ->
  RawCodedPAAxiomWitnessContext M baseWitnessList baseContext ->
  modeName <> boundName ->
  formulaName <> boundName ->
  assignmentCodeName <> boundName ->
  assignmentStepName <> boundName ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail translation baseContext prefix)
    (rawTemplateFormula translation
      (coqFourStateTableAppendEqualityTransportedNewStateLookupTemplate
        boundName index
        modeCode modeStep formulaCode formulaStep
        assignmentCodeCode assignmentCodeStep
        assignmentStepCode assignmentStepStep
        (ttParameter modeName) (ttParameter formulaName)
        (ttParameter assignmentCodeName) (ttParameter assignmentStepName)))
    fixedLookupRoot ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail translation baseContext prefix)
    (rawTemplateFormula translation
      (coqFourStateTableAppendEqualityRowLookupTemplate
        modeName formulaName assignmentCodeName assignmentStepName
        index rowMode rowFormula rowAssignmentCode rowAssignmentStep))
    rowLookupRoot ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail translation baseContext prefix)
    (rawTemplateFormula translation fixedResult) fixedResultRoot ->
  exists (witnesses : StandardPAAxiomWitnessPrefix) resultRoot,
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
        (templateFormulaReplaceParameters
          (coqFourStateTableAppendEqualityFieldBindings
            modeName formulaName assignmentCodeName assignmentStepName
            rowMode rowFormula rowAssignmentCode rowAssignmentStep)
          fixedResult)) resultRoot.
Proof.
  intros M hPA translation hagreement
    baseWitnessList baseContext prefix
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    boundName modeName formulaName assignmentCodeName assignmentStepName
    index rowMode rowFormula rowAssignmentCode rowAssignmentStep
    fixedLookupRoot rowLookupRoot fixedResult fixedResultRoot
    hprefix hbase hmodeFresh hformulaFresh
    hassignmentCodeFresh hassignmentStepFresh
    hfixedLookup hrowLookup hfixedResult.
  destruct
    (raw_codedPALocalProofOf_four_state_table_append_equality_four_equalities_on_witnessed_tail_under_prefix
      M hPA translation hagreement
      baseWitnessList baseContext prefix
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      boundName modeName formulaName assignmentCodeName assignmentStepName
      index rowMode rowFormula rowAssignmentCode rowAssignmentStep
      fixedLookupRoot rowLookupRoot
      hprefix hbase hmodeFresh hformulaFresh
      hassignmentCodeFresh hassignmentStepFresh
      hfixedLookup hrowLookup)
    as (witnesses & modeEqualityRoot & formulaEqualityRoot &
        assignmentCodeEqualityRoot & assignmentStepEqualityRoot &
        hextended & hmodeEquality & hformulaEquality &
        hassignmentCodeEquality & hassignmentStepEquality).
  destruct
    (raw_codedPALocalProof_sameTemplatePrefix_witnessedTail_transport
      M hPA translation
      baseWitnessList baseContext
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        witnesses baseWitnessList)
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses baseContext)
      prefix (rawTemplateFormula translation fixedResult) fixedResultRoot
      hbase hextended
      (raw_standardPAAxiomWitnessPrefixContextCode_target_included
        M hPA witnesses baseContext)
      hfixedResult)
    as [transportedResultRoot htransportedResult].
  assert (hequalityRoots : Forall2
      (fun binding equalityRoot =>
        RawCodedPALocalProofOf M
          (rawTemplateContextCodeOnTail translation
            (rawStandardPAAxiomWitnessPrefixContextCode M
              witnesses baseContext) prefix)
          (rawTemplateFormula translation
            (tfEq (snd binding) (ttParameter (fst binding)))) equalityRoot)
      (coqFourStateTableAppendEqualityFieldBindings
        modeName formulaName assignmentCodeName assignmentStepName
        rowMode rowFormula rowAssignmentCode rowAssignmentStep)
      [modeEqualityRoot; formulaEqualityRoot;
       assignmentCodeEqualityRoot; assignmentStepEqualityRoot]).
  {
    unfold coqFourStateTableAppendEqualityFieldBindings.
    constructor; [exact hmodeEquality |].
    constructor; [exact hformulaEquality |].
    constructor; [exact hassignmentCodeEquality |].
    constructor; [exact hassignmentStepEquality |].
    constructor.
  }
  destruct
    (raw_codedPALocalProofOf_templateParameterTransports_reverse
      M hPA translation
      (rawTemplateContextCodeOnTail translation
        (rawStandardPAAxiomWitnessPrefixContextCode M
          witnesses baseContext) prefix)
      (coqFourStateTableAppendEqualityFieldBindings
        modeName formulaName assignmentCodeName assignmentStepName
        rowMode rowFormula rowAssignmentCode rowAssignmentStep)
      [modeEqualityRoot; formulaEqualityRoot;
       assignmentCodeEqualityRoot; assignmentStepEqualityRoot]
      fixedResult transportedResultRoot
      hequalityRoots htransportedResult)
    as [resultRoot hresult].
  exists witnesses, resultRoot.
  split; assumption.
Qed.

(** Growing-tail packaging of the completed equality branch.  This is the
    exact callback shape consumed by the dependency-ordered successor-bound
    eliminator: beta functionality may select its finite PA theorem batch,
    and the resulting proof advertises the honest inclusion of the caller's
    witness tail into that enlarged context. *)
Corollary
    raw_codedPALocalProofOf_four_state_table_append_equality_transport_result_growing_tail_under_prefix :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall sourceWitnessList sourceContext prefix
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    boundName modeName formulaName assignmentCodeName assignmentStepName
    index rowMode rowFormula rowAssignmentCode rowAssignmentStep
    fixedLookupRoot rowLookupRoot fixedResult fixedResultRoot,
  RawCodedTemplatePrefixAtomicallyAdequate M translation prefix ->
  RawCodedPAAxiomWitnessContext M sourceWitnessList sourceContext ->
  modeName <> boundName ->
  formulaName <> boundName ->
  assignmentCodeName <> boundName ->
  assignmentStepName <> boundName ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail translation sourceContext prefix)
    (rawTemplateFormula translation
      (coqFourStateTableAppendEqualityTransportedNewStateLookupTemplate
        boundName index
        modeCode modeStep formulaCode formulaStep
        assignmentCodeCode assignmentCodeStep
        assignmentStepCode assignmentStepStep
        (ttParameter modeName) (ttParameter formulaName)
        (ttParameter assignmentCodeName) (ttParameter assignmentStepName)))
    fixedLookupRoot ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail translation sourceContext prefix)
    (rawTemplateFormula translation
      (coqFourStateTableAppendEqualityRowLookupTemplate
        modeName formulaName assignmentCodeName assignmentStepName
        index rowMode rowFormula rowAssignmentCode rowAssignmentStep))
    rowLookupRoot ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail translation sourceContext prefix)
    (rawTemplateFormula translation fixedResult) fixedResultRoot ->
  RawCodedPAGrowingTemplateLocalProofAt M translation
    sourceWitnessList sourceContext prefix
    (rawTemplateFormula translation
      (templateFormulaReplaceParameters
        (coqFourStateTableAppendEqualityFieldBindings
          modeName formulaName assignmentCodeName assignmentStepName
          rowMode rowFormula rowAssignmentCode rowAssignmentStep)
        fixedResult)).
Proof.
  intros M hPA translation hagreement
    sourceWitnessList sourceContext prefix
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    boundName modeName formulaName assignmentCodeName assignmentStepName
    index rowMode rowFormula rowAssignmentCode rowAssignmentStep
    fixedLookupRoot rowLookupRoot fixedResult fixedResultRoot
    hprefix hsource hmodeFresh hformulaFresh
    hassignmentCodeFresh hassignmentStepFresh
    hfixedLookup hrowLookup hfixedResult.
  destruct
    (raw_codedPALocalProofOf_four_state_table_append_equality_transport_result_on_witnessed_tail_under_prefix
      M hPA translation hagreement
      sourceWitnessList sourceContext prefix
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      boundName modeName formulaName assignmentCodeName assignmentStepName
      index rowMode rowFormula rowAssignmentCode rowAssignmentStep
      fixedLookupRoot rowLookupRoot fixedResult fixedResultRoot
      hprefix hsource hmodeFresh hformulaFresh
      hassignmentCodeFresh hassignmentStepFresh
      hfixedLookup hrowLookup hfixedResult)
    as (witnesses & resultRoot & hextended & hresult).
  unfold RawCodedPAGrowingTemplateLocalProofAt.
  exists
    (rawStandardPAAxiomWitnessPrefixWitnessListCode M
      witnesses sourceWitnessList),
    (rawStandardPAAxiomWitnessPrefixContextCode M
      witnesses sourceContext),
    resultRoot.
  split; [exact hextended |].
  split.
  - exact (raw_standardPAAxiomWitnessPrefixContextCode_target_included
      M hPA witnesses sourceContext).
  - exact hresult.
Qed.

(** The three equality-branch productions that must coexist under its
    literal arithmetic head.  Naming this package keeps the complete case
    compiler independent of the proof-root choices made by its client. *)
Definition RawFourStateTableAppendEqualityProductionInputsAt
    (M : RawPAModel) (translation : RawCodedTemplateTranslation M)
    (context : M) (prefix : TemplateContext)
    (modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep : TemplateTerm)
    (boundName modeName formulaName assignmentCodeName assignmentStepName
      : TemplateParameterName)
    (index rowMode rowFormula rowAssignmentCode rowAssignmentStep
      : TemplateTerm)
    (fixedResult : TemplateFormula) : Prop :=
  exists fixedLookupRoot rowLookupRoot fixedResultRoot,
    RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation context prefix)
      (rawTemplateFormula translation
        (coqFourStateTableAppendEqualityTransportedNewStateLookupTemplate
          boundName index
          modeCode modeStep formulaCode formulaStep
          assignmentCodeCode assignmentCodeStep
          assignmentStepCode assignmentStepStep
          (ttParameter modeName) (ttParameter formulaName)
          (ttParameter assignmentCodeName)
          (ttParameter assignmentStepName))) fixedLookupRoot /\
    RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation context prefix)
      (rawTemplateFormula translation
        (coqFourStateTableAppendEqualityRowLookupTemplate
          modeName formulaName assignmentCodeName assignmentStepName
          index rowMode rowFormula rowAssignmentCode rowAssignmentStep))
      rowLookupRoot /\
    RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation context prefix)
      (rawTemplateFormula translation fixedResult) fixedResultRoot.

Arguments RawFourStateTableAppendEqualityProductionInputsAt
  M translation context prefix
  modeCode modeStep formulaCode formulaStep
  assignmentCodeCode assignmentCodeStep
  assignmentStepCode assignmentStepStep
  boundName modeName formulaName assignmentCodeName assignmentStepName
  index rowMode rowFormula rowAssignmentCode rowAssignmentStep fixedResult
  : clear implicits.

(** Transport all three equality-production roots along a witnessed-tail
    inclusion.  In particular, the operational fixed-bound lookup can be
    constructed once over a decoded base witness list and then reused in
    every dependency-ordered extension selected by the case compiler. *)
Theorem raw_fourStateTableAppendEqualityProductionInputsAt_transport :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M)
    baseWitnessList baseContext sourceWitnessList sourceContext prefix
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    boundName modeName formulaName assignmentCodeName assignmentStepName
    index rowMode rowFormula rowAssignmentCode rowAssignmentStep fixedResult,
  RawCodedPAAxiomWitnessContext M baseWitnessList baseContext ->
  RawCodedPAAxiomWitnessContext M sourceWitnessList sourceContext ->
  RawContextListIncluded M baseContext sourceContext ->
  RawFourStateTableAppendEqualityProductionInputsAt M translation
    baseContext prefix
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    boundName modeName formulaName assignmentCodeName assignmentStepName
    index rowMode rowFormula rowAssignmentCode rowAssignmentStep fixedResult ->
  RawFourStateTableAppendEqualityProductionInputsAt M translation
    sourceContext prefix
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    boundName modeName formulaName assignmentCodeName assignmentStepName
    index rowMode rowFormula rowAssignmentCode rowAssignmentStep fixedResult.
Proof.
  intros M hPA translation
    baseWitnessList baseContext sourceWitnessList sourceContext prefix
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    boundName modeName formulaName assignmentCodeName assignmentStepName
    index rowMode rowFormula rowAssignmentCode rowAssignmentStep fixedResult
    hbase hsource hincluded
    (fixedLookupRoot & rowLookupRoot & fixedResultRoot &
      hfixedLookup & hrowLookup & hfixedResult).
  destruct
    (raw_codedPALocalProof_sameTemplatePrefix_witnessedTail_transport
      M hPA translation
      baseWitnessList baseContext sourceWitnessList sourceContext prefix
      (rawTemplateFormula translation
        (coqFourStateTableAppendEqualityTransportedNewStateLookupTemplate
          boundName index
          modeCode modeStep formulaCode formulaStep
          assignmentCodeCode assignmentCodeStep
          assignmentStepCode assignmentStepStep
          (ttParameter modeName) (ttParameter formulaName)
          (ttParameter assignmentCodeName)
          (ttParameter assignmentStepName)))
      fixedLookupRoot hbase hsource hincluded hfixedLookup)
    as [transportedFixedLookupRoot htransportedFixedLookup].
  destruct
    (raw_codedPALocalProof_sameTemplatePrefix_witnessedTail_transport
      M hPA translation
      baseWitnessList baseContext sourceWitnessList sourceContext prefix
      (rawTemplateFormula translation
        (coqFourStateTableAppendEqualityRowLookupTemplate
          modeName formulaName assignmentCodeName assignmentStepName
          index rowMode rowFormula rowAssignmentCode rowAssignmentStep))
      rowLookupRoot hbase hsource hincluded hrowLookup)
    as [transportedRowLookupRoot htransportedRowLookup].
  destruct
    (raw_codedPALocalProof_sameTemplatePrefix_witnessedTail_transport
      M hPA translation
      baseWitnessList baseContext sourceWitnessList sourceContext prefix
      (rawTemplateFormula translation fixedResult)
      fixedResultRoot hbase hsource hincluded hfixedResult)
    as [transportedFixedResultRoot htransportedFixedResult].
  exists transportedFixedLookupRoot,
    transportedRowLookupRoot, transportedFixedResultRoot.
  split; [exact htransportedFixedLookup |].
  split; [exact htransportedRowLookup | exact htransportedFixedResult].
Qed.

(** Close one complete appended-row production by represented case
    elimination.  The predecessor compiler is intentionally abstract over
    the particular row predicate; the equality branch is concrete and uses
    the four synchronized beta lookups plus represented parameter transport.
    Both callbacks may grow the witnessed PA tail, and the generic growing
    eliminator reconciles their contexts before constructing [OrE]. *)
Theorem
    raw_codedPALocalProofOf_four_state_table_append_row_production_cases_on_growing_witnessed_tail_under_prefix :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall baseWitnessList baseContext prefix
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    boundName modeName formulaName assignmentCodeName assignmentStepName
    index rowBound rowMode rowFormula rowAssignmentCode rowAssignmentStep
    antecedentRoot fixedResult,
  let result := templateFormulaReplaceParameters
    (coqFourStateTableAppendEqualityFieldBindings
      modeName formulaName assignmentCodeName assignmentStepName
      rowMode rowFormula rowAssignmentCode rowAssignmentStep)
    fixedResult in
  RawCodedTemplatePrefixAtomicallyAdequate M translation prefix ->
  RawCodedFormulaAtomicallyAdequate M
    (rawTemplateFormula translation
      (coqLtSuccCasesEqualTemplate index rowBound)) ->
  RawCodedPAAxiomWitnessContext M baseWitnessList baseContext ->
  modeName <> boundName ->
  formulaName <> boundName ->
  assignmentCodeName <> boundName ->
  assignmentStepName <> boundName ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail translation baseContext prefix)
    (rawTemplateFormula translation
      (coqLtSuccCasesAntecedentTemplate index rowBound)) antecedentRoot ->
  (forall sourceWitnessList sourceContext,
    RawCodedPAAxiomWitnessContext M sourceWitnessList sourceContext ->
    RawCodedPAGrowingTemplateLocalProofAt M translation
      sourceWitnessList sourceContext
      (coqLtSuccCasesBelowTemplate index rowBound :: prefix)
      (rawTemplateFormula translation result)) ->
  (forall sourceWitnessList sourceContext,
    RawCodedPAAxiomWitnessContext M sourceWitnessList sourceContext ->
    RawFourStateTableAppendEqualityProductionInputsAt M translation
      sourceContext
      (coqLtSuccCasesEqualTemplate index rowBound :: prefix)
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      boundName modeName formulaName assignmentCodeName assignmentStepName
      index rowMode rowFormula rowAssignmentCode rowAssignmentStep
      fixedResult) ->
  RawCodedPAGrowingTemplateLocalProofAt M translation
    baseWitnessList baseContext prefix
    (rawTemplateFormula translation result).
Proof.
  intros M hPA translation hagreement
    baseWitnessList baseContext prefix
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    boundName modeName formulaName assignmentCodeName assignmentStepName
    index rowBound rowMode rowFormula rowAssignmentCode rowAssignmentStep
    antecedentRoot fixedResult result
    hprefix hequalHead hbase
    hmodeFresh hformulaFresh hassignmentCodeFresh hassignmentStepFresh
    hantecedent hbelowBranch hequalInputs.
  cbn zeta in *.
  eapply
    (raw_codedPALocalProofOf_lt_succ_cases_eliminate_on_growing_witnessed_tail_under_prefix
      M hPA translation hagreement
      baseWitnessList baseContext prefix index rowBound antecedentRoot
      (rawTemplateFormula translation
        (templateFormulaReplaceParameters
          (coqFourStateTableAppendEqualityFieldBindings
            modeName formulaName assignmentCodeName assignmentStepName
            rowMode rowFormula rowAssignmentCode rowAssignmentStep)
          fixedResult))).
  - exact hprefix.
  - exact hbase.
  - exact hantecedent.
  - exact hbelowBranch.
  - intros sourceWitnessList sourceContext hsource.
    destruct (hequalInputs sourceWitnessList sourceContext hsource)
      as (fixedLookupRoot & rowLookupRoot & fixedResultRoot &
          hfixedLookup & hrowLookup & hfixedResultRoot).
    assert (hequalPrefix :
        RawCodedTemplatePrefixAtomicallyAdequate M translation
          (coqLtSuccCasesEqualTemplate index rowBound :: prefix)).
    {
      intros formula [hformula | hformula].
      - subst formula. exact hequalHead.
      - exact (hprefix formula hformula).
    }
    exact
      (raw_codedPALocalProofOf_four_state_table_append_equality_transport_result_growing_tail_under_prefix
        M hPA translation hagreement
        sourceWitnessList sourceContext
        (coqLtSuccCasesEqualTemplate index rowBound :: prefix)
        modeCode modeStep formulaCode formulaStep
        assignmentCodeCode assignmentCodeStep
        assignmentStepCode assignmentStepStep
        boundName modeName formulaName assignmentCodeName assignmentStepName
        index rowMode rowFormula rowAssignmentCode rowAssignmentStep
        fixedLookupRoot rowLookupRoot fixedResult fixedResultRoot
        hequalPrefix hsource
        hmodeFresh hformulaFresh hassignmentCodeFresh hassignmentStepFresh
        hfixedLookup hrowLookup hfixedResultRoot).
Qed.

(** Base-aware form of the complete row case compiler.  The two callbacks
    are required only on dependency-ordered extensions of [baseContext], and
    receive the inclusion proof that lets them transport pre-split roots. *)
Theorem
    raw_codedPALocalProofOf_four_state_table_append_row_production_cases_on_base_included_growing_witnessed_tail_under_prefix :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall baseWitnessList baseContext prefix
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    boundName modeName formulaName assignmentCodeName assignmentStepName
    index rowBound rowMode rowFormula rowAssignmentCode rowAssignmentStep
    antecedentRoot fixedResult,
  let result := templateFormulaReplaceParameters
    (coqFourStateTableAppendEqualityFieldBindings
      modeName formulaName assignmentCodeName assignmentStepName
      rowMode rowFormula rowAssignmentCode rowAssignmentStep)
    fixedResult in
  RawCodedTemplatePrefixAtomicallyAdequate M translation prefix ->
  RawCodedFormulaAtomicallyAdequate M
    (rawTemplateFormula translation
      (coqLtSuccCasesEqualTemplate index rowBound)) ->
  RawCodedPAAxiomWitnessContext M baseWitnessList baseContext ->
  modeName <> boundName ->
  formulaName <> boundName ->
  assignmentCodeName <> boundName ->
  assignmentStepName <> boundName ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail translation baseContext prefix)
    (rawTemplateFormula translation
      (coqLtSuccCasesAntecedentTemplate index rowBound)) antecedentRoot ->
  (forall sourceWitnessList sourceContext,
    RawCodedPAAxiomWitnessContext M sourceWitnessList sourceContext ->
    RawContextListIncluded M baseContext sourceContext ->
    RawCodedPAGrowingTemplateLocalProofAt M translation
      sourceWitnessList sourceContext
      (coqLtSuccCasesBelowTemplate index rowBound :: prefix)
      (rawTemplateFormula translation result)) ->
  (forall sourceWitnessList sourceContext,
    RawCodedPAAxiomWitnessContext M sourceWitnessList sourceContext ->
    RawContextListIncluded M baseContext sourceContext ->
    RawFourStateTableAppendEqualityProductionInputsAt M translation
      sourceContext
      (coqLtSuccCasesEqualTemplate index rowBound :: prefix)
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      boundName modeName formulaName assignmentCodeName assignmentStepName
      index rowMode rowFormula rowAssignmentCode rowAssignmentStep
      fixedResult) ->
  RawCodedPAGrowingTemplateLocalProofAt M translation
    baseWitnessList baseContext prefix
    (rawTemplateFormula translation result).
Proof.
  intros M hPA translation hagreement
    baseWitnessList baseContext prefix
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    boundName modeName formulaName assignmentCodeName assignmentStepName
    index rowBound rowMode rowFormula rowAssignmentCode rowAssignmentStep
    antecedentRoot fixedResult result
    hprefix hequalHead hbase
    hmodeFresh hformulaFresh hassignmentCodeFresh hassignmentStepFresh
    hantecedent hbelowBranch hequalInputs.
  cbn zeta in *.
  eapply
    (raw_codedPALocalProofOf_lt_succ_cases_eliminate_on_base_included_growing_witnessed_tail_under_prefix
      M hPA translation hagreement
      baseWitnessList baseContext prefix index rowBound antecedentRoot
      (rawTemplateFormula translation
        (templateFormulaReplaceParameters
          (coqFourStateTableAppendEqualityFieldBindings
            modeName formulaName assignmentCodeName assignmentStepName
            rowMode rowFormula rowAssignmentCode rowAssignmentStep)
          fixedResult))).
  - exact hprefix.
  - exact hbase.
  - exact hantecedent.
  - exact hbelowBranch.
  - intros sourceWitnessList sourceContext hsource hbaseIncluded.
    destruct
      (hequalInputs sourceWitnessList sourceContext
        hsource hbaseIncluded)
      as (fixedLookupRoot & rowLookupRoot & fixedResultRoot &
          hfixedLookup & hrowLookup & hfixedResultRoot).
    assert (hequalPrefix :
        RawCodedTemplatePrefixAtomicallyAdequate M translation
          (coqLtSuccCasesEqualTemplate index rowBound :: prefix)).
    {
      intros formula [hformula | hformula].
      - subst formula. exact hequalHead.
      - exact (hprefix formula hformula).
    }
    exact
      (raw_codedPALocalProofOf_four_state_table_append_equality_transport_result_growing_tail_under_prefix
        M hPA translation hagreement
        sourceWitnessList sourceContext
        (coqLtSuccCasesEqualTemplate index rowBound :: prefix)
        modeCode modeStep formulaCode formulaStep
        assignmentCodeCode assignmentCodeStep
        assignmentStepCode assignmentStepStep
        boundName modeName formulaName assignmentCodeName assignmentStepName
        index rowMode rowFormula rowAssignmentCode rowAssignmentStep
        fixedLookupRoot rowLookupRoot fixedResult fixedResultRoot
        hequalPrefix hsource
        hmodeFresh hformulaFresh hassignmentCodeFresh hassignmentStepFresh
        hfixedLookup hrowLookup hfixedResultRoot).
Qed.

(** Concrete global-row client.  The five traversal variables are fixed to
    [index, mode, formula, assignmentCode, assignmentStep = #4..#0], and the
    named production is normalized to the literal polarity split returned to
    the caller.  Only the two genuine branch producers remain as inputs. *)
Theorem
    raw_codedPALocalProofOf_four_state_table_append_concrete_closed_row_cases_on_growing_witnessed_tail_under_prefix :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall baseWitnessList baseContext prefix
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    boundName rowBound antecedentRoot sigmaProduction piProduction,
  let fixedResult :=
    coqFourStateTableAppendNamedClosedRowProductionTemplate
      sigmaProduction piProduction in
  let result :=
    coqFourStateTableAppendConcreteClosedRowProductionTemplate
      sigmaProduction piProduction in
  RawCodedTemplatePrefixAtomicallyAdequate M translation prefix ->
  RawCodedFormulaAtomicallyAdequate M
    (rawTemplateFormula translation
      (coqLtSuccCasesEqualTemplate (ttVar 4) rowBound)) ->
  RawCodedPAAxiomWitnessContext M baseWitnessList baseContext ->
  coqFourStateTableAppendRowModeParameterName <> boundName ->
  coqFourStateTableAppendRowFormulaParameterName <> boundName ->
  coqFourStateTableAppendRowAssignmentCodeParameterName <> boundName ->
  coqFourStateTableAppendRowAssignmentStepParameterName <> boundName ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail translation baseContext prefix)
    (rawTemplateFormula translation
      (coqLtSuccCasesAntecedentTemplate (ttVar 4) rowBound))
    antecedentRoot ->
  (forall sourceWitnessList sourceContext,
    RawCodedPAAxiomWitnessContext M sourceWitnessList sourceContext ->
    RawCodedPAGrowingTemplateLocalProofAt M translation
      sourceWitnessList sourceContext
      (coqLtSuccCasesBelowTemplate (ttVar 4) rowBound :: prefix)
      (rawTemplateFormula translation result)) ->
  (forall sourceWitnessList sourceContext,
    RawCodedPAAxiomWitnessContext M sourceWitnessList sourceContext ->
    RawFourStateTableAppendEqualityProductionInputsAt M translation
      sourceContext
      (coqLtSuccCasesEqualTemplate (ttVar 4) rowBound :: prefix)
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      boundName
      coqFourStateTableAppendRowModeParameterName
      coqFourStateTableAppendRowFormulaParameterName
      coqFourStateTableAppendRowAssignmentCodeParameterName
      coqFourStateTableAppendRowAssignmentStepParameterName
      (ttVar 4) (ttVar 3) (ttVar 2) (ttVar 1) (ttVar 0)
      fixedResult) ->
  RawCodedPAGrowingTemplateLocalProofAt M translation
    baseWitnessList baseContext prefix
    (rawTemplateFormula translation result).
Proof.
  intros M hPA translation hagreement
    baseWitnessList baseContext prefix
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    boundName rowBound antecedentRoot sigmaProduction piProduction
    fixedResult result hprefix hequalHead hbase
    hmodeFresh hformulaFresh hassignmentCodeFresh hassignmentStepFresh
    hantecedent hbelow hequalInputs.
  cbn zeta in *.
  assert (hsyntax :
      templateFormulaReplaceParameters
        coqFourStateTableAppendConcreteRowFieldBindings
        (coqFourStateTableAppendNamedClosedRowProductionTemplate
          sigmaProduction piProduction) =
      coqFourStateTableAppendConcreteClosedRowProductionTemplate
        sigmaProduction piProduction).
  {
    apply
      coqFourStateTableAppendNamedClosedRowProductionTemplate_replace_fields.
  }
  assert (hcode :
      rawTemplateFormula translation
        (templateFormulaReplaceParameters
          coqFourStateTableAppendConcreteRowFieldBindings
          (coqFourStateTableAppendNamedClosedRowProductionTemplate
            sigmaProduction piProduction)) =
      rawTemplateFormula translation
        (coqFourStateTableAppendConcreteClosedRowProductionTemplate
          sigmaProduction piProduction)).
  { now rewrite hsyntax. }
  assert (hbelowForNamed : forall sourceWitnessList sourceContext,
      RawCodedPAAxiomWitnessContext M sourceWitnessList sourceContext ->
      RawCodedPAGrowingTemplateLocalProofAt M translation
        sourceWitnessList sourceContext
        (coqLtSuccCasesBelowTemplate (ttVar 4) rowBound :: prefix)
        (rawTemplateFormula translation
          (templateFormulaReplaceParameters
            coqFourStateTableAppendConcreteRowFieldBindings
            (coqFourStateTableAppendNamedClosedRowProductionTemplate
              sigmaProduction piProduction)))).
  {
    intros sourceWitnessList sourceContext hsource.
    eapply raw_codedPAGrowingTemplateLocalProofAt_conclusion_eq.
    - symmetry. exact hcode.
    - exact (hbelow sourceWitnessList sourceContext hsource).
  }
  pose proof
    (raw_codedPALocalProofOf_four_state_table_append_row_production_cases_on_growing_witnessed_tail_under_prefix
      M hPA translation hagreement
      baseWitnessList baseContext prefix
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      boundName
      coqFourStateTableAppendRowModeParameterName
      coqFourStateTableAppendRowFormulaParameterName
      coqFourStateTableAppendRowAssignmentCodeParameterName
      coqFourStateTableAppendRowAssignmentStepParameterName
      (ttVar 4) rowBound (ttVar 3) (ttVar 2) (ttVar 1) (ttVar 0)
      antecedentRoot
      (coqFourStateTableAppendNamedClosedRowProductionTemplate
        sigmaProduction piProduction)
      hprefix hequalHead hbase
      hmodeFresh hformulaFresh hassignmentCodeFresh hassignmentStepFresh
      hantecedent hbelowForNamed hequalInputs) as hnamed.
  eapply raw_codedPAGrowingTemplateLocalProofAt_conclusion_eq.
  - exact hcode.
  - exact hnamed.
Qed.

(** Base-aware concrete closed-row client.  This is the specialization used
    when the branch products depend on roots already present in the initial
    witnessed tail. *)
Theorem
    raw_codedPALocalProofOf_four_state_table_append_concrete_closed_row_cases_on_base_included_growing_witnessed_tail_under_prefix :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall baseWitnessList baseContext prefix
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    boundName rowBound antecedentRoot sigmaProduction piProduction,
  let fixedResult :=
    coqFourStateTableAppendNamedClosedRowProductionTemplate
      sigmaProduction piProduction in
  let result :=
    coqFourStateTableAppendConcreteClosedRowProductionTemplate
      sigmaProduction piProduction in
  RawCodedTemplatePrefixAtomicallyAdequate M translation prefix ->
  RawCodedFormulaAtomicallyAdequate M
    (rawTemplateFormula translation
      (coqLtSuccCasesEqualTemplate (ttVar 4) rowBound)) ->
  RawCodedPAAxiomWitnessContext M baseWitnessList baseContext ->
  coqFourStateTableAppendRowModeParameterName <> boundName ->
  coqFourStateTableAppendRowFormulaParameterName <> boundName ->
  coqFourStateTableAppendRowAssignmentCodeParameterName <> boundName ->
  coqFourStateTableAppendRowAssignmentStepParameterName <> boundName ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail translation baseContext prefix)
    (rawTemplateFormula translation
      (coqLtSuccCasesAntecedentTemplate (ttVar 4) rowBound))
    antecedentRoot ->
  (forall sourceWitnessList sourceContext,
    RawCodedPAAxiomWitnessContext M sourceWitnessList sourceContext ->
    RawContextListIncluded M baseContext sourceContext ->
    RawCodedPAGrowingTemplateLocalProofAt M translation
      sourceWitnessList sourceContext
      (coqLtSuccCasesBelowTemplate (ttVar 4) rowBound :: prefix)
      (rawTemplateFormula translation result)) ->
  (forall sourceWitnessList sourceContext,
    RawCodedPAAxiomWitnessContext M sourceWitnessList sourceContext ->
    RawContextListIncluded M baseContext sourceContext ->
    RawFourStateTableAppendEqualityProductionInputsAt M translation
      sourceContext
      (coqLtSuccCasesEqualTemplate (ttVar 4) rowBound :: prefix)
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      boundName
      coqFourStateTableAppendRowModeParameterName
      coqFourStateTableAppendRowFormulaParameterName
      coqFourStateTableAppendRowAssignmentCodeParameterName
      coqFourStateTableAppendRowAssignmentStepParameterName
      (ttVar 4) (ttVar 3) (ttVar 2) (ttVar 1) (ttVar 0)
      fixedResult) ->
  RawCodedPAGrowingTemplateLocalProofAt M translation
    baseWitnessList baseContext prefix
    (rawTemplateFormula translation result).
Proof.
  intros M hPA translation hagreement
    baseWitnessList baseContext prefix
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    boundName rowBound antecedentRoot sigmaProduction piProduction
    fixedResult result hprefix hequalHead hbase
    hmodeFresh hformulaFresh hassignmentCodeFresh hassignmentStepFresh
    hantecedent hbelow hequalInputs.
  cbn zeta in *.
  assert (hsyntax :
      templateFormulaReplaceParameters
        coqFourStateTableAppendConcreteRowFieldBindings
        (coqFourStateTableAppendNamedClosedRowProductionTemplate
          sigmaProduction piProduction) =
      coqFourStateTableAppendConcreteClosedRowProductionTemplate
        sigmaProduction piProduction).
  {
    apply
      coqFourStateTableAppendNamedClosedRowProductionTemplate_replace_fields.
  }
  assert (hcode :
      rawTemplateFormula translation
        (templateFormulaReplaceParameters
          coqFourStateTableAppendConcreteRowFieldBindings
          (coqFourStateTableAppendNamedClosedRowProductionTemplate
            sigmaProduction piProduction)) =
      rawTemplateFormula translation
        (coqFourStateTableAppendConcreteClosedRowProductionTemplate
          sigmaProduction piProduction)).
  { now rewrite hsyntax. }
  assert (hbelowForNamed : forall sourceWitnessList sourceContext,
      RawCodedPAAxiomWitnessContext M sourceWitnessList sourceContext ->
      RawContextListIncluded M baseContext sourceContext ->
      RawCodedPAGrowingTemplateLocalProofAt M translation
        sourceWitnessList sourceContext
        (coqLtSuccCasesBelowTemplate (ttVar 4) rowBound :: prefix)
        (rawTemplateFormula translation
          (templateFormulaReplaceParameters
            coqFourStateTableAppendConcreteRowFieldBindings
            (coqFourStateTableAppendNamedClosedRowProductionTemplate
              sigmaProduction piProduction)))).
  {
    intros sourceWitnessList sourceContext hsource hbaseIncluded.
    eapply raw_codedPAGrowingTemplateLocalProofAt_conclusion_eq.
    - symmetry. exact hcode.
    - exact
        (hbelow sourceWitnessList sourceContext
          hsource hbaseIncluded).
  }
  pose proof
    (raw_codedPALocalProofOf_four_state_table_append_row_production_cases_on_base_included_growing_witnessed_tail_under_prefix
      M hPA translation hagreement
      baseWitnessList baseContext prefix
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      boundName
      coqFourStateTableAppendRowModeParameterName
      coqFourStateTableAppendRowFormulaParameterName
      coqFourStateTableAppendRowAssignmentCodeParameterName
      coqFourStateTableAppendRowAssignmentStepParameterName
      (ttVar 4) rowBound (ttVar 3) (ttVar 2) (ttVar 1) (ttVar 0)
      antecedentRoot
      (coqFourStateTableAppendNamedClosedRowProductionTemplate
        sigmaProduction piProduction)
      hprefix hequalHead hbase
      hmodeFresh hformulaFresh hassignmentCodeFresh hassignmentStepFresh
      hantecedent hbelowForNamed hequalInputs) as hnamed.
  eapply raw_codedPAGrowingTemplateLocalProofAt_conclusion_eq.
  - exact hcode.
  - exact hnamed.
Qed.

(** Fully staged predecessor client.  Instead of accepting an arbitrary
    below-branch callback, this endpoint opens the inherited five-variable
    traversal and applies its bound and old-lookup premises in the literal
    [i < b] branch context.  The equality branch remains the concrete beta
    functionality package assembled above. *)
Theorem
    raw_codedPALocalProofOf_four_state_table_append_concrete_closed_row_of_inherited_traversal_on_growing_witnessed_tail_under_prefix :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall baseWitnessList baseContext prefix
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    boundName rowBound antecedentRoot
    sigmaProduction piProduction inheritedTraversal oldLookup,
  let fixedResult :=
    coqFourStateTableAppendNamedClosedRowProductionTemplate
      sigmaProduction piProduction in
  let result :=
    coqFourStateTableAppendConcreteClosedRowProductionTemplate
      sigmaProduction piProduction in
  templateUniversalOpenMany inheritedTraversal
    coqFourStateTableAppendConcreteRowVariables =
    Some (tfImp
      (coqLtSuccCasesBelowTemplate (ttVar 4) rowBound)
      (tfImp oldLookup result)) ->
  RawCodedTemplatePrefixAtomicallyAdequate M translation prefix ->
  RawCodedFormulaAtomicallyAdequate M
    (rawTemplateFormula translation
      (coqLtSuccCasesEqualTemplate (ttVar 4) rowBound)) ->
  RawCodedPAAxiomWitnessContext M baseWitnessList baseContext ->
  coqFourStateTableAppendRowModeParameterName <> boundName ->
  coqFourStateTableAppendRowFormulaParameterName <> boundName ->
  coqFourStateTableAppendRowAssignmentCodeParameterName <> boundName ->
  coqFourStateTableAppendRowAssignmentStepParameterName <> boundName ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail translation baseContext prefix)
    (rawTemplateFormula translation
      (coqLtSuccCasesAntecedentTemplate (ttVar 4) rowBound))
    antecedentRoot ->
  (forall sourceWitnessList sourceContext,
    RawCodedPAAxiomWitnessContext M sourceWitnessList sourceContext ->
    RawFourStateTableAppendInheritedProductionInputsAt M translation
      sourceContext
      (coqLtSuccCasesBelowTemplate (ttVar 4) rowBound :: prefix)
      inheritedTraversal
      (coqLtSuccCasesBelowTemplate (ttVar 4) rowBound)
      oldLookup) ->
  (forall sourceWitnessList sourceContext,
    RawCodedPAAxiomWitnessContext M sourceWitnessList sourceContext ->
    RawFourStateTableAppendEqualityProductionInputsAt M translation
      sourceContext
      (coqLtSuccCasesEqualTemplate (ttVar 4) rowBound :: prefix)
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      boundName
      coqFourStateTableAppendRowModeParameterName
      coqFourStateTableAppendRowFormulaParameterName
      coqFourStateTableAppendRowAssignmentCodeParameterName
      coqFourStateTableAppendRowAssignmentStepParameterName
      (ttVar 4) (ttVar 3) (ttVar 2) (ttVar 1) (ttVar 0)
      fixedResult) ->
  RawCodedPAGrowingTemplateLocalProofAt M translation
    baseWitnessList baseContext prefix
    (rawTemplateFormula translation result).
Proof.
  intros M hPA translation hagreement
    baseWitnessList baseContext prefix
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    boundName rowBound antecedentRoot
    sigmaProduction piProduction inheritedTraversal oldLookup
    fixedResult result hopen hprefix hequalHead hbase
    hmodeFresh hformulaFresh hassignmentCodeFresh hassignmentStepFresh
    hantecedent hpredecessorInputs hequalInputs.
  cbn zeta in *.
  eapply
    (raw_codedPALocalProofOf_four_state_table_append_concrete_closed_row_cases_on_growing_witnessed_tail_under_prefix
      M hPA translation hagreement
      baseWitnessList baseContext prefix
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      boundName rowBound antecedentRoot sigmaProduction piProduction).
  - exact hprefix.
  - exact hequalHead.
  - exact hbase.
  - exact hmodeFresh.
  - exact hformulaFresh.
  - exact hassignmentCodeFresh.
  - exact hassignmentStepFresh.
  - exact hantecedent.
  - intros sourceWitnessList sourceContext hsource.
    exact
      (raw_codedPALocalProofOf_four_state_table_append_inherited_row_production_growing_tail
        M hPA translation sourceWitnessList sourceContext
        (coqLtSuccCasesBelowTemplate (ttVar 4) rowBound :: prefix)
        inheritedTraversal
        (coqLtSuccCasesBelowTemplate (ttVar 4) rowBound)
        oldLookup
        (coqFourStateTableAppendConcreteClosedRowProductionTemplate
          sigmaProduction piProduction)
        hsource hopen
        (hpredecessorInputs sourceWitnessList sourceContext hsource)).
  - exact hequalInputs.
Qed.

(** Folding an outer finite template prefix over an already folded inner
    prefix is the same as folding their concatenation over the original raw
    tail.  This normalization is useful whenever temporary implication
    assumptions sit in front of the fixed append-row context. *)
Lemma rawTemplateContextCodeOnTail_app : forall
    (M : RawPAModel) (translation : RawCodedTemplateTranslation M)
    baseContext outer inner,
  rawTemplateContextCodeOnTail translation baseContext (outer ++ inner) =
  rawTemplateContextCodeOnTail translation
    (rawTemplateContextCodeOnTail translation baseContext inner) outer.
Proof.
  intros M translation baseContext outer.
  induction outer as [|formula tail ih]; intro inner.
  - reflexivity.
  - change (rawListNode M (rawTemplateFormula translation formula)
      (rawTemplateContextCodeOnTail translation baseContext
        (tail ++ inner)) =
      rawListNode M (rawTemplateFormula translation formula)
        (rawTemplateContextCodeOnTail translation
          (rawTemplateContextCodeOnTail translation baseContext inner)
          tail)).
    now rewrite ih.
Qed.

(** Repeated universal introduction over an arbitrary self-shifting raw
    context tail.  This relaxes the zero-tail chain used by closed template
    proofs and is reusable for every compiler whose finite eigenvariable
    prefix sits above a witnessed PA-axiom context. *)
Theorem raw_codedPALocalProofOf_universal_introduction_chain_on_self_shift_tail :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M)
    baseTail count context body deepRoot,
  RawContextListRealizable M baseTail ->
  RawContextShift M baseTail baseTail ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail translation baseTail
      (templateContextShiftMany count context))
    (rawTemplateFormula translation body) deepRoot ->
  exists root,
    RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation baseTail context)
      (rawTemplateFormula translation
        (templateFormulaAllMany count body)) root.
Proof.
  intros M hPA translation baseTail count.
  induction count as [|smaller ih];
    intros context body deepRoot htail hselfShift hdeep.
  - exists deepRoot. exact hdeep.
  - cbn [templateContextShiftMany templateFormulaAllMany] in hdeep |- *.
    destruct
      (ih (templateContextShift context) body deepRoot
        htail hselfShift hdeep) as [innerRoot hinner].
    exists (rawProofAllIRoot M
      (rawTemplateContextCodeOnTail translation baseTail context)
      (rawTemplateFormula translation
        (templateFormulaAllMany smaller body)) innerRoot).
    split.
    + exact (raw_proofAllI_ruleCoverage M hPA
        (rawTemplateContextCodeOnTail translation baseTail context)
        (rawTemplateContextCodeOnTail translation baseTail
          (templateContextShift context))
        (rawTemplateFormula translation
          (templateFormulaAllMany smaller body)) innerRoot
        (raw_templateContextOnTail_shift M hPA
          translation baseTail context hselfShift)
        (proj1 hinner) (proj2 hinner)).
    + rewrite rawTemplateFormula_all.
      exact (raw_proofAllI_endpoint M
        (rawTemplateContextCodeOnTail translation baseTail context)
        (rawTemplateFormula translation
          (templateFormulaAllMany smaller body)) innerRoot).
Qed.

Corollary raw_codedPALocalProofOf_universal_introduction_chain_on_witnessed_tail :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M)
    witnessList baseContext count context body deepRoot,
  RawCodedPAAxiomWitnessContext M witnessList baseContext ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail translation baseContext
      (templateContextShiftMany count context))
    (rawTemplateFormula translation body) deepRoot ->
  exists root,
    RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation baseContext context)
      (rawTemplateFormula translation
        (templateFormulaAllMany count body)) root.
Proof.
  intros M hPA translation witnessList baseContext count context body
    deepRoot hwitness hdeep.
  exact
    (raw_codedPALocalProofOf_universal_introduction_chain_on_self_shift_tail
      M hPA translation baseContext count context body deepRoot
      (raw_codedPAAxiomWitnessContext_context_realizable M
        witnessList baseContext hwitness)
      (raw_codedPAAxiomWitnessContext_selfShift M hPA
        witnessList baseContext hwitness)
      hdeep).
Qed.

(** Lift an already growing local proof through a finite universal block
    without changing its selected final witness context or its advertised
    inclusion from the source tail. *)
Theorem raw_codedPAGrowingTemplateLocalProofAt_universal_introduction_chain :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M)
    sourceWitnessList sourceContext count context body,
  RawCodedPAGrowingTemplateLocalProofAt M translation
    sourceWitnessList sourceContext
    (templateContextShiftMany count context)
    (rawTemplateFormula translation body) ->
  RawCodedPAGrowingTemplateLocalProofAt M translation
    sourceWitnessList sourceContext context
    (rawTemplateFormula translation
      (templateFormulaAllMany count body)).
Proof.
  intros M hPA translation sourceWitnessList sourceContext count context body
    (finalWitnessList & finalContext & deepRoot &
      hfinalContext & hsourceIncluded & hdeep).
  destruct
    (raw_codedPALocalProofOf_universal_introduction_chain_on_witnessed_tail
      M hPA translation finalWitnessList finalContext count context body
      deepRoot hfinalContext hdeep) as [root hroot].
  unfold RawCodedPAGrowingTemplateLocalProofAt.
  exists finalWitnessList, finalContext, root.
  split; [exact hfinalContext |].
  split; [exact hsourceIncluded | exact hroot].
Qed.

(** Finite existential elimination over an arbitrary realizable,
    self-shifting raw tail.  The zero-tail compiler is insufficient after a
    branch helper has enlarged the witnessed PA context; this form retains
    that exact tail through every eigenvariable step. *)
Theorem raw_codedPALocalProofOf_existential_elimination_chain_on_self_shift_tail :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M)
    baseTail count source context conclusion deepContext sourceRoot deepRoot,
  RawContextListRealizable M baseTail ->
  RawContextShift M baseTail baseTail ->
  templateExistentialEliminationContext count source context =
    Some deepContext ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail translation baseTail context)
    (rawTemplateFormula translation source) sourceRoot ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail translation baseTail deepContext)
    (rawTemplateFormula translation
      (templateFormulaShiftMany count conclusion)) deepRoot ->
  exists root,
    RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation baseTail context)
      (rawTemplateFormula translation conclusion) root.
Proof.
  intros M hPA translation baseTail count.
  induction count as [|count ih];
    intros source context conclusion deepContext sourceRoot deepRoot
      htail hselfShift hdeepContext hsource hdeep.
  - cbn [templateExistentialEliminationContext
      templateFormulaShiftMany] in hdeepContext, hdeep.
    inversion hdeepContext; subst deepContext.
    exists deepRoot. exact hdeep.
  - destruct source; try discriminate hdeepContext.
    cbn [templateExistentialEliminationContext] in hdeepContext.
    assert (hbodyAssumption : RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation baseTail
        (source :: templateContextShift context))
      (rawTemplateFormula translation source)
      (rawProofAssumptionRoot M
        (rawTemplateContextCodeOnTail translation baseTail
          (source :: templateContextShift context))
        (rawTemplateFormula translation source))).
    {
      cbn [rawTemplateContextCodeOnTail].
      apply (raw_codedPALocalProofOf_assumption M hPA).
      apply (raw_templateContextOnTail_realizable M hPA).
      exact htail.
    }
    destruct (ih source
      (source :: templateContextShift context)
      (templateFormulaRename S conclusion)
      deepContext
      (rawProofAssumptionRoot M
        (rawTemplateContextCodeOnTail translation baseTail
          (source :: templateContextShift context))
        (rawTemplateFormula translation source))
      deepRoot htail hselfShift hdeepContext hbodyAssumption hdeep)
      as [bodyRoot hbody].
    exists (rawProofExERoot M
      (rawTemplateContextCodeOnTail translation baseTail context)
      (rawTemplateFormula translation source)
      (rawTemplateFormula translation conclusion)
      sourceRoot bodyRoot).
    apply (raw_codedPALocalProofOf_exE M hPA
      (rawTemplateContextCodeOnTail translation baseTail context)
      (rawTemplateContextCodeOnTail translation baseTail
        (templateContextShift context))
      (rawTemplateFormula translation source)
      (rawTemplateFormula translation conclusion)
      (rawTemplateFormula translation
        (templateFormulaRename S conclusion))
      sourceRoot bodyRoot).
    + rewrite <- rawTemplateFormula_ex. exact hsource.
    + exact (raw_templateContextOnTail_shift M hPA
        translation baseTail context hselfShift).
    + exact (rawTemplateFormula_shift translation conclusion).
    + cbn [rawTemplateContextCodeOnTail] in hbody. exact hbody.
Qed.

Corollary raw_codedPALocalProofOf_existential_elimination_chain_on_witnessed_tail :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M)
    witnessList baseContext count source context conclusion deepContext
    sourceRoot deepRoot,
  RawCodedPAAxiomWitnessContext M witnessList baseContext ->
  templateExistentialEliminationContext count source context =
    Some deepContext ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail translation baseContext context)
    (rawTemplateFormula translation source) sourceRoot ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail translation baseContext deepContext)
    (rawTemplateFormula translation
      (templateFormulaShiftMany count conclusion)) deepRoot ->
  exists root,
    RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation baseContext context)
      (rawTemplateFormula translation conclusion) root.
Proof.
  intros M hPA translation witnessList baseContext count source context
    conclusion deepContext sourceRoot deepRoot hwitness hdeepContext
    hsource hdeep.
  exact
    (raw_codedPALocalProofOf_existential_elimination_chain_on_self_shift_tail
      M hPA translation baseContext count source context conclusion
      deepContext sourceRoot deepRoot
      (raw_codedPAAxiomWitnessContext_context_realizable M
        witnessList baseContext hwitness)
      (raw_codedPAAxiomWitnessContext_selfShift M hPA
        witnessList baseContext hwitness)
      hdeepContext hsource hdeep).
Qed.

(** Dependency-ordered growing existential elimination.  The existential
    source proof is selected on the initial witnessed tail, while the deep
    continuation may compile additional PA helper batches.  Transport the
    source proof to that final tail before rebuilding the elimination chain. *)
Theorem raw_codedPAGrowingTemplateLocalProofAt_existential_elimination_chain :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M)
    sourceWitnessList sourceContext count source context conclusion
    deepContext sourceRoot,
  RawCodedPAAxiomWitnessContext M sourceWitnessList sourceContext ->
  templateExistentialEliminationContext count source context =
    Some deepContext ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail translation sourceContext context)
    (rawTemplateFormula translation source) sourceRoot ->
  RawCodedPAGrowingTemplateLocalProofAt M translation
    sourceWitnessList sourceContext deepContext
    (rawTemplateFormula translation
      (templateFormulaShiftMany count conclusion)) ->
  RawCodedPAGrowingTemplateLocalProofAt M translation
    sourceWitnessList sourceContext context
    (rawTemplateFormula translation conclusion).
Proof.
  intros M hPA translation sourceWitnessList sourceContext count source
    context conclusion deepContext sourceRoot hsource hdeepContext
    hsourceProof
    (finalWitnessList & finalContext & deepRoot &
      hfinalContext & hsourceIncluded & hdeep).
  destruct
    (raw_codedPALocalProof_sameTemplatePrefix_witnessedTail_transport
      M hPA translation
      sourceWitnessList sourceContext finalWitnessList finalContext
      context (rawTemplateFormula translation source) sourceRoot
      hsource hfinalContext hsourceIncluded hsourceProof)
    as [transportedSourceRoot htransportedSource].
  destruct
    (raw_codedPALocalProofOf_existential_elimination_chain_on_witnessed_tail
      M hPA translation finalWitnessList finalContext count source context
      conclusion deepContext transportedSourceRoot deepRoot
      hfinalContext hdeepContext htransportedSource hdeep)
    as [root hroot].
  unfold RawCodedPAGrowingTemplateLocalProofAt.
  exists finalWitnessList, finalContext, root.
  split; [exact hfinalContext |].
  split; [exact hsourceIncluded | exact hroot].
Qed.

(** Normalize the generic growing universal chain to the five row variables
    introduced after all eight append witnesses. *)
Corollary raw_codedPAGrowingTemplateLocalProofAt_four_state_table_append_row_all5 :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M)
    sourceWitnessList sourceContext
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    bound mode formula assignmentCode assignmentStep body,
  RawCodedPAGrowingTemplateLocalProofAt M translation
    sourceWitnessList sourceContext
    (coqFourStateTableAppendRowPrefix
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      bound mode formula assignmentCode assignmentStep)
    (rawTemplateFormula translation body) ->
  RawCodedPAGrowingTemplateLocalProofAt M translation
    sourceWitnessList sourceContext
    (coqFourStateTableAppendWitnessContext
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      bound mode formula assignmentCode assignmentStep [])
    (rawTemplateFormula translation
      (templateFormulaAllMany 5 body)).
Proof.
  intros M hPA translation sourceWitnessList sourceContext
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    bound mode formula assignmentCode assignmentStep body hbody.
  apply
    (raw_codedPAGrowingTemplateLocalProofAt_universal_introduction_chain
      M hPA translation sourceWitnessList sourceContext 5
      (coqFourStateTableAppendWitnessContext
        modeCode modeStep formulaCode formulaStep
        assignmentCodeCode assignmentCodeStep
        assignmentStepCode assignmentStepStep
        bound mode formula assignmentCode assignmentStep []) body).
  exact hbody.
Qed.

(** Agreement on embedded PA syntax identifies the metatheoretic witnessed
    template tail with its synchronized carrier-coded context. *)
Lemma raw_templateContextCode_embedPAAxiomWitnesses : forall
    (M : RawPAModel) (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall witnesses,
  rawTemplateContextCode translation
    (embedPAContext (map witnessedAxiom witnesses)) =
  rawStandardPAAxiomWitnessPrefixContextCode M witnesses (raw_zero M).
Proof.
  intros M translation hagreement witnesses.
  rewrite raw_templateContextCode_as_on_tail_general.
  apply (raw_templateContextCodeOnTail_embedPAAxiomWitnesses
    M translation hagreement witnesses (raw_zero M)).
Qed.

(** Carrier-code form of the exact thirteen-assumption prefix equation. *)
Lemma raw_fourStateTableAppendRowContext_witnessed_tail_code : forall
    (M : RawPAModel) (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    bound mode formula assignmentCode assignmentStep witnesses,
  rawTemplateContextCode translation
    (templateContextShiftMany 5
      (coqFourStateTableAppendWitnessContext
        modeCode modeStep formulaCode formulaStep
        assignmentCodeCode assignmentCodeStep
        assignmentStepCode assignmentStepStep
        bound mode formula assignmentCode assignmentStep
        (embedPAContext (map witnessedAxiom witnesses)))) =
  rawTemplateContextCodeOnTail translation
    (rawStandardPAAxiomWitnessPrefixContextCode M
      witnesses (raw_zero M))
    (coqFourStateTableAppendRowPrefix
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      bound mode formula assignmentCode assignmentStep).
Proof.
  intros M translation hagreement
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    bound mode formula assignmentCode assignmentStep witnesses.
  rewrite coqFourStateTableAppendRowContext_witnessed_tail.
  rewrite raw_templateContextCode_app_on_tail_general.
  rewrite (raw_templateContextCode_embedPAAxiomWitnesses
    M translation hagreement witnesses).
  reflexivity.
Qed.

(** Reassociate a newly selected standard witness batch with the caller's
    existing batch, while presenting the context through embedded templates. *)
Lemma raw_fourStateTableAppendRow_combined_witnessed_tail : forall
    (M : RawPAModel) (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall extra witnesses,
  RawCodedPAAxiomWitnessContext M
    (rawStandardPAAxiomWitnessPrefixWitnessListCode M extra
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        witnesses (raw_zero M)))
    (rawStandardPAAxiomWitnessPrefixContextCode M extra
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses (raw_zero M))) ->
  RawCodedPAAxiomWitnessContext M
    (rawStandardPAAxiomWitnessPrefixWitnessListCode M
      (extra ++ witnesses) (raw_zero M))
    (rawTemplateContextCode translation
      (embedPAContext (map witnessedAxiom (extra ++ witnesses)))).
Proof.
  intros M translation hagreement extra witnesses hwitnessed.
  rewrite rawStandardPAAxiomWitnessPrefixWitnessListCode_app.
  rewrite (raw_templateContextCode_embedPAAxiomWitnesses
    M translation hagreement (extra ++ witnesses)).
  rewrite rawStandardPAAxiomWitnessPrefixContextCode_app.
  exact hwitnessed.
Qed.

(** The same reassociation at the full temporary-row context code. *)
Lemma raw_fourStateTableAppendRowContext_combined_tail_code : forall
    (M : RawPAModel) (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    bound mode formula assignmentCode assignmentStep extra witnesses,
  rawTemplateContextCode translation
    (templateContextShiftMany 5
      (coqFourStateTableAppendWitnessContext
        modeCode modeStep formulaCode formulaStep
        assignmentCodeCode assignmentCodeStep
        assignmentStepCode assignmentStepStep
        bound mode formula assignmentCode assignmentStep
        (embedPAContext
          (map witnessedAxiom (extra ++ witnesses))))) =
  rawTemplateContextCodeOnTail translation
    (rawStandardPAAxiomWitnessPrefixContextCode M extra
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses (raw_zero M)))
    (coqFourStateTableAppendRowPrefix
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      bound mode formula assignmentCode assignmentStep).
Proof.
  intros M translation hagreement
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    bound mode formula assignmentCode assignmentStep extra witnesses.
  rewrite (raw_fourStateTableAppendRowContext_witnessed_tail_code
    M translation hagreement
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    bound mode formula assignmentCode assignmentStep
    (extra ++ witnesses)).
  rewrite rawStandardPAAxiomWitnessPrefixContextCode_app.
  reflexivity.
Qed.

(** Align the operational equality lookup with the growing row-prefix view.
    The lookup constructor works below the context obtained by eight
    existential eliminations and five variable shifts.  For an embedded
    witnessed PA tail, [raw_fourStateTableAppendRowContext_witnessed_tail_code]
    identifies that context literally with the prefix consumed by the
    growing case theorem. *)
Theorem
    raw_fourStateTableAppendEqualityProductionInputsAt_on_witnessed_row_context :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    boundName rowBound sigmaProduction piProduction witnesses
    rowLookupRoot fixedResultRoot,
  let baseContext := rawStandardPAAxiomWitnessPrefixContextCode M
    witnesses (raw_zero M) in
  let rowPrefix := coqFourStateTableAppendRowPrefix
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    (ttParameter boundName)
    (ttParameter coqFourStateTableAppendRowModeParameterName)
    (ttParameter coqFourStateTableAppendRowFormulaParameterName)
    (ttParameter coqFourStateTableAppendRowAssignmentCodeParameterName)
    (ttParameter coqFourStateTableAppendRowAssignmentStepParameterName) in
  let equalityHead :=
    coqLtSuccCasesEqualTemplate (ttVar 4) rowBound in
  let fixedResult :=
    coqFourStateTableAppendNamedClosedRowProductionTemplate
      sigmaProduction piProduction in
  equalityHead = tfEq (ttVar 4) (ttParameter boundName) ->
  RawCodedFormulaAtomicallyAdequate M
    (rawTemplateFormula translation equalityHead) ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail translation baseContext
      (equalityHead :: rowPrefix))
    (rawTemplateFormula translation
      (coqFourStateTableAppendEqualityRowLookupTemplate
        coqFourStateTableAppendRowModeParameterName
        coqFourStateTableAppendRowFormulaParameterName
        coqFourStateTableAppendRowAssignmentCodeParameterName
        coqFourStateTableAppendRowAssignmentStepParameterName
        (ttVar 4) (ttVar 3) (ttVar 2) (ttVar 1) (ttVar 0)))
    rowLookupRoot ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail translation baseContext
      (equalityHead :: rowPrefix))
    (rawTemplateFormula translation fixedResult) fixedResultRoot ->
  RawFourStateTableAppendEqualityProductionInputsAt M translation
    baseContext (equalityHead :: rowPrefix)
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    boundName
    coqFourStateTableAppendRowModeParameterName
    coqFourStateTableAppendRowFormulaParameterName
    coqFourStateTableAppendRowAssignmentCodeParameterName
    coqFourStateTableAppendRowAssignmentStepParameterName
    (ttVar 4) (ttVar 3) (ttVar 2) (ttVar 1) (ttVar 0)
    fixedResult.
Proof.
  intros M hPA translation hagreement
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    boundName rowBound sigmaProduction piProduction witnesses
    rowLookupRoot fixedResultRoot
    baseContext rowPrefix equalityHead fixedResult
    hequalityHead hhead hrowLookup hfixedResult.
  cbn zeta in *.
  destruct
    (raw_codedPALocalProofOf_four_state_table_append_equality_branch_lookup_parameter
      M hPA translation
      (embedPAContext (map witnessedAxiom witnesses))
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      boundName
      (ttParameter coqFourStateTableAppendRowModeParameterName)
      (ttParameter coqFourStateTableAppendRowFormulaParameterName)
      (ttParameter coqFourStateTableAppendRowAssignmentCodeParameterName)
      (ttParameter coqFourStateTableAppendRowAssignmentStepParameterName)
      (ttVar 4) rowBound hequalityHead hhead)
    as [fixedLookupRoot hfixedLookup].
  rewrite
    (raw_fourStateTableAppendRowContext_witnessed_tail_code
      M translation hagreement
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      (ttParameter boundName)
      (ttParameter coqFourStateTableAppendRowModeParameterName)
      (ttParameter coqFourStateTableAppendRowFormulaParameterName)
      (ttParameter coqFourStateTableAppendRowAssignmentCodeParameterName)
      (ttParameter coqFourStateTableAppendRowAssignmentStepParameterName)
      witnesses) in hfixedLookup.
  unfold RawFourStateTableAppendEqualityProductionInputsAt.
  exists fixedLookupRoot, rowLookupRoot, fixedResultRoot.
  cbn in hfixedLookup |- *.
  split; [exact hfixedLookup |].
  split; [exact hrowLookup | exact hfixedResult].
Qed.

(** The row lookup and fixed production genuinely exist before the equality
    case is selected.  Insert the adequate equality head above both proofs,
    then use the operational append lookup constructor to supply the third
    root in the identical context. *)
Theorem
    raw_fourStateTableAppendEqualityProductionInputsAt_on_witnessed_row_context_of_local_roots :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    boundName rowBound sigmaProduction piProduction witnesses
    rowLookupRoot fixedResultRoot,
  let baseContext := rawStandardPAAxiomWitnessPrefixContextCode M
    witnesses (raw_zero M) in
  let rowPrefix := coqFourStateTableAppendRowPrefix
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    (ttParameter boundName)
    (ttParameter coqFourStateTableAppendRowModeParameterName)
    (ttParameter coqFourStateTableAppendRowFormulaParameterName)
    (ttParameter coqFourStateTableAppendRowAssignmentCodeParameterName)
    (ttParameter coqFourStateTableAppendRowAssignmentStepParameterName) in
  let equalityHead :=
    coqLtSuccCasesEqualTemplate (ttVar 4) rowBound in
  let fixedResult :=
    coqFourStateTableAppendNamedClosedRowProductionTemplate
      sigmaProduction piProduction in
  equalityHead = tfEq (ttVar 4) (ttParameter boundName) ->
  RawCodedFormulaAtomicallyAdequate M
    (rawTemplateFormula translation equalityHead) ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail translation baseContext rowPrefix)
    (rawTemplateFormula translation
      (coqFourStateTableAppendEqualityRowLookupTemplate
        coqFourStateTableAppendRowModeParameterName
        coqFourStateTableAppendRowFormulaParameterName
        coqFourStateTableAppendRowAssignmentCodeParameterName
        coqFourStateTableAppendRowAssignmentStepParameterName
        (ttVar 4) (ttVar 3) (ttVar 2) (ttVar 1) (ttVar 0)))
    rowLookupRoot ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail translation baseContext rowPrefix)
    (rawTemplateFormula translation fixedResult) fixedResultRoot ->
  RawFourStateTableAppendEqualityProductionInputsAt M translation
    baseContext (equalityHead :: rowPrefix)
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    boundName
    coqFourStateTableAppendRowModeParameterName
    coqFourStateTableAppendRowFormulaParameterName
    coqFourStateTableAppendRowAssignmentCodeParameterName
    coqFourStateTableAppendRowAssignmentStepParameterName
    (ttVar 4) (ttVar 3) (ttVar 2) (ttVar 1) (ttVar 0)
    fixedResult.
Proof.
  intros M hPA translation hagreement
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    boundName rowBound sigmaProduction piProduction witnesses
    rowLookupRoot fixedResultRoot
    baseContext rowPrefix equalityHead fixedResult
    hequalityHead hhead hrowLookup hfixedResult.
  cbn zeta in *.
  assert (hbase : RawCodedPAAxiomWitnessContext M
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        witnesses (raw_zero M))
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses (raw_zero M))).
  {
    pose proof (raw_templateEmbeddedPAAxiomWitnessContext
      M hPA translation hagreement witnesses) as hbaseTemplate.
    rewrite (raw_templateContextCode_embedPAAxiomWitnesses
      M translation hagreement witnesses) in hbaseTemplate.
    exact hbaseTemplate.
  }
  assert (hrowContext : RawContextListRealizable M
      (rawTemplateContextCodeOnTail translation
        (rawStandardPAAxiomWitnessPrefixContextCode M
          witnesses (raw_zero M))
        (coqFourStateTableAppendRowPrefix
          modeCode modeStep formulaCode formulaStep
          assignmentCodeCode assignmentCodeStep
          assignmentStepCode assignmentStepStep
          (ttParameter boundName)
          (ttParameter coqFourStateTableAppendRowModeParameterName)
          (ttParameter coqFourStateTableAppendRowFormulaParameterName)
          (ttParameter coqFourStateTableAppendRowAssignmentCodeParameterName)
          (ttParameter
            coqFourStateTableAppendRowAssignmentStepParameterName)))).
  {
    apply (raw_templateContextOnTail_realizable M hPA).
    exact (raw_codedPAAxiomWitnessContext_context_realizable M
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        witnesses (raw_zero M))
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses (raw_zero M)) hbase).
  }
  assert (hequalityPrefix :
      RawCodedTemplatePrefixAtomicallyAdequate M translation [equalityHead]).
  {
    intros formula [hformula | hformula].
    - subst formula. exact hhead.
    - contradiction.
  }
  destruct (raw_codedPALocalProof_templatePrefix
    M hPA translation
    (rawTemplateContextCodeOnTail translation
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses (raw_zero M))
      (coqFourStateTableAppendRowPrefix
        modeCode modeStep formulaCode formulaStep
        assignmentCodeCode assignmentCodeStep
        assignmentStepCode assignmentStepStep
        (ttParameter boundName)
        (ttParameter coqFourStateTableAppendRowModeParameterName)
        (ttParameter coqFourStateTableAppendRowFormulaParameterName)
        (ttParameter coqFourStateTableAppendRowAssignmentCodeParameterName)
        (ttParameter coqFourStateTableAppendRowAssignmentStepParameterName)))
    [equalityHead]
    (rawTemplateFormula translation
      (coqFourStateTableAppendEqualityRowLookupTemplate
        coqFourStateTableAppendRowModeParameterName
        coqFourStateTableAppendRowFormulaParameterName
        coqFourStateTableAppendRowAssignmentCodeParameterName
        coqFourStateTableAppendRowAssignmentStepParameterName
        (ttVar 4) (ttVar 3) (ttVar 2) (ttVar 1) (ttVar 0)))
    rowLookupRoot hrowContext hequalityPrefix hrowLookup)
    as [shiftedRowLookupRoot hshiftedRowLookup].
  destruct (raw_codedPALocalProof_templatePrefix
    M hPA translation
    (rawTemplateContextCodeOnTail translation
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses (raw_zero M))
      (coqFourStateTableAppendRowPrefix
        modeCode modeStep formulaCode formulaStep
        assignmentCodeCode assignmentCodeStep
        assignmentStepCode assignmentStepStep
        (ttParameter boundName)
        (ttParameter coqFourStateTableAppendRowModeParameterName)
        (ttParameter coqFourStateTableAppendRowFormulaParameterName)
        (ttParameter coqFourStateTableAppendRowAssignmentCodeParameterName)
        (ttParameter coqFourStateTableAppendRowAssignmentStepParameterName)))
    [equalityHead]
    (rawTemplateFormula translation
      (coqFourStateTableAppendNamedClosedRowProductionTemplate
        sigmaProduction piProduction))
    fixedResultRoot hrowContext hequalityPrefix hfixedResult)
    as [shiftedFixedResultRoot hshiftedFixedResult].
  cbn in hshiftedRowLookup, hshiftedFixedResult.
  exact
    (raw_fourStateTableAppendEqualityProductionInputsAt_on_witnessed_row_context
      M hPA translation hagreement
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      boundName rowBound sigmaProduction piProduction witnesses
      shiftedRowLookupRoot shiftedFixedResultRoot
      hequalityHead hhead hshiftedRowLookup hshiftedFixedResult).
Qed.

(** Equality-input assembly with arbitrary adequate row assumptions between
    the branch head and the fixed append prefix.  The operational lookup is
    produced by the prefix-general compiler above; the caller's row lookup
    and fixed production are weakened beneath the equality head in the same
    combined context. *)
Theorem
    raw_fourStateTableAppendEqualityProductionInputsAt_on_witnessed_row_context_under_prefix_of_local_roots :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    boundName rowBound sigmaProduction piProduction witnesses
    extraPrefix rowLookupRoot fixedResultRoot,
  let baseContext := rawStandardPAAxiomWitnessPrefixContextCode M
    witnesses (raw_zero M) in
  let rowPrefix := coqFourStateTableAppendRowPrefix
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    (ttParameter boundName)
    (ttParameter coqFourStateTableAppendRowModeParameterName)
    (ttParameter coqFourStateTableAppendRowFormulaParameterName)
    (ttParameter coqFourStateTableAppendRowAssignmentCodeParameterName)
    (ttParameter coqFourStateTableAppendRowAssignmentStepParameterName) in
  let equalityHead :=
    coqLtSuccCasesEqualTemplate (ttVar 4) rowBound in
  let fixedResult :=
    coqFourStateTableAppendNamedClosedRowProductionTemplate
      sigmaProduction piProduction in
  RawCodedTemplatePrefixAtomicallyAdequate M translation extraPrefix ->
  equalityHead = tfEq (ttVar 4) (ttParameter boundName) ->
  RawCodedFormulaAtomicallyAdequate M
    (rawTemplateFormula translation equalityHead) ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail translation baseContext
      (extraPrefix ++ rowPrefix))
    (rawTemplateFormula translation
      (coqFourStateTableAppendEqualityRowLookupTemplate
        coqFourStateTableAppendRowModeParameterName
        coqFourStateTableAppendRowFormulaParameterName
        coqFourStateTableAppendRowAssignmentCodeParameterName
        coqFourStateTableAppendRowAssignmentStepParameterName
        (ttVar 4) (ttVar 3) (ttVar 2) (ttVar 1) (ttVar 0)))
    rowLookupRoot ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail translation baseContext
      (extraPrefix ++ rowPrefix))
    (rawTemplateFormula translation fixedResult) fixedResultRoot ->
  RawFourStateTableAppendEqualityProductionInputsAt M translation
    baseContext (equalityHead :: extraPrefix ++ rowPrefix)
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    boundName
    coqFourStateTableAppendRowModeParameterName
    coqFourStateTableAppendRowFormulaParameterName
    coqFourStateTableAppendRowAssignmentCodeParameterName
    coqFourStateTableAppendRowAssignmentStepParameterName
    (ttVar 4) (ttVar 3) (ttVar 2) (ttVar 1) (ttVar 0)
    fixedResult.
Proof.
  intros M hPA translation hagreement
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    boundName rowBound sigmaProduction piProduction witnesses
    extraPrefix rowLookupRoot fixedResultRoot
    baseContext rowPrefix equalityHead fixedResult
    hextraPrefix hequalityHead hhead hrowLookup hfixedResult.
  cbn zeta in *.
  destruct
    (raw_codedPALocalProofOf_four_state_table_append_equality_branch_lookup_parameter_under_prefix
      M hPA translation
      (embedPAContext (map witnessedAxiom witnesses)) extraPrefix
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      boundName
      (ttParameter coqFourStateTableAppendRowModeParameterName)
      (ttParameter coqFourStateTableAppendRowFormulaParameterName)
      (ttParameter coqFourStateTableAppendRowAssignmentCodeParameterName)
      (ttParameter coqFourStateTableAppendRowAssignmentStepParameterName)
      (ttVar 4) rowBound hextraPrefix hequalityHead hhead)
    as [fixedLookupRoot hfixedLookup].
  rewrite
    (raw_fourStateTableAppendRowContext_witnessed_tail_code
      M translation hagreement
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      (ttParameter boundName)
      (ttParameter coqFourStateTableAppendRowModeParameterName)
      (ttParameter coqFourStateTableAppendRowFormulaParameterName)
      (ttParameter coqFourStateTableAppendRowAssignmentCodeParameterName)
      (ttParameter coqFourStateTableAppendRowAssignmentStepParameterName)
      witnesses) in hfixedLookup.
  rewrite <- (rawTemplateContextCodeOnTail_app M translation
    (rawStandardPAAxiomWitnessPrefixContextCode M
      witnesses (raw_zero M)) extraPrefix
    (coqFourStateTableAppendRowPrefix
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      (ttParameter boundName)
      (ttParameter coqFourStateTableAppendRowModeParameterName)
      (ttParameter coqFourStateTableAppendRowFormulaParameterName)
      (ttParameter coqFourStateTableAppendRowAssignmentCodeParameterName)
      (ttParameter
        coqFourStateTableAppendRowAssignmentStepParameterName)))
    in hfixedLookup.
  assert (hbase : RawCodedPAAxiomWitnessContext M
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        witnesses (raw_zero M))
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses (raw_zero M))).
  {
    pose proof (raw_templateEmbeddedPAAxiomWitnessContext
      M hPA translation hagreement witnesses) as hbaseTemplate.
    rewrite (raw_templateContextCode_embedPAAxiomWitnesses
      M translation hagreement witnesses) in hbaseTemplate.
    exact hbaseTemplate.
  }
  assert (hcombinedContext : RawContextListRealizable M
      (rawTemplateContextCodeOnTail translation
        (rawStandardPAAxiomWitnessPrefixContextCode M
          witnesses (raw_zero M))
        (extraPrefix ++
          coqFourStateTableAppendRowPrefix
            modeCode modeStep formulaCode formulaStep
            assignmentCodeCode assignmentCodeStep
            assignmentStepCode assignmentStepStep
            (ttParameter boundName)
            (ttParameter coqFourStateTableAppendRowModeParameterName)
            (ttParameter coqFourStateTableAppendRowFormulaParameterName)
            (ttParameter
              coqFourStateTableAppendRowAssignmentCodeParameterName)
            (ttParameter
              coqFourStateTableAppendRowAssignmentStepParameterName)))).
  {
    apply (raw_templateContextOnTail_realizable M hPA).
    exact (raw_codedPAAxiomWitnessContext_context_realizable M
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        witnesses (raw_zero M))
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses (raw_zero M)) hbase).
  }
  assert (hequalityPrefix :
      RawCodedTemplatePrefixAtomicallyAdequate M translation [equalityHead]).
  {
    intros formula [hformula | hformula].
    - subst formula. exact hhead.
    - contradiction.
  }
  destruct (raw_codedPALocalProof_templatePrefix
    M hPA translation
    (rawTemplateContextCodeOnTail translation
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses (raw_zero M))
      (extraPrefix ++
        coqFourStateTableAppendRowPrefix
          modeCode modeStep formulaCode formulaStep
          assignmentCodeCode assignmentCodeStep
          assignmentStepCode assignmentStepStep
          (ttParameter boundName)
          (ttParameter coqFourStateTableAppendRowModeParameterName)
          (ttParameter coqFourStateTableAppendRowFormulaParameterName)
          (ttParameter coqFourStateTableAppendRowAssignmentCodeParameterName)
          (ttParameter coqFourStateTableAppendRowAssignmentStepParameterName)))
    [equalityHead]
    (rawTemplateFormula translation
      (coqFourStateTableAppendEqualityRowLookupTemplate
        coqFourStateTableAppendRowModeParameterName
        coqFourStateTableAppendRowFormulaParameterName
        coqFourStateTableAppendRowAssignmentCodeParameterName
        coqFourStateTableAppendRowAssignmentStepParameterName
        (ttVar 4) (ttVar 3) (ttVar 2) (ttVar 1) (ttVar 0)))
    rowLookupRoot hcombinedContext hequalityPrefix hrowLookup)
    as [shiftedRowLookupRoot hshiftedRowLookup].
  destruct (raw_codedPALocalProof_templatePrefix
    M hPA translation
    (rawTemplateContextCodeOnTail translation
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses (raw_zero M))
      (extraPrefix ++
        coqFourStateTableAppendRowPrefix
          modeCode modeStep formulaCode formulaStep
          assignmentCodeCode assignmentCodeStep
          assignmentStepCode assignmentStepStep
          (ttParameter boundName)
          (ttParameter coqFourStateTableAppendRowModeParameterName)
          (ttParameter coqFourStateTableAppendRowFormulaParameterName)
          (ttParameter coqFourStateTableAppendRowAssignmentCodeParameterName)
          (ttParameter coqFourStateTableAppendRowAssignmentStepParameterName)))
    [equalityHead]
    (rawTemplateFormula translation
      (coqFourStateTableAppendNamedClosedRowProductionTemplate
        sigmaProduction piProduction))
    fixedResultRoot hcombinedContext hequalityPrefix hfixedResult)
    as [shiftedFixedResultRoot hshiftedFixedResult].
  unfold RawFourStateTableAppendEqualityProductionInputsAt.
  exists fixedLookupRoot, shiftedRowLookupRoot, shiftedFixedResultRoot.
  cbn in hfixedLookup, hshiftedRowLookup, hshiftedFixedResult |- *.
  split; [exact hfixedLookup |].
  split; [exact hshiftedRowLookup | exact hshiftedFixedResult].
Qed.

(** Close the concrete row case split from roots that all exist before the
    arithmetic helper batch is selected.  The predecessor pair and the
    equality triple are each built once over the original witnessed row
    context, then transported to the dependency-ordered branch context by
    the inclusion supplied by the base-aware eliminator. *)
Theorem
    raw_codedPALocalProofOf_four_state_table_append_concrete_closed_row_of_inherited_local_roots_on_witnessed_row_context :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    boundName rowBound sigmaProduction piProduction
    inheritedTraversal oldLookup witnesses
    antecedentRoot rowLookupRoot fixedResultRoot,
  let baseWitnessList :=
    rawStandardPAAxiomWitnessPrefixWitnessListCode M
      witnesses (raw_zero M) in
  let baseContext :=
    rawStandardPAAxiomWitnessPrefixContextCode M
      witnesses (raw_zero M) in
  let rowPrefix := coqFourStateTableAppendRowPrefix
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    (ttParameter boundName)
    (ttParameter coqFourStateTableAppendRowModeParameterName)
    (ttParameter coqFourStateTableAppendRowFormulaParameterName)
    (ttParameter coqFourStateTableAppendRowAssignmentCodeParameterName)
    (ttParameter coqFourStateTableAppendRowAssignmentStepParameterName) in
  let below := coqLtSuccCasesBelowTemplate (ttVar 4) rowBound in
  let equalityHead := coqLtSuccCasesEqualTemplate (ttVar 4) rowBound in
  let fixedResult :=
    coqFourStateTableAppendNamedClosedRowProductionTemplate
      sigmaProduction piProduction in
  let result :=
    coqFourStateTableAppendConcreteClosedRowProductionTemplate
      sigmaProduction piProduction in
  templateUniversalOpenMany inheritedTraversal
    coqFourStateTableAppendConcreteRowVariables =
    Some (tfImp below (tfImp oldLookup result)) ->
  RawCodedTemplatePrefixAtomicallyAdequate M translation rowPrefix ->
  RawCodedFormulaAtomicallyAdequate M
    (rawTemplateFormula translation below) ->
  equalityHead = tfEq (ttVar 4) (ttParameter boundName) ->
  RawCodedFormulaAtomicallyAdequate M
    (rawTemplateFormula translation equalityHead) ->
  coqFourStateTableAppendRowModeParameterName <> boundName ->
  coqFourStateTableAppendRowFormulaParameterName <> boundName ->
  coqFourStateTableAppendRowAssignmentCodeParameterName <> boundName ->
  coqFourStateTableAppendRowAssignmentStepParameterName <> boundName ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail translation baseContext rowPrefix)
    (rawTemplateFormula translation
      (coqLtSuccCasesAntecedentTemplate (ttVar 4) rowBound))
    antecedentRoot ->
  RawFourStateTableAppendInheritedLocalRootsAt M translation
    baseContext rowPrefix inheritedTraversal oldLookup ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail translation baseContext rowPrefix)
    (rawTemplateFormula translation
      (coqFourStateTableAppendEqualityRowLookupTemplate
        coqFourStateTableAppendRowModeParameterName
        coqFourStateTableAppendRowFormulaParameterName
        coqFourStateTableAppendRowAssignmentCodeParameterName
        coqFourStateTableAppendRowAssignmentStepParameterName
        (ttVar 4) (ttVar 3) (ttVar 2) (ttVar 1) (ttVar 0)))
    rowLookupRoot ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail translation baseContext rowPrefix)
    (rawTemplateFormula translation fixedResult) fixedResultRoot ->
  RawCodedPAGrowingTemplateLocalProofAt M translation
    baseWitnessList baseContext rowPrefix
    (rawTemplateFormula translation result).
Proof.
  intros M hPA translation hagreement
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    boundName rowBound sigmaProduction piProduction
    inheritedTraversal oldLookup witnesses
    antecedentRoot rowLookupRoot fixedResultRoot
    baseWitnessList baseContext rowPrefix below equalityHead
    fixedResult result
    hopen hprefix hbelowAdequate hequalityHead hequalityAdequate
    hmodeFresh hformulaFresh hassignmentCodeFresh hassignmentStepFresh
    hantecedent hinheritedRoots hrowLookup hfixedResult.
  cbn zeta in *.
  assert (hbase : RawCodedPAAxiomWitnessContext M
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        witnesses (raw_zero M))
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses (raw_zero M))).
  {
    pose proof (raw_templateEmbeddedPAAxiomWitnessContext
      M hPA translation hagreement witnesses) as hbaseTemplate.
    rewrite (raw_templateContextCode_embedPAAxiomWitnesses
      M translation hagreement witnesses) in hbaseTemplate.
    exact hbaseTemplate.
  }
  pose proof
    (raw_fourStateTableAppendEqualityProductionInputsAt_on_witnessed_row_context_of_local_roots
      M hPA translation hagreement
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      boundName rowBound sigmaProduction piProduction witnesses
      rowLookupRoot fixedResultRoot
      hequalityHead hequalityAdequate hrowLookup hfixedResult)
    as hequalityBaseInputs.
  eapply
    (raw_codedPALocalProofOf_four_state_table_append_concrete_closed_row_cases_on_base_included_growing_witnessed_tail_under_prefix
      M hPA translation hagreement
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        witnesses (raw_zero M))
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses (raw_zero M))
      (coqFourStateTableAppendRowPrefix
        modeCode modeStep formulaCode formulaStep
        assignmentCodeCode assignmentCodeStep
        assignmentStepCode assignmentStepStep
        (ttParameter boundName)
        (ttParameter coqFourStateTableAppendRowModeParameterName)
        (ttParameter coqFourStateTableAppendRowFormulaParameterName)
        (ttParameter coqFourStateTableAppendRowAssignmentCodeParameterName)
        (ttParameter coqFourStateTableAppendRowAssignmentStepParameterName))
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      boundName rowBound antecedentRoot sigmaProduction piProduction).
  - exact hprefix.
  - exact hequalityAdequate.
  - exact hbase.
  - exact hmodeFresh.
  - exact hformulaFresh.
  - exact hassignmentCodeFresh.
  - exact hassignmentStepFresh.
  - exact hantecedent.
  - intros sourceWitnessList sourceContext hsource hbaseIncluded.
    pose proof
      (raw_fourStateTableAppendInheritedLocalRootsAt_transport
        M hPA translation
        (rawStandardPAAxiomWitnessPrefixWitnessListCode M
          witnesses (raw_zero M))
        (rawStandardPAAxiomWitnessPrefixContextCode M
          witnesses (raw_zero M))
        sourceWitnessList sourceContext
        (coqFourStateTableAppendRowPrefix
          modeCode modeStep formulaCode formulaStep
          assignmentCodeCode assignmentCodeStep
          assignmentStepCode assignmentStepStep
          (ttParameter boundName)
          (ttParameter coqFourStateTableAppendRowModeParameterName)
          (ttParameter coqFourStateTableAppendRowFormulaParameterName)
          (ttParameter coqFourStateTableAppendRowAssignmentCodeParameterName)
          (ttParameter
            coqFourStateTableAppendRowAssignmentStepParameterName))
        inheritedTraversal oldLookup
        hbase hsource hbaseIncluded hinheritedRoots)
      as hsourceInheritedRoots.
    pose proof
      (raw_fourStateTableAppendInheritedProductionInputsAt_of_local_root_package
        M hPA translation sourceWitnessList sourceContext
        (coqFourStateTableAppendRowPrefix
          modeCode modeStep formulaCode formulaStep
          assignmentCodeCode assignmentCodeStep
          assignmentStepCode assignmentStepStep
          (ttParameter boundName)
          (ttParameter coqFourStateTableAppendRowModeParameterName)
          (ttParameter coqFourStateTableAppendRowFormulaParameterName)
          (ttParameter coqFourStateTableAppendRowAssignmentCodeParameterName)
          (ttParameter
            coqFourStateTableAppendRowAssignmentStepParameterName))
        inheritedTraversal
        (coqLtSuccCasesBelowTemplate (ttVar 4) rowBound)
        oldLookup hsource hbelowAdequate hsourceInheritedRoots)
      as hpredecessorInputs.
    exact
      (raw_codedPALocalProofOf_four_state_table_append_inherited_row_production_growing_tail
        M hPA translation sourceWitnessList sourceContext
        (coqLtSuccCasesBelowTemplate (ttVar 4) rowBound ::
          coqFourStateTableAppendRowPrefix
            modeCode modeStep formulaCode formulaStep
            assignmentCodeCode assignmentCodeStep
            assignmentStepCode assignmentStepStep
            (ttParameter boundName)
            (ttParameter coqFourStateTableAppendRowModeParameterName)
            (ttParameter coqFourStateTableAppendRowFormulaParameterName)
            (ttParameter
              coqFourStateTableAppendRowAssignmentCodeParameterName)
            (ttParameter
              coqFourStateTableAppendRowAssignmentStepParameterName))
        inheritedTraversal
        (coqLtSuccCasesBelowTemplate (ttVar 4) rowBound)
        oldLookup
        (coqFourStateTableAppendConcreteClosedRowProductionTemplate
          sigmaProduction piProduction)
        hsource hopen hpredecessorInputs).
  - intros sourceWitnessList sourceContext hsource hbaseIncluded.
    exact
      (raw_fourStateTableAppendEqualityProductionInputsAt_transport
        M hPA translation
        (rawStandardPAAxiomWitnessPrefixWitnessListCode M
          witnesses (raw_zero M))
        (rawStandardPAAxiomWitnessPrefixContextCode M
          witnesses (raw_zero M))
        sourceWitnessList sourceContext
        (coqLtSuccCasesEqualTemplate (ttVar 4) rowBound ::
          coqFourStateTableAppendRowPrefix
            modeCode modeStep formulaCode formulaStep
            assignmentCodeCode assignmentCodeStep
            assignmentStepCode assignmentStepStep
            (ttParameter boundName)
            (ttParameter coqFourStateTableAppendRowModeParameterName)
            (ttParameter coqFourStateTableAppendRowFormulaParameterName)
            (ttParameter
              coqFourStateTableAppendRowAssignmentCodeParameterName)
            (ttParameter
              coqFourStateTableAppendRowAssignmentStepParameterName))
        modeCode modeStep formulaCode formulaStep
        assignmentCodeCode assignmentCodeStep
        assignmentStepCode assignmentStepStep
        boundName
        coqFourStateTableAppendRowModeParameterName
        coqFourStateTableAppendRowFormulaParameterName
        coqFourStateTableAppendRowAssignmentCodeParameterName
        coqFourStateTableAppendRowAssignmentStepParameterName
        (ttVar 4) (ttVar 3) (ttVar 2) (ttVar 1) (ttVar 0)
        (coqFourStateTableAppendNamedClosedRowProductionTemplate
          sigmaProduction piProduction)
        hbase hsource hbaseIncluded hequalityBaseInputs).
Qed.

(** Prefix-general staged row compiler.  The caller may place finite row
    assumptions in front of the fixed append-witness prefix; all inherited
    and equality roots are transported and assembled in that literal
    combined context. *)
Theorem
    raw_codedPALocalProofOf_four_state_table_append_concrete_closed_row_of_inherited_local_roots_on_witnessed_row_context_under_prefix :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    boundName rowBound sigmaProduction piProduction
    inheritedTraversal oldLookup witnesses extraPrefix
    antecedentRoot rowLookupRoot fixedResultRoot,
  let baseWitnessList :=
    rawStandardPAAxiomWitnessPrefixWitnessListCode M
      witnesses (raw_zero M) in
  let baseContext :=
    rawStandardPAAxiomWitnessPrefixContextCode M
      witnesses (raw_zero M) in
  let rowPrefix := coqFourStateTableAppendRowPrefix
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    (ttParameter boundName)
    (ttParameter coqFourStateTableAppendRowModeParameterName)
    (ttParameter coqFourStateTableAppendRowFormulaParameterName)
    (ttParameter coqFourStateTableAppendRowAssignmentCodeParameterName)
    (ttParameter coqFourStateTableAppendRowAssignmentStepParameterName) in
  let combinedPrefix := extraPrefix ++ rowPrefix in
  let below := coqLtSuccCasesBelowTemplate (ttVar 4) rowBound in
  let equalityHead := coqLtSuccCasesEqualTemplate (ttVar 4) rowBound in
  let fixedResult :=
    coqFourStateTableAppendNamedClosedRowProductionTemplate
      sigmaProduction piProduction in
  let result :=
    coqFourStateTableAppendConcreteClosedRowProductionTemplate
      sigmaProduction piProduction in
  templateUniversalOpenMany inheritedTraversal
    coqFourStateTableAppendConcreteRowVariables =
    Some (tfImp below (tfImp oldLookup result)) ->
  RawCodedTemplatePrefixAtomicallyAdequate M translation combinedPrefix ->
  RawCodedFormulaAtomicallyAdequate M
    (rawTemplateFormula translation below) ->
  equalityHead = tfEq (ttVar 4) (ttParameter boundName) ->
  RawCodedFormulaAtomicallyAdequate M
    (rawTemplateFormula translation equalityHead) ->
  coqFourStateTableAppendRowModeParameterName <> boundName ->
  coqFourStateTableAppendRowFormulaParameterName <> boundName ->
  coqFourStateTableAppendRowAssignmentCodeParameterName <> boundName ->
  coqFourStateTableAppendRowAssignmentStepParameterName <> boundName ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail translation baseContext combinedPrefix)
    (rawTemplateFormula translation
      (coqLtSuccCasesAntecedentTemplate (ttVar 4) rowBound))
    antecedentRoot ->
  RawFourStateTableAppendInheritedLocalRootsAt M translation
    baseContext combinedPrefix inheritedTraversal oldLookup ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail translation baseContext combinedPrefix)
    (rawTemplateFormula translation
      (coqFourStateTableAppendEqualityRowLookupTemplate
        coqFourStateTableAppendRowModeParameterName
        coqFourStateTableAppendRowFormulaParameterName
        coqFourStateTableAppendRowAssignmentCodeParameterName
        coqFourStateTableAppendRowAssignmentStepParameterName
        (ttVar 4) (ttVar 3) (ttVar 2) (ttVar 1) (ttVar 0)))
    rowLookupRoot ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail translation baseContext combinedPrefix)
    (rawTemplateFormula translation fixedResult) fixedResultRoot ->
  RawCodedPAGrowingTemplateLocalProofAt M translation
    baseWitnessList baseContext combinedPrefix
    (rawTemplateFormula translation result).
Proof.
  intros M hPA translation hagreement
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    boundName rowBound sigmaProduction piProduction
    inheritedTraversal oldLookup witnesses extraPrefix
    antecedentRoot rowLookupRoot fixedResultRoot
    baseWitnessList baseContext rowPrefix combinedPrefix below equalityHead
    fixedResult result
    hopen hprefix hbelowAdequate hequalityHead hequalityAdequate
    hmodeFresh hformulaFresh hassignmentCodeFresh hassignmentStepFresh
    hantecedent hinheritedRoots hrowLookup hfixedResult.
  cbn zeta in *.
  assert (hbase : RawCodedPAAxiomWitnessContext M
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        witnesses (raw_zero M))
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses (raw_zero M))).
  {
    pose proof (raw_templateEmbeddedPAAxiomWitnessContext
      M hPA translation hagreement witnesses) as hbaseTemplate.
    rewrite (raw_templateContextCode_embedPAAxiomWitnesses
      M translation hagreement witnesses) in hbaseTemplate.
    exact hbaseTemplate.
  }
  assert (hextraPrefix :
      RawCodedTemplatePrefixAtomicallyAdequate M translation extraPrefix).
  {
    intros formula hformula.
    apply hprefix. apply in_or_app. left. exact hformula.
  }
  pose proof
    (raw_fourStateTableAppendEqualityProductionInputsAt_on_witnessed_row_context_under_prefix_of_local_roots
      M hPA translation hagreement
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      boundName rowBound sigmaProduction piProduction witnesses
      extraPrefix rowLookupRoot fixedResultRoot
      hextraPrefix hequalityHead hequalityAdequate
      hrowLookup hfixedResult)
    as hequalityBaseInputs.
  eapply
    (raw_codedPALocalProofOf_four_state_table_append_concrete_closed_row_cases_on_base_included_growing_witnessed_tail_under_prefix
      M hPA translation hagreement
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        witnesses (raw_zero M))
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses (raw_zero M))
      (extraPrefix ++ coqFourStateTableAppendRowPrefix
        modeCode modeStep formulaCode formulaStep
        assignmentCodeCode assignmentCodeStep
        assignmentStepCode assignmentStepStep
        (ttParameter boundName)
        (ttParameter coqFourStateTableAppendRowModeParameterName)
        (ttParameter coqFourStateTableAppendRowFormulaParameterName)
        (ttParameter coqFourStateTableAppendRowAssignmentCodeParameterName)
        (ttParameter coqFourStateTableAppendRowAssignmentStepParameterName))
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      boundName rowBound antecedentRoot sigmaProduction piProduction).
  - exact hprefix.
  - exact hequalityAdequate.
  - exact hbase.
  - exact hmodeFresh.
  - exact hformulaFresh.
  - exact hassignmentCodeFresh.
  - exact hassignmentStepFresh.
  - exact hantecedent.
  - intros sourceWitnessList sourceContext hsource hbaseIncluded.
    pose proof
      (raw_fourStateTableAppendInheritedLocalRootsAt_transport
        M hPA translation
        (rawStandardPAAxiomWitnessPrefixWitnessListCode M
          witnesses (raw_zero M))
        (rawStandardPAAxiomWitnessPrefixContextCode M
          witnesses (raw_zero M))
        sourceWitnessList sourceContext
        (extraPrefix ++ coqFourStateTableAppendRowPrefix
          modeCode modeStep formulaCode formulaStep
          assignmentCodeCode assignmentCodeStep
          assignmentStepCode assignmentStepStep
          (ttParameter boundName)
          (ttParameter coqFourStateTableAppendRowModeParameterName)
          (ttParameter coqFourStateTableAppendRowFormulaParameterName)
          (ttParameter coqFourStateTableAppendRowAssignmentCodeParameterName)
          (ttParameter
            coqFourStateTableAppendRowAssignmentStepParameterName))
        inheritedTraversal oldLookup
        hbase hsource hbaseIncluded hinheritedRoots)
      as hsourceInheritedRoots.
    pose proof
      (raw_fourStateTableAppendInheritedProductionInputsAt_of_local_root_package
        M hPA translation sourceWitnessList sourceContext
        (extraPrefix ++ coqFourStateTableAppendRowPrefix
          modeCode modeStep formulaCode formulaStep
          assignmentCodeCode assignmentCodeStep
          assignmentStepCode assignmentStepStep
          (ttParameter boundName)
          (ttParameter coqFourStateTableAppendRowModeParameterName)
          (ttParameter coqFourStateTableAppendRowFormulaParameterName)
          (ttParameter coqFourStateTableAppendRowAssignmentCodeParameterName)
          (ttParameter
            coqFourStateTableAppendRowAssignmentStepParameterName))
        inheritedTraversal
        (coqLtSuccCasesBelowTemplate (ttVar 4) rowBound)
        oldLookup hsource hbelowAdequate hsourceInheritedRoots)
      as hpredecessorInputs.
    exact
      (raw_codedPALocalProofOf_four_state_table_append_inherited_row_production_growing_tail
        M hPA translation sourceWitnessList sourceContext
        (coqLtSuccCasesBelowTemplate (ttVar 4) rowBound ::
          extraPrefix ++ coqFourStateTableAppendRowPrefix
            modeCode modeStep formulaCode formulaStep
            assignmentCodeCode assignmentCodeStep
            assignmentStepCode assignmentStepStep
            (ttParameter boundName)
            (ttParameter coqFourStateTableAppendRowModeParameterName)
            (ttParameter coqFourStateTableAppendRowFormulaParameterName)
            (ttParameter
              coqFourStateTableAppendRowAssignmentCodeParameterName)
            (ttParameter
              coqFourStateTableAppendRowAssignmentStepParameterName))
        inheritedTraversal
        (coqLtSuccCasesBelowTemplate (ttVar 4) rowBound)
        oldLookup
        (coqFourStateTableAppendConcreteClosedRowProductionTemplate
          sigmaProduction piProduction)
        hsource hopen hpredecessorInputs).
  - intros sourceWitnessList sourceContext hsource hbaseIncluded.
    exact
      (raw_fourStateTableAppendEqualityProductionInputsAt_transport
        M hPA translation
        (rawStandardPAAxiomWitnessPrefixWitnessListCode M
          witnesses (raw_zero M))
        (rawStandardPAAxiomWitnessPrefixContextCode M
          witnesses (raw_zero M))
        sourceWitnessList sourceContext
        (coqLtSuccCasesEqualTemplate (ttVar 4) rowBound ::
          extraPrefix ++ coqFourStateTableAppendRowPrefix
            modeCode modeStep formulaCode formulaStep
            assignmentCodeCode assignmentCodeStep
            assignmentStepCode assignmentStepStep
            (ttParameter boundName)
            (ttParameter coqFourStateTableAppendRowModeParameterName)
            (ttParameter coqFourStateTableAppendRowFormulaParameterName)
            (ttParameter
              coqFourStateTableAppendRowAssignmentCodeParameterName)
            (ttParameter
              coqFourStateTableAppendRowAssignmentStepParameterName))
        modeCode modeStep formulaCode formulaStep
        assignmentCodeCode assignmentCodeStep
        assignmentStepCode assignmentStepStep
        boundName
        coqFourStateTableAppendRowModeParameterName
        coqFourStateTableAppendRowFormulaParameterName
        coqFourStateTableAppendRowAssignmentCodeParameterName
        coqFourStateTableAppendRowAssignmentStepParameterName
        (ttVar 4) (ttVar 3) (ttVar 2) (ttVar 1) (ttVar 0)
        (coqFourStateTableAppendNamedClosedRowProductionTemplate
          sigmaProduction piProduction)
        hbase hsource hbaseIncluded hequalityBaseInputs).
Qed.

(** Instantiate the intervening prefix with the two premises of the literal
    traversal row, construct both premises as represented assumption leaves,
    run the complete case compiler, and discharge the assumptions in the
    required [bound -> lookup -> production] order. *)
Theorem
    raw_codedPALocalProofOf_four_state_table_append_concrete_closed_row_implications_on_witnessed_row_context :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    boundName rowBound sigmaProduction piProduction
    inheritedTraversal oldLookup witnesses fixedResultRoot,
  let baseWitnessList :=
    rawStandardPAAxiomWitnessPrefixWitnessListCode M
      witnesses (raw_zero M) in
  let baseContext :=
    rawStandardPAAxiomWitnessPrefixContextCode M
      witnesses (raw_zero M) in
  let rowPrefix := coqFourStateTableAppendRowPrefix
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    (ttParameter boundName)
    (ttParameter coqFourStateTableAppendRowModeParameterName)
    (ttParameter coqFourStateTableAppendRowFormulaParameterName)
    (ttParameter coqFourStateTableAppendRowAssignmentCodeParameterName)
    (ttParameter coqFourStateTableAppendRowAssignmentStepParameterName) in
  let antecedent := coqLtSuccCasesAntecedentTemplate (ttVar 4) rowBound in
  let rowLookup :=
    coqFourStateTableAppendEqualityRowLookupTemplate
      coqFourStateTableAppendRowModeParameterName
      coqFourStateTableAppendRowFormulaParameterName
      coqFourStateTableAppendRowAssignmentCodeParameterName
      coqFourStateTableAppendRowAssignmentStepParameterName
      (ttVar 4) (ttVar 3) (ttVar 2) (ttVar 1) (ttVar 0) in
  let below := coqLtSuccCasesBelowTemplate (ttVar 4) rowBound in
  let equalityHead := coqLtSuccCasesEqualTemplate (ttVar 4) rowBound in
  let fixedResult :=
    coqFourStateTableAppendNamedClosedRowProductionTemplate
      sigmaProduction piProduction in
  let result :=
    coqFourStateTableAppendConcreteClosedRowProductionTemplate
      sigmaProduction piProduction in
  templateUniversalOpenMany inheritedTraversal
    coqFourStateTableAppendConcreteRowVariables =
    Some (tfImp below (tfImp oldLookup result)) ->
  RawCodedTemplatePrefixAtomicallyAdequate M translation rowPrefix ->
  RawCodedFormulaAtomicallyAdequate M
    (rawTemplateFormula translation antecedent) ->
  RawCodedFormulaAtomicallyAdequate M
    (rawTemplateFormula translation rowLookup) ->
  RawCodedFormulaAtomicallyAdequate M
    (rawTemplateFormula translation below) ->
  equalityHead = tfEq (ttVar 4) (ttParameter boundName) ->
  RawCodedFormulaAtomicallyAdequate M
    (rawTemplateFormula translation equalityHead) ->
  coqFourStateTableAppendRowModeParameterName <> boundName ->
  coqFourStateTableAppendRowFormulaParameterName <> boundName ->
  coqFourStateTableAppendRowAssignmentCodeParameterName <> boundName ->
  coqFourStateTableAppendRowAssignmentStepParameterName <> boundName ->
  RawFourStateTableAppendInheritedLocalRootsAt M translation
    baseContext rowPrefix inheritedTraversal oldLookup ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail translation baseContext rowPrefix)
    (rawTemplateFormula translation fixedResult) fixedResultRoot ->
  RawCodedPAGrowingTemplateLocalProofAt M translation
    baseWitnessList baseContext rowPrefix
    (rawTemplateFormula translation
      (tfImp antecedent (tfImp rowLookup result))).
Proof.
  intros M hPA translation hagreement
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    boundName rowBound sigmaProduction piProduction
    inheritedTraversal oldLookup witnesses fixedResultRoot
    baseWitnessList baseContext rowPrefix antecedent rowLookup below
    equalityHead fixedResult result
    hopen hrowPrefix hantecedentAdequate hrowLookupAdequate
    hbelowAdequate hequalityHead hequalityAdequate
    hmodeFresh hformulaFresh hassignmentCodeFresh hassignmentStepFresh
    hinheritedRoots hfixedResult.
  cbn zeta in *.
  assert (hbase : RawCodedPAAxiomWitnessContext M
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        witnesses (raw_zero M))
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses (raw_zero M))).
  {
    pose proof (raw_templateEmbeddedPAAxiomWitnessContext
      M hPA translation hagreement witnesses) as hbaseTemplate.
    rewrite (raw_templateContextCode_embedPAAxiomWitnesses
      M translation hagreement witnesses) in hbaseTemplate.
    exact hbaseTemplate.
  }
  set (actualRowPrefix := coqFourStateTableAppendRowPrefix
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    (ttParameter boundName)
    (ttParameter coqFourStateTableAppendRowModeParameterName)
    (ttParameter coqFourStateTableAppendRowFormulaParameterName)
    (ttParameter coqFourStateTableAppendRowAssignmentCodeParameterName)
    (ttParameter coqFourStateTableAppendRowAssignmentStepParameterName)).
  set (actualAntecedent :=
    coqLtSuccCasesAntecedentTemplate (ttVar 4) rowBound).
  set (actualRowLookup :=
    coqFourStateTableAppendEqualityRowLookupTemplate
      coqFourStateTableAppendRowModeParameterName
      coqFourStateTableAppendRowFormulaParameterName
      coqFourStateTableAppendRowAssignmentCodeParameterName
      coqFourStateTableAppendRowAssignmentStepParameterName
      (ttVar 4) (ttVar 3) (ttVar 2) (ttVar 1) (ttVar 0)).
  set (extraPrefix := [actualRowLookup; actualAntecedent]).
  assert (hextraPrefix :
      RawCodedTemplatePrefixAtomicallyAdequate M translation extraPrefix).
  {
    intros formula [hformula | [hformula | hformula]].
    - subst formula. exact hrowLookupAdequate.
    - subst formula. exact hantecedentAdequate.
    - contradiction.
  }
  assert (hcombinedPrefix :
      RawCodedTemplatePrefixAtomicallyAdequate M translation
        (extraPrefix ++ actualRowPrefix)).
  {
    intros formula hformula.
    apply in_app_or in hformula.
    destruct hformula as [hformula | hformula].
    - exact (hextraPrefix formula hformula).
    - exact (hrowPrefix formula hformula).
  }
  assert (hrowContext : RawContextListRealizable M
      (rawTemplateContextCodeOnTail translation
        (rawStandardPAAxiomWitnessPrefixContextCode M
          witnesses (raw_zero M)) actualRowPrefix)).
  {
    apply (raw_templateContextOnTail_realizable M hPA).
    exact (raw_codedPAAxiomWitnessContext_context_realizable M
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        witnesses (raw_zero M))
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses (raw_zero M)) hbase).
  }
  destruct hinheritedRoots as
    (traversalRoot & oldLookupRoot & htraversal & holdLookup).
  destruct (raw_codedPALocalProof_templatePrefix
    M hPA translation
    (rawTemplateContextCodeOnTail translation
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses (raw_zero M)) actualRowPrefix)
    extraPrefix (rawTemplateFormula translation inheritedTraversal)
    traversalRoot hrowContext hextraPrefix htraversal)
    as [prefixedTraversalRoot hprefixedTraversal].
  destruct (raw_codedPALocalProof_templatePrefix
    M hPA translation
    (rawTemplateContextCodeOnTail translation
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses (raw_zero M)) actualRowPrefix)
    extraPrefix (rawTemplateFormula translation oldLookup)
    oldLookupRoot hrowContext hextraPrefix holdLookup)
    as [prefixedOldLookupRoot hprefixedOldLookup].
  destruct (raw_codedPALocalProof_templatePrefix
    M hPA translation
    (rawTemplateContextCodeOnTail translation
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses (raw_zero M)) actualRowPrefix)
    extraPrefix
    (rawTemplateFormula translation
      (coqFourStateTableAppendNamedClosedRowProductionTemplate
        sigmaProduction piProduction))
    fixedResultRoot hrowContext hextraPrefix hfixedResult)
    as [prefixedFixedResultRoot hprefixedFixedResult].
  assert (hantecedentTail : RawContextListRealizable M
      (rawTemplateContextCodeOnTail translation
        (rawStandardPAAxiomWitnessPrefixContextCode M
          witnesses (raw_zero M)) actualRowPrefix)).
  { exact hrowContext. }
  pose proof (raw_codedPALocalProofOf_assumption M hPA
    (rawTemplateContextCodeOnTail translation
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses (raw_zero M)) actualRowPrefix)
    (rawTemplateFormula translation actualAntecedent)
    hantecedentTail) as hantecedentHead.
  assert (hrowLookupSingleton :
      RawCodedTemplatePrefixAtomicallyAdequate M translation
        [actualRowLookup]).
  {
    intros formula [hformula | hformula].
    - subst formula. exact hrowLookupAdequate.
    - contradiction.
  }
  assert (hantecedentContext : RawContextListRealizable M
      (rawTemplateContextCodeOnTail translation
        (rawStandardPAAxiomWitnessPrefixContextCode M
          witnesses (raw_zero M))
        (actualAntecedent :: actualRowPrefix))).
  {
    apply (raw_templateContextOnTail_realizable M hPA).
    exact (raw_codedPAAxiomWitnessContext_context_realizable M
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        witnesses (raw_zero M))
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses (raw_zero M)) hbase).
  }
  destruct (raw_codedPALocalProof_templatePrefix
    M hPA translation
    (rawTemplateContextCodeOnTail translation
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses (raw_zero M))
      (actualAntecedent :: actualRowPrefix))
    [actualRowLookup]
    (rawTemplateFormula translation actualAntecedent)
    (rawProofAssumptionRoot M
      (rawListNode M (rawTemplateFormula translation actualAntecedent)
        (rawTemplateContextCodeOnTail translation
          (rawStandardPAAxiomWitnessPrefixContextCode M
            witnesses (raw_zero M)) actualRowPrefix))
      (rawTemplateFormula translation actualAntecedent))
    hantecedentContext hrowLookupSingleton hantecedentHead)
    as [antecedentRoot hantecedent].
  pose proof (raw_codedPALocalProofOf_assumption M hPA
    (rawTemplateContextCodeOnTail translation
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses (raw_zero M))
      (actualAntecedent :: actualRowPrefix))
    (rawTemplateFormula translation actualRowLookup)
    hantecedentContext) as hrowLookup.
  pose proof
    (raw_codedPALocalProofOf_four_state_table_append_concrete_closed_row_of_inherited_local_roots_on_witnessed_row_context_under_prefix
      M hPA translation hagreement
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      boundName rowBound sigmaProduction piProduction
      inheritedTraversal oldLookup witnesses extraPrefix
      antecedentRoot
      (rawProofAssumptionRoot M
        (rawListNode M (rawTemplateFormula translation actualRowLookup)
          (rawTemplateContextCodeOnTail translation
            (rawStandardPAAxiomWitnessPrefixContextCode M
              witnesses (raw_zero M))
            (actualAntecedent :: actualRowPrefix)))
        (rawTemplateFormula translation actualRowLookup))
      prefixedFixedResultRoot
      hopen hcombinedPrefix hbelowAdequate
      hequalityHead hequalityAdequate
      hmodeFresh hformulaFresh hassignmentCodeFresh hassignmentStepFresh
      hantecedent
      (ex_intro _ prefixedTraversalRoot
        (ex_intro _ prefixedOldLookupRoot
          (conj hprefixedTraversal hprefixedOldLookup)))
      hrowLookup hprefixedFixedResult) as hresult.
  destruct hresult as
    (finalWitnessList & finalContext & resultRoot &
      hfinalContext & hbaseFinalIncluded & hresult).
  pose proof (raw_codedPALocalProofOf_impI M hPA
    (rawTemplateContextCodeOnTail translation finalContext
      (actualAntecedent :: actualRowPrefix))
    (rawTemplateFormula translation actualRowLookup)
    (rawTemplateFormula translation
      (coqFourStateTableAppendConcreteClosedRowProductionTemplate
        sigmaProduction piProduction))
    resultRoot hresult) as hlookupImp.
  rewrite <- rawTemplateFormula_imp in hlookupImp.
  pose proof (raw_codedPALocalProofOf_impI M hPA
    (rawTemplateContextCodeOnTail translation finalContext actualRowPrefix)
    (rawTemplateFormula translation actualAntecedent)
    (rawTemplateFormula translation
      (tfImp actualRowLookup
        (coqFourStateTableAppendConcreteClosedRowProductionTemplate
          sigmaProduction piProduction)))
    (rawProofImpIRoot M
      (rawTemplateContextCodeOnTail translation finalContext
        (actualAntecedent :: actualRowPrefix))
      (rawTemplateFormula translation actualRowLookup)
      (rawTemplateFormula translation
        (coqFourStateTableAppendConcreteClosedRowProductionTemplate
          sigmaProduction piProduction)) resultRoot)
    hlookupImp) as hboundImp.
  rewrite <- rawTemplateFormula_imp in hboundImp.
  unfold RawCodedPAGrowingTemplateLocalProofAt.
  exists finalWitnessList, finalContext,
    (rawProofImpIRoot M
      (rawTemplateContextCodeOnTail translation finalContext actualRowPrefix)
      (rawTemplateFormula translation actualAntecedent)
      (rawTemplateFormula translation
        (tfImp actualRowLookup
          (coqFourStateTableAppendConcreteClosedRowProductionTemplate
            sigmaProduction piProduction)))
      (rawProofImpIRoot M
        (rawTemplateContextCodeOnTail translation finalContext
          (actualAntecedent :: actualRowPrefix))
        (rawTemplateFormula translation actualRowLookup)
        (rawTemplateFormula translation
          (coqFourStateTableAppendConcreteClosedRowProductionTemplate
            sigmaProduction piProduction)) resultRoot)).
  split; [exact hfinalContext |].
  split; [exact hbaseFinalIncluded | exact hboundImp].
Qed.

(** Compile [i < S b -> i < b \/ i = b] in the literal appended-row
    context.  The returned standard witness batch is concatenated ahead of
    the caller's batch in both the witness-list and context views. *)
Theorem
    raw_codedPALocalProofOf_four_state_table_append_row_lt_succ_cases :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    bound mode formula assignmentCode assignmentStep
    witnesses index rowBound antecedentRoot,
  RawCodedTemplatePrefixAtomicallyAdequate M translation
    (coqFourStateTableAppendRowPrefix
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      bound mode formula assignmentCode assignmentStep) ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCode translation
      (templateContextShiftMany 5
        (coqFourStateTableAppendWitnessContext
          modeCode modeStep formulaCode formulaStep
          assignmentCodeCode assignmentCodeStep
          assignmentStepCode assignmentStepStep
          bound mode formula assignmentCode assignmentStep
          (embedPAContext (map witnessedAxiom witnesses)))))
    (rawTemplateFormula translation
      (coqLtSuccCasesAntecedentTemplate index rowBound)) antecedentRoot ->
  exists (extra : StandardPAAxiomWitnessPrefix) (root : M),
    RawCodedPAAxiomWitnessContext M
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        (extra ++ witnesses) (raw_zero M))
      (rawTemplateContextCode translation
        (embedPAContext (map witnessedAxiom (extra ++ witnesses)))) /\
    RawCodedPALocalProofOf M
      (rawTemplateContextCode translation
        (templateContextShiftMany 5
          (coqFourStateTableAppendWitnessContext
            modeCode modeStep formulaCode formulaStep
            assignmentCodeCode assignmentCodeStep
            assignmentStepCode assignmentStepStep
            bound mode formula assignmentCode assignmentStep
            (embedPAContext
              (map witnessedAxiom (extra ++ witnesses))))))
      (rawTemplateFormula translation
        (coqLtSuccCasesResultTemplate index rowBound)) root.
Proof.
  intros M hPA translation hagreement
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    bound mode formula assignmentCode assignmentStep
    witnesses index rowBound antecedentRoot hprefix hantecedent.
  assert (hbase : RawCodedPAAxiomWitnessContext M
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        witnesses (raw_zero M))
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses (raw_zero M))).
  {
    pose proof (raw_templateEmbeddedPAAxiomWitnessContext
      M hPA translation hagreement witnesses) as hbaseTemplate.
    rewrite (raw_templateContextCode_embedPAAxiomWitnesses
      M translation hagreement witnesses) in hbaseTemplate.
    exact hbaseTemplate.
  }
  assert (hantecedentPrefix : RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation
        (rawStandardPAAxiomWitnessPrefixContextCode M
          witnesses (raw_zero M))
        (coqFourStateTableAppendRowPrefix
          modeCode modeStep formulaCode formulaStep
          assignmentCodeCode assignmentCodeStep
          assignmentStepCode assignmentStepStep
          bound mode formula assignmentCode assignmentStep))
      (rawTemplateFormula translation
        (coqLtSuccCasesAntecedentTemplate index rowBound))
      antecedentRoot).
  {
    rewrite <- (raw_fourStateTableAppendRowContext_witnessed_tail_code
      M translation hagreement
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      bound mode formula assignmentCode assignmentStep witnesses).
    exact hantecedent.
  }
  destruct
    (raw_codedPALocalProofOf_lt_succ_cases_on_witnessed_tail_under_prefix
      M hPA translation hagreement
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        witnesses (raw_zero M))
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses (raw_zero M))
      (coqFourStateTableAppendRowPrefix
        modeCode modeStep formulaCode formulaStep
        assignmentCodeCode assignmentCodeStep
        assignmentStepCode assignmentStepStep
        bound mode formula assignmentCode assignmentStep)
      index rowBound antecedentRoot hprefix hbase hantecedentPrefix)
    as (extra & root & hextended & hcases).
  exists extra, root.
  split.
  - rewrite rawStandardPAAxiomWitnessPrefixWitnessListCode_app.
    rewrite (raw_templateContextCode_embedPAAxiomWitnesses
      M translation hagreement (extra ++ witnesses)).
    rewrite rawStandardPAAxiomWitnessPrefixContextCode_app.
    exact hextended.
  - rewrite (raw_fourStateTableAppendRowContext_witnessed_tail_code
      M translation hagreement
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      bound mode formula assignmentCode assignmentStep
      (extra ++ witnesses)).
    rewrite rawStandardPAAxiomWitnessPrefixContextCode_app.
    exact hcases.
Qed.

(** Exact represented case elimination in the append-row context.  Each
    callback sees its arithmetic branch formula as the literal head of the
    combined temporary context. *)
Theorem
    raw_codedPALocalProofOf_four_state_table_append_row_lt_succ_cases_eliminate :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    bound mode formula assignmentCode assignmentStep
    witnesses index rowBound antecedentRoot conclusion,
  RawCodedTemplatePrefixAtomicallyAdequate M translation
    (coqFourStateTableAppendRowPrefix
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      bound mode formula assignmentCode assignmentStep) ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCode translation
      (templateContextShiftMany 5
        (coqFourStateTableAppendWitnessContext
          modeCode modeStep formulaCode formulaStep
          assignmentCodeCode assignmentCodeStep
          assignmentStepCode assignmentStepStep
          bound mode formula assignmentCode assignmentStep
          (embedPAContext (map witnessedAxiom witnesses)))))
    (rawTemplateFormula translation
      (coqLtSuccCasesAntecedentTemplate index rowBound)) antecedentRoot ->
  (forall extra,
    RawCodedPAAxiomWitnessContext M
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        (extra ++ witnesses) (raw_zero M))
      (rawTemplateContextCode translation
        (embedPAContext (map witnessedAxiom (extra ++ witnesses)))) ->
    exists root,
      RawCodedPALocalProofOf M
        (rawListNode M
          (rawTemplateFormula translation
            (coqLtSuccCasesBelowTemplate index rowBound))
          (rawTemplateContextCode translation
            (templateContextShiftMany 5
              (coqFourStateTableAppendWitnessContext
                modeCode modeStep formulaCode formulaStep
                assignmentCodeCode assignmentCodeStep
                assignmentStepCode assignmentStepStep
                bound mode formula assignmentCode assignmentStep
                (embedPAContext
                  (map witnessedAxiom (extra ++ witnesses)))))))
        conclusion root) ->
  (forall extra,
    RawCodedPAAxiomWitnessContext M
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        (extra ++ witnesses) (raw_zero M))
      (rawTemplateContextCode translation
        (embedPAContext (map witnessedAxiom (extra ++ witnesses)))) ->
    exists root,
      RawCodedPALocalProofOf M
        (rawListNode M
          (rawTemplateFormula translation
            (coqLtSuccCasesEqualTemplate index rowBound))
          (rawTemplateContextCode translation
            (templateContextShiftMany 5
              (coqFourStateTableAppendWitnessContext
                modeCode modeStep formulaCode formulaStep
                assignmentCodeCode assignmentCodeStep
                assignmentStepCode assignmentStepStep
                bound mode formula assignmentCode assignmentStep
                (embedPAContext
                  (map witnessedAxiom (extra ++ witnesses)))))))
        conclusion root) ->
  exists (extra : StandardPAAxiomWitnessPrefix) (root : M),
    RawCodedPAAxiomWitnessContext M
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        (extra ++ witnesses) (raw_zero M))
      (rawTemplateContextCode translation
        (embedPAContext (map witnessedAxiom (extra ++ witnesses)))) /\
    RawCodedPALocalProofOf M
      (rawTemplateContextCode translation
        (templateContextShiftMany 5
          (coqFourStateTableAppendWitnessContext
            modeCode modeStep formulaCode formulaStep
            assignmentCodeCode assignmentCodeStep
            assignmentStepCode assignmentStepStep
            bound mode formula assignmentCode assignmentStep
            (embedPAContext
              (map witnessedAxiom (extra ++ witnesses))))))
      conclusion root.
Proof.
  intros M hPA translation hagreement
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    bound mode formula assignmentCode assignmentStep
    witnesses index rowBound antecedentRoot conclusion
    hprefix hantecedent hbelowBranch hequalBranch.
  assert (hbase : RawCodedPAAxiomWitnessContext M
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        witnesses (raw_zero M))
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses (raw_zero M))).
  {
    pose proof (raw_templateEmbeddedPAAxiomWitnessContext
      M hPA translation hagreement witnesses) as hbaseTemplate.
    rewrite (raw_templateContextCode_embedPAAxiomWitnesses
      M translation hagreement witnesses) in hbaseTemplate.
    exact hbaseTemplate.
  }
  assert (hantecedentPrefix : RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation
        (rawStandardPAAxiomWitnessPrefixContextCode M
          witnesses (raw_zero M))
        (coqFourStateTableAppendRowPrefix
          modeCode modeStep formulaCode formulaStep
          assignmentCodeCode assignmentCodeStep
          assignmentStepCode assignmentStepStep
          bound mode formula assignmentCode assignmentStep))
      (rawTemplateFormula translation
        (coqLtSuccCasesAntecedentTemplate index rowBound))
      antecedentRoot).
  {
    rewrite <- (raw_fourStateTableAppendRowContext_witnessed_tail_code
      M translation hagreement
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      bound mode formula assignmentCode assignmentStep witnesses).
    exact hantecedent.
  }
  pose proof
    (raw_codedPALocalProofOf_lt_succ_cases_eliminate_on_witnessed_tail_under_prefix
      M hPA translation hagreement
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        witnesses (raw_zero M))
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses (raw_zero M))
      (coqFourStateTableAppendRowPrefix
        modeCode modeStep formulaCode formulaStep
        assignmentCodeCode assignmentCodeStep
        assignmentStepCode assignmentStepStep
        bound mode formula assignmentCode assignmentStep)
      index rowBound antecedentRoot conclusion
      hprefix hbase hantecedentPrefix) as hsplit.
  lazymatch type of hsplit with
  | ?belowType -> ?equalType -> _ =>
      assert (hbelowForSplit : belowType);
      [ intros extra hextended;
        pose proof (raw_fourStateTableAppendRow_combined_witnessed_tail
          M translation hagreement extra witnesses hextended) as hcombined;
        destruct (hbelowBranch extra hcombined) as [root hroot];
        exists root;
        rewrite <- (raw_fourStateTableAppendRowContext_combined_tail_code
          M translation hagreement
          modeCode modeStep formulaCode formulaStep
          assignmentCodeCode assignmentCodeStep
          assignmentStepCode assignmentStepStep
          bound mode formula assignmentCode assignmentStep extra witnesses);
        exact hroot
      | assert (hequalForSplit : equalType);
        [ intros extra hextended;
          pose proof (raw_fourStateTableAppendRow_combined_witnessed_tail
            M translation hagreement extra witnesses hextended) as hcombined;
          destruct (hequalBranch extra hcombined) as [root hroot];
          exists root;
          rewrite <- (raw_fourStateTableAppendRowContext_combined_tail_code
            M translation hagreement
            modeCode modeStep formulaCode formulaStep
            assignmentCodeCode assignmentCodeStep
            assignmentStepCode assignmentStepStep
            bound mode formula assignmentCode assignmentStep extra witnesses);
          exact hroot
        | destruct (hsplit hbelowForSplit hequalForSplit)
            as (extra & root & hextended & hroot);
          exists extra, root;
          split;
          [ exact (raw_fourStateTableAppendRow_combined_witnessed_tail
              M translation hagreement extra witnesses hextended)
          | rewrite (raw_fourStateTableAppendRowContext_combined_tail_code
              M translation hagreement
              modeCode modeStep formulaCode formulaStep
              assignmentCodeCode assignmentCodeStep
              assignmentStepCode assignmentStepStep
              bound mode formula assignmentCode assignmentStep
              extra witnesses);
            exact hroot ] ] ]
  end.
Qed.

(** Concrete predecessor callback for the represented case split.  Two
    structural equalities identify the arithmetic source's antecedent and
    left branch with the append preservation law's current and old bounds.
    The old bound is then obtained by an honest head-assumption proof. *)
Theorem
    raw_codedPALocalProofOf_four_state_table_append_row_predecessor_branch_lookup :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M)
    context
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    bound mode formula assignmentCode assignmentStep
    index rowBound rowMode rowFormula rowAssignmentCode rowAssignmentStep
    currentBoundRoot oldStateLookupRoot,
  let shiftedWitnessContext := templateContextShiftMany 5
    (coqFourStateTableAppendWitnessContext
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      bound mode formula assignmentCode assignmentStep context) in
  let shiftedWitnessContextCode :=
    rawTemplateContextCode translation shiftedWitnessContext in
  let branchHead := rawTemplateFormula translation
    (coqLtSuccCasesBelowTemplate index rowBound) in
  let modeAt := coqFourStateTableAppendRowModePreservationAtTemplate
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    bound mode formula assignmentCode assignmentStep index rowMode in
  let formulaAt := coqFourStateTableAppendRowFormulaPreservationAtTemplate
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    bound mode formula assignmentCode assignmentStep index rowFormula in
  let assignmentCodeAt :=
    coqFourStateTableAppendRowAssignmentCodePreservationAtTemplate
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      bound mode formula assignmentCode assignmentStep
      index rowAssignmentCode in
  let assignmentStepAt :=
    coqFourStateTableAppendRowAssignmentStepPreservationAtTemplate
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      bound mode formula assignmentCode assignmentStep
      index rowAssignmentStep in
  templateImpAntecedent formulaAt = templateImpAntecedent modeAt ->
  templateImpAntecedent assignmentCodeAt = templateImpAntecedent modeAt ->
  templateImpAntecedent assignmentStepAt = templateImpAntecedent modeAt ->
  templateImp3SecondPremise formulaAt =
    templateImp3SecondPremise modeAt ->
  templateImp3SecondPremise assignmentCodeAt =
    templateImp3SecondPremise modeAt ->
  templateImp3SecondPremise assignmentStepAt =
    templateImp3SecondPremise modeAt ->
  coqLtSuccCasesAntecedentTemplate index rowBound =
    coqFourStateTableAppendRowPredecessorCurrentBoundTemplate
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      bound mode formula assignmentCode assignmentStep index rowMode ->
  coqLtSuccCasesBelowTemplate index rowBound =
    coqFourStateTableAppendRowPredecessorOldBoundTemplate
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      bound mode formula assignmentCode assignmentStep index rowMode ->
  RawCodedFormulaAtomicallyAdequate M branchHead ->
  RawCodedPALocalProofOf M shiftedWitnessContextCode
    (rawTemplateFormula translation
      (coqLtSuccCasesAntecedentTemplate index rowBound))
    currentBoundRoot ->
  RawCodedPALocalProofOf M shiftedWitnessContextCode
    (rawTemplateFormula translation
      (coqFourStateTableAppendRowPredecessorOldStateLookupTemplate
        modeCode modeStep formulaCode formulaStep
        assignmentCodeCode assignmentCodeStep
        assignmentStepCode assignmentStepStep
        bound mode formula assignmentCode assignmentStep
        index rowMode rowFormula rowAssignmentCode rowAssignmentStep))
    oldStateLookupRoot ->
  exists root,
    RawCodedPALocalProofOf M
      (rawListNode M branchHead shiftedWitnessContextCode)
      (rawTemplateFormula translation
        (coqFourStateTableAppendRowPredecessorNewStateLookupTemplate
          modeCode modeStep formulaCode formulaStep
          assignmentCodeCode assignmentCodeStep
          assignmentStepCode assignmentStepStep
          bound mode formula assignmentCode assignmentStep
          index rowMode rowFormula rowAssignmentCode rowAssignmentStep)) root.
Proof.
  intros M hPA translation context
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    bound mode formula assignmentCode assignmentStep
    index rowBound rowMode rowFormula rowAssignmentCode rowAssignmentStep
    currentBoundRoot oldStateLookupRoot
    shiftedWitnessContext shiftedWitnessContextCode branchHead
    modeAt formulaAt assignmentCodeAt assignmentStepAt
    hformulaFirst hassignmentCodeFirst hassignmentStepFirst
    hformulaSecond hassignmentCodeSecond hassignmentStepSecond
    hantecedentCurrent hbelowOld hhead hcurrent holdLookup.
  cbn zeta in *.
  pose proof (raw_templateContext_realizable M hPA translation
    (templateContextShiftMany 5
      (coqFourStateTableAppendWitnessContext
        modeCode modeStep formulaCode formulaStep
        assignmentCodeCode assignmentCodeStep
        assignmentStepCode assignmentStepStep
        bound mode formula assignmentCode assignmentStep context)))
    as hcontext.
  pose proof (raw_codedPALocalProofOf_assumption M hPA
    (rawTemplateContextCode translation
      (templateContextShiftMany 5
        (coqFourStateTableAppendWitnessContext
          modeCode modeStep formulaCode formulaStep
          assignmentCodeCode assignmentCodeStep
          assignmentStepCode assignmentStepStep
          bound mode formula assignmentCode assignmentStep context)))
    (rawTemplateFormula translation
      (coqLtSuccCasesBelowTemplate index rowBound)) hcontext)
    as holdBoundAssumption.
  assert (hcurrentBound : RawCodedPALocalProofOf M
      (rawTemplateContextCode translation
        (templateContextShiftMany 5
          (coqFourStateTableAppendWitnessContext
            modeCode modeStep formulaCode formulaStep
            assignmentCodeCode assignmentCodeStep
            assignmentStepCode assignmentStepStep
            bound mode formula assignmentCode assignmentStep context)))
      (rawTemplateFormula translation
        (coqFourStateTableAppendRowPredecessorCurrentBoundTemplate
          modeCode modeStep formulaCode formulaStep
          assignmentCodeCode assignmentCodeStep
          assignmentStepCode assignmentStepStep
          bound mode formula assignmentCode assignmentStep index rowMode))
      currentBoundRoot).
  {
    rewrite <- hantecedentCurrent.
    exact hcurrent.
  }
  assert (holdBound : RawCodedPALocalProofOf M
      (rawListNode M
        (rawTemplateFormula translation
          (coqLtSuccCasesBelowTemplate index rowBound))
        (rawTemplateContextCode translation
          (templateContextShiftMany 5
            (coqFourStateTableAppendWitnessContext
              modeCode modeStep formulaCode formulaStep
              assignmentCodeCode assignmentCodeStep
              assignmentStepCode assignmentStepStep
              bound mode formula assignmentCode assignmentStep context))))
      (rawTemplateFormula translation
        (coqFourStateTableAppendRowPredecessorOldBoundTemplate
          modeCode modeStep formulaCode formulaStep
          assignmentCodeCode assignmentCodeStep
          assignmentStepCode assignmentStepStep
          bound mode formula assignmentCode assignmentStep index rowMode))
      (rawProofAssumptionRoot M
        (rawListNode M
          (rawTemplateFormula translation
            (coqLtSuccCasesBelowTemplate index rowBound))
          (rawTemplateContextCode translation
            (templateContextShiftMany 5
              (coqFourStateTableAppendWitnessContext
                modeCode modeStep formulaCode formulaStep
                assignmentCodeCode assignmentCodeStep
                assignmentStepCode assignmentStepStep
                bound mode formula assignmentCode assignmentStep context))))
        (rawTemplateFormula translation
          (coqLtSuccCasesBelowTemplate index rowBound)))).
  {
    rewrite <- hbelowOld.
    exact holdBoundAssumption.
  }
  eapply
    (raw_codedPALocalProofOf_four_state_table_append_row_predecessor_state_lookup_under_adequate_head
      M hPA translation context
      (rawTemplateFormula translation
        (coqLtSuccCasesBelowTemplate index rowBound))
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      bound mode formula assignmentCode assignmentStep
      index rowMode rowFormula rowAssignmentCode rowAssignmentStep
      currentBoundRoot _ oldStateLookupRoot).
  - exact hformulaFirst.
  - exact hassignmentCodeFirst.
  - exact hassignmentStepFirst.
  - exact hformulaSecond.
  - exact hassignmentCodeSecond.
  - exact hassignmentStepSecond.
  - exact hhead.
  - exact hcurrentBound.
  - exact holdBound.
  - exact holdLookup.
Qed.

End PABoundedRawCodedFourStateTableAppendRowLtSuccCases.
