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
  RawCodedRestrictedPAProof
  RawCodedFixedLevelTruth
  RawCodedFixedLevelTruthTotality
  RawCodedPAAxiomWitnessPrefix
  RawCodedProofAssumptionLeaf
  RawCodedPALocalProofExistential
  RawCodedPALocalProofComposition
  RawCodedPALocalProofContextInsertUnconditional
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
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedFixedLevelTruth.
Import PABoundedRawCodedFixedLevelTruthTotality.
Import PABoundedRawCodedPAAxiomWitnessPrefix.
Import PABoundedRawCodedProofAssumptionLeaf.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPALocalProofComposition.
Import PABoundedRawCodedPALocalProofContextInsertUnconditional.
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
