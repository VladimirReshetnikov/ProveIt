(**
  Proof-code compilation of simultaneous four-table append.

  [RawCodedFourStateTableAppendSource] packages the synchronized mode,
  formula, assignment-code, and assignment-step extensions as one fixed PA
  theorem.  This module opens all thirteen universal binders inside a raw PA
  model and applies the resulting implication to a caller proof of the four
  defined-through premises.

  Selecting one standard axiom witness prefix before all thirteen openings is
  important for traversal clients: all eight existential outputs then share
  one literal coded proof context.
*)

From Stdlib Require Import List.
From PAHF Require Import PAHF.
From PAListCoding Require Import ListCode.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors
  RawCodedRestrictedPAProof
  RawCodedPAAxiomWitnessPrefix
  RawCodedProofBinaryConstructors
  RawCodedProofAndIConstructor
  RawCodedPALocalProofExistential
  RawCodedPALocalProofAndIntroduction
  RawCodedPALocalProofConjunction
  RawCodedPALocalProofComposition
  RawCodedTemplateSyntax
  RawCodedTemplateProofCompiler
  RawCodedTemplateDirectStructuralTranslation
  RawCodedTemplateDirectStructuralPAAgreement
  RawCodedPALocalProofUniversalEliminationChain
  RawCodedFixedLevelTruth
  RawCodedFourStateTableAppendSource.

Import ListNotations.

Module PABoundedRawCodedFourStateTableAppendProofCompilation.

Import PA.
Import PAListCode.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedPAAxiomWitnessPrefix.
Import PABoundedRawCodedProofBinaryConstructors.
Import PABoundedRawCodedProofAndIConstructor.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPALocalProofAndIntroduction.
Import PABoundedRawCodedPALocalProofConjunction.
Import PABoundedRawCodedPALocalProofComposition.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedTemplateDirectStructuralTranslation.
Import PABoundedRawCodedTemplateDirectStructuralPAAgreement.
Import PABoundedRawCodedPALocalProofUniversalEliminationChain.
Import PABoundedRawCodedFixedLevelTruth.
Import PABoundedRawCodedFourStateTableAppendSource.

(** The replacements follow the source theorem's outer-to-inner order. *)
Definition coqFourStateTableAppendInstanceTemplate
    (modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      bound mode formula assignmentCode assignmentStep : TemplateTerm)
    : TemplateFormula :=
  match templateUniversalOpenMany
    (embedPAFormula codedFourStateTableAppendFormula)
    [modeCode; modeStep; formulaCode; formulaStep;
     assignmentCodeCode; assignmentCodeStep;
     assignmentStepCode; assignmentStepStep;
     bound; mode; formula; assignmentCode; assignmentStep] with
  | Some target => target
  | None => tfBot
  end.

(** The fallback branch is unreachable because the source has exactly
    thirteen leading universal binders. *)
Lemma coqFourStateTableAppendInstanceTemplate_open_many : forall
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    bound mode formula assignmentCode assignmentStep,
  templateUniversalOpenMany
    (embedPAFormula codedFourStateTableAppendFormula)
    [modeCode; modeStep; formulaCode; formulaStep;
     assignmentCodeCode; assignmentCodeStep;
     assignmentStepCode; assignmentStepStep;
     bound; mode; formula; assignmentCode; assignmentStep] =
  Some (coqFourStateTableAppendInstanceTemplate
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    bound mode formula assignmentCode assignmentStep).
Proof.
  intros.
  unfold coqFourStateTableAppendInstanceTemplate,
    codedFourStateTableAppendFormula,
    fourStateTableAppendRepeatedAll.
  reflexivity.
Qed.

(** Named projections hide the expanded beta-table arithmetic from clients. *)
Definition coqFourStateTableAppendDefinedTemplate
    (modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      bound mode formula assignmentCode assignmentStep : TemplateTerm)
    : TemplateFormula :=
  match coqFourStateTableAppendInstanceTemplate
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    bound mode formula assignmentCode assignmentStep with
  | tfImp defined _ => defined
  | _ => tfBot
  end.

Definition coqFourStateTableAppendExistsTemplate
    (modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      bound mode formula assignmentCode assignmentStep : TemplateTerm)
    : TemplateFormula :=
  match coqFourStateTableAppendInstanceTemplate
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    bound mode formula assignmentCode assignmentStep with
  | tfImp _ extensionExists => extensionExists
  | _ => tfBot
  end.

Lemma coqFourStateTableAppendInstanceTemplate_shape : forall
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    bound mode formula assignmentCode assignmentStep,
  coqFourStateTableAppendInstanceTemplate
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    bound mode formula assignmentCode assignmentStep =
  tfImp
    (coqFourStateTableAppendDefinedTemplate
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      bound mode formula assignmentCode assignmentStep)
    (coqFourStateTableAppendExistsTemplate
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      bound mode formula assignmentCode assignmentStep).
Proof.
  intros.
  unfold coqFourStateTableAppendDefinedTemplate,
    coqFourStateTableAppendExistsTemplate,
    coqFourStateTableAppendInstanceTemplate,
    codedFourStateTableAppendFormula,
    fourStateTableAppendRepeatedAll.
  reflexivity.
Qed.

(** Stable projections for a right-associated four-way conjunction.  Keeping
    these generic avoids unfolding the large beta-definedness formula when a
    traversal client needs just one of its four proof roots. *)
Definition templateAndFirst (source : TemplateFormula) : TemplateFormula :=
  match source with
  | tfAnd first _ => first
  | _ => tfBot
  end.

Definition templateAndSecond (source : TemplateFormula) : TemplateFormula :=
  match source with
  | tfAnd _ second => second
  | _ => tfBot
  end.

Definition templateAnd4First (source : TemplateFormula) : TemplateFormula :=
  match source with
  | tfAnd first _ => first
  | _ => tfBot
  end.

Definition templateAnd4Second (source : TemplateFormula) : TemplateFormula :=
  match source with
  | tfAnd _ (tfAnd second _) => second
  | _ => tfBot
  end.

Definition templateAnd4Third (source : TemplateFormula) : TemplateFormula :=
  match source with
  | tfAnd _ (tfAnd _ (tfAnd third _)) => third
  | _ => tfBot
  end.

Definition templateAnd4Fourth (source : TemplateFormula) : TemplateFormula :=
  match source with
  | tfAnd _ (tfAnd _ (tfAnd _ fourth)) => fourth
  | _ => tfBot
  end.

(** The combined premise retains the source theorem's literal
    right-associated four-component shape after all thirteen openings. *)
Lemma coqFourStateTableAppendDefinedTemplate_components : forall
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    bound mode formula assignmentCode assignmentStep,
  coqFourStateTableAppendDefinedTemplate
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    bound mode formula assignmentCode assignmentStep =
  let defined := coqFourStateTableAppendDefinedTemplate
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    bound mode formula assignmentCode assignmentStep in
  tfAnd (templateAnd4First defined)
    (tfAnd (templateAnd4Second defined)
      (tfAnd (templateAnd4Third defined)
        (templateAnd4Fourth defined))).
Proof.
  intros.
  cbn zeta.
  unfold coqFourStateTableAppendDefinedTemplate,
    coqFourStateTableAppendInstanceTemplate,
    codedFourStateTableAppendFormula,
    fourStateTableAppendRepeatedAll,
    fourStateTableAppendDefinedBody,
    fixedLevelAnd4,
    templateAnd4First, templateAnd4Second,
    templateAnd4Third, templateAnd4Fourth.
  cbn [templateUniversalOpenMany embedPAFormula
    templateFormulaOpen templateFormulaSubst].
  reflexivity.
Qed.

(** Assemble any template with the same four-way shape from component local
    proofs.  Returning an existential root keeps clients independent of the
    particular right-associated proof-tree code. *)
Theorem raw_codedPALocalProofOf_templateAnd4 : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M)
    context source firstRoot secondRoot thirdRoot fourthRoot,
  source = tfAnd (templateAnd4First source)
    (tfAnd (templateAnd4Second source)
      (tfAnd (templateAnd4Third source) (templateAnd4Fourth source))) ->
  RawCodedPALocalProofOf M context
    (rawTemplateFormula translation (templateAnd4First source)) firstRoot ->
  RawCodedPALocalProofOf M context
    (rawTemplateFormula translation (templateAnd4Second source)) secondRoot ->
  RawCodedPALocalProofOf M context
    (rawTemplateFormula translation (templateAnd4Third source)) thirdRoot ->
  RawCodedPALocalProofOf M context
    (rawTemplateFormula translation (templateAnd4Fourth source)) fourthRoot ->
  exists root,
    RawCodedPALocalProofOf M context
      (rawTemplateFormula translation source) root.
Proof.
  intros M hPA translation context source
    firstRoot secondRoot thirdRoot fourthRoot
    hshape hfirst hsecond hthird hfourth.
  pose proof (raw_codedPALocalProofOf_andI M hPA context _ _
    thirdRoot fourthRoot hthird hfourth) as hthirdFourth.
  pose proof (raw_codedPALocalProofOf_andI M hPA context _ _
    secondRoot
    (rawProofAndIRoot M context _ _ thirdRoot fourthRoot)
    hsecond hthirdFourth) as hsecondThroughFourth.
  pose proof (raw_codedPALocalProofOf_andI M hPA context _ _
    firstRoot
    (rawProofAndIRoot M context _ _ secondRoot
      (rawProofAndIRoot M context _ _ thirdRoot fourthRoot))
    hfirst hsecondThroughFourth) as hall.
  lazymatch type of hall with
  | RawCodedPALocalProofOf _ _ _ ?root =>
      exists root;
      rewrite hshape;
      repeat rewrite rawTemplateFormula_and;
      exact hall
  end.
Qed.

(** Dual projection interface for the same stable four-way shape. *)
Theorem raw_codedPALocalProofOf_templateAnd4_components : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M)
    context source sourceRoot,
  source = tfAnd (templateAnd4First source)
    (tfAnd (templateAnd4Second source)
      (tfAnd (templateAnd4Third source) (templateAnd4Fourth source))) ->
  RawCodedPALocalProofOf M context
    (rawTemplateFormula translation source) sourceRoot ->
  exists firstRoot secondRoot thirdRoot fourthRoot,
    RawCodedPALocalProofOf M context
      (rawTemplateFormula translation (templateAnd4First source)) firstRoot /\
    RawCodedPALocalProofOf M context
      (rawTemplateFormula translation (templateAnd4Second source)) secondRoot /\
    RawCodedPALocalProofOf M context
      (rawTemplateFormula translation (templateAnd4Third source)) thirdRoot /\
    RawCodedPALocalProofOf M context
      (rawTemplateFormula translation (templateAnd4Fourth source)) fourthRoot.
Proof.
  intros M hPA translation context source sourceRoot hshape hsource.
  rewrite hshape in hsource.
  repeat rewrite rawTemplateFormula_and in hsource.
  pose proof (raw_codedPALocalProofOf_andE1 M hPA context _ _
    sourceRoot hsource) as hfirst.
  pose proof (raw_codedPALocalProofOf_andE2 M hPA context _ _
    sourceRoot hsource) as hrest1.
  lazymatch type of hrest1 with
  | RawCodedPALocalProofOf _ _ _ ?rest1Root =>
      pose proof (raw_codedPALocalProofOf_andE1 M hPA context _ _
        rest1Root hrest1) as hsecond;
      pose proof (raw_codedPALocalProofOf_andE2 M hPA context _ _
        rest1Root hrest1) as hrest2
  end.
  lazymatch type of hrest2 with
  | RawCodedPALocalProofOf _ _ _ ?rest2Root =>
      pose proof (raw_codedPALocalProofOf_andE1 M hPA context _ _
        rest2Root hrest2) as hthird;
      pose proof (raw_codedPALocalProofOf_andE2 M hPA context _ _
        rest2Root hrest2) as hfourth
  end.
  lazymatch type of hfirst with
  | RawCodedPALocalProofOf _ _ _ ?firstRoot =>
    lazymatch type of hsecond with
    | RawCodedPALocalProofOf _ _ _ ?secondRoot =>
      lazymatch type of hthird with
      | RawCodedPALocalProofOf _ _ _ ?thirdRoot =>
        lazymatch type of hfourth with
        | RawCodedPALocalProofOf _ _ _ ?fourthRoot =>
            exists firstRoot, secondRoot, thirdRoot, fourthRoot;
            split; [exact hfirst |];
            split; [exact hsecond |];
            split; [exact hthird | exact hfourth]
        end
      end
    end
  end.
Qed.

(** Specialize the fixed theorem on an arbitrary witnessed base. *)
Theorem
    raw_codedPALocalProofOf_four_state_table_append_instance_on_witnessed_tail :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    baseWitnessList baseContext
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    bound mode formula assignmentCode assignmentStep,
  RawCodedPAAxiomWitnessContext M baseWitnessList baseContext ->
  exists (witnesses : StandardPAAxiomWitnessPrefix) (root : M),
    RawCodedPAAxiomWitnessContext M
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        witnesses baseWitnessList)
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses baseContext) /\
    RawCodedPALocalProofOf M
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses baseContext)
      (rawDirectTemplateFormula inputs
        (coqFourStateTableAppendInstanceTemplate
          modeCode modeStep formulaCode formulaStep
          assignmentCodeCode assignmentCodeStep
          assignmentStepCode assignmentStepStep
          bound mode formula assignmentCode assignmentStep)) root.
Proof.
  intros M hPA inputs baseWitnessList baseContext
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    bound mode formula assignmentCode assignmentStep hbase.
  exact
    (raw_codedTemplatePALocalProofOf_of_BProv_open_many_on_witnessed_tail
      M hPA
      (rawDirectStructuralTemplateTranslation M hPA inputs)
      (rawDirectStructuralTemplatePAAgreement M hPA inputs)
      baseWitnessList baseContext codedFourStateTableAppendFormula
      [modeCode; modeStep; formulaCode; formulaStep;
       assignmentCodeCode; assignmentCodeStep;
       assignmentStepCode; assignmentStepStep;
       bound; mode; formula; assignmentCode; assignmentStep]
      (coqFourStateTableAppendInstanceTemplate
        modeCode modeStep formulaCode formulaStep
        assignmentCodeCode assignmentCodeStep
        assignmentStepCode assignmentStepStep
        bound mode formula assignmentCode assignmentStep)
      hbase PA_proves_codedFourStateTableAppendFormula
      (coqFourStateTableAppendInstanceTemplate_open_many
        modeCode modeStep formulaCode formulaStep
        assignmentCodeCode assignmentCodeStep
        assignmentStepCode assignmentStepStep
        bound mode formula assignmentCode assignmentStep)).
Qed.

(** Rebuild a caller proof of the four defined-through premises across the
    selected standard prefix, then perform represented implication
    elimination.  The result is the shared eight-witness existential. *)
Theorem
    raw_codedPALocalProofOf_four_state_table_append_exists_of_defined_on_witnessed_tail
    : forall (M : RawPAModel), RawPASatisfies M -> forall
      (inputs : RawCodedTemplateDirectStructuralInputs M)
      baseWitnessList baseContext
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      bound mode formula assignmentCode assignmentStep definedRoot,
  RawCodedPAAxiomWitnessContext M baseWitnessList baseContext ->
  RawCodedPALocalProofOf M baseContext
    (rawDirectTemplateFormula inputs
      (coqFourStateTableAppendDefinedTemplate
        modeCode modeStep formulaCode formulaStep
        assignmentCodeCode assignmentCodeStep
        assignmentStepCode assignmentStepStep
        bound mode formula assignmentCode assignmentStep)) definedRoot ->
  exists (witnesses : StandardPAAxiomWitnessPrefix) (root : M),
    RawCodedPAAxiomWitnessContext M
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        witnesses baseWitnessList)
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses baseContext) /\
    RawCodedPALocalProofOf M
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses baseContext)
      (rawDirectTemplateFormula inputs
        (coqFourStateTableAppendExistsTemplate
          modeCode modeStep formulaCode formulaStep
          assignmentCodeCode assignmentCodeStep
          assignmentStepCode assignmentStepStep
          bound mode formula assignmentCode assignmentStep)) root.
Proof.
  intros M hPA inputs baseWitnessList baseContext
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    bound mode formula assignmentCode assignmentStep definedRoot
    hbase hdefined.
  destruct
    (raw_codedPALocalProofOf_four_state_table_append_instance_on_witnessed_tail
      M hPA inputs baseWitnessList baseContext
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      bound mode formula assignmentCode assignmentStep hbase) as
    (witnesses & implicationRoot & hextended & himplication).
  destruct (raw_codedPALocalProofOf_standardPAAxiomWitnessPrefix
    M hPA witnesses baseContext
    (rawDirectTemplateFormula inputs
      (coqFourStateTableAppendDefinedTemplate
        modeCode modeStep formulaCode formulaStep
        assignmentCodeCode assignmentCodeStep
        assignmentStepCode assignmentStepStep
        bound mode formula assignmentCode assignmentStep))
    definedRoot
    (raw_codedPAAxiomWitnessPrefix_context_realizable_of_witnessed
      M baseWitnessList baseContext hbase)
    hdefined) as [transportedDefinedRoot htransportedDefined].
  rewrite coqFourStateTableAppendInstanceTemplate_shape in himplication.
  change (RawCodedPALocalProofOf M
    (rawStandardPAAxiomWitnessPrefixContextCode M witnesses baseContext)
    (rawFormulaImpCode M
      (rawDirectTemplateFormula inputs
        (coqFourStateTableAppendDefinedTemplate
          modeCode modeStep formulaCode formulaStep
          assignmentCodeCode assignmentCodeStep
          assignmentStepCode assignmentStepStep
          bound mode formula assignmentCode assignmentStep))
      (rawDirectTemplateFormula inputs
        (coqFourStateTableAppendExistsTemplate
          modeCode modeStep formulaCode formulaStep
          assignmentCodeCode assignmentCodeStep
          assignmentStepCode assignmentStepStep
          bound mode formula assignmentCode assignmentStep))) implicationRoot)
    in himplication.
  exists witnesses.
  exists (rawProofImpERoot M
    (rawStandardPAAxiomWitnessPrefixContextCode M witnesses baseContext)
    (rawDirectTemplateFormula inputs
      (coqFourStateTableAppendDefinedTemplate
        modeCode modeStep formulaCode formulaStep
        assignmentCodeCode assignmentCodeStep
        assignmentStepCode assignmentStepStep
        bound mode formula assignmentCode assignmentStep))
    (rawDirectTemplateFormula inputs
      (coqFourStateTableAppendExistsTemplate
        modeCode modeStep formulaCode formulaStep
        assignmentCodeCode assignmentCodeStep
        assignmentStepCode assignmentStepStep
        bound mode formula assignmentCode assignmentStep))
    implicationRoot transportedDefinedRoot).
  split; [exact hextended |].
  exact (raw_codedPALocalProofOf_impE M hPA
    (rawStandardPAAxiomWitnessPrefixContextCode M witnesses baseContext)
    (rawDirectTemplateFormula inputs
      (coqFourStateTableAppendDefinedTemplate
        modeCode modeStep formulaCode formulaStep
        assignmentCodeCode assignmentCodeStep
        assignmentStepCode assignmentStepStep
        bound mode formula assignmentCode assignmentStep))
    (rawDirectTemplateFormula inputs
      (coqFourStateTableAppendExistsTemplate
        modeCode modeStep formulaCode formulaStep
        assignmentCodeCode assignmentCodeStep
        assignmentStepCode assignmentStepStep
        bound mode formula assignmentCode assignmentStep))
    implicationRoot transportedDefinedRoot
    himplication htransportedDefined).
Qed.

(** Component-facing endpoint.  Traversal code normally owns four separate
    defined-through roots rather than a preassembled conjunction.  This
    theorem performs the three conjunction introductions and then invokes
    the synchronized append compiler, selecting its standard witness prefix
    only after the caller roots have been combined. *)
Theorem
    raw_codedPALocalProofOf_four_state_table_append_exists_of_components_on_witnessed_tail
    : forall (M : RawPAModel), RawPASatisfies M -> forall
      (inputs : RawCodedTemplateDirectStructuralInputs M)
      baseWitnessList baseContext
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      bound mode formula assignmentCode assignmentStep
      modeDefinedRoot formulaDefinedRoot
      assignmentCodeDefinedRoot assignmentStepDefinedRoot,
  let defined := coqFourStateTableAppendDefinedTemplate
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    bound mode formula assignmentCode assignmentStep in
  RawCodedPAAxiomWitnessContext M baseWitnessList baseContext ->
  RawCodedPALocalProofOf M baseContext
    (rawDirectTemplateFormula inputs (templateAnd4First defined))
    modeDefinedRoot ->
  RawCodedPALocalProofOf M baseContext
    (rawDirectTemplateFormula inputs (templateAnd4Second defined))
    formulaDefinedRoot ->
  RawCodedPALocalProofOf M baseContext
    (rawDirectTemplateFormula inputs (templateAnd4Third defined))
    assignmentCodeDefinedRoot ->
  RawCodedPALocalProofOf M baseContext
    (rawDirectTemplateFormula inputs (templateAnd4Fourth defined))
    assignmentStepDefinedRoot ->
  exists (witnesses : StandardPAAxiomWitnessPrefix) (root : M),
    RawCodedPAAxiomWitnessContext M
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        witnesses baseWitnessList)
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses baseContext) /\
    RawCodedPALocalProofOf M
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses baseContext)
      (rawDirectTemplateFormula inputs
        (coqFourStateTableAppendExistsTemplate
          modeCode modeStep formulaCode formulaStep
          assignmentCodeCode assignmentCodeStep
          assignmentStepCode assignmentStepStep
          bound mode formula assignmentCode assignmentStep)) root.
Proof.
  intros M hPA inputs baseWitnessList baseContext
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    bound mode formula assignmentCode assignmentStep
    modeDefinedRoot formulaDefinedRoot
    assignmentCodeDefinedRoot assignmentStepDefinedRoot.
  cbn zeta.
  intros hbase hmodeDefined hformulaDefined
    hassignmentCodeDefined hassignmentStepDefined.
  set (defined := coqFourStateTableAppendDefinedTemplate
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    bound mode formula assignmentCode assignmentStep).
  assert (hdefinedShape : defined =
      tfAnd (templateAnd4First defined)
        (tfAnd (templateAnd4Second defined)
          (tfAnd (templateAnd4Third defined)
            (templateAnd4Fourth defined)))).
  {
    unfold defined.
    exact (coqFourStateTableAppendDefinedTemplate_components
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      bound mode formula assignmentCode assignmentStep).
  }
  destruct (raw_codedPALocalProofOf_templateAnd4 M hPA
    (rawDirectStructuralTemplateTranslation M hPA inputs)
    baseContext defined
    modeDefinedRoot formulaDefinedRoot
    assignmentCodeDefinedRoot assignmentStepDefinedRoot
    hdefinedShape hmodeDefined hformulaDefined
    hassignmentCodeDefined hassignmentStepDefined)
    as [definedRoot hdefined].
  exact
    (raw_codedPALocalProofOf_four_state_table_append_exists_of_defined_on_witnessed_tail
      M hPA inputs baseWitnessList baseContext
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      bound mode formula assignmentCode assignmentStep definedRoot
      hbase hdefined).
Qed.

End PABoundedRawCodedFourStateTableAppendProofCompilation.
