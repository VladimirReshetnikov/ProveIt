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
  RawCodedPALocalProofExistential
  RawCodedPALocalProofComposition
  RawCodedTemplateSyntax
  RawCodedTemplateProofCompiler
  RawCodedTemplateDirectStructuralTranslation
  RawCodedTemplateDirectStructuralPAAgreement
  RawCodedPALocalProofUniversalEliminationChain
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
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPALocalProofComposition.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedTemplateDirectStructuralTranslation.
Import PABoundedRawCodedTemplateDirectStructuralPAAgreement.
Import PABoundedRawCodedPALocalProofUniversalEliminationChain.
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

End PABoundedRawCodedFourStateTableAppendProofCompilation.
