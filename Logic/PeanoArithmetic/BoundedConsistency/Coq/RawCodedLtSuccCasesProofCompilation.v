(**
  Compile PA's successor-bound case split in any witnessed local context.

  This module is translation-generic: the fixed source contains no opaque
  leaves, so every template translation agreeing with ordinary PA syntax can
  instantiate it.  The endpoint transports a caller proof of [i < S b]
  through the selected finite PA-axiom prefix and returns a genuine local
  proof of [i < b \/ i = b].
*)

From Stdlib Require Import List.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedPALocalProofExistential
  RawCodedPALocalProofComposition
  RawCodedPAAxiomWitnessPrefix
  RawCodedRestrictedPAProof
  RawCodedTemplateSyntax
  RawCodedTemplateProofCompiler
  RawCodedTemplatePAEmbedding
  RawCodedTemplatePAEmbeddingSelfShiftTail
  RawCodedPALocalProofUniversalEliminationChain
  RawCodedLtSuccCasesSource.

Module PABoundedRawCodedLtSuccCasesProofCompilation.

Import ListNotations.
Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPALocalProofComposition.
Import PABoundedRawCodedPAAxiomWitnessPrefix.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedTemplatePAEmbedding.
Import PABoundedRawCodedTemplatePAEmbeddingSelfShiftTail.
Import PABoundedRawCodedPALocalProofUniversalEliminationChain.
Import PABoundedRawCodedLtSuccCasesSource.

Definition coqLtSuccCasesInstanceTemplate
    (index bound : TemplateTerm) : TemplateFormula :=
  templateUniversalOpenManyOrBot
    (embedPAFormula codedLtSuccCasesFormula) [index; bound].

Definition coqLtSuccCasesAntecedentTemplate
    (index bound : TemplateTerm) : TemplateFormula :=
  templateImpAntecedent (coqLtSuccCasesInstanceTemplate index bound).

Definition coqLtSuccCasesResultTemplate
    (index bound : TemplateTerm) : TemplateFormula :=
  templateImpConsequent (coqLtSuccCasesInstanceTemplate index bound).

Definition templateOrLeft (source : TemplateFormula) : TemplateFormula :=
  match source with
  | tfOr lhs _ => lhs
  | _ => tfBot
  end.

Definition templateOrRight (source : TemplateFormula) : TemplateFormula :=
  match source with
  | tfOr _ rhs => rhs
  | _ => tfBot
  end.

Definition coqLtSuccCasesBelowTemplate
    (index bound : TemplateTerm) : TemplateFormula :=
  templateOrLeft (coqLtSuccCasesResultTemplate index bound).

Definition coqLtSuccCasesEqualTemplate
    (index bound : TemplateTerm) : TemplateFormula :=
  templateOrRight (coqLtSuccCasesResultTemplate index bound).

Lemma coqLtSuccCasesInstanceTemplate_open : forall index bound,
  templateUniversalOpenMany
    (embedPAFormula codedLtSuccCasesFormula) [index; bound] =
  Some (coqLtSuccCasesInstanceTemplate index bound).
Proof.
  intros index bound.
  unfold coqLtSuccCasesInstanceTemplate,
    templateUniversalOpenManyOrBot,
    codedLtSuccCasesFormula.
  cbn [templateUniversalOpenMany embedPAFormula
    templateFormulaOpen templateFormulaSubst].
  reflexivity.
Qed.

(** Exact propositional shape after the two universal openings. *)
Lemma coqLtSuccCasesInstanceTemplate_shape : forall index bound,
  coqLtSuccCasesInstanceTemplate index bound =
    tfImp (coqLtSuccCasesAntecedentTemplate index bound)
      (coqLtSuccCasesResultTemplate index bound) /\
  coqLtSuccCasesResultTemplate index bound =
    tfOr (coqLtSuccCasesBelowTemplate index bound)
      (coqLtSuccCasesEqualTemplate index bound).
Proof.
  intros index bound.
  unfold coqLtSuccCasesInstanceTemplate,
    coqLtSuccCasesAntecedentTemplate,
    coqLtSuccCasesResultTemplate,
    coqLtSuccCasesBelowTemplate, coqLtSuccCasesEqualTemplate,
    templateImpAntecedent, templateImpConsequent,
    templateOrLeft, templateOrRight,
    templateUniversalOpenManyOrBot,
    codedLtSuccCasesFormula.
  cbn [templateUniversalOpenMany embedPAFormula
    templateFormulaOpen templateFormulaSubst].
  split; reflexivity.
Qed.

Theorem raw_codedPALocalProofOf_lt_succ_cases_instance_on_witnessed_tail :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall baseWitnessList baseContext index bound,
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
      (rawTemplateFormula translation
        (coqLtSuccCasesInstanceTemplate index bound)) root.
Proof.
  intros M hPA translation hagreement
    baseWitnessList baseContext index bound hbase.
  exact
    (raw_codedTemplatePALocalProofOf_of_BProv_open_many_on_witnessed_tail
      M hPA translation hagreement
      baseWitnessList baseContext codedLtSuccCasesFormula
      [index; bound] (coqLtSuccCasesInstanceTemplate index bound)
      hbase PA_proves_codedLtSuccCasesFormula
      (coqLtSuccCasesInstanceTemplate_open index bound)).
Qed.

Theorem raw_codedPALocalProofOf_lt_succ_cases_on_witnessed_tail :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall baseWitnessList baseContext index bound antecedentRoot,
  RawCodedPAAxiomWitnessContext M baseWitnessList baseContext ->
  RawCodedPALocalProofOf M baseContext
    (rawTemplateFormula translation
      (coqLtSuccCasesAntecedentTemplate index bound)) antecedentRoot ->
  exists (witnesses : StandardPAAxiomWitnessPrefix) (root : M),
    RawCodedPAAxiomWitnessContext M
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        witnesses baseWitnessList)
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses baseContext) /\
    RawCodedPALocalProofOf M
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses baseContext)
      (rawTemplateFormula translation
        (coqLtSuccCasesResultTemplate index bound)) root.
Proof.
  intros M hPA translation hagreement
    baseWitnessList baseContext index bound antecedentRoot
    hbase hantecedent.
  destruct
    (raw_codedPALocalProofOf_lt_succ_cases_instance_on_witnessed_tail
      M hPA translation hagreement baseWitnessList baseContext
      index bound hbase)
    as (witnesses & implicationRoot & hextended & himplication).
  destruct (raw_codedPALocalProofOf_standardPAAxiomWitnessPrefix
    M hPA witnesses baseContext
    (rawTemplateFormula translation
      (coqLtSuccCasesAntecedentTemplate index bound))
    antecedentRoot
    (raw_codedPAAxiomWitnessPrefix_context_realizable_of_witnessed
      M baseWitnessList baseContext hbase)
    hantecedent) as [transportedRoot htransported].
  destruct (coqLtSuccCasesInstanceTemplate_shape index bound)
    as [himpShape _].
  rewrite himpShape, rawTemplateFormula_imp in himplication.
  pose proof (raw_codedPALocalProofOf_impE M hPA
    (rawStandardPAAxiomWitnessPrefixContextCode M witnesses baseContext)
    (rawTemplateFormula translation
      (coqLtSuccCasesAntecedentTemplate index bound))
    (rawTemplateFormula translation
      (coqLtSuccCasesResultTemplate index bound))
    implicationRoot transportedRoot himplication htransported) as hresult.
  lazymatch type of hresult with
  | RawCodedPALocalProofOf _ _ _ ?root =>
      exists witnesses, root; split; [exact hextended | exact hresult]
  end.
Qed.

End PABoundedRawCodedLtSuccCasesProofCompilation.
