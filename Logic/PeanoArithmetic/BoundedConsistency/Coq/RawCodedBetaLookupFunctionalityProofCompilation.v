(**
  Compile PA's beta-lookup functionality theorem in witnessed local contexts.

  The fixed source is ordinary PA syntax.  This module opens its five
  universal binders at arbitrary template terms, selects the finite standard
  PA-axiom witnesses needed by its derivation, and applies the two represented
  lookup premises.  A prefix-general endpoint keeps temporary append and row
  assumptions in their literal order while extending only the witnessed PA
  tail.
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
  RawCodedTemplateProofCompilerSelfShiftTail
  RawCodedTemplatePAEmbedding
  RawCodedTemplatePAEmbeddingSelfShiftTail
  RawCodedTemplateLocalProofWitnessedTailTransport
  RawCodedTemplateLocalProofStandardWitnessTailTransport
  RawCodedPALocalProofUniversalEliminationChain
  RawCodedBetaLookupFunctionalitySource.

Module PABoundedRawCodedBetaLookupFunctionalityProofCompilation.

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
Import PABoundedRawCodedTemplateProofCompilerSelfShiftTail.
Import PABoundedRawCodedTemplatePAEmbedding.
Import PABoundedRawCodedTemplatePAEmbeddingSelfShiftTail.
Import PABoundedRawCodedTemplateLocalProofWitnessedTailTransport.
Import PABoundedRawCodedTemplateLocalProofStandardWitnessTailTransport.
Import PABoundedRawCodedPALocalProofUniversalEliminationChain.
Import PABoundedRawCodedBetaLookupFunctionalitySource.

Definition coqBetaLookupFunctionalityInstanceTemplate
    (out1 out2 code step index : TemplateTerm) : TemplateFormula :=
  templateUniversalOpenManyOrBot
    (embedPAFormula codedBetaLookupFunctionalityFormula)
    [out1; out2; code; step; index].

Definition coqBetaLookupFunctionalityFirstLookupTemplate
    (out1 out2 code step index : TemplateTerm) : TemplateFormula :=
  templateImpAntecedent
    (coqBetaLookupFunctionalityInstanceTemplate
      out1 out2 code step index).

Definition coqBetaLookupFunctionalityAfterFirstTemplate
    (out1 out2 code step index : TemplateTerm) : TemplateFormula :=
  templateImpConsequent
    (coqBetaLookupFunctionalityInstanceTemplate
      out1 out2 code step index).

Definition coqBetaLookupFunctionalitySecondLookupTemplate
    (out1 out2 code step index : TemplateTerm) : TemplateFormula :=
  templateImpAntecedent
    (coqBetaLookupFunctionalityAfterFirstTemplate
      out1 out2 code step index).

Definition coqBetaLookupFunctionalityEqualityTemplate
    (out1 out2 code step index : TemplateTerm) : TemplateFormula :=
  templateImpConsequent
    (coqBetaLookupFunctionalityAfterFirstTemplate
      out1 out2 code step index).

Lemma coqBetaLookupFunctionalityInstanceTemplate_open : forall
    out1 out2 code step index,
  templateUniversalOpenMany
    (embedPAFormula codedBetaLookupFunctionalityFormula)
    [out1; out2; code; step; index] =
  Some (coqBetaLookupFunctionalityInstanceTemplate
    out1 out2 code step index).
Proof.
  intros out1 out2 code step index.
  unfold coqBetaLookupFunctionalityInstanceTemplate,
    templateUniversalOpenManyOrBot,
    codedBetaLookupFunctionalityFormula.
  cbn [templateUniversalOpenMany embedPAFormula
    templateFormulaOpen templateFormulaSubst].
  reflexivity.
Qed.

(** Package one five-term instantiation so a finite family can share a
    single compilation of the closed functionality theorem. *)
Record CoqBetaLookupFunctionalityArguments : Type := {
  coqBetaLookupFunctionalityOut1 : TemplateTerm;
  coqBetaLookupFunctionalityOut2 : TemplateTerm;
  coqBetaLookupFunctionalityCode : TemplateTerm;
  coqBetaLookupFunctionalityStep : TemplateTerm;
  coqBetaLookupFunctionalityIndex : TemplateTerm
}.

Definition coqBetaLookupFunctionalityReplacementList
    (arguments : CoqBetaLookupFunctionalityArguments)
    : list TemplateTerm :=
  [coqBetaLookupFunctionalityOut1 arguments;
   coqBetaLookupFunctionalityOut2 arguments;
   coqBetaLookupFunctionalityCode arguments;
   coqBetaLookupFunctionalityStep arguments;
   coqBetaLookupFunctionalityIndex arguments].

Definition coqBetaLookupFunctionalityInstanceOf
    (arguments : CoqBetaLookupFunctionalityArguments)
    : TemplateFormula :=
  coqBetaLookupFunctionalityInstanceTemplate
    (coqBetaLookupFunctionalityOut1 arguments)
    (coqBetaLookupFunctionalityOut2 arguments)
    (coqBetaLookupFunctionalityCode arguments)
    (coqBetaLookupFunctionalityStep arguments)
    (coqBetaLookupFunctionalityIndex arguments).

Lemma coqBetaLookupFunctionalityInstanceOf_open : forall arguments,
  templateUniversalOpenMany
    (embedPAFormula codedBetaLookupFunctionalityFormula)
    (coqBetaLookupFunctionalityReplacementList arguments) =
  Some (coqBetaLookupFunctionalityInstanceOf arguments).
Proof.
  intros [out1 out2 code step index].
  exact (coqBetaLookupFunctionalityInstanceTemplate_open
    out1 out2 code step index).
Qed.

(** Exact two-implication shape after opening all five binders. *)
Lemma coqBetaLookupFunctionalityInstanceTemplate_shape : forall
    out1 out2 code step index,
  coqBetaLookupFunctionalityInstanceTemplate out1 out2 code step index =
    tfImp
      (coqBetaLookupFunctionalityFirstLookupTemplate
        out1 out2 code step index)
      (tfImp
        (coqBetaLookupFunctionalitySecondLookupTemplate
          out1 out2 code step index)
        (coqBetaLookupFunctionalityEqualityTemplate
          out1 out2 code step index)).
Proof.
  intros out1 out2 code step index.
  unfold coqBetaLookupFunctionalityInstanceTemplate,
    coqBetaLookupFunctionalityFirstLookupTemplate,
    coqBetaLookupFunctionalityAfterFirstTemplate,
    coqBetaLookupFunctionalitySecondLookupTemplate,
    coqBetaLookupFunctionalityEqualityTemplate,
    templateImpAntecedent, templateImpConsequent,
    templateUniversalOpenManyOrBot,
    codedBetaLookupFunctionalityFormula.
  cbn [templateUniversalOpenMany embedPAFormula
    templateFormulaOpen templateFormulaSubst].
  reflexivity.
Qed.

Theorem
    raw_codedPALocalProofOf_beta_lookup_functionality_instance_on_witnessed_tail :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall baseWitnessList baseContext out1 out2 code step index,
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
        (coqBetaLookupFunctionalityInstanceTemplate
          out1 out2 code step index)) root.
Proof.
  intros M hPA translation hagreement
    baseWitnessList baseContext out1 out2 code step index hbase.
  exact
    (raw_codedTemplatePALocalProofOf_of_BProv_open_many_on_witnessed_tail
      M hPA translation hagreement
      baseWitnessList baseContext codedBetaLookupFunctionalityFormula
      [out1; out2; code; step; index]
      (coqBetaLookupFunctionalityInstanceTemplate
        out1 out2 code step index)
      hbase PA_proves_codedBetaLookupFunctionalityFormula
      (coqBetaLookupFunctionalityInstanceTemplate_open
        out1 out2 code step index)).
Qed.

(** Compile the closed theorem once, then instantiate it at an arbitrary
    finite family of beta-table positions.  This is used with four entries
    for a state row, but the statement deliberately exposes no fixed arity. *)
Theorem
    raw_codedPALocalProofOf_beta_lookup_functionality_instances_on_witnessed_tail :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall baseWitnessList baseContext arguments,
  RawCodedPAAxiomWitnessContext M baseWitnessList baseContext ->
  exists (witnesses : StandardPAAxiomWitnessPrefix) roots,
    RawCodedPAAxiomWitnessContext M
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        witnesses baseWitnessList)
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses baseContext) /\
    Forall2
      (fun target root =>
        RawCodedPALocalProofOf M
          (rawStandardPAAxiomWitnessPrefixContextCode M
            witnesses baseContext)
          (rawTemplateFormula translation target) root)
      (map coqBetaLookupFunctionalityInstanceOf arguments) roots.
Proof.
  intros M hPA translation hagreement
    baseWitnessList baseContext arguments hbase.
  assert (hopen : Forall2
      (fun replacements target =>
        templateUniversalOpenMany
          (embedPAFormula codedBetaLookupFunctionalityFormula)
          replacements = Some target)
      (map coqBetaLookupFunctionalityReplacementList arguments)
      (map coqBetaLookupFunctionalityInstanceOf arguments)).
  {
    induction arguments as [|argument remaining ih].
    - constructor.
    - cbn [map]. constructor.
      + exact (coqBetaLookupFunctionalityInstanceOf_open argument).
      + exact ih.
  }
  exact
    (raw_codedTemplatePALocalProofOf_of_BProv_open_many_list_on_witnessed_tail
      M hPA translation hagreement baseWitnessList baseContext
      codedBetaLookupFunctionalityFormula
      (map coqBetaLookupFunctionalityReplacementList arguments)
      (map coqBetaLookupFunctionalityInstanceOf arguments)
      hbase PA_proves_codedBetaLookupFunctionalityFormula hopen).
Qed.

(** Apply both represented lookup premises while preserving an arbitrary
    finite temporary template prefix. *)
Theorem
    raw_codedPALocalProofOf_beta_lookup_functionality_on_witnessed_tail_under_prefix :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall baseWitnessList baseContext prefix out1 out2 code step index
    firstRoot secondRoot,
  RawCodedTemplatePrefixAtomicallyAdequate M translation prefix ->
  RawCodedPAAxiomWitnessContext M baseWitnessList baseContext ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail translation baseContext prefix)
    (rawTemplateFormula translation
      (coqBetaLookupFunctionalityFirstLookupTemplate
        out1 out2 code step index)) firstRoot ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail translation baseContext prefix)
    (rawTemplateFormula translation
      (coqBetaLookupFunctionalitySecondLookupTemplate
        out1 out2 code step index)) secondRoot ->
  exists (witnesses : StandardPAAxiomWitnessPrefix) (root : M),
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
        (coqBetaLookupFunctionalityEqualityTemplate
          out1 out2 code step index)) root.
Proof.
  intros M hPA translation hagreement
    baseWitnessList baseContext prefix out1 out2 code step index
    firstRoot secondRoot hprefix hbase hfirst hsecond.
  destruct
    (raw_codedPALocalProofOf_beta_lookup_functionality_instance_on_witnessed_tail
      M hPA translation hagreement baseWitnessList baseContext
      out1 out2 code step index hbase)
    as (witnesses & implicationRoot & hextended & himplication).
  set (extendedContext :=
    rawStandardPAAxiomWitnessPrefixContextCode M witnesses baseContext).
  destruct (raw_codedPALocalProof_templatePrefix M hPA translation
    extendedContext prefix
    (rawTemplateFormula translation
      (coqBetaLookupFunctionalityInstanceTemplate
        out1 out2 code step index))
    implicationRoot
    (raw_codedPAAxiomWitnessPrefix_context_realizable_of_witnessed M
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        witnesses baseWitnessList)
      extendedContext hextended)
    hprefix himplication) as [prefixedImplicationRoot hprefixedImplication].
  destruct
    (raw_codedPALocalProof_sameTemplatePrefix_witnessedTail_transport
      M hPA translation
      baseWitnessList baseContext
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        witnesses baseWitnessList)
      extendedContext prefix
      (rawTemplateFormula translation
        (coqBetaLookupFunctionalityFirstLookupTemplate
          out1 out2 code step index))
      firstRoot hbase hextended
      (raw_standardPAAxiomWitnessPrefixContextCode_target_included
        M hPA witnesses baseContext)
      hfirst) as [transportedFirstRoot htransportedFirst].
  destruct
    (raw_codedPALocalProof_sameTemplatePrefix_witnessedTail_transport
      M hPA translation
      baseWitnessList baseContext
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        witnesses baseWitnessList)
      extendedContext prefix
      (rawTemplateFormula translation
        (coqBetaLookupFunctionalitySecondLookupTemplate
          out1 out2 code step index))
      secondRoot hbase hextended
      (raw_standardPAAxiomWitnessPrefixContextCode_target_included
        M hPA witnesses baseContext)
      hsecond) as [transportedSecondRoot htransportedSecond].
  rewrite (coqBetaLookupFunctionalityInstanceTemplate_shape
    out1 out2 code step index) in hprefixedImplication.
  rewrite !rawTemplateFormula_imp in hprefixedImplication.
  pose proof (raw_codedPALocalProofOf_impE M hPA
    (rawTemplateContextCodeOnTail translation extendedContext prefix)
    (rawTemplateFormula translation
      (coqBetaLookupFunctionalityFirstLookupTemplate
        out1 out2 code step index))
    _
    prefixedImplicationRoot transportedFirstRoot
    hprefixedImplication htransportedFirst) as hafterFirst.
  pose proof (raw_codedPALocalProofOf_impE M hPA
    (rawTemplateContextCodeOnTail translation extendedContext prefix)
    (rawTemplateFormula translation
      (coqBetaLookupFunctionalitySecondLookupTemplate
        out1 out2 code step index))
    (rawTemplateFormula translation
      (coqBetaLookupFunctionalityEqualityTemplate
        out1 out2 code step index))
    _ transportedSecondRoot hafterFirst htransportedSecond) as hresult.
  exists witnesses.
  eexists.
  split; [exact hextended | exact hresult].
Qed.

End PABoundedRawCodedBetaLookupFunctionalityProofCompilation.
