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
