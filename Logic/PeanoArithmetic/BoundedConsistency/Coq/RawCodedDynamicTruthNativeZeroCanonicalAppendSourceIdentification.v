(**
  Identify canonical rank-zero append sources with canonical applications.

  The permuted append traversal reverses its three exposed argument slots.
  When its two local rows are the literal first-successor rows above the
  fixed global base predicates, the resulting template is exactly the
  standard ternary application isolated by canonical trace exactification.
  This is a syntax theorem; no semantic or proof-producing premise occurs.
*)

From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors
  RawCodedTemplateSyntax
  RawCodedTemplateProofCompiler
  RawCodedTemplatePAEmbedding
  RawCodedRestrictedPAProof
  RawCodedPAGrowingTemplateConjunction
  RawCodedDynamicTruthPredecessorStateExclusivityCompilation
  RawCodedDynamicTruthPredecessorAtomicDomainGlobalRootsSynchronization
  RawCodedDynamicTruthSigmaSuccessorRowGraph
  RawCodedDynamicTruthPiSuccessorRowGraph
  RawCodedDynamicTruthPairedGlobalSuccessorGraph
  RawCodedDynamicTruthGlobalBaseRootClosure
  RawCodedFourStateTableAppendPermutedTemplateGlobalTraversalAssembly
  RawCodedDynamicTruthNativeZeroCanonicalTraceExactification.

Module
  PABoundedRawCodedDynamicTruthNativeZeroCanonicalAppendSourceIdentification.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedTemplatePAEmbedding.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedPAGrowingTemplateConjunction.
Import
  PABoundedRawCodedDynamicTruthPredecessorStateExclusivityCompilation.
Import
  PABoundedRawCodedDynamicTruthPredecessorAtomicDomainGlobalRootsSynchronization.
Import PABoundedRawCodedDynamicTruthSigmaSuccessorRowGraph.
Import PABoundedRawCodedDynamicTruthPiSuccessorRowGraph.
Import PABoundedRawCodedDynamicTruthPairedGlobalSuccessorGraph.
Import PABoundedRawCodedDynamicTruthGlobalBaseRootClosure.
Import
  PABoundedRawCodedFourStateTableAppendPermutedTemplateGlobalTraversalAssembly.
Import
  PABoundedRawCodedDynamicTruthNativeZeroCanonicalTraceExactification.

(** Literal local rows used by the first global successor. *)
Definition dynamicTruthZeroCanonicalSigmaRowFormula : formula :=
  dynamicTruthSigmaSuccessorRowFormula (Term.numeral 1)
    dynamicTruthGlobalPiBaseFormula.

Definition dynamicTruthZeroCanonicalPiRowFormula : formula :=
  dynamicTruthPiSuccessorRowFormula (Term.numeral 1)
    dynamicTruthGlobalSigmaBaseFormula.

(** Reversing the exposed tuple is definitionally the protected three-open
    application at [#2,#1,#0].  Kernel computation is intentional here: it
    audits the complete binder-sensitive syntax tree. *)
Lemma coqFourStateTableAppendPermutedTemplateGlobalSource_zero_sigma :
  coqFourStateTableAppendPermutedTemplateGlobalSource 0
      (embedPAFormula dynamicTruthZeroCanonicalSigmaRowFormula)
      (embedPAFormula dynamicTruthZeroCanonicalPiRowFormula) =
  embedPAFormula dynamicTruthZeroInputGlobalSigmaApplicationFormula.
Proof.
  vm_compute. reflexivity.
Qed.

Lemma coqFourStateTableAppendPermutedTemplateGlobalSource_zero_pi :
  coqFourStateTableAppendPermutedTemplateGlobalSource 1
      (embedPAFormula dynamicTruthZeroCanonicalSigmaRowFormula)
      (embedPAFormula dynamicTruthZeroCanonicalPiRowFormula) =
  embedPAFormula dynamicTruthZeroInputGlobalPiApplicationFormula.
Proof.
  vm_compute. reflexivity.
Qed.

(** Carrier-facing forms for arbitrary PA-agreeing translations. *)
Theorem rawTemplateFormula_zeroCanonicalPermutedGlobalSource_sigma : forall
    (M : RawPAModel) (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  rawTemplateFormula translation
      (coqFourStateTableAppendPermutedTemplateGlobalSource 0
        (embedPAFormula dynamicTruthZeroCanonicalSigmaRowFormula)
        (embedPAFormula dynamicTruthZeroCanonicalPiRowFormula)) =
  rawQuotedFormulaCode M
    dynamicTruthZeroInputGlobalSigmaApplicationFormula.
Proof.
  intros M translation hagreement.
  rewrite coqFourStateTableAppendPermutedTemplateGlobalSource_zero_sigma.
  exact (rawTemplateFormula_embedPA hagreement
    dynamicTruthZeroInputGlobalSigmaApplicationFormula).
Qed.

Theorem rawTemplateFormula_zeroCanonicalPermutedGlobalSource_pi : forall
    (M : RawPAModel) (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  rawTemplateFormula translation
      (coqFourStateTableAppendPermutedTemplateGlobalSource 1
        (embedPAFormula dynamicTruthZeroCanonicalSigmaRowFormula)
        (embedPAFormula dynamicTruthZeroCanonicalPiRowFormula)) =
  rawQuotedFormulaCode M
    dynamicTruthZeroInputGlobalPiApplicationFormula.
Proof.
  intros M translation hagreement.
  rewrite coqFourStateTableAppendPermutedTemplateGlobalSource_zero_pi.
  exact (rawTemplateFormula_embedPA hagreement
    dynamicTruthZeroInputGlobalPiApplicationFormula).
Qed.

(** Any append traversal which returns the two embedded-row permuted sources
    can be rebased directly onto a witnessed callback context.  The two raw
    conclusion rewrites happen before context merging, so no structural
    translation remains in the resulting global-root package. *)
Theorem
    raw_dynamicTruthZeroCanonicalGlobalApplicationRoots_of_permuted_append_pair :
    forall (M : RawPAModel), RawPASatisfies M -> forall
      (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall producerSourceContext sourceWitnessList sourceContext,
  RawCodedPAAxiomWitnessContext M sourceWitnessList sourceContext ->
  RawCodedPAGrowingTemplateLocalProofPairAtEmpty M producerSourceContext
    (rawTemplateFormula translation
      (coqFourStateTableAppendPermutedTemplateGlobalSource 0
        (embedPAFormula dynamicTruthZeroCanonicalSigmaRowFormula)
        (embedPAFormula dynamicTruthZeroCanonicalPiRowFormula)))
    (rawTemplateFormula translation
      (coqFourStateTableAppendPermutedTemplateGlobalSource 1
        (embedPAFormula dynamicTruthZeroCanonicalSigmaRowFormula)
        (embedPAFormula dynamicTruthZeroCanonicalPiRowFormula))) ->
  RawDynamicTruthPredecessorGlobalRootsOnWitnessedExtensionFrom M
    sourceContext
    (rawQuotedFormulaCode M
      dynamicTruthZeroInputGlobalSigmaApplicationFormula)
    (rawQuotedFormulaCode M
      dynamicTruthZeroInputGlobalPiApplicationFormula).
Proof.
  intros M hPA translation hagreement producerSourceContext
    sourceWitnessList sourceContext hsource hpair.
  rewrite (rawTemplateFormula_zeroCanonicalPermutedGlobalSource_sigma
    M translation hagreement) in hpair.
  rewrite (rawTemplateFormula_zeroCanonicalPermutedGlobalSource_pi
    M translation hagreement) in hpair.
  exact
    (raw_dynamicTruthPredecessorGlobalRootsOnWitnessedExtensionFrom_of_rebased_growing_pair
      M hPA producerSourceContext sourceWitnessList sourceContext
      (rawQuotedFormulaCode M
        dynamicTruthZeroInputGlobalSigmaApplicationFormula)
      (rawQuotedFormulaCode M
        dynamicTruthZeroInputGlobalPiApplicationFormula)
      hsource hpair).
Qed.

End
  PABoundedRawCodedDynamicTruthNativeZeroCanonicalAppendSourceIdentification.
