(**
  Join the dual append traversal with predecessor-state context insertion.

  The append compiler constructs the Sigma- and Pi-rooted global formulas in
  independently growing PA-witness tails and then synchronizes them.  The
  predecessor compiler knows how to place any such synchronized pair below
  its two literal state assumptions.  This module is the small, dependency-
  directional composition of those two completed pieces.

  The result retains the selected witnessed context and inclusion of the
  original standard witness-prefix context.  It therefore feeds both the
  represented global-formula eliminator and the growing aligned callback;
  no context equality or proof-root reselection is hidden here.
*)

From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors
  RawCodedTemplateSyntax
  RawCodedTemplateProofCompiler
  RawCodedTemplatePAEmbedding
  RawCodedPAAxiomWitnessPrefix
  RawCodedDynamicTruthPairedGlobalSuccessorGraph
  RawCodedDynamicTruthPredecessorStateExclusivityCompilation
  RawCodedFourStateTableAppendGlobalTraversalAssembly.

Module PABoundedRawCodedDynamicTruthPredecessorAppendGlobalRoots.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedTemplatePAEmbedding.
Import PABoundedRawCodedPAAxiomWitnessPrefix.
Import PABoundedRawCodedDynamicTruthPairedGlobalSuccessorGraph.
Import
  PABoundedRawCodedDynamicTruthPredecessorStateExclusivityCompilation.
Import PABoundedRawCodedFourStateTableAppendGlobalTraversalAssembly.

Theorem
    raw_dynamicTruthPredecessorGlobalRootsOnWitnessedExtensionFrom_of_append_concrete_global_row_input_packages :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall localSigma localPi boundName witnesses,
  RawFourStateTableAppendConcreteGlobalRowInputsAt M translation
    0 localSigma localPi boundName witnesses ->
  RawFourStateTableAppendConcreteGlobalRowInputsAt M translation
    1 localSigma localPi boundName witnesses ->
  RawDynamicTruthPredecessorGlobalRootsOnWitnessedExtensionFrom M
    (rawStandardPAAxiomWitnessPrefixContextCode M
      witnesses (raw_zero M))
    (rawTemplateFormula translation
      (embedPAFormula
        (dynamicTruthGlobalFormula (Term.numeral 0)
          localSigma localPi)))
    (rawTemplateFormula translation
      (embedPAFormula
        (dynamicTruthGlobalFormula (Term.numeral 1)
          localSigma localPi))).
Proof.
  intros M hPA translation hagreement
    localSigma localPi boundName witnesses hSigmaInputs hPiInputs.
  apply
    (raw_dynamicTruthPredecessorGlobalRootsOnWitnessedExtensionFrom_of_growing_pair
      M hPA
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses (raw_zero M))).
  exact
    (raw_codedPAGrowingTemplateLocalProofPairAtEmpty_dynamic_truth_global_sigma_pi_of_append_concrete_global_row_input_packages
      M hPA translation hagreement localSigma localPi
      boundName witnesses hSigmaInputs hPiInputs).
Qed.

End PABoundedRawCodedDynamicTruthPredecessorAppendGlobalRoots.
