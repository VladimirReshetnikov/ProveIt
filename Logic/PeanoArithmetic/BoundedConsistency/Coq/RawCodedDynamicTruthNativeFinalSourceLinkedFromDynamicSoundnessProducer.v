(**
  Connect the canonical dynamic-soundness producer to the final native
  staged source boundary.

  The final trace already exposes the successor numeral-term code, while its
  prerequisite package carries the exact witnessed PA context used by the
  current master certificate.  The dynamic-soundness producer is quantified
  over precisely those two pieces of data.  This adapter therefore does not
  weaken a context, replace a nonstandard numeral by a standard one, or
  manufacture a semantic proof: it simply applies the producer to the
  trace-selected successor and the shared witness context.
*)

From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA.
From BoundedPAConsistency Require Import
  RawCodedDynamicTruthNativeFinalStagedRootCompilation
  RawCodedRestrictedPADynamicSoundnessProducer.

Module
  PABoundedRawCodedDynamicTruthNativeFinalSourceLinkedFromDynamicSoundnessProducer.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import
  PABoundedRawCodedDynamicTruthNativeFinalStagedRootCompilation.
Import PABoundedRawCodedRestrictedPADynamicSoundnessProducer.

(**
  A model-local producer supplies the exact implication root demanded by the
  final staged compiler.  The [RawDynamicTruthNativeFinalSourceTraceAt]
  projection is important: it is what supplies the [RawNumeralTermCodeAt]
  witness for the same successor code appearing in the requested target.
*)
Theorem
    raw_dynamicTruthNativeFinalSourceLinkedImplicationRootCompiler_of_dynamicSoundnessProducer
    : forall (M : RawPAModel), RawPASatisfies M ->
  RawRestrictedPADynamicSoundnessProducer M ->
  RawDynamicTruthNativeFinalSourceLinkedImplicationRootCompiler M.
Proof.
  intros M hPA hproducer tail level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal
    nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
    nextFinal successorNumeralCode witnessList baseContext
    htrace hprerequisites.
  destruct htrace as
    [hcurrentGraph hnextLocalGraph hnextCrossGraph hnextShiftGraph
      hnextSubstitutionGraph hnextAxiomGraph hnextFinalGraph hsource].
  destruct hsource as
    [hcurrentTarget hnumeral hnextTarget hsourceSubstitution].
  destruct hprerequisites as
    (currentLocalRoot & currentCrossLevelRoot & currentShiftRoot &
      currentSubstitutionRoot & currentAxiomSoundnessRoot & currentFinalRoot &
      nextLocalRoot & nextCrossLevelRoot & nextShiftRoot & nextSubstitutionRoot &
      nextAxiomSoundnessRoot & [hprefix hnextAxiomRoot]).
  destruct hprefix as
    [hwitness hcurrentLocalRoot hcurrentCrossRoot hcurrentShiftRoot
      hcurrentSubstitutionRoot hcurrentAxiomRoot hcurrentFinalRoot
      hnextLocalRoot hnextCrossRoot hnextShiftRoot hnextSubstitutionRoot].
  exact
    (hproducer (raw_succ M level) successorNumeralCode
      witnessList baseContext hnumeral hwitness).
Qed.

Theorem
    raw_dynamicTruthNativeFinalSourceLinkedImplicationRootCompilerInAllModels_of_dynamicSoundnessProducer
  : RawRestrictedPADynamicSoundnessProducerInAllModels ->
  forall (M : RawPAModel), RawPASatisfies M ->
    RawDynamicTruthNativeFinalSourceLinkedImplicationRootCompiler M.
Proof.
  intros hproducer M hPA.
  exact
    (raw_dynamicTruthNativeFinalSourceLinkedImplicationRootCompiler_of_dynamicSoundnessProducer
      M hPA (hproducer M hPA)).
Qed.

End
  PABoundedRawCodedDynamicTruthNativeFinalSourceLinkedFromDynamicSoundnessProducer.
