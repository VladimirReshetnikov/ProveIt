(**
  Remove a hypothetical native predecessor-state prefix by represented cuts.

  Native predecessor evidence is compiled under two literal state
  assumptions: Pi is the outer head and Sigma is the next head.  If proofs of
  both state atoms are supplied in a base context, the generic two-assumption
  discharge theorem performs the corresponding rerooting.

  This is a structural cut lemma, not a producer for the native Imp-I branch.
  The predecessor-state exclusivity compiler proves that Sigma and Pi state
  evidence cannot coexist in a consistent ready context.  Consequently the
  real branch compiler must construct its decision directly in that ready
  context instead of trying to instantiate this theorem with both roots.

  This theorem is deliberately conclusion-generic.  In particular it can
  reroot the predecessor decision disjunction without assuming any dynamic
  truth or implication-introduction law.
*)

From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA.
From BoundedPAConsistency Require Import
  RawCodedContextLists
  RawCodedPALocalProofExistential
  RawCodedTemplateSyntax
  RawCodedTemplateProofCompiler
  RawCodedTemplateProofCompilerSelfShiftTail
  RawCodedTemplatePAEmbedding
  RawCodedTemplateLocalProofAssumptionDischarge
  RawCodedDynamicTruthPredecessorStateExclusivityCompilation
  RawCodedDynamicTruthPredecessorGlobalExistentialElimination
  RawCodedDynamicTruthPredecessorAdmissibilityAssignmentCompilation.

Module PABoundedRawCodedDynamicTruthPredecessorJointStateDischarge.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PABoundedRawCodedContextLists.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedTemplateProofCompilerSelfShiftTail.
Import PABoundedRawCodedTemplatePAEmbedding.
Import PABoundedRawCodedTemplateLocalProofAssumptionDischarge.
Import
  PABoundedRawCodedDynamicTruthPredecessorGlobalExistentialElimination.
Import
  PABoundedRawCodedDynamicTruthPredecessorStateExclusivityCompilation.
Import
  PABoundedRawCodedDynamicTruthPredecessorAdmissibilityAssignmentCompilation.

(** The order of the two hypothetical source roots follows the literal context order:
    Pi first, then Sigma.  The raw/template code equalities are consequences
    of PA agreement, so no carrier-code identification premise leaks into
    the public boundary. *)
Theorem raw_codedPALocalProofOf_predecessor_joint_state_discharge : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall baseContext conclusion piStateRoot sigmaStateRoot childRoot,
  RawContextListRealizable M baseContext ->
  RawCodedPALocalProofOf M baseContext
    (rawDynamicTruthPredecessorPiStateMemberBodyCode M) piStateRoot ->
  RawCodedPALocalProofOf M baseContext
    (rawDynamicTruthPredecessorSigmaStateMemberBodyCode M) sigmaStateRoot ->
  RawCodedPALocalProofOf M
    (rawDynamicTruthPredecessorJointStateContext M baseContext)
    conclusion childRoot ->
  exists resultRoot,
    RawCodedPALocalProofOf M baseContext conclusion resultRoot.
Proof.
  intros M hPA translation hagreement
    baseContext conclusion piStateRoot sigmaStateRoot childRoot
    hbase hpi hsigma hchild.
  assert (hpiTemplate : RawCodedPALocalProofOf M baseContext
      (rawTemplateFormula translation
        (embedPAFormula dynamicTruthPredecessorPiStateMemberBodyFormula))
      piStateRoot).
  {
    rewrite (rawTemplateFormula_embedPA hagreement
      dynamicTruthPredecessorPiStateMemberBodyFormula).
    unfold rawDynamicTruthPredecessorPiStateMemberBodyCode.
    exact hpi.
  }
  assert (hsigmaTemplate : RawCodedPALocalProofOf M baseContext
      (rawTemplateFormula translation
        (embedPAFormula dynamicTruthPredecessorSigmaStateMemberBodyFormula))
      sigmaStateRoot).
  {
    rewrite (rawTemplateFormula_embedPA hagreement
      dynamicTruthPredecessorSigmaStateMemberBodyFormula).
    unfold rawDynamicTruthPredecessorSigmaStateMemberBodyCode.
    exact hsigma.
  }
  assert (hchildTemplate : RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation baseContext
        coqDynamicTruthPredecessorStateTemplateContext)
      conclusion childRoot).
  {
    rewrite (raw_dynamicTruthPredecessorStateTemplateContextCode
      M translation hagreement baseContext).
    exact hchild.
  }
  exact
    (raw_codedPALocalProof_discharge_two_template_assumptions
      M hPA translation baseContext
      (embedPAFormula dynamicTruthPredecessorPiStateMemberBodyFormula)
      (embedPAFormula dynamicTruthPredecessorSigmaStateMemberBodyFormula)
      conclusion piStateRoot sigmaStateRoot childRoot
      hbase
      (raw_dynamicTruthPredecessorStateTemplateContext_atomically_adequate
        M hPA translation hagreement)
      hpiTemplate hsigmaTemplate hchildTemplate).
Qed.

End PABoundedRawCodedDynamicTruthPredecessorJointStateDischarge.
