(**
  Eliminate the ten global-traversal witnesses over predecessor state.

  A dynamic global formula begins with ten existential witnesses.  Its
  predecessor client already has the formula proof below two state-member
  assumptions.  Those assumptions cannot be treated as a self-shifting raw
  tail: under each existential eigenvariable they must themselves be shifted.
  We therefore represent them as a two-formula template prefix over the
  witnessed PA tail and invoke the completed finite elimination chain there.

  This module handles every eigenvariable context, formula shift, and Ex-E
  proof node.  The caller supplies only a proof of the appropriately shifted
  conclusion in the computed deepest context.  Later row-projection code can
  focus on that continuation without repeating ten binder steps.
*)

From Stdlib Require Import List.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedContextLists
  RawCodedRestrictedPAProof
  RawCodedPALocalProofExistential
  RawCodedPALocalProofExistentialEliminationChain
  RawCodedTemplateSyntax
  RawCodedTemplateProofCompiler
  RawCodedTemplateProofCompilerSelfShiftTail
  RawCodedTemplatePAEmbedding
  RawCodedDynamicTruthPairedGlobalSuccessorGraph
  RawCodedDynamicTruthPredecessorStateExclusivityCompilation
  RawCodedFourStateTableAppendRowLtSuccCases.

Module
  PABoundedRawCodedDynamicTruthPredecessorGlobalExistentialElimination.

Import ListNotations.
Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedContextLists.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPALocalProofExistentialEliminationChain.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedTemplateProofCompilerSelfShiftTail.
Import PABoundedRawCodedTemplatePAEmbedding.
Import PABoundedRawCodedDynamicTruthPairedGlobalSuccessorGraph.
Import
  PABoundedRawCodedDynamicTruthPredecessorStateExclusivityCompilation.
Import PABoundedRawCodedFourStateTableAppendRowLtSuccCases.

(** The prefix order is the literal raw context order: Pi is the outer head,
    Sigma is the next head, and the witnessed PA context is the tail. *)
Definition coqDynamicTruthPredecessorStateTemplateContext : TemplateContext :=
  [ embedPAFormula dynamicTruthPredecessorPiStateMemberBodyFormula;
    embedPAFormula dynamicTruthPredecessorSigmaStateMemberBodyFormula ].

Definition coqDynamicTruthGlobalExistentialSource
    (rootMode : nat) (localSigma localPi : formula) : TemplateFormula :=
  embedPAFormula
    (dynamicTruthGlobalFormula (Term.numeral rootMode)
      localSigma localPi).

(** Compute, rather than hand-write, the ten successively shifted contexts.
    The fallback branch is unreachable and audited by the success lemma. *)
Definition coqDynamicTruthGlobalExistentialDeepContext
    (rootMode : nat) (localSigma localPi : formula) : TemplateContext :=
  match templateExistentialEliminationContext 10
    (coqDynamicTruthGlobalExistentialSource rootMode localSigma localPi)
    coqDynamicTruthPredecessorStateTemplateContext with
  | Some context => context
  | None => []
  end.

(** Variant retaining an arbitrary caller prefix behind the two predecessor
    state assumptions.  Every formula in that prefix is shifted by the
    generic elimination-chain machinery as the ten eigenvariables enter. *)
Definition coqDynamicTruthGlobalExistentialDeepContextUnderPrefix
    (rootMode : nat) (localSigma localPi : formula)
    (prefix : TemplateContext) : TemplateContext :=
  match templateExistentialEliminationContext 10
    (coqDynamicTruthGlobalExistentialSource rootMode localSigma localPi)
    (coqDynamicTruthPredecessorStateTemplateContext ++ prefix) with
  | Some context => context
  | None => []
  end.

Lemma coqDynamicTruthGlobalExistentialDeepContext_success : forall
    rootMode localSigma localPi,
  templateExistentialEliminationContext 10
    (coqDynamicTruthGlobalExistentialSource rootMode localSigma localPi)
    coqDynamicTruthPredecessorStateTemplateContext =
  Some (coqDynamicTruthGlobalExistentialDeepContext
    rootMode localSigma localPi).
Proof.
  intros rootMode localSigma localPi.
  reflexivity.
Qed.

Lemma coqDynamicTruthGlobalExistentialDeepContextUnderPrefix_success :
  forall rootMode localSigma localPi prefix,
  templateExistentialEliminationContext 10
    (coqDynamicTruthGlobalExistentialSource rootMode localSigma localPi)
    (coqDynamicTruthPredecessorStateTemplateContext ++ prefix) =
  Some (coqDynamicTruthGlobalExistentialDeepContextUnderPrefix
    rootMode localSigma localPi prefix).
Proof.
  intros rootMode localSigma localPi prefix.
  reflexivity.
Qed.

(** Agreement identifies the translated two-formula prefix with the raw
    context used by the predecessor closure. *)
Lemma raw_dynamicTruthPredecessorStateTemplateContextCode : forall
    (M : RawPAModel) (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall baseContext,
  rawTemplateContextCodeOnTail translation baseContext
    coqDynamicTruthPredecessorStateTemplateContext =
  rawDynamicTruthPredecessorJointStateContext M baseContext.
Proof.
  intros M translation hagreement baseContext.
  unfold coqDynamicTruthPredecessorStateTemplateContext,
    rawDynamicTruthPredecessorJointStateContext,
    rawDynamicTruthPredecessorSigmaStateContext,
    rawDynamicTruthPredecessorPiStateMemberBodyCode,
    rawDynamicTruthPredecessorSigmaStateMemberBodyCode.
  cbn [rawTemplateContextCodeOnTail].
  rewrite !rawTemplateFormula_embedPA by exact hagreement.
  reflexivity.
Qed.

(** Context normalization with additional temporary assumptions.  Keeping
    this equation next to the existential context definition lets both the
    admissibility and row-elimination layers share it without a dependency
    cycle. *)
Lemma raw_dynamicTruthPredecessorStateTemplateContext_app_code : forall
    (M : RawPAModel) (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall baseContext prefix,
  rawTemplateContextCodeOnTail translation baseContext
      (coqDynamicTruthPredecessorStateTemplateContext ++ prefix) =
    rawDynamicTruthPredecessorJointStateContext M
      (rawTemplateContextCodeOnTail translation baseContext prefix).
Proof.
  intros M translation hagreement baseContext prefix.
  unfold coqDynamicTruthPredecessorStateTemplateContext,
    rawDynamicTruthPredecessorJointStateContext,
    rawDynamicTruthPredecessorSigmaStateContext,
    rawDynamicTruthPredecessorPiStateMemberBodyCode,
    rawDynamicTruthPredecessorSigmaStateMemberBodyCode.
  cbn [List.app rawTemplateContextCodeOnTail].
  rewrite !rawTemplateFormula_embedPA by exact hagreement.
  reflexivity.
Qed.

(** Complete ten-step elimination beneath predecessor state plus an arbitrary
    caller prefix.  The witnessed tail remains the only raw context on which
    the generic elimination compiler relies. *)
Theorem
    raw_codedPALocalProofOf_dynamicTruthGlobal_existential_elimination_on_predecessor_state_context_under_prefix :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall witnessList baseContext prefix rootMode localSigma localPi
      conclusion sourceRoot deepRoot,
  RawCodedPAAxiomWitnessContext M witnessList baseContext ->
  RawCodedPALocalProofOf M
    (rawDynamicTruthPredecessorJointStateContext M
      (rawTemplateContextCodeOnTail translation baseContext prefix))
    (rawTemplateFormula translation
      (coqDynamicTruthGlobalExistentialSource
        rootMode localSigma localPi)) sourceRoot ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail translation baseContext
      (coqDynamicTruthGlobalExistentialDeepContextUnderPrefix
        rootMode localSigma localPi prefix))
    (rawTemplateFormula translation
      (templateFormulaShiftMany 10 conclusion)) deepRoot ->
  exists root,
    RawCodedPALocalProofOf M
      (rawDynamicTruthPredecessorJointStateContext M
        (rawTemplateContextCodeOnTail translation baseContext prefix))
      (rawTemplateFormula translation conclusion) root.
Proof.
  intros M hPA translation hagreement witnessList baseContext prefix
    rootMode localSigma localPi conclusion sourceRoot deepRoot
    hwitnessed hsource hdeep.
  assert (hsourceOnTemplateContext : RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation baseContext
        (coqDynamicTruthPredecessorStateTemplateContext ++ prefix))
      (rawTemplateFormula translation
        (coqDynamicTruthGlobalExistentialSource
          rootMode localSigma localPi)) sourceRoot).
  {
    rewrite (raw_dynamicTruthPredecessorStateTemplateContext_app_code
      M translation hagreement baseContext prefix).
    exact hsource.
  }
  destruct
    (raw_codedPALocalProofOf_existential_elimination_chain_on_witnessed_tail
      M hPA translation witnessList baseContext 10
      (coqDynamicTruthGlobalExistentialSource
        rootMode localSigma localPi)
      (coqDynamicTruthPredecessorStateTemplateContext ++ prefix) conclusion
      (coqDynamicTruthGlobalExistentialDeepContextUnderPrefix
        rootMode localSigma localPi prefix)
      sourceRoot deepRoot hwitnessed
      (coqDynamicTruthGlobalExistentialDeepContextUnderPrefix_success
        rootMode localSigma localPi prefix)
      hsourceOnTemplateContext hdeep) as [root hroot].
  exists root.
  rewrite <- (raw_dynamicTruthPredecessorStateTemplateContext_app_code
    M translation hagreement baseContext prefix).
  exact hroot.
Qed.

(** The complete ten-step elimination endpoint.  [conclusion] is a template
    formula because its shift through the eigenvariable block must be tracked
    syntactically.  Carrier-valued evidence conclusions will be connected to
    such templates by the trace's direct structural translation. *)
Corollary
    raw_codedPALocalProofOf_dynamicTruthGlobal_existential_elimination_on_predecessor_state_context :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall witnessList baseContext rootMode localSigma localPi
      conclusion sourceRoot deepRoot,
  RawCodedPAAxiomWitnessContext M witnessList baseContext ->
  RawCodedPALocalProofOf M
    (rawDynamicTruthPredecessorJointStateContext M baseContext)
    (rawTemplateFormula translation
      (coqDynamicTruthGlobalExistentialSource
        rootMode localSigma localPi)) sourceRoot ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail translation baseContext
      (coqDynamicTruthGlobalExistentialDeepContext
        rootMode localSigma localPi))
    (rawTemplateFormula translation
      (templateFormulaShiftMany 10 conclusion)) deepRoot ->
  exists root,
    RawCodedPALocalProofOf M
      (rawDynamicTruthPredecessorJointStateContext M baseContext)
      (rawTemplateFormula translation conclusion) root.
Proof.
  intros M hPA translation hagreement witnessList baseContext
    rootMode localSigma localPi conclusion sourceRoot deepRoot
    hwitnessed hsource hdeep.
  pose proof
    (raw_codedPALocalProofOf_dynamicTruthGlobal_existential_elimination_on_predecessor_state_context_under_prefix
      M hPA translation hagreement witnessList baseContext []
      rootMode localSigma localPi conclusion sourceRoot deepRoot
      hwitnessed hsource hdeep) as hresult.
  cbn [rawTemplateContextCodeOnTail
    coqDynamicTruthGlobalExistentialDeepContextUnderPrefix
    coqDynamicTruthGlobalExistentialDeepContext] in hresult.
  exact hresult.
Qed.

End
  PABoundedRawCodedDynamicTruthPredecessorGlobalExistentialElimination.
