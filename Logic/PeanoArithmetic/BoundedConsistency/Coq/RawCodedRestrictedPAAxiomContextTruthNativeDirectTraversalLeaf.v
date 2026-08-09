(**
  Expose the synchronized-row core of native PA axiom-context truth.

  The preceding body-shell module leaves one proof in a context reached by
  two represented universal-binder shifts.  Those target contexts are not
  opaque: inversion of [RawContextShift] exposes the twice-shifted selected
  axiom field and the twice-shifted tail literally.  This module performs
  that inversion and constructs covered assumption leaves for all four
  inputs needed by the row argument:

    - the witnessed axiom/context relation;
    - context-wide quantifier boundedness;
    - context-wide atomic adequacy; and
    - the graph-selected axiom-soundness field after both binder shifts.

  Consequently the remaining compiler below is only the synchronized-row
  composition: open the represented traversal witnesses, transfer lookups
  between their tables, and apply the shifted pointwise axiom field.  It no
  longer contains context-shift inversion or assumption lookup plumbing.
*)

From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors
  RawCodedFormulaOperations
  RawCodedContextLists
  RawCodedContextShift
  RawCodedContextInsertShiftCommutation
  RawCodedProofAssumptionLeaf
  RawCodedPALocalProofExistential
  RawCodedTemplateDirectStructuralTranslation
  RawCodedTemplateNumeralParameters
  RawCodedTemplateTernaryApplication
  RawCodedDynamicContextTruthSelector
  RawCodedRestrictedPAAxiomContextTruthNativeDirectCoherenceLink
  RawCodedRestrictedPAAxiomContextTruthNativeDirectBodyShell.

Module
  PABoundedRawCodedRestrictedPAAxiomContextTruthNativeDirectTraversalLeaf.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedContextLists.
Import PABoundedRawCodedContextShift.
Import PABoundedRawCodedContextInsertShiftCommutation.
Import PABoundedRawCodedProofAssumptionLeaf.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedTemplateDirectStructuralTranslation.
Import PABoundedRawCodedTemplateNumeralParameters.
Import PABoundedRawCodedTemplateTernaryApplication.
Import PABoundedRawCodedDynamicContextTruthSelector.
Import
  PABoundedRawCodedRestrictedPAAxiomContextTruthNativeDirectCoherenceLink.
Import
  PABoundedRawCodedRestrictedPAAxiomContextTruthNativeDirectBodyShell.

(** The literal context in which the row proof starts.  Keeping its four
    meaningful heads named avoids hiding their order in repeated [rawListNode]
    expressions throughout the residual interface. *)
Definition rawCoqRestrictedPANativeAxiomContextTruthRowContext
    (M : RawPAModel)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    (shiftedAxiomSoundness shiftedTail : M) : M :=
  rawListNode M
    (rawCoqRestrictedPANativeAxiomContextAdequacyCode M inputs)
    (rawListNode M
      (rawCoqRestrictedPANativeAxiomContextBoundedCode M inputs)
      (rawListNode M
        (rawCoqRestrictedPANativeAxiomContextWitnessCode M inputs)
        (rawListNode M shiftedAxiomSoundness shiftedTail))).

Arguments rawCoqRestrictedPANativeAxiomContextTruthRowContext
  M inputs shiftedAxiomSoundness shiftedTail : clear implicits.

(** Covered assumption roots for the four row resources.  The record stores
    proof existence rather than fixed constructor numbers, so downstream row
    composition is independent of the particular membership tables selected
    by the assumption-leaf compiler. *)
Record RawCoqRestrictedPANativeAxiomContextTruthRowProofInputsOn
    (M : RawPAModel)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    (shiftedAxiomSoundness shiftedTail : M) : Prop := {
  rawCoqRestrictedPANativeAxiomContextTruth_witness_root :
    exists root : M,
      RawCodedPALocalProofOf M
        (rawCoqRestrictedPANativeAxiomContextTruthRowContext
          M inputs shiftedAxiomSoundness shiftedTail)
        (rawCoqRestrictedPANativeAxiomContextWitnessCode M inputs)
        root;
  rawCoqRestrictedPANativeAxiomContextTruth_bounded_root :
    exists root : M,
      RawCodedPALocalProofOf M
        (rawCoqRestrictedPANativeAxiomContextTruthRowContext
          M inputs shiftedAxiomSoundness shiftedTail)
        (rawCoqRestrictedPANativeAxiomContextBoundedCode M inputs)
        root;
  rawCoqRestrictedPANativeAxiomContextTruth_adequacy_root :
    exists root : M,
      RawCodedPALocalProofOf M
        (rawCoqRestrictedPANativeAxiomContextTruthRowContext
          M inputs shiftedAxiomSoundness shiftedTail)
        (rawCoqRestrictedPANativeAxiomContextAdequacyCode M inputs)
        root;
  rawCoqRestrictedPANativeAxiomContextTruth_axiom_root :
    exists root : M,
      RawCodedPALocalProofOf M
        (rawCoqRestrictedPANativeAxiomContextTruthRowContext
          M inputs shiftedAxiomSoundness shiftedTail)
        shiftedAxiomSoundness root
}.

Arguments RawCoqRestrictedPANativeAxiomContextTruthRowProofInputsOn
  M inputs shiftedAxiomSoundness shiftedTail : clear implicits.

(** A local assumption leaf may target any represented member, not only the
    current head.  This wrapper is useful for the three inherited heads. *)
Lemma raw_codedPALocalProofOf_member_assumption : forall
    (M : RawPAModel), RawPASatisfies M -> forall context formula,
  RawContextListMember M context formula ->
  RawCodedPALocalProofOf M context formula
    (rawProofAssumptionRoot M context formula).
Proof.
  intros M hPA context formula hmember.
  split.
  - exact (raw_proofAssumption_ruleCoverage M hPA
      context formula hmember).
  - exact (raw_proofAssumption_endpoint M context formula).
Qed.

(** Construct all four leaves from one realizable shifted tail.  No formula
    adequacy is needed for an assumption rule; realizability is used only to
    certify literal list membership through the successive cons cells. *)
Theorem raw_coqRestrictedPANativeAxiomContextTruthRowProofInputs_exists :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    shiftedAxiomSoundness shiftedTail,
  RawContextListRealizable M shiftedTail ->
  RawCoqRestrictedPANativeAxiomContextTruthRowProofInputsOn
    M inputs shiftedAxiomSoundness shiftedTail.
Proof.
  intros M hPA inputs shiftedAxiomSoundness shiftedTail htail.
  set (witnessCode :=
    rawCoqRestrictedPANativeAxiomContextWitnessCode M inputs).
  set (boundedCode :=
    rawCoqRestrictedPANativeAxiomContextBoundedCode M inputs).
  set (adequacyCode :=
    rawCoqRestrictedPANativeAxiomContextAdequacyCode M inputs).
  set (axiomContext :=
    rawListNode M shiftedAxiomSoundness shiftedTail).
  set (witnessContext := rawListNode M witnessCode axiomContext).
  set (boundedContext := rawListNode M boundedCode witnessContext).
  set (rowContext := rawListNode M adequacyCode boundedContext).
  assert (haxiomContext : RawContextListRealizable M axiomContext).
  {
    unfold axiomContext.
    exact (raw_contextList_cons_realizable M hPA
      shiftedTail shiftedAxiomSoundness htail).
  }
  assert (hwitnessContext : RawContextListRealizable M witnessContext).
  {
    unfold witnessContext.
    exact (raw_contextList_cons_realizable M hPA
      axiomContext witnessCode haxiomContext).
  }
  assert (hboundedContext : RawContextListRealizable M boundedContext).
  {
    unfold boundedContext.
    exact (raw_contextList_cons_realizable M hPA
      witnessContext boundedCode hwitnessContext).
  }
  assert (hrowContext : RawContextListRealizable M rowContext).
  {
    unfold rowContext.
    exact (raw_contextList_cons_realizable M hPA
      boundedContext adequacyCode hboundedContext).
  }
  assert (hadequacyMember : RawContextListMember M rowContext adequacyCode).
  {
    unfold rowContext.
    exact (raw_contextList_cons_head_member M hPA
      boundedContext adequacyCode hboundedContext).
  }
  assert (hboundedMember : RawContextListMember M rowContext boundedCode).
  {
    unfold rowContext.
    apply (raw_contextList_cons_tail_member M hPA).
    unfold boundedContext.
    exact (raw_contextList_cons_head_member M hPA
      witnessContext boundedCode hwitnessContext).
  }
  assert (hwitnessMember : RawContextListMember M rowContext witnessCode).
  {
    unfold rowContext.
    apply (raw_contextList_cons_tail_member M hPA).
    unfold boundedContext.
    apply (raw_contextList_cons_tail_member M hPA).
    unfold witnessContext.
    exact (raw_contextList_cons_head_member M hPA
      axiomContext witnessCode haxiomContext).
  }
  assert (haxiomMember :
      RawContextListMember M rowContext shiftedAxiomSoundness).
  {
    unfold rowContext.
    apply (raw_contextList_cons_tail_member M hPA).
    unfold boundedContext.
    apply (raw_contextList_cons_tail_member M hPA).
    unfold witnessContext.
    apply (raw_contextList_cons_tail_member M hPA).
    unfold axiomContext.
    exact (raw_contextList_cons_head_member M hPA
      shiftedTail shiftedAxiomSoundness htail).
  }
  assert (hrowCode : rowContext =
      rawCoqRestrictedPANativeAxiomContextTruthRowContext
        M inputs shiftedAxiomSoundness shiftedTail).
  {
    unfold rowContext, boundedContext, witnessContext, axiomContext,
      witnessCode, boundedCode, adequacyCode,
      rawCoqRestrictedPANativeAxiomContextTruthRowContext.
    reflexivity.
  }
  rewrite <- hrowCode.
  constructor.
  - exists (rawProofAssumptionRoot M rowContext witnessCode).
    exact (raw_codedPALocalProofOf_member_assumption M hPA
      rowContext witnessCode hwitnessMember).
  - exists (rawProofAssumptionRoot M rowContext boundedCode).
    exact (raw_codedPALocalProofOf_member_assumption M hPA
      rowContext boundedCode hboundedMember).
  - exists (rawProofAssumptionRoot M rowContext adequacyCode).
    exact (raw_codedPALocalProofOf_member_assumption M hPA
      rowContext adequacyCode hadequacyMember).
  - exists (rawProofAssumptionRoot M rowContext shiftedAxiomSoundness).
    exact (raw_codedPALocalProofOf_member_assumption M hPA
      rowContext shiftedAxiomSoundness haxiomMember).
Qed.

(** ------------------------------------------------------------------
    The exact remaining synchronized-row compiler. *)

(** The two formula-shift edges record precisely which version of the
    selected axiom field is available below the two universal binders.  The
    two tail-shift edges retain the provenance of the remaining context.  All
    four logical inputs are already covered proof roots in the literal row
    context. *)
Definition RawCoqRestrictedPANativeAxiomContextTruthSynchronizedRowsCompiler
    (M : RawPAModel) : Prop :=
  forall (parameters : RawCodedTemplateNumeralParameters M)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    (tail : nat -> M)
    predecessorLevel currentGlobalSigma currentGlobalPi
    sigmaDomain piDomain nextSigmaEvidence nextAxiomSoundness
    nextGlobalSigma nextGlobalPi
    (sigmaApplicationSelector :
      RawCodedTernaryApplicationSelector M nextGlobalSigma)
    (contextApplicationSelector :
      RawCodedTernaryApplicationSelector M
        (rawDynamicContextAllSigmaCode sigmaApplicationSelector))
    context0 shiftedTail1 shiftedTail2
    shiftedAxiomSoundness1 shiftedAxiomSoundness2,
  RawCoqRestrictedPANativeAxiomContextTruthLinkAt
    M parameters inputs tail predecessorLevel
    currentGlobalSigma currentGlobalPi sigmaDomain piDomain
    nextSigmaEvidence nextAxiomSoundness
    nextGlobalSigma nextGlobalPi sigmaApplicationSelector
    contextApplicationSelector ->
  RawCodedFormulaShift M
    (raw_zero M) (rawNumeralValue M 1)
    nextAxiomSoundness shiftedAxiomSoundness1 ->
  RawCodedFormulaShift M
    (raw_zero M) (rawNumeralValue M 1)
    shiftedAxiomSoundness1 shiftedAxiomSoundness2 ->
  RawContextShift M context0 shiftedTail1 ->
  RawContextShift M shiftedTail1 shiftedTail2 ->
  RawCoqRestrictedPANativeAxiomContextTruthRowProofInputsOn
    M inputs shiftedAxiomSoundness2 shiftedTail2 ->
  exists leafRoot : M,
    RawCodedPALocalProofOf M
      (rawCoqRestrictedPANativeAxiomContextTruthRowContext
        M inputs shiftedAxiomSoundness2 shiftedTail2)
      (rawCoqRestrictedPANativeAxiomContextSelectedLeafCode
        M parameters nextGlobalSigma sigmaApplicationSelector
        contextApplicationSelector)
      leafRoot.

Arguments
  RawCoqRestrictedPANativeAxiomContextTruthSynchronizedRowsCompiler
  M : clear implicits.

(** Context-shift inversion and assumption-leaf construction compile the
    synchronized-row interface to the traversal-leaf interface consumed by
    the completed logical shell. *)
Theorem
    raw_coqRestrictedPANativeAxiomContextTruthTraversalLeafCompiler_of_synchronized_rows
    : forall (M : RawPAModel), RawPASatisfies M ->
  RawCoqRestrictedPANativeAxiomContextTruthSynchronizedRowsCompiler M ->
  RawCoqRestrictedPANativeAxiomContextTruthTraversalLeafCompiler M.
Proof.
  intros M hPA hrows parameters inputs tail predecessorLevel
    currentGlobalSigma currentGlobalPi sigmaDomain piDomain
    nextSigmaEvidence nextAxiomSoundness nextGlobalSigma nextGlobalPi
    sigmaApplicationSelector contextApplicationSelector
    context0 context1 context2 hlink hshift01 hshift12.
  destruct (raw_contextShift_cons_invert M hPA
    nextAxiomSoundness context0 context1 hshift01) as
    (shiftedAxiomSoundness1 & shiftedTail1 & hcontext1 &
      haxiomShift1 & htailShift1).
  subst context1.
  destruct (raw_contextShift_cons_invert M hPA
    shiftedAxiomSoundness1 shiftedTail1 context2 hshift12) as
    (shiftedAxiomSoundness2 & shiftedTail2 & hcontext2 &
      haxiomShift2 & htailShift2).
  subst context2.
  pose proof (raw_contextShift_target_realizable M
    shiftedTail1 shiftedTail2 htailShift2) as htail2Realizable.
  pose proof
    (raw_coqRestrictedPANativeAxiomContextTruthRowProofInputs_exists
      M hPA inputs shiftedAxiomSoundness2 shiftedTail2 htail2Realizable)
    as hproofInputs.
  change (exists leafRoot : M,
    RawCodedPALocalProofOf M
      (rawCoqRestrictedPANativeAxiomContextTruthRowContext
        M inputs shiftedAxiomSoundness2 shiftedTail2)
      (rawCoqRestrictedPANativeAxiomContextSelectedLeafCode
        M parameters nextGlobalSigma sigmaApplicationSelector
        contextApplicationSelector)
      leafRoot).
  exact (hrows parameters inputs tail predecessorLevel
    currentGlobalSigma currentGlobalPi sigmaDomain piDomain
    nextSigmaEvidence nextAxiomSoundness nextGlobalSigma nextGlobalPi
    sigmaApplicationSelector contextApplicationSelector
    context0 shiftedTail1 shiftedTail2
    shiftedAxiomSoundness1 shiftedAxiomSoundness2
    hlink haxiomShift1 haxiomShift2 htailShift1 htailShift2 hproofInputs).
Qed.

(** Direct end-to-end adapter: the final selected-axiom root now depends only
    on the synchronized-row compiler above. *)
Corollary
    raw_dynamicTruthNativeFinalSelectedAxiomContextTruthRootCompiler_of_synchronized_rows
    : forall (M : RawPAModel), RawPASatisfies M -> forall
      (inputs : RawCodedTemplateDirectStructuralInputs M),
  RawCoqRestrictedPANativeAxiomContextTruthSynchronizedRowsCompiler M ->
  RawDynamicTruthNativeFinalSelectedAxiomContextTruthRootCompiler M inputs.
Proof.
  intros M hPA inputs hrows.
  exact
    (raw_dynamicTruthNativeFinalSelectedAxiomContextTruthRootCompiler_of_traversal_leaf
      M hPA inputs
      (raw_coqRestrictedPANativeAxiomContextTruthTraversalLeafCompiler_of_synchronized_rows
        M hPA hrows)).
Qed.

End
  PABoundedRawCodedRestrictedPAAxiomContextTruthNativeDirectTraversalLeaf.
