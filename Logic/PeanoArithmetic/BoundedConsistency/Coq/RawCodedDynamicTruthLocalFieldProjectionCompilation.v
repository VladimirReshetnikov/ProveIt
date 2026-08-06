(**
  Proof-code projections from the native local decision/exclusivity field.

  A positive local field is a conjunction of two triple-universal laws.  Its
  clients previously carried the conjunction proof as an opaque root and
  would have had to repeat represented And-E assembly before using either
  law.  These projections are independent of the dynamic orbit, row
  parameters, and proof context, so they are factored here once.

  No semantic soundness is used: each result is one represented conjunction
  elimination node over the literal caller-supplied proof root.
*)

From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors
  RawCodedProofBinaryConstructors
  RawCodedProofAndEConstructors
  RawCodedPALocalProofExistential
  RawCodedPALocalProofConjunction
  RawCodedPALocalProofComposition
  RawCodedPALocalProofUniversalEliminationChain
  RawCodedDynamicTruthNativeLocalPositiveGraph
  RawCodedDynamicTruthNativeLocalProofCompilation
  RawCodedDynamicTruthLocalExclusiveTemplateDirectInputs
  RawCodedDynamicTruthLocalExclusiveTemplateTraceCompilation.

Module PABoundedRawCodedDynamicTruthLocalFieldProjectionCompilation.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedProofBinaryConstructors.
Import PABoundedRawCodedProofAndEConstructors.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPALocalProofConjunction.
Import PABoundedRawCodedPALocalProofComposition.
Import PABoundedRawCodedPALocalProofUniversalEliminationChain.
Import PABoundedRawCodedDynamicTruthNativeLocalPositiveGraph.
Import PABoundedRawCodedDynamicTruthNativeLocalProofCompilation.
Import
  PABoundedRawCodedDynamicTruthLocalExclusiveTemplateDirectInputs.
Import
  PABoundedRawCodedDynamicTruthLocalExclusiveTemplateTraceCompilation.

Definition rawDynamicTruthLocalDecisionProjectionRoot
    (M : RawPAModel) (context sigmaDomain piDomain
      sigmaEvidence piEvidence sourceRoot : M) : M :=
  rawProofAndERoot M RawAndLeft context
    (rawDynamicTruthLocalFormulaAll3Code M
      (rawDynamicTruthLocalDecisionCode M
        sigmaDomain piDomain sigmaEvidence piEvidence))
    (rawDynamicTruthLocalFormulaAll3Code M
      (rawDynamicTruthLocalExclusiveCode M
        sigmaDomain piDomain sigmaEvidence piEvidence))
    sourceRoot.

Definition rawDynamicTruthLocalExclusiveProjectionRoot
    (M : RawPAModel) (context sigmaDomain piDomain
      sigmaEvidence piEvidence sourceRoot : M) : M :=
  rawProofAndERoot M RawAndRight context
    (rawDynamicTruthLocalFormulaAll3Code M
      (rawDynamicTruthLocalDecisionCode M
        sigmaDomain piDomain sigmaEvidence piEvidence))
    (rawDynamicTruthLocalFormulaAll3Code M
      (rawDynamicTruthLocalExclusiveCode M
        sigmaDomain piDomain sigmaEvidence piEvidence))
    sourceRoot.

Arguments rawDynamicTruthLocalDecisionProjectionRoot
  M context sigmaDomain piDomain sigmaEvidence piEvidence sourceRoot
  : clear implicits.
Arguments rawDynamicTruthLocalExclusiveProjectionRoot
  M context sigmaDomain piDomain sigmaEvidence piEvidence sourceRoot
  : clear implicits.

Theorem raw_codedPALocalProofOf_dynamicTruthLocalDecisionProjection : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      context sigmaDomain piDomain sigmaEvidence piEvidence sourceRoot,
  RawCodedPALocalProofOf M context
    (rawDynamicTruthLocalDecisionExclusiveFieldCode M
      sigmaDomain piDomain sigmaEvidence piEvidence) sourceRoot ->
  RawCodedPALocalProofOf M context
    (rawDynamicTruthLocalFormulaAll3Code M
      (rawDynamicTruthLocalDecisionCode M
        sigmaDomain piDomain sigmaEvidence piEvidence))
    (rawDynamicTruthLocalDecisionProjectionRoot M context
      sigmaDomain piDomain sigmaEvidence piEvidence sourceRoot).
Proof.
  intros M hPA context sigmaDomain piDomain sigmaEvidence piEvidence
    sourceRoot hsource.
  unfold rawDynamicTruthLocalDecisionExclusiveFieldCode in hsource.
  exact (raw_codedPALocalProofOf_andE1 M hPA context
    (rawDynamicTruthLocalFormulaAll3Code M
      (rawDynamicTruthLocalDecisionCode M
        sigmaDomain piDomain sigmaEvidence piEvidence))
    (rawDynamicTruthLocalFormulaAll3Code M
      (rawDynamicTruthLocalExclusiveCode M
        sigmaDomain piDomain sigmaEvidence piEvidence))
    sourceRoot hsource).
Qed.

Theorem raw_codedPALocalProofOf_dynamicTruthLocalExclusiveProjection : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      context sigmaDomain piDomain sigmaEvidence piEvidence sourceRoot,
  RawCodedPALocalProofOf M context
    (rawDynamicTruthLocalDecisionExclusiveFieldCode M
      sigmaDomain piDomain sigmaEvidence piEvidence) sourceRoot ->
  RawCodedPALocalProofOf M context
    (rawDynamicTruthLocalFormulaAll3Code M
      (rawDynamicTruthLocalExclusiveCode M
        sigmaDomain piDomain sigmaEvidence piEvidence))
    (rawDynamicTruthLocalExclusiveProjectionRoot M context
      sigmaDomain piDomain sigmaEvidence piEvidence sourceRoot).
Proof.
  intros M hPA context sigmaDomain piDomain sigmaEvidence piEvidence
    sourceRoot hsource.
  unfold rawDynamicTruthLocalDecisionExclusiveFieldCode in hsource.
  exact (raw_codedPALocalProofOf_andE2 M hPA context
    (rawDynamicTruthLocalFormulaAll3Code M
      (rawDynamicTruthLocalDecisionCode M
        sigmaDomain piDomain sigmaEvidence piEvidence))
    (rawDynamicTruthLocalFormulaAll3Code M
      (rawDynamicTruthLocalExclusiveCode M
        sigmaDomain piDomain sigmaEvidence piEvidence))
    sourceRoot hsource).
Qed.

(** Package both projections when a later stage needs the complete local
    pair.  The record stores the deterministic represented roots rather than
    hiding them behind fresh existentials. *)
Record RawDynamicTruthLocalDecisionExclusiveProjectedRootsAt
    (M : RawPAModel) (context sigmaDomain piDomain
      sigmaEvidence piEvidence sourceRoot : M) : Prop := {
  rawDynamicTruthLocalProjected_decision :
    RawCodedPALocalProofOf M context
      (rawDynamicTruthLocalFormulaAll3Code M
        (rawDynamicTruthLocalDecisionCode M
          sigmaDomain piDomain sigmaEvidence piEvidence))
      (rawDynamicTruthLocalDecisionProjectionRoot M context
        sigmaDomain piDomain sigmaEvidence piEvidence sourceRoot);
  rawDynamicTruthLocalProjected_exclusive :
    RawCodedPALocalProofOf M context
      (rawDynamicTruthLocalFormulaAll3Code M
        (rawDynamicTruthLocalExclusiveCode M
          sigmaDomain piDomain sigmaEvidence piEvidence))
      (rawDynamicTruthLocalExclusiveProjectionRoot M context
        sigmaDomain piDomain sigmaEvidence piEvidence sourceRoot)
}.

Arguments RawDynamicTruthLocalDecisionExclusiveProjectedRootsAt
  M context sigmaDomain piDomain sigmaEvidence piEvidence sourceRoot
  : clear implicits.

Theorem raw_dynamicTruthLocalDecisionExclusiveProjectedRootsAt_of_local :
    forall (M : RawPAModel), RawPASatisfies M -> forall
      context sigmaDomain piDomain sigmaEvidence piEvidence sourceRoot,
  RawCodedPALocalProofOf M context
    (rawDynamicTruthLocalDecisionExclusiveFieldCode M
      sigmaDomain piDomain sigmaEvidence piEvidence) sourceRoot ->
  RawDynamicTruthLocalDecisionExclusiveProjectedRootsAt M context
    sigmaDomain piDomain sigmaEvidence piEvidence sourceRoot.
Proof.
  intros M hPA context sigmaDomain piDomain sigmaEvidence piEvidence
    sourceRoot hsource.
  split.
  - exact (raw_codedPALocalProofOf_dynamicTruthLocalDecisionProjection
      M hPA context sigmaDomain piDomain sigmaEvidence piEvidence
      sourceRoot hsource).
  - exact (raw_codedPALocalProofOf_dynamicTruthLocalExclusiveProjection
      M hPA context sigmaDomain piDomain sigmaEvidence piEvidence
      sourceRoot hsource).
Qed.

(** A client which knows the desired represented instance supplies only the
    elimination chain.  Projection of the relevant conjunct and compilation
    of every All-E node stay internal to these two general adapters. *)
Theorem raw_codedPALocalProofOf_dynamicTruthLocalDecisionInstance : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      context sigmaDomain piDomain sigmaEvidence piEvidence
      sourceRoot target,
  RawCodedPALocalProofOf M context
    (rawDynamicTruthLocalDecisionExclusiveFieldCode M
      sigmaDomain piDomain sigmaEvidence piEvidence) sourceRoot ->
  RawCodedUniversalEliminationChain M
    (rawDynamicTruthLocalFormulaAll3Code M
      (rawDynamicTruthLocalDecisionCode M
        sigmaDomain piDomain sigmaEvidence piEvidence)) target ->
  exists targetRoot,
    RawCodedPALocalProofOf M context target targetRoot.
Proof.
  intros M hPA context sigmaDomain piDomain sigmaEvidence piEvidence
    sourceRoot target hsource hchain.
  exact (raw_codedPALocalProofOf_universal_elimination_chain
    M hPA context
    (rawDynamicTruthLocalFormulaAll3Code M
      (rawDynamicTruthLocalDecisionCode M
        sigmaDomain piDomain sigmaEvidence piEvidence))
    target hchain
    (rawDynamicTruthLocalDecisionProjectionRoot M context
      sigmaDomain piDomain sigmaEvidence piEvidence sourceRoot)
    (raw_codedPALocalProofOf_dynamicTruthLocalDecisionProjection
      M hPA context sigmaDomain piDomain sigmaEvidence piEvidence
      sourceRoot hsource)).
Qed.

Theorem raw_codedPALocalProofOf_dynamicTruthLocalExclusiveInstance : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      context sigmaDomain piDomain sigmaEvidence piEvidence
      sourceRoot target,
  RawCodedPALocalProofOf M context
    (rawDynamicTruthLocalDecisionExclusiveFieldCode M
      sigmaDomain piDomain sigmaEvidence piEvidence) sourceRoot ->
  RawCodedUniversalEliminationChain M
    (rawDynamicTruthLocalFormulaAll3Code M
      (rawDynamicTruthLocalExclusiveCode M
        sigmaDomain piDomain sigmaEvidence piEvidence)) target ->
  exists targetRoot,
    RawCodedPALocalProofOf M context target targetRoot.
Proof.
  intros M hPA context sigmaDomain piDomain sigmaEvidence piEvidence
    sourceRoot target hsource hchain.
  exact (raw_codedPALocalProofOf_universal_elimination_chain
    M hPA context
    (rawDynamicTruthLocalFormulaAll3Code M
      (rawDynamicTruthLocalExclusiveCode M
        sigmaDomain piDomain sigmaEvidence piEvidence))
    target hchain
    (rawDynamicTruthLocalExclusiveProjectionRoot M context
      sigmaDomain piDomain sigmaEvidence piEvidence sourceRoot)
    (raw_codedPALocalProofOf_dynamicTruthLocalExclusiveProjection
      M hPA context sigmaDomain piDomain sigmaEvidence piEvidence
      sourceRoot hsource)).
Qed.

(** The proof-theoretic core does not depend on how the three universal
    instantiations were identified.  A native trace is one source of this
    chain, while the rank-zero callback has a separate fixed-quotation
    identification.  Keeping the chain explicit here gives both clients the
    same implication-elimination endpoint without imposing either source's
    stronger syntactic package on the other. *)
Theorem
    raw_codedPALocalProofOf_dynamicTruthLocalEvidenceDecision_of_elimination_chain :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    context sigmaDomain piDomain sigmaEvidence piEvidence
    decisionSourceRoot admissibleRoot,
  RawCodedUniversalEliminationChain M
    (rawDynamicTruthLocalFormulaAll3Code M
      (rawDynamicTruthLocalDecisionCode M
        sigmaDomain piDomain sigmaEvidence piEvidence))
    (rawDynamicTruthLocalDecisionCode M
      sigmaDomain piDomain sigmaEvidence piEvidence) ->
  RawCodedPALocalProofOf M context
    (rawDynamicTruthLocalFormulaAll3Code M
      (rawDynamicTruthLocalDecisionCode M
        sigmaDomain piDomain sigmaEvidence piEvidence))
    decisionSourceRoot ->
  RawCodedPALocalProofOf M context
    (rawDynamicTruthLocalAdmissibleCode M sigmaDomain piDomain)
    admissibleRoot ->
  exists decisionRoot,
    RawCodedPALocalProofOf M context
      (rawFormulaOrCode M sigmaEvidence piEvidence) decisionRoot.
Proof.
  intros M hPA context sigmaDomain piDomain sigmaEvidence piEvidence
    decisionSourceRoot admissibleRoot hchain hdecision hadmissible.
  destruct
    (raw_codedPALocalProofOf_universal_elimination_chain
      M hPA context
      (rawDynamicTruthLocalFormulaAll3Code M
        (rawDynamicTruthLocalDecisionCode M
          sigmaDomain piDomain sigmaEvidence piEvidence))
      (rawDynamicTruthLocalDecisionCode M
        sigmaDomain piDomain sigmaEvidence piEvidence)
      hchain decisionSourceRoot hdecision)
    as [openedRoot hopened].
  exists
    (rawProofImpERoot M context
      (rawDynamicTruthLocalAdmissibleCode M sigmaDomain piDomain)
      (rawFormulaOrCode M sigmaEvidence piEvidence)
      openedRoot admissibleRoot).
  exact
    (raw_codedPALocalProofOf_impE M hPA context
      (rawDynamicTruthLocalAdmissibleCode M sigmaDomain piDomain)
      (rawFormulaOrCode M sigmaEvidence piEvidence)
      openedRoot admissibleRoot hopened hadmissible).
Qed.

(** Native traces already select the honest dual-predicate translation used
    by both local laws.  These adapters construct the represented opening
    chains internally, so clients no longer have to duplicate the selector
    choice merely to instantiate one projected conjunct. *)
Theorem
    raw_codedPALocalProofOf_dynamicTruthLocalDecisionInstance_of_native_trace :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (tail : nat -> M) predecessorLevel inputGlobalSigma inputGlobalPi
    context sigmaDomain piDomain sigmaEvidence piEvidence sourceRoot,
  RawDynamicTruthNativeLocalProofTraceAt M tail predecessorLevel
    inputGlobalSigma inputGlobalPi sigmaDomain piDomain
    sigmaEvidence piEvidence ->
  RawCodedPALocalProofOf M context
    (rawDynamicTruthLocalFormulaAll3Code M
      (rawDynamicTruthLocalDecisionCode M
        sigmaDomain piDomain sigmaEvidence piEvidence)) sourceRoot ->
  exists targetRoot,
    RawCodedPALocalProofOf M context
      (rawDynamicTruthLocalDecisionCode M
        sigmaDomain piDomain sigmaEvidence piEvidence) targetRoot.
Proof.
  intros M hPA tail predecessorLevel inputGlobalSigma inputGlobalPi
    context sigmaDomain piDomain sigmaEvidence piEvidence sourceRoot
    htrace hsource.
  destruct
    (raw_coqDynamicTruthLocalExclusiveTemplateIdentification_of_native_trace
      M hPA tail predecessorLevel inputGlobalSigma inputGlobalPi
      sigmaDomain piDomain sigmaEvidence piEvidence htrace)
    as [inputs hidentification].
  exact
    (raw_codedPALocalProofOf_universal_elimination_chain
      M hPA context
      (rawDynamicTruthLocalFormulaAll3Code M
        (rawDynamicTruthLocalDecisionCode M
          sigmaDomain piDomain sigmaEvidence piEvidence))
      (rawDynamicTruthLocalDecisionCode M
        sigmaDomain piDomain sigmaEvidence piEvidence)
      (rawCoqDynamicTruthLocalDecisionEliminationChain_identified
        M hPA inputs sigmaDomain piDomain sigmaEvidence piEvidence
        hidentification)
      sourceRoot hsource).
Qed.

Theorem
    raw_codedPALocalProofOf_dynamicTruthLocalExclusiveInstance_of_native_trace :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (tail : nat -> M) predecessorLevel inputGlobalSigma inputGlobalPi
    context sigmaDomain piDomain sigmaEvidence piEvidence sourceRoot,
  RawDynamicTruthNativeLocalProofTraceAt M tail predecessorLevel
    inputGlobalSigma inputGlobalPi sigmaDomain piDomain
    sigmaEvidence piEvidence ->
  RawCodedPALocalProofOf M context
    (rawDynamicTruthLocalFormulaAll3Code M
      (rawDynamicTruthLocalExclusiveCode M
        sigmaDomain piDomain sigmaEvidence piEvidence)) sourceRoot ->
  exists targetRoot,
    RawCodedPALocalProofOf M context
      (rawDynamicTruthLocalExclusiveCode M
        sigmaDomain piDomain sigmaEvidence piEvidence) targetRoot.
Proof.
  intros M hPA tail predecessorLevel inputGlobalSigma inputGlobalPi
    context sigmaDomain piDomain sigmaEvidence piEvidence sourceRoot
    htrace hsource.
  destruct
    (raw_coqDynamicTruthLocalExclusiveTemplateIdentification_of_native_trace
      M hPA tail predecessorLevel inputGlobalSigma inputGlobalPi
      sigmaDomain piDomain sigmaEvidence piEvidence htrace)
    as [inputs hidentification].
  exact
    (raw_codedPALocalProofOf_universal_elimination_chain
      M hPA context
      (rawDynamicTruthLocalFormulaAll3Code M
        (rawDynamicTruthLocalExclusiveCode M
          sigmaDomain piDomain sigmaEvidence piEvidence))
      (rawDynamicTruthLocalExclusiveCode M
        sigmaDomain piDomain sigmaEvidence piEvidence)
      (rawCoqDynamicTruthLocalExclusiveEliminationChain_identified
        M hPA inputs sigmaDomain piDomain sigmaEvidence piEvidence
        hidentification)
      sourceRoot hsource).
Qed.

(** Apply the opened decision implication to an admissibility root in the
    same literal context.  This is the first proof-producing use of the
    projected decision component at the normalized callback boundary. *)
Corollary
    raw_codedPALocalProofOf_dynamicTruthLocalEvidenceDecision_of_native_trace :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (tail : nat -> M) predecessorLevel inputGlobalSigma inputGlobalPi
    context sigmaDomain piDomain sigmaEvidence piEvidence
    decisionSourceRoot admissibleRoot,
  RawDynamicTruthNativeLocalProofTraceAt M tail predecessorLevel
    inputGlobalSigma inputGlobalPi sigmaDomain piDomain
    sigmaEvidence piEvidence ->
  RawCodedPALocalProofOf M context
    (rawDynamicTruthLocalFormulaAll3Code M
      (rawDynamicTruthLocalDecisionCode M
        sigmaDomain piDomain sigmaEvidence piEvidence))
    decisionSourceRoot ->
  RawCodedPALocalProofOf M context
    (rawDynamicTruthLocalAdmissibleCode M sigmaDomain piDomain)
    admissibleRoot ->
  exists decisionRoot,
    RawCodedPALocalProofOf M context
      (rawFormulaOrCode M sigmaEvidence piEvidence) decisionRoot.
Proof.
  intros M hPA tail predecessorLevel inputGlobalSigma inputGlobalPi
    context sigmaDomain piDomain sigmaEvidence piEvidence
    decisionSourceRoot admissibleRoot htrace hdecision hadmissible.
  destruct
    (raw_coqDynamicTruthLocalExclusiveTemplateIdentification_of_native_trace
      M hPA tail predecessorLevel inputGlobalSigma inputGlobalPi
      sigmaDomain piDomain sigmaEvidence piEvidence htrace)
    as [inputs hidentification].
  exact
    (raw_codedPALocalProofOf_dynamicTruthLocalEvidenceDecision_of_elimination_chain
      M hPA context sigmaDomain piDomain sigmaEvidence piEvidence
      decisionSourceRoot admissibleRoot
      (rawCoqDynamicTruthLocalDecisionEliminationChain_identified
        M hPA inputs sigmaDomain piDomain sigmaEvidence piEvidence
        hidentification)
      hdecision hadmissible).
Qed.

End PABoundedRawCodedDynamicTruthLocalFieldProjectionCompilation.
