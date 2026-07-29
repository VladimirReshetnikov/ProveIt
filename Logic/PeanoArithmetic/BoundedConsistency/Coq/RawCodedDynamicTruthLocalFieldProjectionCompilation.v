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
  RawCodedProofAndEConstructors
  RawCodedPALocalProofExistential
  RawCodedPALocalProofConjunction
  RawCodedPALocalProofUniversalEliminationChain
  RawCodedDynamicTruthNativeLocalPositiveGraph.

Module PABoundedRawCodedDynamicTruthLocalFieldProjectionCompilation.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedProofAndEConstructors.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPALocalProofConjunction.
Import PABoundedRawCodedPALocalProofUniversalEliminationChain.
Import PABoundedRawCodedDynamicTruthNativeLocalPositiveGraph.

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

End PABoundedRawCodedDynamicTruthLocalFieldProjectionCompilation.
