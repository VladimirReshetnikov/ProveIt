(**
  Pair the mutually polarized dynamic-truth successor rows.

  The Sigma component consumes the preceding Pi-falsity formula code, while
  the Pi component consumes the preceding Sigma-truth formula code.  This
  file combines those two checked transformations in the public convention

      nextSigma :: nextPi :: previousSigma :: previousPi ::
        lowerLevel :: tail.

  Keeping the cross-dependencies visible in the exact semantic relation is
  important: replacing either input with the same-polarity code would define
  a different truth hierarchy even though all four values are formula codes.
*)

From Stdlib Require Import Arith Lia.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedCarrierIndexedCodeOrbitGraph
  RawCodedCarrierIndexedPairedCodeOrbitGraph
  RawCodedDynamicTruthSigmaSuccessorRowGraph
  RawCodedDynamicTruthPiSuccessorRowGraph.

Module PABoundedRawCodedDynamicTruthPairedSuccessorRowGraph.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedCarrierIndexedCodeOrbitGraph.
Import PABoundedRawCodedCarrierIndexedPairedCodeOrbitGraph.
Import PABoundedRawCodedDynamicTruthSigmaSuccessorRowGraph.
Import PABoundedRawCodedDynamicTruthPiSuccessorRowGraph.

(** The Sigma row reads [nextSigma, previousPi, lowerLevel], followed by the
    untouched tail. *)
Definition dynamicTruthPairedSigmaSuccessorRenaming (index : nat) : nat :=
  match index with
  | 0 => 0
  | 1 => 3
  | 2 => 4
  | S (S (S tailIndex)) => 5 + tailIndex
  end.

(** Dually, the Pi row reads [nextPi, previousSigma, lowerLevel]. *)
Definition dynamicTruthPairedPiSuccessorRenaming (index : nat) : nat :=
  match index with
  | 0 => 1
  | 1 => 2
  | 2 => 4
  | S (S (S tailIndex)) => 5 + tailIndex
  end.

Lemma raw_sat_dynamicTruthPairedSigmaSuccessorRenamed_iff : forall
    (M : RawPAModel) tail lowerLevel previousPi previousSigma
      nextPi nextSigma,
  raw_formula_sat M
    (scons M nextSigma (scons M nextPi
      (scons M previousSigma (scons M previousPi
        (scons M lowerLevel tail)))))
    (Formula.rename dynamicTruthPairedSigmaSuccessorRenaming
      dynamicTruthSigmaSuccessorRowGraph) <->
  raw_formula_sat M
    (scons M nextSigma
      (scons M previousPi (scons M lowerLevel tail)))
    dynamicTruthSigmaSuccessorRowGraph.
Proof.
  intros M tail lowerLevel previousPi previousSigma nextPi nextSigma.
  rewrite raw_formula_sat_rename.
  apply raw_formula_sat_ext. intro index.
  destruct index as [|[|[|tailIndex]]];
    cbn [dynamicTruthPairedSigmaSuccessorRenaming].
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - replace (5 + tailIndex) with
      (S (S (S (S (S tailIndex))))) by lia.
    reflexivity.
Qed.

Lemma raw_sat_dynamicTruthPairedPiSuccessorRenamed_iff : forall
    (M : RawPAModel) tail lowerLevel previousPi previousSigma
      nextPi nextSigma,
  raw_formula_sat M
    (scons M nextSigma (scons M nextPi
      (scons M previousSigma (scons M previousPi
        (scons M lowerLevel tail)))))
    (Formula.rename dynamicTruthPairedPiSuccessorRenaming
      dynamicTruthPiSuccessorRowGraph) <->
  raw_formula_sat M
    (scons M nextPi
      (scons M previousSigma (scons M lowerLevel tail)))
    dynamicTruthPiSuccessorRowGraph.
Proof.
  intros M tail lowerLevel previousPi previousSigma nextPi nextSigma.
  rewrite raw_formula_sat_rename.
  apply raw_formula_sat_ext. intro index.
  destruct index as [|[|[|tailIndex]]];
    cbn [dynamicTruthPairedPiSuccessorRenaming].
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - replace (5 + tailIndex) with
      (S (S (S (S (S tailIndex))))) by lia.
    reflexivity.
Qed.

Definition dynamicTruthPairedSuccessorRowGraph : formula :=
  pAnd
    (Formula.rename dynamicTruthPairedSigmaSuccessorRenaming
      dynamicTruthSigmaSuccessorRowGraph)
    (Formula.rename dynamicTruthPairedPiSuccessorRenaming
      dynamicTruthPiSuccessorRowGraph).

Definition RawDynamicTruthPairedSuccessorRowAt (M : RawPAModel)
    (previousSigma previousPi lowerLevel nextSigma nextPi : M) : Prop :=
  RawDynamicTruthSigmaSuccessorRowAt M
    previousPi lowerLevel nextSigma /\
  RawDynamicTruthPiSuccessorRowAt M
    previousSigma lowerLevel nextPi.

Arguments RawDynamicTruthPairedSuccessorRowAt
  M previousSigma previousPi lowerLevel nextSigma nextPi : clear implicits.

(** Exact law-free semantics of the paired row. *)
Theorem raw_sat_dynamicTruthPairedSuccessorRowGraph_iff : forall
    (M : RawPAModel) tail lowerLevel previousSigma previousPi
      nextSigma nextPi,
  raw_formula_sat M
    (scons M nextSigma (scons M nextPi
      (scons M previousSigma (scons M previousPi
        (scons M lowerLevel tail)))))
    dynamicTruthPairedSuccessorRowGraph <->
  RawDynamicTruthPairedSuccessorRowAt M
    previousSigma previousPi lowerLevel nextSigma nextPi.
Proof.
  intros M tail lowerLevel previousSigma previousPi nextSigma nextPi.
  unfold dynamicTruthPairedSuccessorRowGraph,
    RawDynamicTruthPairedSuccessorRowAt.
  cbn [raw_formula_sat].
  rewrite raw_sat_dynamicTruthPairedSigmaSuccessorRenamed_iff.
  rewrite raw_sat_dynamicTruthPairedPiSuccessorRenamed_iff.
  rewrite raw_sat_dynamicTruthSigmaSuccessorRowGraph_iff.
  rewrite raw_sat_dynamicTruthPiSuccessorRowGraph_iff.
  reflexivity.
Qed.

(** The paired graph implements the generic paired-orbit successor interface
    whenever the four honest component operations are total.  The operation
    premises are left visible here; later adequacy-preserving modules can
    discharge their restricted variants without manufacturing outputs for
    malformed formula codes. *)
Theorem dynamicTruthPairedSuccessorRowGraph_raw_total : forall
    (M : RawPAModel), RawPASatisfies M ->
  RawDynamicTruthSigmaDomainStepTotal M ->
  RawDynamicTruthCoqLowerApplicationTotal M ->
  RawDynamicTruthPiDomainStepTotal M ->
  RawDynamicTruthPiCoqLowerApplicationTotal M ->
  RawCarrierIndexedPairedCodeOrbitSuccessorTotal M
    dynamicTruthPairedSuccessorRowGraph.
Proof.
  intros M hPA hsigmaDomain hsigmaLower hpiDomain hpiLower
    tail lowerLevel previousSigma previousPi.
  pose proof (dynamicTruthSigmaSuccessorRowGraph_raw_total M hPA
    hsigmaDomain hsigmaLower) as hsigmaTotal.
  pose proof (dynamicTruthPiSuccessorRowGraph_raw_total M hPA
    hpiDomain hpiLower) as hpiTotal.
  destruct (hsigmaTotal tail lowerLevel previousPi)
    as [nextSigma hnextSigma].
  destruct (hpiTotal tail lowerLevel previousSigma)
    as [nextPi hnextPi].
  exists nextSigma, nextPi.
  apply (proj2
    (raw_sat_dynamicTruthPairedSuccessorRowGraph_iff M tail lowerLevel
      previousSigma previousPi nextSigma nextPi)).
  split.
  - apply (proj1 (raw_sat_dynamicTruthSigmaSuccessorRowGraph_iff
      M tail previousPi lowerLevel nextSigma)).
    exact hnextSigma.
  - apply (proj1 (raw_sat_dynamicTruthPiSuccessorRowGraph_iff
      M tail previousSigma lowerLevel nextPi)).
    exact hnextPi.
Qed.

End PABoundedRawCodedDynamicTruthPairedSuccessorRowGraph.
