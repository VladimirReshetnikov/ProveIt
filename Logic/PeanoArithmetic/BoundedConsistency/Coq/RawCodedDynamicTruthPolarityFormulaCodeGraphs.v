(**
  Ordinary output-first projections of the paired local-row code iteration.

  The mutually recursive construction naturally produces both coordinates
  at once:

      sigmaCode :: piCode :: level :: tail.

  Diagnostic consumers of one local polarity should not need to expose the
  other coordinate.  This file therefore defines two ordinary output-first
  graphs, each read under

      output :: level :: tail.

  The Sigma projection existentially hides the Pi coordinate.  Since a new
  existential witness enters at de Bruijn slot zero, its body sees

      piCode :: sigmaCode :: level :: tail;

  the explicit swap below restores the paired graph's Sigma-first order.
  The Pi projection existentially hides Sigma, so its body already has the
  paired order and needs no renaming.

  Both projections retain exact arbitrary-model semantics.  Their totality
  results simply project the adequate paired orbit: no coordinate is decoded,
  recomputed, or replaced by a fallback value.

  As in the paired module, the exported names predate the distinction made
  explicit here.  These graphs select codes of local table-row predicates,
  not codes of the globally closed ten-witness Sigma/Pi certificates.  They
  are therefore unsuitable as the truth-predicate inputs of the five final
  certificate fields; those fields must use projections of the separately
  wrapped global orbit.
*)

From Stdlib Require Import Arith Lia.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA.
From BoundedPAConsistency Require Import
  RawCodedFixedLevelTruthTotality
  RawCodedCarrierIndexedPairedAdequateCodeOrbitGraph
  RawCodedDynamicTruthPairedBaseFormulaCodeGraph
  RawCodedDynamicTruthPairedSuccessorRowGraph
  RawCodedDynamicTruthPairedFormulaCodeOrbitGraph.

Module PABoundedRawCodedDynamicTruthPolarityFormulaCodeGraphs.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PABoundedRawCodedFixedLevelTruthTotality.
Import PABoundedRawCodedCarrierIndexedPairedAdequateCodeOrbitGraph.
Import PABoundedRawCodedDynamicTruthPairedBaseFormulaCodeGraph.
Import PABoundedRawCodedDynamicTruthPairedSuccessorRowGraph.
Import PABoundedRawCodedDynamicTruthPairedFormulaCodeOrbitGraph.

(** ------------------------------------------------------------------
    Sigma projection. *)

(** Under the hidden Pi witness the environment is
    [piCode :: sigmaCode :: level :: tail].  The paired graph must instead
    read [sigmaCode :: piCode :: level :: tail]. *)
Definition dynamicTruthSigmaFormulaCodeProjectionRenaming
    (index : nat) : nat :=
  match index with
  | 0 => 1
  | 1 => 0
  | S (S tailIndex) => S (S tailIndex)
  end.

Lemma raw_sat_dynamicTruthSigmaFormulaCodeProjectionRenamed_iff : forall
    (M : RawPAModel) tail level sigmaCode piCode,
  raw_formula_sat M
    (scons M piCode (scons M sigmaCode (scons M level tail)))
    (Formula.rename dynamicTruthSigmaFormulaCodeProjectionRenaming
      dynamicTruthPairedFormulaCodeOrbitGraph) <->
  raw_formula_sat M
    (scons M sigmaCode (scons M piCode (scons M level tail)))
    dynamicTruthPairedFormulaCodeOrbitGraph.
Proof.
  intros M tail level sigmaCode piCode.
  rewrite raw_formula_sat_rename.
  apply raw_formula_sat_ext. intro index.
  destruct index as [|[|tailIndex]];
    cbn [dynamicTruthSigmaFormulaCodeProjectionRenaming].
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Definition dynamicTruthSigmaFormulaCodeGraph : formula :=
  pEx
    (Formula.rename dynamicTruthSigmaFormulaCodeProjectionRenaming
      dynamicTruthPairedFormulaCodeOrbitGraph).

Definition RawDynamicTruthSigmaFormulaCodeAt (M : RawPAModel)
    (tail : nat -> M) (level sigmaCode : M) : Prop :=
  exists piCode : M,
    RawDynamicTruthPairedFormulaCodeOrbitAt M
      tail level sigmaCode piCode.

Arguments RawDynamicTruthSigmaFormulaCodeAt
  M tail level sigmaCode : clear implicits.

(** Exact, law-free output-first semantics of the Sigma projection. *)
Theorem raw_sat_dynamicTruthSigmaFormulaCodeGraph_iff : forall
    (M : RawPAModel) tail level sigmaCode,
  raw_formula_sat M
    (scons M sigmaCode (scons M level tail))
    dynamicTruthSigmaFormulaCodeGraph <->
  RawDynamicTruthSigmaFormulaCodeAt M tail level sigmaCode.
Proof.
  intros M tail level sigmaCode.
  unfold dynamicTruthSigmaFormulaCodeGraph,
    RawDynamicTruthSigmaFormulaCodeAt.
  cbn [raw_formula_sat].
  setoid_rewrite
    raw_sat_dynamicTruthSigmaFormulaCodeProjectionRenamed_iff.
  setoid_rewrite raw_sat_dynamicTruthPairedFormulaCodeOrbitGraph_iff.
  reflexivity.
Qed.

(** ------------------------------------------------------------------
    Pi projection. *)

(** The hidden Sigma witness enters at slot zero, giving exactly
    [sigmaCode :: piCode :: level :: tail]. *)
Definition dynamicTruthPiFormulaCodeGraph : formula :=
  pEx dynamicTruthPairedFormulaCodeOrbitGraph.

Definition RawDynamicTruthPiFormulaCodeAt (M : RawPAModel)
    (tail : nat -> M) (level piCode : M) : Prop :=
  exists sigmaCode : M,
    RawDynamicTruthPairedFormulaCodeOrbitAt M
      tail level sigmaCode piCode.

Arguments RawDynamicTruthPiFormulaCodeAt
  M tail level piCode : clear implicits.

(** Exact, law-free output-first semantics of the Pi projection. *)
Theorem raw_sat_dynamicTruthPiFormulaCodeGraph_iff : forall
    (M : RawPAModel) tail level piCode,
  raw_formula_sat M
    (scons M piCode (scons M level tail))
    dynamicTruthPiFormulaCodeGraph <->
  RawDynamicTruthPiFormulaCodeAt M tail level piCode.
Proof.
  intros M tail level piCode.
  unfold dynamicTruthPiFormulaCodeGraph,
    RawDynamicTruthPiFormulaCodeAt.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_dynamicTruthPairedFormulaCodeOrbitGraph_iff.
  reflexivity.
Qed.

(** ------------------------------------------------------------------
    Zero views.  These expose the genuine paired *local* base graph while
    retaining only the requested public coordinate. *)

Theorem raw_dynamicTruthSigmaFormulaCodeAt_zero_iff : forall
    (M : RawPAModel), RawPASatisfies M -> forall tail sigmaCode,
  RawDynamicTruthSigmaFormulaCodeAt M tail (raw_zero M) sigmaCode <->
  exists piCode : M,
    raw_formula_sat M
      (scons M sigmaCode (scons M piCode tail))
      dynamicTruthPairedBaseFormulaCodeGraph.
Proof.
  intros M hPA tail sigmaCode.
  unfold RawDynamicTruthSigmaFormulaCodeAt.
  split.
  - intros [piCode horbit].
    exists piCode.
    exact (proj1
      (raw_dynamicTruthPairedFormulaCodeOrbitAt_zero_iff M hPA
        tail sigmaCode piCode) horbit).
  - intros [piCode hbase].
    exists piCode.
    exact (proj2
      (raw_dynamicTruthPairedFormulaCodeOrbitAt_zero_iff M hPA
        tail sigmaCode piCode) hbase).
Qed.

Theorem raw_dynamicTruthPiFormulaCodeAt_zero_iff : forall
    (M : RawPAModel), RawPASatisfies M -> forall tail piCode,
  RawDynamicTruthPiFormulaCodeAt M tail (raw_zero M) piCode <->
  exists sigmaCode : M,
    raw_formula_sat M
      (scons M sigmaCode (scons M piCode tail))
      dynamicTruthPairedBaseFormulaCodeGraph.
Proof.
  intros M hPA tail piCode.
  unfold RawDynamicTruthPiFormulaCodeAt.
  split.
  - intros [sigmaCode horbit].
    exists sigmaCode.
    exact (proj1
      (raw_dynamicTruthPairedFormulaCodeOrbitAt_zero_iff M hPA
        tail sigmaCode piCode) horbit).
  - intros [sigmaCode hbase].
    exists sigmaCode.
    exact (proj2
      (raw_dynamicTruthPairedFormulaCodeOrbitAt_zero_iff M hPA
        tail sigmaCode piCode) hbase).
Qed.

(** ------------------------------------------------------------------
    Successor views.  The hidden next coordinate and both preceding
    coordinates are made existential, while the cross-polarized paired row
    relation remains completely visible. *)

Theorem raw_dynamicTruthSigmaFormulaCodeAt_succ_iff : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      tail level nextSigmaCode,
  RawDynamicTruthSigmaFormulaCodeAt M
    tail (raw_succ M level) nextSigmaCode <->
  exists previousSigmaCode previousPiCode nextPiCode : M,
    RawDynamicTruthPairedFormulaCodeOrbitAt M
      tail level previousSigmaCode previousPiCode /\
    RawDynamicTruthPairedSuccessorRowAt M
      previousSigmaCode previousPiCode level
      nextSigmaCode nextPiCode.
Proof.
  intros M hPA tail level nextSigmaCode.
  unfold RawDynamicTruthSigmaFormulaCodeAt.
  split.
  - intros [nextPiCode hnext].
    apply (proj1
      (raw_dynamicTruthPairedFormulaCodeOrbitAt_succ_iff M hPA
        tail level nextSigmaCode nextPiCode)) in hnext.
    destruct hnext as
      (previousSigmaCode & previousPiCode & hprevious & hrow).
    exists previousSigmaCode, previousPiCode, nextPiCode.
    split; assumption.
  - intros
      (previousSigmaCode & previousPiCode & nextPiCode & hprevious & hrow).
    exists nextPiCode.
    apply (proj2
      (raw_dynamicTruthPairedFormulaCodeOrbitAt_succ_iff M hPA
        tail level nextSigmaCode nextPiCode)).
    exists previousSigmaCode, previousPiCode. split; assumption.
Qed.

Theorem raw_dynamicTruthPiFormulaCodeAt_succ_iff : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      tail level nextPiCode,
  RawDynamicTruthPiFormulaCodeAt M
    tail (raw_succ M level) nextPiCode <->
  exists previousSigmaCode previousPiCode nextSigmaCode : M,
    RawDynamicTruthPairedFormulaCodeOrbitAt M
      tail level previousSigmaCode previousPiCode /\
    RawDynamicTruthPairedSuccessorRowAt M
      previousSigmaCode previousPiCode level
      nextSigmaCode nextPiCode.
Proof.
  intros M hPA tail level nextPiCode.
  unfold RawDynamicTruthPiFormulaCodeAt.
  split.
  - intros [nextSigmaCode hnext].
    apply (proj1
      (raw_dynamicTruthPairedFormulaCodeOrbitAt_succ_iff M hPA
        tail level nextSigmaCode nextPiCode)) in hnext.
    destruct hnext as
      (previousSigmaCode & previousPiCode & hprevious & hrow).
    exists previousSigmaCode, previousPiCode, nextSigmaCode.
    split; assumption.
  - intros
      (previousSigmaCode & previousPiCode & nextSigmaCode & hprevious & hrow).
    exists nextSigmaCode.
    apply (proj2
      (raw_dynamicTruthPairedFormulaCodeOrbitAt_succ_iff M hPA
        tail level nextSigmaCode nextPiCode)).
    exists previousSigmaCode, previousPiCode. split; assumption.
Qed.

(** Formula-level zero views in the ordinary output-first conventions. *)
Theorem raw_sat_dynamicTruthSigmaFormulaCodeGraph_zero_iff : forall
    (M : RawPAModel), RawPASatisfies M -> forall tail sigmaCode,
  raw_formula_sat M
    (scons M sigmaCode (scons M (raw_zero M) tail))
    dynamicTruthSigmaFormulaCodeGraph <->
  exists piCode : M,
    raw_formula_sat M
      (scons M sigmaCode (scons M piCode tail))
      dynamicTruthPairedBaseFormulaCodeGraph.
Proof.
  intros M hPA tail sigmaCode.
  rewrite raw_sat_dynamicTruthSigmaFormulaCodeGraph_iff.
  exact (raw_dynamicTruthSigmaFormulaCodeAt_zero_iff M hPA
    tail sigmaCode).
Qed.

Theorem raw_sat_dynamicTruthPiFormulaCodeGraph_zero_iff : forall
    (M : RawPAModel), RawPASatisfies M -> forall tail piCode,
  raw_formula_sat M
    (scons M piCode (scons M (raw_zero M) tail))
    dynamicTruthPiFormulaCodeGraph <->
  exists sigmaCode : M,
    raw_formula_sat M
      (scons M sigmaCode (scons M piCode tail))
      dynamicTruthPairedBaseFormulaCodeGraph.
Proof.
  intros M hPA tail piCode.
  rewrite raw_sat_dynamicTruthPiFormulaCodeGraph_iff.
  exact (raw_dynamicTruthPiFormulaCodeAt_zero_iff M hPA tail piCode).
Qed.

(** ------------------------------------------------------------------
    Adequacy-preserving totality.

    Both the existence proof and the adequacy proof are literal projections
    of [dynamicTruthPairedFormulaCodeOrbitGraph_adequate_total].  The only
    operation premise is therefore exactly the paired successor-adequacy
    interface accepted by that theorem. *)

Theorem dynamicTruthSigmaFormulaCodeGraph_adequate_total : forall
    (M : RawPAModel), RawPASatisfies M ->
  RawCarrierIndexedPairedAdequateCodeOrbitSuccessorTotal M
    dynamicTruthPairedSuccessorRowGraph ->
  forall (tail : nat -> M) level,
  exists sigmaCode : M,
    raw_formula_sat M
      (scons M sigmaCode (scons M level tail))
      dynamicTruthSigmaFormulaCodeGraph /\
    RawCodedFormulaAtomicallyAdequate M sigmaCode.
Proof.
  intros M hPA hsuccessor tail level.
  destruct (dynamicTruthPairedFormulaCodeOrbitGraph_adequate_total
    M hPA hsuccessor tail level)
    as (sigmaCode & piCode & horbit & hsigmaAdequate & _).
  exists sigmaCode. split; [|exact hsigmaAdequate].
  apply (proj2
    (raw_sat_dynamicTruthSigmaFormulaCodeGraph_iff M
      tail level sigmaCode)).
  exists piCode.
  exact (proj1
    (raw_sat_dynamicTruthPairedFormulaCodeOrbitGraph_iff M
      tail level sigmaCode piCode) horbit).
Qed.

Theorem dynamicTruthPiFormulaCodeGraph_adequate_total : forall
    (M : RawPAModel), RawPASatisfies M ->
  RawCarrierIndexedPairedAdequateCodeOrbitSuccessorTotal M
    dynamicTruthPairedSuccessorRowGraph ->
  forall (tail : nat -> M) level,
  exists piCode : M,
    raw_formula_sat M
      (scons M piCode (scons M level tail))
      dynamicTruthPiFormulaCodeGraph /\
    RawCodedFormulaAtomicallyAdequate M piCode.
Proof.
  intros M hPA hsuccessor tail level.
  destruct (dynamicTruthPairedFormulaCodeOrbitGraph_adequate_total
    M hPA hsuccessor tail level)
    as (sigmaCode & piCode & horbit & _ & hpiAdequate).
  exists piCode. split; [|exact hpiAdequate].
  apply (proj2
    (raw_sat_dynamicTruthPiFormulaCodeGraph_iff M
      tail level piCode)).
  exists sigmaCode.
  exact (proj1
    (raw_sat_dynamicTruthPairedFormulaCodeOrbitGraph_iff M
      tail level sigmaCode piCode) horbit).
Qed.

(** The concrete paired successor now discharges the conditional interface,
    so local-row diagnostics may select either polarity without supplying an
    additional operation callback.  Global certificate fields still require
    the wrapper described in the module header. *)
Corollary dynamicTruthSigmaFormulaCodeGraph_raw_adequate_total : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      (tail : nat -> M) level,
  exists sigmaCode : M,
    raw_formula_sat M
      (scons M sigmaCode (scons M level tail))
      dynamicTruthSigmaFormulaCodeGraph /\
    RawCodedFormulaAtomicallyAdequate M sigmaCode.
Proof.
  intros M hPA tail level.
  destruct (dynamicTruthPairedFormulaCodeOrbitGraph_raw_adequate_total
    M hPA tail level)
    as (sigmaCode & piCode & horbit & hsigmaAdequate & _).
  exists sigmaCode. split; [|exact hsigmaAdequate].
  apply (proj2
    (raw_sat_dynamicTruthSigmaFormulaCodeGraph_iff M
      tail level sigmaCode)).
  exists piCode.
  exact (proj1
    (raw_sat_dynamicTruthPairedFormulaCodeOrbitGraph_iff M
      tail level sigmaCode piCode) horbit).
Qed.

Corollary dynamicTruthPiFormulaCodeGraph_raw_adequate_total : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      (tail : nat -> M) level,
  exists piCode : M,
    raw_formula_sat M
      (scons M piCode (scons M level tail))
      dynamicTruthPiFormulaCodeGraph /\
    RawCodedFormulaAtomicallyAdequate M piCode.
Proof.
  intros M hPA tail level.
  destruct (dynamicTruthPairedFormulaCodeOrbitGraph_raw_adequate_total
    M hPA tail level)
    as (sigmaCode & piCode & horbit & _ & hpiAdequate).
  exists piCode. split; [|exact hpiAdequate].
  apply (proj2
    (raw_sat_dynamicTruthPiFormulaCodeGraph_iff M
      tail level piCode)).
  exists sigmaCode.
  exact (proj1
    (raw_sat_dynamicTruthPairedFormulaCodeOrbitGraph_iff M
      tail level sigmaCode piCode) horbit).
Qed.

End PABoundedRawCodedDynamicTruthPolarityFormulaCodeGraphs.
