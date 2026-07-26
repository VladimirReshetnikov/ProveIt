(**
  Ordinary output-first projections of the paired *global* truth-code orbit.

  The mutually recursive construction produces the Sigma-truth and
  Pi-falsity predicate codes together, under the public environment

      globalSigmaCode :: globalPiCode :: level :: tail.

  Most certificate fields consume just one polarity under

      output :: level :: tail.

  This file hides the unused coordinate existentially.  For Sigma, the
  hidden Pi witness is inserted at de Bruijn slot zero, so the body sees

      globalPiCode :: globalSigmaCode :: level :: tail;

  the explicit transposition below restores the paired graph's Sigma-first
  convention.  For Pi, hiding Sigma already gives the required paired order.

  Unlike the older local-row projections, both outputs here are codes of
  globally closed ten-witness traversal predicates.  Thus these are the
  polarity graphs intended for the final certificate fields.  Their
  arbitrary-model totality is inherited literally from the paired global
  orbit and consequently covers nonstandard carrier levels.
*)

From Stdlib Require Import Arith Lia.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA.
From BoundedPAConsistency Require Import
  RawCodedFixedLevelTruthTotality
  RawCodedCarrierIndexedPairedAdequateCodeOrbitGraph
  RawCodedDynamicTruthPairedGlobalSuccessorGraph
  RawCodedDynamicTruthPairedGlobalFormulaCodeOrbitGraph.

Module PABoundedRawCodedDynamicTruthGlobalPolarityFormulaCodeGraphs.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PABoundedRawCodedFixedLevelTruthTotality.
Import PABoundedRawCodedCarrierIndexedPairedAdequateCodeOrbitGraph.
Import PABoundedRawCodedDynamicTruthPairedGlobalSuccessorGraph.
Import PABoundedRawCodedDynamicTruthPairedGlobalFormulaCodeOrbitGraph.

(** ------------------------------------------------------------------
    Sigma projection. *)

(** Under the hidden global-Pi witness, swap slots zero and one while
    preserving [level] and every parameter in [tail]. *)
Definition dynamicTruthGlobalSigmaFormulaCodeProjectionRenaming
    (index : nat) : nat :=
  match index with
  | 0 => 1
  | 1 => 0
  | S (S tailIndex) => S (S tailIndex)
  end.

Lemma raw_sat_dynamicTruthGlobalSigmaFormulaCodeProjectionRenamed_iff :
  forall (M : RawPAModel) tail level globalSigmaCode globalPiCode,
  raw_formula_sat M
    (scons M globalPiCode
      (scons M globalSigmaCode (scons M level tail)))
    (Formula.rename
      dynamicTruthGlobalSigmaFormulaCodeProjectionRenaming
      dynamicTruthPairedGlobalFormulaCodeOrbitGraph) <->
  raw_formula_sat M
    (scons M globalSigmaCode
      (scons M globalPiCode (scons M level tail)))
    dynamicTruthPairedGlobalFormulaCodeOrbitGraph.
Proof.
  intros M tail level globalSigmaCode globalPiCode.
  rewrite raw_formula_sat_rename.
  apply raw_formula_sat_ext. intro index.
  destruct index as [|[|tailIndex]];
    cbn [dynamicTruthGlobalSigmaFormulaCodeProjectionRenaming].
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Definition dynamicTruthGlobalSigmaFormulaCodeGraph : formula :=
  pEx
    (Formula.rename
      dynamicTruthGlobalSigmaFormulaCodeProjectionRenaming
      dynamicTruthPairedGlobalFormulaCodeOrbitGraph).

Definition RawDynamicTruthGlobalSigmaFormulaCodeAt (M : RawPAModel)
    (tail : nat -> M) (level globalSigmaCode : M) : Prop :=
  exists globalPiCode : M,
    RawDynamicTruthPairedGlobalFormulaCodeOrbitAt M
      tail level globalSigmaCode globalPiCode.

Arguments RawDynamicTruthGlobalSigmaFormulaCodeAt
  M tail level globalSigmaCode : clear implicits.

(** Exact, law-free output-first semantics of the global Sigma projection. *)
Theorem raw_sat_dynamicTruthGlobalSigmaFormulaCodeGraph_iff : forall
    (M : RawPAModel) tail level globalSigmaCode,
  raw_formula_sat M
    (scons M globalSigmaCode (scons M level tail))
    dynamicTruthGlobalSigmaFormulaCodeGraph <->
  RawDynamicTruthGlobalSigmaFormulaCodeAt M
    tail level globalSigmaCode.
Proof.
  intros M tail level globalSigmaCode.
  unfold dynamicTruthGlobalSigmaFormulaCodeGraph,
    RawDynamicTruthGlobalSigmaFormulaCodeAt.
  cbn [raw_formula_sat].
  setoid_rewrite
    raw_sat_dynamicTruthGlobalSigmaFormulaCodeProjectionRenamed_iff.
  setoid_rewrite
    raw_sat_dynamicTruthPairedGlobalFormulaCodeOrbitGraph_iff.
  reflexivity.
Qed.

(** ------------------------------------------------------------------
    Pi projection. *)

(** The hidden global-Sigma witness enters at slot zero, yielding exactly
    [globalSigmaCode :: globalPiCode :: level :: tail]. *)
Definition dynamicTruthGlobalPiFormulaCodeGraph : formula :=
  pEx dynamicTruthPairedGlobalFormulaCodeOrbitGraph.

Definition RawDynamicTruthGlobalPiFormulaCodeAt (M : RawPAModel)
    (tail : nat -> M) (level globalPiCode : M) : Prop :=
  exists globalSigmaCode : M,
    RawDynamicTruthPairedGlobalFormulaCodeOrbitAt M
      tail level globalSigmaCode globalPiCode.

Arguments RawDynamicTruthGlobalPiFormulaCodeAt
  M tail level globalPiCode : clear implicits.

(** Exact, law-free output-first semantics of the global Pi projection. *)
Theorem raw_sat_dynamicTruthGlobalPiFormulaCodeGraph_iff : forall
    (M : RawPAModel) tail level globalPiCode,
  raw_formula_sat M
    (scons M globalPiCode (scons M level tail))
    dynamicTruthGlobalPiFormulaCodeGraph <->
  RawDynamicTruthGlobalPiFormulaCodeAt M tail level globalPiCode.
Proof.
  intros M tail level globalPiCode.
  unfold dynamicTruthGlobalPiFormulaCodeGraph,
    RawDynamicTruthGlobalPiFormulaCodeAt.
  cbn [raw_formula_sat].
  setoid_rewrite
    raw_sat_dynamicTruthPairedGlobalFormulaCodeOrbitGraph_iff.
  reflexivity.
Qed.

(** ------------------------------------------------------------------
    Zero views.

    The hidden coordinate remains existential, while the visible pair is
    pinned to the genuine globally wrapped rank-zero base graph. *)

Theorem raw_dynamicTruthGlobalSigmaFormulaCodeAt_zero_iff : forall
    (M : RawPAModel), RawPASatisfies M -> forall tail globalSigmaCode,
  RawDynamicTruthGlobalSigmaFormulaCodeAt M
    tail (raw_zero M) globalSigmaCode <->
  exists globalPiCode : M,
    raw_formula_sat M
      (scons M globalSigmaCode (scons M globalPiCode tail))
      dynamicTruthPairedGlobalBaseGraph.
Proof.
  intros M hPA tail globalSigmaCode.
  unfold RawDynamicTruthGlobalSigmaFormulaCodeAt.
  split.
  - intros [globalPiCode horbit].
    exists globalPiCode.
    exact (proj1
      (raw_dynamicTruthPairedGlobalFormulaCodeOrbitAt_zero_iff M hPA
        tail globalSigmaCode globalPiCode) horbit).
  - intros [globalPiCode hbase].
    exists globalPiCode.
    exact (proj2
      (raw_dynamicTruthPairedGlobalFormulaCodeOrbitAt_zero_iff M hPA
        tail globalSigmaCode globalPiCode) hbase).
Qed.

Theorem raw_dynamicTruthGlobalPiFormulaCodeAt_zero_iff : forall
    (M : RawPAModel), RawPASatisfies M -> forall tail globalPiCode,
  RawDynamicTruthGlobalPiFormulaCodeAt M
    tail (raw_zero M) globalPiCode <->
  exists globalSigmaCode : M,
    raw_formula_sat M
      (scons M globalSigmaCode (scons M globalPiCode tail))
      dynamicTruthPairedGlobalBaseGraph.
Proof.
  intros M hPA tail globalPiCode.
  unfold RawDynamicTruthGlobalPiFormulaCodeAt.
  split.
  - intros [globalSigmaCode horbit].
    exists globalSigmaCode.
    exact (proj1
      (raw_dynamicTruthPairedGlobalFormulaCodeOrbitAt_zero_iff M hPA
        tail globalSigmaCode globalPiCode) horbit).
  - intros [globalSigmaCode hbase].
    exists globalSigmaCode.
    exact (proj2
      (raw_dynamicTruthPairedGlobalFormulaCodeOrbitAt_zero_iff M hPA
        tail globalSigmaCode globalPiCode) hbase).
Qed.

(** Formula-level zero views in the ordinary output-first conventions. *)
Theorem raw_sat_dynamicTruthGlobalSigmaFormulaCodeGraph_zero_iff : forall
    (M : RawPAModel), RawPASatisfies M -> forall tail globalSigmaCode,
  raw_formula_sat M
    (scons M globalSigmaCode (scons M (raw_zero M) tail))
    dynamicTruthGlobalSigmaFormulaCodeGraph <->
  exists globalPiCode : M,
    raw_formula_sat M
      (scons M globalSigmaCode (scons M globalPiCode tail))
      dynamicTruthPairedGlobalBaseGraph.
Proof.
  intros M hPA tail globalSigmaCode.
  rewrite raw_sat_dynamicTruthGlobalSigmaFormulaCodeGraph_iff.
  exact (raw_dynamicTruthGlobalSigmaFormulaCodeAt_zero_iff M hPA
    tail globalSigmaCode).
Qed.

Theorem raw_sat_dynamicTruthGlobalPiFormulaCodeGraph_zero_iff : forall
    (M : RawPAModel), RawPASatisfies M -> forall tail globalPiCode,
  raw_formula_sat M
    (scons M globalPiCode (scons M (raw_zero M) tail))
    dynamicTruthGlobalPiFormulaCodeGraph <->
  exists globalSigmaCode : M,
    raw_formula_sat M
      (scons M globalSigmaCode (scons M globalPiCode tail))
      dynamicTruthPairedGlobalBaseGraph.
Proof.
  intros M hPA tail globalPiCode.
  rewrite raw_sat_dynamicTruthGlobalPiFormulaCodeGraph_iff.
  exact (raw_dynamicTruthGlobalPiFormulaCodeAt_zero_iff M hPA
    tail globalPiCode).
Qed.

(** ------------------------------------------------------------------
    Successor views.

    The unused next coordinate and both preceding global codes are exposed
    existentially.  The step is the checked global successor relation: it
    first builds the two local rows and then wraps both in closed traversals. *)

Theorem raw_dynamicTruthGlobalSigmaFormulaCodeAt_succ_iff : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      tail level nextGlobalSigmaCode,
  RawDynamicTruthGlobalSigmaFormulaCodeAt M
    tail (raw_succ M level) nextGlobalSigmaCode <->
  exists previousGlobalSigmaCode previousGlobalPiCode
      nextGlobalPiCode : M,
    RawDynamicTruthPairedGlobalFormulaCodeOrbitAt M
      tail level previousGlobalSigmaCode previousGlobalPiCode /\
    RawDynamicTruthPairedGlobalSuccessorAt M
      previousGlobalSigmaCode previousGlobalPiCode level
      nextGlobalSigmaCode nextGlobalPiCode.
Proof.
  intros M hPA tail level nextGlobalSigmaCode.
  unfold RawDynamicTruthGlobalSigmaFormulaCodeAt.
  split.
  - intros [nextGlobalPiCode hnext].
    apply (proj1
      (raw_dynamicTruthPairedGlobalFormulaCodeOrbitAt_succ_iff M hPA
        tail level nextGlobalSigmaCode nextGlobalPiCode)) in hnext.
    destruct hnext as
      (previousGlobalSigmaCode & previousGlobalPiCode &
       hprevious & hsuccessor).
    exists previousGlobalSigmaCode, previousGlobalPiCode,
      nextGlobalPiCode.
    split; assumption.
  - intros
      (previousGlobalSigmaCode & previousGlobalPiCode &
       nextGlobalPiCode & hprevious & hsuccessor).
    exists nextGlobalPiCode.
    apply (proj2
      (raw_dynamicTruthPairedGlobalFormulaCodeOrbitAt_succ_iff M hPA
        tail level nextGlobalSigmaCode nextGlobalPiCode)).
    exists previousGlobalSigmaCode, previousGlobalPiCode.
    split; assumption.
Qed.

Theorem raw_dynamicTruthGlobalPiFormulaCodeAt_succ_iff : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      tail level nextGlobalPiCode,
  RawDynamicTruthGlobalPiFormulaCodeAt M
    tail (raw_succ M level) nextGlobalPiCode <->
  exists previousGlobalSigmaCode previousGlobalPiCode
      nextGlobalSigmaCode : M,
    RawDynamicTruthPairedGlobalFormulaCodeOrbitAt M
      tail level previousGlobalSigmaCode previousGlobalPiCode /\
    RawDynamicTruthPairedGlobalSuccessorAt M
      previousGlobalSigmaCode previousGlobalPiCode level
      nextGlobalSigmaCode nextGlobalPiCode.
Proof.
  intros M hPA tail level nextGlobalPiCode.
  unfold RawDynamicTruthGlobalPiFormulaCodeAt.
  split.
  - intros [nextGlobalSigmaCode hnext].
    apply (proj1
      (raw_dynamicTruthPairedGlobalFormulaCodeOrbitAt_succ_iff M hPA
        tail level nextGlobalSigmaCode nextGlobalPiCode)) in hnext.
    destruct hnext as
      (previousGlobalSigmaCode & previousGlobalPiCode &
       hprevious & hsuccessor).
    exists previousGlobalSigmaCode, previousGlobalPiCode,
      nextGlobalSigmaCode.
    split; assumption.
  - intros
      (previousGlobalSigmaCode & previousGlobalPiCode &
       nextGlobalSigmaCode & hprevious & hsuccessor).
    exists nextGlobalSigmaCode.
    apply (proj2
      (raw_dynamicTruthPairedGlobalFormulaCodeOrbitAt_succ_iff M hPA
        tail level nextGlobalSigmaCode nextGlobalPiCode)).
    exists previousGlobalSigmaCode, previousGlobalPiCode.
    split; assumption.
Qed.

(** Formula-level successor views in the ordinary output-first
    conventions. *)
Theorem raw_sat_dynamicTruthGlobalSigmaFormulaCodeGraph_succ_iff : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      tail level nextGlobalSigmaCode,
  raw_formula_sat M
    (scons M nextGlobalSigmaCode
      (scons M (raw_succ M level) tail))
    dynamicTruthGlobalSigmaFormulaCodeGraph <->
  exists previousGlobalSigmaCode previousGlobalPiCode
      nextGlobalPiCode : M,
    RawDynamicTruthPairedGlobalFormulaCodeOrbitAt M
      tail level previousGlobalSigmaCode previousGlobalPiCode /\
    RawDynamicTruthPairedGlobalSuccessorAt M
      previousGlobalSigmaCode previousGlobalPiCode level
      nextGlobalSigmaCode nextGlobalPiCode.
Proof.
  intros M hPA tail level nextGlobalSigmaCode.
  rewrite raw_sat_dynamicTruthGlobalSigmaFormulaCodeGraph_iff.
  exact (raw_dynamicTruthGlobalSigmaFormulaCodeAt_succ_iff M hPA
    tail level nextGlobalSigmaCode).
Qed.

Theorem raw_sat_dynamicTruthGlobalPiFormulaCodeGraph_succ_iff : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      tail level nextGlobalPiCode,
  raw_formula_sat M
    (scons M nextGlobalPiCode
      (scons M (raw_succ M level) tail))
    dynamicTruthGlobalPiFormulaCodeGraph <->
  exists previousGlobalSigmaCode previousGlobalPiCode
      nextGlobalSigmaCode : M,
    RawDynamicTruthPairedGlobalFormulaCodeOrbitAt M
      tail level previousGlobalSigmaCode previousGlobalPiCode /\
    RawDynamicTruthPairedGlobalSuccessorAt M
      previousGlobalSigmaCode previousGlobalPiCode level
      nextGlobalSigmaCode nextGlobalPiCode.
Proof.
  intros M hPA tail level nextGlobalPiCode.
  rewrite raw_sat_dynamicTruthGlobalPiFormulaCodeGraph_iff.
  exact (raw_dynamicTruthGlobalPiFormulaCodeAt_succ_iff M hPA
    tail level nextGlobalPiCode).
Qed.

(** ------------------------------------------------------------------
    Adequacy-preserving totality.

    These theorems are coordinate projections only.  No global code is
    decoded, recomputed, or repaired by a fallback branch. *)

Theorem dynamicTruthGlobalSigmaFormulaCodeGraph_adequate_total : forall
    (M : RawPAModel), RawPASatisfies M ->
  RawCarrierIndexedPairedAdequateCodeOrbitSuccessorTotal M
    dynamicTruthPairedGlobalSuccessorGraph ->
  forall (tail : nat -> M) level,
  exists globalSigmaCode : M,
    raw_formula_sat M
      (scons M globalSigmaCode (scons M level tail))
      dynamicTruthGlobalSigmaFormulaCodeGraph /\
    RawCodedFormulaAtomicallyAdequate M globalSigmaCode.
Proof.
  intros M hPA hsuccessor tail level.
  destruct (raw_carrierIndexedPairedAdequateCodeOrbitGraph_total
    M hPA
    dynamicTruthPairedGlobalBaseGraph
    dynamicTruthPairedGlobalSuccessorGraph
    (dynamicTruthPairedGlobalBaseGraph_raw_adequate_total M hPA)
    hsuccessor tail level) as
    (globalSigmaCode & globalPiCode & horbit & hSigmaAdequate & _).
  exists globalSigmaCode. split; [|exact hSigmaAdequate].
  apply (proj2
    (raw_sat_dynamicTruthGlobalSigmaFormulaCodeGraph_iff M
      tail level globalSigmaCode)).
  exists globalPiCode.
  exact (proj1
    (raw_sat_dynamicTruthPairedGlobalFormulaCodeOrbitGraph_iff M
      tail level globalSigmaCode globalPiCode) horbit).
Qed.

Theorem dynamicTruthGlobalPiFormulaCodeGraph_adequate_total : forall
    (M : RawPAModel), RawPASatisfies M ->
  RawCarrierIndexedPairedAdequateCodeOrbitSuccessorTotal M
    dynamicTruthPairedGlobalSuccessorGraph ->
  forall (tail : nat -> M) level,
  exists globalPiCode : M,
    raw_formula_sat M
      (scons M globalPiCode (scons M level tail))
      dynamicTruthGlobalPiFormulaCodeGraph /\
    RawCodedFormulaAtomicallyAdequate M globalPiCode.
Proof.
  intros M hPA hsuccessor tail level.
  destruct (raw_carrierIndexedPairedAdequateCodeOrbitGraph_total
    M hPA
    dynamicTruthPairedGlobalBaseGraph
    dynamicTruthPairedGlobalSuccessorGraph
    (dynamicTruthPairedGlobalBaseGraph_raw_adequate_total M hPA)
    hsuccessor tail level) as
    (globalSigmaCode & globalPiCode & horbit & _ & hPiAdequate).
  exists globalPiCode. split; [|exact hPiAdequate].
  apply (proj2
    (raw_sat_dynamicTruthGlobalPiFormulaCodeGraph_iff M
      tail level globalPiCode)).
  exists globalSigmaCode.
  exact (proj1
    (raw_sat_dynamicTruthPairedGlobalFormulaCodeOrbitGraph_iff M
      tail level globalSigmaCode globalPiCode) horbit).
Qed.

(** The concrete global successor discharges the only operation premise. *)
Corollary dynamicTruthGlobalSigmaFormulaCodeGraph_raw_adequate_total :
  forall (M : RawPAModel), RawPASatisfies M -> forall
      (tail : nat -> M) level,
  exists globalSigmaCode : M,
    raw_formula_sat M
      (scons M globalSigmaCode (scons M level tail))
      dynamicTruthGlobalSigmaFormulaCodeGraph /\
    RawCodedFormulaAtomicallyAdequate M globalSigmaCode.
Proof.
  intros M hPA tail level.
  destruct
    (dynamicTruthPairedGlobalFormulaCodeOrbitGraph_raw_adequate_total
      M hPA tail level) as
    (globalSigmaCode & globalPiCode & horbit & hSigmaAdequate & _).
  exists globalSigmaCode. split; [|exact hSigmaAdequate].
  apply (proj2
    (raw_sat_dynamicTruthGlobalSigmaFormulaCodeGraph_iff M
      tail level globalSigmaCode)).
  exists globalPiCode.
  exact (proj1
    (raw_sat_dynamicTruthPairedGlobalFormulaCodeOrbitGraph_iff M
      tail level globalSigmaCode globalPiCode) horbit).
Qed.

Corollary dynamicTruthGlobalPiFormulaCodeGraph_raw_adequate_total :
  forall (M : RawPAModel), RawPASatisfies M -> forall
      (tail : nat -> M) level,
  exists globalPiCode : M,
    raw_formula_sat M
      (scons M globalPiCode (scons M level tail))
      dynamicTruthGlobalPiFormulaCodeGraph /\
    RawCodedFormulaAtomicallyAdequate M globalPiCode.
Proof.
  intros M hPA tail level.
  destruct
    (dynamicTruthPairedGlobalFormulaCodeOrbitGraph_raw_adequate_total
      M hPA tail level) as
    (globalSigmaCode & globalPiCode & horbit & _ & hPiAdequate).
  exists globalPiCode. split; [|exact hPiAdequate].
  apply (proj2
    (raw_sat_dynamicTruthGlobalPiFormulaCodeGraph_iff M
      tail level globalPiCode)).
  exists globalSigmaCode.
  exact (proj1
    (raw_sat_dynamicTruthPairedGlobalFormulaCodeOrbitGraph_iff M
      tail level globalSigmaCode globalPiCode) horbit).
Qed.

End PABoundedRawCodedDynamicTruthGlobalPolarityFormulaCodeGraphs.
