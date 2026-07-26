(**
  Existential composition of output-first formula graphs.

  The source graph is read under

      intermediate :: level :: tail,

  while the transforming graph is read under

      output :: intermediate :: level :: tail.

  Their composition hides [intermediate] and exposes the ordinary
  output-first interface

      output :: level :: tail.

  The witness introduced by the existential binder actually gives the body
  the environment

      intermediate :: output :: level :: tail.

  Consequently both component graphs require an explicit de Bruijn map.
  The semantic theorem below uses no arithmetic laws; it is just the exact
  interpretation of the binder, conjunction, and the two renamings.
*)

From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import HierarchyReduction.

Module PABoundedRawCodedOutputFirstFormulaGraphComposition.

Import PA.
Import PAHierarchyReduction.

(** The environment visible inside the single existential binder. *)
Definition outputFirstFormulaGraphCompositionEnvironment
    (M : RawPAModel) (intermediate output level : M)
    (tail : nat -> M) : nat -> M :=
  scons M intermediate (scons M output (scons M level tail)).

(** The source graph expects [intermediate :: level :: tail].  Slot zero is
    already correct; the public output at body slot one must be skipped. *)
Definition outputFirstFormulaGraphCompositionSourceRenaming
    (index : nat) : nat :=
  match index with
  | 0 => 0
  | 1 => 2
  | S (S tailIndex) => S (S (S tailIndex))
  end.

(** The transforming graph expects [output :: intermediate :: level ::
    tail].  Its first two slots are swapped in the existential body, while
    the level and tail slots are already in their final positions. *)
Definition outputFirstFormulaGraphCompositionTransformRenaming
    (index : nat) : nat :=
  match index with
  | 0 => 1
  | 1 => 0
  | S (S remainingIndex) => S (S remainingIndex)
  end.

Lemma raw_sat_outputFirstFormulaGraphCompositionSourceRenamed_iff : forall
    (M : RawPAModel) sourceGraph intermediate output level tail,
  raw_formula_sat M
    (outputFirstFormulaGraphCompositionEnvironment M
      intermediate output level tail)
    (Formula.rename
      outputFirstFormulaGraphCompositionSourceRenaming sourceGraph) <->
  raw_formula_sat M
    (scons M intermediate (scons M level tail)) sourceGraph.
Proof.
  intros M sourceGraph intermediate output level tail.
  rewrite raw_formula_sat_rename.
  apply raw_formula_sat_ext. intro index.
  destruct index as [|[|tailIndex]];
    cbn [outputFirstFormulaGraphCompositionEnvironment
      outputFirstFormulaGraphCompositionSourceRenaming scons];
    reflexivity.
Qed.

Lemma raw_sat_outputFirstFormulaGraphCompositionTransformRenamed_iff :
  forall (M : RawPAModel) transformGraph intermediate output level tail,
  raw_formula_sat M
    (outputFirstFormulaGraphCompositionEnvironment M
      intermediate output level tail)
    (Formula.rename
      outputFirstFormulaGraphCompositionTransformRenaming transformGraph) <->
  raw_formula_sat M
    (scons M output
      (scons M intermediate (scons M level tail))) transformGraph.
Proof.
  intros M transformGraph intermediate output level tail.
  rewrite raw_formula_sat_rename.
  apply raw_formula_sat_ext. intro index.
  destruct index as [|[|remainingIndex]];
    cbn [outputFirstFormulaGraphCompositionEnvironment
      outputFirstFormulaGraphCompositionTransformRenaming scons];
    reflexivity.
Qed.

(** The explicit existential composition combinator. *)
Definition outputFirstFormulaGraphComposition
    (sourceGraph transformGraph : formula) : formula :=
  pEx
    (pAnd
      (Formula.rename
        outputFirstFormulaGraphCompositionSourceRenaming sourceGraph)
      (Formula.rename
        outputFirstFormulaGraphCompositionTransformRenaming transformGraph)).

Definition RawOutputFirstFormulaGraphCompositionAt
    (M : RawPAModel) (sourceGraph transformGraph : formula)
    (tail : nat -> M) (level output : M) : Prop :=
  exists intermediate : M,
    raw_formula_sat M
      (scons M intermediate (scons M level tail)) sourceGraph /\
    raw_formula_sat M
      (scons M output
        (scons M intermediate (scons M level tail))) transformGraph.

Arguments RawOutputFirstFormulaGraphCompositionAt
  M sourceGraph transformGraph tail level output : clear implicits.

(** Exact semantics in every raw arithmetic structure. *)
Theorem raw_sat_outputFirstFormulaGraphComposition_iff : forall
    (M : RawPAModel) sourceGraph transformGraph tail level output,
  raw_formula_sat M
    (scons M output (scons M level tail))
    (outputFirstFormulaGraphComposition sourceGraph transformGraph) <->
  RawOutputFirstFormulaGraphCompositionAt M
    sourceGraph transformGraph tail level output.
Proof.
  intros M sourceGraph transformGraph tail level output.
  unfold outputFirstFormulaGraphComposition,
    RawOutputFirstFormulaGraphCompositionAt.
  cbn [raw_formula_sat].
  setoid_rewrite
    raw_sat_outputFirstFormulaGraphCompositionSourceRenamed_iff.
  setoid_rewrite
    raw_sat_outputFirstFormulaGraphCompositionTransformRenamed_iff.
  reflexivity.
Qed.

(** A graph is total together with an invariant of its selected output.  The
    invariant may depend on the untouched tail and on the level; this makes
    the interface usable for indexed carriers without baking any particular
    adequacy notion into the generic combinator. *)
Definition RawOutputFirstFormulaGraphTotalWithInvariant
    (M : RawPAModel) (graph : formula)
    (invariant : (nat -> M) -> M -> M -> Prop) : Prop :=
  forall (tail : nat -> M) level,
    exists output : M,
      raw_formula_sat M
        (scons M output (scons M level tail)) graph /\
      invariant tail level output.

Arguments RawOutputFirstFormulaGraphTotalWithInvariant
  M graph invariant : clear implicits.

(** Dependent totality of a transform.  The source satisfaction proof is
    deliberately supplied as well as its invariant: a later transform may
    depend on either fact, while simple transforms can ignore the former. *)
Definition RawOutputFirstFormulaTransformTotalFromInvariant
    (M : RawPAModel) (sourceGraph transformGraph : formula)
    (sourceInvariant targetInvariant :
      (nat -> M) -> M -> M -> Prop) : Prop :=
  forall (tail : nat -> M) level intermediate,
    raw_formula_sat M
      (scons M intermediate (scons M level tail)) sourceGraph ->
    sourceInvariant tail level intermediate ->
    exists output : M,
      raw_formula_sat M
        (scons M output
          (scons M intermediate (scons M level tail))) transformGraph /\
      targetInvariant tail level output.

Arguments RawOutputFirstFormulaTransformTotalFromInvariant
  M sourceGraph transformGraph sourceInvariant targetInvariant
  : clear implicits.

(** Invariant-preserving dependent totality of existential composition. *)
Theorem outputFirstFormulaGraphComposition_raw_dependent_total : forall
    (M : RawPAModel) sourceGraph transformGraph
      sourceInvariant targetInvariant,
  RawOutputFirstFormulaGraphTotalWithInvariant M
    sourceGraph sourceInvariant ->
  RawOutputFirstFormulaTransformTotalFromInvariant M
    sourceGraph transformGraph sourceInvariant targetInvariant ->
  RawOutputFirstFormulaGraphTotalWithInvariant M
    (outputFirstFormulaGraphComposition sourceGraph transformGraph)
    targetInvariant.
Proof.
  intros M sourceGraph transformGraph sourceInvariant targetInvariant
    hsource htransform tail level.
  destruct (hsource tail level) as
    (intermediate & hsourceGraph & hintermediateInvariant).
  destruct (htransform tail level intermediate hsourceGraph
    hintermediateInvariant) as
    (output & htransformGraph & houtputInvariant).
  exists output. split; [|exact houtputInvariant].
  apply (proj2
    (raw_sat_outputFirstFormulaGraphComposition_iff M
      sourceGraph transformGraph tail level output)).
  exists intermediate. split; assumption.
Qed.

(** The invariant-free form is a convenient corollary.  It too is entirely
    law-free: totality of the composite is just sequential choice of the two
    component witnesses. *)
Corollary outputFirstFormulaGraphComposition_raw_total : forall
    (M : RawPAModel) sourceGraph transformGraph,
  (forall (tail : nat -> M) level,
    exists intermediate : M,
      raw_formula_sat M
        (scons M intermediate (scons M level tail)) sourceGraph) ->
  (forall (tail : nat -> M) level intermediate,
    raw_formula_sat M
      (scons M intermediate (scons M level tail)) sourceGraph ->
    exists output : M,
      raw_formula_sat M
        (scons M output
          (scons M intermediate (scons M level tail))) transformGraph) ->
  forall (tail : nat -> M) level,
    exists output : M,
      raw_formula_sat M
        (scons M output (scons M level tail))
        (outputFirstFormulaGraphComposition sourceGraph transformGraph).
Proof.
  intros M sourceGraph transformGraph hsource htransform tail level.
  destruct (hsource tail level) as (intermediate & hsourceGraph).
  destruct (htransform tail level intermediate hsourceGraph) as
    (output & htransformGraph).
  exists output.
  apply (proj2
    (raw_sat_outputFirstFormulaGraphComposition_iff M
      sourceGraph transformGraph tail level output)).
  exists intermediate. split; assumption.
Qed.

End PABoundedRawCodedOutputFirstFormulaGraphComposition.
