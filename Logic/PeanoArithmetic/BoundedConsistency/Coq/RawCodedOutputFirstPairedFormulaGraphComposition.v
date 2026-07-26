(**
  Existential composition from a paired formula-code graph.

  The source graph is read under

      first :: second :: level :: tail,

  while the transforming graph is read under

      output :: first :: second :: level :: tail.

  The composite hides both source outputs and exposes the usual

      output :: level :: tail

  convention used by the six-field master.  This is the correct generic
  bridge for the paired global Sigma/Pi truth orbit: composing its two unary
  projections separately would not ensure that the hidden opposite
  polarities came from the same orbit witness.

  Besides exact graph semantics, the final theorem carries a genuine
  [RawCodedPAProofOf] invariant.  Thus an eventual local-law transform must
  compile an ordinary PA proof targeted at precisely the output code it
  constructs; semantic validity alone cannot discharge the interface.
*)

From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import HierarchyReduction.
From BoundedPAConsistency Require Import RawCodedPAProvability.

Module PABoundedRawCodedOutputFirstPairedFormulaGraphComposition.

Import PA.
Import PAHierarchyReduction.
Import PABoundedRawCodedPAProvability.

(** Two existential binders give the body the environment

      second :: first :: output :: level :: tail.
*)
Definition outputFirstPairedFormulaGraphCompositionEnvironment
    (M : RawPAModel) (second first output level : M)
    (tail : nat -> M) : nat -> M :=
  scons M second
    (scons M first (scons M output (scons M level tail))).

(** Restore the paired source's [first, second, level, tail] order. *)
Definition outputFirstPairedFormulaGraphCompositionSourceRenaming
    (index : nat) : nat :=
  match index with
  | 0 => 1
  | 1 => 0
  | 2 => 3
  | S (S (S tailIndex)) => 4 + tailIndex
  end.

(** Restore the transform's [output, first, second, level, tail] order. *)
Definition outputFirstPairedFormulaGraphCompositionTransformRenaming
    (index : nat) : nat :=
  match index with
  | 0 => 2
  | 1 => 1
  | 2 => 0
  | S (S (S remainingIndex)) => S (S (S remainingIndex))
  end.

Lemma raw_sat_outputFirstPairedFormulaGraphCompositionSourceRenamed_iff :
    forall (M : RawPAModel) sourceGraph second first output level tail,
  raw_formula_sat M
    (outputFirstPairedFormulaGraphCompositionEnvironment M
      second first output level tail)
    (Formula.rename
      outputFirstPairedFormulaGraphCompositionSourceRenaming sourceGraph) <->
  raw_formula_sat M
    (scons M first (scons M second (scons M level tail))) sourceGraph.
Proof.
  intros M sourceGraph second first output level tail.
  rewrite raw_formula_sat_rename.
  apply raw_formula_sat_ext. intro index.
  destruct index as [|[|[|tailIndex]]];
    cbn [outputFirstPairedFormulaGraphCompositionEnvironment
      outputFirstPairedFormulaGraphCompositionSourceRenaming scons];
    reflexivity.
Qed.

Lemma raw_sat_outputFirstPairedFormulaGraphCompositionTransformRenamed_iff :
    forall (M : RawPAModel) transformGraph second first output level tail,
  raw_formula_sat M
    (outputFirstPairedFormulaGraphCompositionEnvironment M
      second first output level tail)
    (Formula.rename
      outputFirstPairedFormulaGraphCompositionTransformRenaming
      transformGraph) <->
  raw_formula_sat M
    (scons M output
      (scons M first (scons M second (scons M level tail))))
    transformGraph.
Proof.
  intros M transformGraph second first output level tail.
  rewrite raw_formula_sat_rename.
  apply raw_formula_sat_ext. intro index.
  destruct index as [|[|[|remainingIndex]]];
    cbn [outputFirstPairedFormulaGraphCompositionEnvironment
      outputFirstPairedFormulaGraphCompositionTransformRenaming scons];
    reflexivity.
Qed.

Definition outputFirstPairedFormulaGraphComposition
    (sourceGraph transformGraph : formula) : formula :=
  pEx (pEx
    (pAnd
      (Formula.rename
        outputFirstPairedFormulaGraphCompositionSourceRenaming sourceGraph)
      (Formula.rename
        outputFirstPairedFormulaGraphCompositionTransformRenaming
        transformGraph))).

Definition RawOutputFirstPairedFormulaGraphCompositionAt
    (M : RawPAModel) (sourceGraph transformGraph : formula)
    (tail : nat -> M) (level output : M) : Prop :=
  exists first second : M,
    raw_formula_sat M
      (scons M first (scons M second (scons M level tail))) sourceGraph /\
    raw_formula_sat M
      (scons M output
        (scons M first (scons M second (scons M level tail))))
      transformGraph.

Arguments RawOutputFirstPairedFormulaGraphCompositionAt
  M sourceGraph transformGraph tail level output : clear implicits.

Theorem raw_sat_outputFirstPairedFormulaGraphComposition_iff : forall
    (M : RawPAModel) sourceGraph transformGraph tail level output,
  raw_formula_sat M
    (scons M output (scons M level tail))
    (outputFirstPairedFormulaGraphComposition sourceGraph transformGraph) <->
  RawOutputFirstPairedFormulaGraphCompositionAt M
    sourceGraph transformGraph tail level output.
Proof.
  intros M sourceGraph transformGraph tail level output.
  unfold outputFirstPairedFormulaGraphComposition,
    RawOutputFirstPairedFormulaGraphCompositionAt.
  cbn [raw_formula_sat].
  setoid_rewrite
    raw_sat_outputFirstPairedFormulaGraphCompositionSourceRenamed_iff.
  setoid_rewrite
    raw_sat_outputFirstPairedFormulaGraphCompositionTransformRenamed_iff.
  reflexivity.
Qed.

(** Totality of a paired source graph. *)
Definition RawOutputFirstPairedFormulaSourceTotal
    (M : RawPAModel) (sourceGraph : formula) : Prop :=
  forall (tail : nat -> M) level,
    exists first second : M,
      raw_formula_sat M
        (scons M first (scons M second (scons M level tail))) sourceGraph.

Arguments RawOutputFirstPairedFormulaSourceTotal M sourceGraph
  : clear implicits.

(** The deliberately proof-producing transform obligation.  Its certificate
    target is the same [output] accepted by [transformGraph]. *)
Definition RawOutputFirstPairedFormulaTransformProofTotal
    (M : RawPAModel) (sourceGraph transformGraph : formula) : Prop :=
  forall (tail : nat -> M) level first second,
    raw_formula_sat M
      (scons M first (scons M second (scons M level tail))) sourceGraph ->
    exists output certificate : M,
      raw_formula_sat M
        (scons M output
          (scons M first (scons M second (scons M level tail))))
        transformGraph /\
      RawCodedPAProofOf M output certificate.

Arguments RawOutputFirstPairedFormulaTransformProofTotal
  M sourceGraph transformGraph : clear implicits.

(** Composition preserves the exact ordinary proof target. *)
Theorem outputFirstPairedFormulaGraphComposition_raw_proof_total : forall
    (M : RawPAModel) sourceGraph transformGraph,
  RawOutputFirstPairedFormulaSourceTotal M sourceGraph ->
  RawOutputFirstPairedFormulaTransformProofTotal M
    sourceGraph transformGraph ->
  forall (tail : nat -> M) level,
    exists output certificate : M,
      raw_formula_sat M
        (scons M output (scons M level tail))
        (outputFirstPairedFormulaGraphComposition
          sourceGraph transformGraph) /\
      RawCodedPAProofOf M output certificate.
Proof.
  intros M sourceGraph transformGraph hsource htransform tail level.
  destruct (hsource tail level) as
    (first & second & hsourceGraph).
  destruct (htransform tail level first second hsourceGraph) as
    (output & certificate & htransformGraph & hcertificate).
  exists output, certificate. split; [|exact hcertificate].
  apply (proj2
    (raw_sat_outputFirstPairedFormulaGraphComposition_iff M
      sourceGraph transformGraph tail level output)).
  exists first, second. split; assumption.
Qed.

End PABoundedRawCodedOutputFirstPairedFormulaGraphComposition.
