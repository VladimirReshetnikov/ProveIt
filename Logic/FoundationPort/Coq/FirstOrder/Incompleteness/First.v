(** Recursive predicates and semantic consequences of first incompleteness.

    The arithmetic layer identifies certified recursively enumerable
    predicates with Sigma-one definability.  Foundation specializes the
    remaining results to arithmetic truth in the natural numbers; their
    selection argument itself needs only that truth is bivalent and that a
    false formula has a true negation. *)

From Stdlib Require Import Vectors.Fin.
From FoundationModal Require Import Syntax LogicInfrastructure.
From Foundation.FirstOrder.Basic.Semantics Require Import Semantics.
From Foundation.FirstOrder.Arithmetic.Basic Require Import
  Hierarchy Misc Model.
From Foundation.FirstOrder.Arithmetic.Definability Require Import
  Hierarchy Definable.
From Foundation.FirstOrder.Arithmetic.R0 Require Import
  Representation CertifiedSigmaOne.
From Foundation.FirstOrder.Incompleteness Require Import
  ProvabilityAbstraction.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

(** A predicate on finite vectors is Sigma-one when a sorted arithmetic
    formula with natural parameters defines it in the standard model. *)
Definition r0_sigma_one_definable {n}
    (P : (Fin.t n -> nat) -> Prop) : Prop :=
  exists p : arithmetic_sorted_formula nat n arithmetic_sigma_one_symbol,
    arithmetic_sorted_is_defined_by_with_params
      nat_standard_structure P p.

(** Arbitrary-arity strengthening of the source theorem [re_iff_sigma1].
    The recursive-enumerability side retains an explicit arithmetic
    partial-recursion certificate. *)
Theorem r0_arithmetically_semidecidable_iff_sigma_one_definable : forall n
    (P : (Fin.t n -> nat) -> Prop),
  arithmetically_semidecidable P <-> r0_sigma_one_definable P.
Proof.
  intros n P. split.
  - intro Hsemi.
    destruct (r0_arithmetically_semidecidable_representation Hsemi)
      as [p [Hp Hspec]].
    set (sp := ArithmeticSortedSigma 1 p Hp).
    assert (Hdefined :
        arithmetic_sorted_defined nat_standard_structure P sp).
    { constructor. split.
      - exact I.
      - exact Hspec. }
    pose (Hdef := arithmetic_sorted_defined_to_definable Hdefined).
    exists (arithmetic_sorted_definable_formula Hdef).
    exact (arithmetic_sorted_definable_spec Hdef).
  - intros [p [Hp Hspec]].
    destruct (r0_sigma_one_arithmetically_semidecidable
      (fun x : nat => x) (arithmetic_sorted_sigma_prop p))
      as [f [Hf Hdom]].
    exists f. split; [exact Hf |].
    intro v.
    transitivity
      (semiformula_eval nat_standard_structure v
        (fun x : nat => x) (arithmetic_sorted_formula_val p)).
    + symmetry. exact (Hspec v).
    + exact (Hdom v).
Qed.

(** Unary source-facing specialization. *)
Definition r0_sigma_one_definable_predicate (P : nat -> Prop) : Prop :=
  r0_sigma_one_definable
    (fun v : Fin.t 1 -> nat => P (v Fin.F1)).

Definition r0_arithmetically_semidecidable_predicate
    (P : nat -> Prop) : Prop :=
  arithmetically_semidecidable
    (fun v : Fin.t 1 -> nat => P (v Fin.F1)).

Corollary r0_re_iff_sigma_one : forall P : nat -> Prop,
  r0_arithmetically_semidecidable_predicate P <->
  r0_sigma_one_definable_predicate P.
Proof.
  intro P.
  apply r0_arithmetically_semidecidable_iff_sigma_one_definable.
Qed.

(** Every independent formula has a true, still-unprovable orientation.
    Making the truth split explicit keeps this theorem constructive. *)
Theorem pa_exists_true_unprovable_of_incomplete : forall (A : Type)
    (L truth : modal_logic_set A),
  (forall p, truth p \/ ~ truth p) ->
  (forall p, ~ truth p -> truth (Neg p)) ->
  pa_incomplete L ->
  exists sigma, truth sigma /\ ~ L sigma.
Proof.
  intros A L truth Htruth_cases Hneg_complete
    [sigma [Hunprovable Hunrefutable]].
  destruct (Htruth_cases sigma) as [Htrue | Hfalse].
  - exists sigma. now split.
  - exists (Neg sigma). split.
    + now apply Hneg_complete.
    + exact Hunrefutable.
Qed.

(** If all theorems of an incomplete predicate are true, the complete truth
    predicate is strictly stronger.  This factors the source instance
    [T strictly weaker than true arithmetic] from its arithmetic adapters. *)
Theorem pa_incomplete_strictly_weaker_than_truth : forall (A : Type)
    (L truth : modal_logic_set A),
  logic_subset L truth ->
  (forall p, truth p \/ ~ truth p) ->
  (forall p, ~ truth p -> truth (Neg p)) ->
  pa_incomplete L ->
  logic_strictly_weaker L truth.
Proof.
  intros A L truth Hsound Htruth_cases Hneg_complete Hincomplete.
  destruct (pa_exists_true_unprovable_of_incomplete
    Htruth_cases Hneg_complete Hincomplete)
    as [sigma [Htrue Hunprovable]].
  split; [exact Hsound |].
  exists sigma. now split.
Qed.
