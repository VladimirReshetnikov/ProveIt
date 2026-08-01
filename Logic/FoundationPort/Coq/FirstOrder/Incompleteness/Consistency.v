(** Abstract consistency sentences and semantic readback.

    Foundation defines these formulas through a bootstrapped Π1 proof
    predicate.  Once the resulting provability endomorphism is exposed, the
    semantic theorems use only classical explosion and the truth laws for
    negation and that endomorphism. *)

From FoundationModal Require Import Syntax LogicInfrastructure.
From Foundation.FirstOrder.Incompleteness Require Import
  ProvabilityAbstraction.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

Lemma pa_logic_consistent_iff_unprovable_bottom : forall (A : Type)
    (L : modal_logic_set A),
  classical_logic L ->
  (logic_consistent L <-> ~ L Bottom).
Proof.
  intros A L Hclass. split.
  - now apply logic_no_bot.
  - intros Hnot_bottom Hinc.
    exact (Hnot_bottom (Hinc Bottom)).
Qed.

(** Consistency with [p] is unprovability of its negation; this is exactly
    the source predicate after quotation/substitution is erased. *)
Definition pa_consistent_with {A L0 L}
    (B : pa_provability L0 L) (p : formula A) : formula A :=
  pa_dia B p.

Lemma pa_consistent_with_unfold : forall (A : Type)
    (L0 L : modal_logic_set A) (B : pa_provability L0 L) p,
  pa_consistent_with B p = Neg (pa_box B (Neg p)).
Proof. reflexivity. Qed.

Lemma pa_consistent_with_truth_iff : forall (A : Type)
    (L0 L : modal_logic_set A) (B : pa_provability L0 L)
    (truth : modal_logic_set A),
  (forall p, truth (Neg p) <-> ~ truth p) ->
  (forall p, truth (pa_box B p) <-> L p) ->
  forall p,
  truth (pa_consistent_with B p) <-> ~ L (Neg p).
Proof.
  intros A L0 L B truth Hneg Hbox p.
  unfold pa_consistent_with, pa_dia.
  rewrite Hneg, Hbox. reflexivity.
Qed.

(** Foundation's [standard_consistent], generalized from arithmetic truth in
    naturals to any truth predicate satisfying the two exact readback laws. *)
Theorem pa_con_truth_iff_logic_consistent : forall (A : Type)
    (L0 L : modal_logic_set A) (Hclass : classical_logic L)
    (B : pa_provability L0 L) (truth : modal_logic_set A),
  (forall p, truth (Neg p) <-> ~ truth p) ->
  (forall p, truth (pa_box B p) <-> L p) ->
  truth (pa_con B) <-> logic_consistent L.
Proof.
  intros A L0 L Hclass B truth Hneg Hbox.
  unfold pa_con. rewrite Hneg, Hbox.
  symmetry. exact (pa_logic_consistent_iff_unprovable_bottom Hclass).
Qed.
