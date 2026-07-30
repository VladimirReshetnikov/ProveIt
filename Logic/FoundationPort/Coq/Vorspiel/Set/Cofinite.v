(** Cofinite predicate sets through finite list covers. *)

From Stdlib Require Import Lists.List.
From Foundation.Vorspiel.Set Require Import Basic.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

Definition set_complement {A} (s : pred_set A) : pred_set A :=
  fun x => ~ s x.

Definition set_union {A} (s t : pred_set A) : pred_set A :=
  fun x => s x \/ t x.

(** A cover, rather than an exact duplicate-free enumeration, is the weakest
    finite-set representation needed by every theorem in this module. *)
Definition set_finitely_covered {A} (s : pred_set A) : Prop :=
  exists xs : list A, forall x, s x -> List.In x xs.

Definition set_infinite {A} (s : pred_set A) : Prop :=
  ~ set_finitely_covered s.

Definition set_cofinite {A} (s : pred_set A) : Prop :=
  set_finitely_covered (set_complement s).

Definition set_coinfinite {A} (s : pred_set A) : Prop :=
  set_infinite (set_complement s).

Lemma set_finitely_covered_subset : forall A (s t : pred_set A),
  set_subset s t -> set_finitely_covered t -> set_finitely_covered s.
Proof.
  intros A s t Hst [xs Hxs]. exists xs. intros x Hx.
  now apply Hxs, Hst.
Qed.

Lemma set_cofinite_complement_iff : forall A (s : pred_set A),
  set_cofinite s <-> set_finitely_covered (set_complement s).
Proof. reflexivity. Qed.

Lemma set_coinfinite_complement_iff : forall A (s : pred_set A),
  set_coinfinite s <-> set_infinite (set_complement s).
Proof. reflexivity. Qed.

Lemma set_coinfinite_iff_not_cofinite : forall A (s : pred_set A),
  set_coinfinite s <-> ~ set_cofinite s.
Proof. reflexivity. Qed.

Theorem set_cofinite_iff_not_coinfinite : forall A (s : pred_set A),
  (forall P : Prop, ~ ~ P -> P) ->
  (set_cofinite s <-> ~ set_coinfinite s).
Proof.
  intros A s Hdne. unfold set_coinfinite, set_infinite. split.
  - intros Hco Hnot. now apply Hnot.
  - apply Hdne.
Qed.

Theorem set_cofinite_subset : forall A (s t : pred_set A),
  set_subset s t -> set_cofinite s -> set_cofinite t.
Proof.
  intros A s t Hst Hco.
  eapply set_finitely_covered_subset; [|exact Hco].
  intros x Hnot_t Hs. now apply Hnot_t, Hst.
Qed.

Theorem set_coinfinite_subset : forall A (s t : pred_set A),
  set_subset t s -> set_coinfinite s -> set_coinfinite t.
Proof.
  intros A s t Hts Hinf Hco_t. apply Hinf.
  now apply (set_cofinite_subset Hts).
Qed.

Lemma set_full_cofinite : forall A,
  set_cofinite (fun _ : A => True).
Proof.
  intro A. exists nil. intros x Hnot. exfalso. now apply Hnot.
Qed.

Lemma set_cofinite_union_left : forall A (s t : pred_set A),
  set_cofinite s -> set_cofinite (set_union s t).
Proof.
  intros A s t Hs. eapply set_finitely_covered_subset; [|exact Hs].
  intros x Hnot_union Hs_member. apply Hnot_union. now left.
Qed.

Lemma set_cofinite_union_right : forall A (s t : pred_set A),
  set_cofinite t -> set_cofinite (set_union s t).
Proof.
  intros A s t Ht. eapply set_finitely_covered_subset; [|exact Ht].
  intros x Hnot_union Ht_member. apply Hnot_union. now right.
Qed.
