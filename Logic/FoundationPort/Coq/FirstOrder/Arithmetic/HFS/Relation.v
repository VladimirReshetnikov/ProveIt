(** Executable finite-relation operations in the standard HFS model.

    The source HFS layer defines mappings, restriction, image, and
    Sigma-one replacement on raw hereditary-finite-set codes.  After a
    relation is presented by a finite list of arithmetic pairs, their
    membership content is elementary: filtering gives restriction, a
    mapping is a relation with unique fibers, and a mapped list gives an
    image with a unique extensional code.  This module records those
    generalized standard-model laws.
*)

From Stdlib Require Import Bool.Bool Lists.List NArith.NArith.
From Foundation.FirstOrder.Arithmetic.HFS Require Import Basic Coding Seq BigOps.

Import ListNotations.

Set Implicit Arguments.
Unset Strict Implicit.

(** * Images and replacement *)

Definition hfs_list_image (f : hfs_code -> hfs_code)
    (xs : list hfs_code) : hfs_code :=
  hfs_arithmetize_list (map f xs).

Lemma hfs_mem_list_image_iff : forall (f : hfs_code -> hfs_code)
    (xs : list hfs_code) (y : hfs_code),
  hfs_mem y (hfs_list_image f xs) <->
  exists x, In x xs /\ y = f x.
Proof.
  intros f xs y. unfold hfs_list_image.
  rewrite hfs_mem_arithmetize_list_iff. split.
  - intro H. apply in_map_iff in H.
    destruct H as [x [Hfx Hx]].
    exists x. split; [exact Hx|symmetry; exact Hfx].
  - intros [x [Hx ->]]. apply in_map_iff.
    exists x. split; [reflexivity|exact Hx].
Qed.

Theorem hfs_list_image_existsUnique : forall (f : hfs_code -> hfs_code)
    (xs : list hfs_code),
  exists! t, forall y,
    hfs_mem y t <->
    exists x, In x xs /\ y = f x.
Proof.
  intros f xs. exists (hfs_list_image f xs). split.
  - intro y. apply hfs_mem_list_image_iff.
  - intros t Ht. apply hfs_extensionality. intro y.
    rewrite Ht, hfs_mem_list_image_iff. reflexivity.
Qed.

(** * Restriction *)

Definition hfs_list_restrict (relation domain : list hfs_code)
    : list hfs_code :=
  filter (fun p =>
    if in_dec N.eq_dec (hfs_index_fst p) domain then true else false)
    relation.

Lemma hfs_list_restrict_In_iff : forall relation domain p,
  In p (hfs_list_restrict relation domain) <->
  In p relation /\ In (hfs_index_fst p) domain.
Proof.
  intros relation domain p. unfold hfs_list_restrict.
  rewrite filter_In. destruct (in_dec N.eq_dec (hfs_index_fst p) domain)
    as [Hin | Hnin].
  - simpl. split.
    + intros [Hp _]. split; [exact Hp|exact Hin].
    + intros [Hp _]. split; [exact Hp|exact eq_refl].
  - simpl. split.
    + intros [_ H]. discriminate.
    + intros [_ H]. exfalso. apply Hnin. exact H.
Qed.

Definition hfs_list_restrict_code (relation domain : list hfs_code) : hfs_code :=
  hfs_arithmetize_list (hfs_list_restrict relation domain).

Lemma hfs_mem_list_restrict_code_iff : forall relation domain p,
  hfs_mem p (hfs_list_restrict_code relation domain) <->
  hfs_mem p (hfs_arithmetize_list relation) /\
  hfs_mem (hfs_index_fst p) (hfs_arithmetize_list domain).
Proof.
  intros relation domain p. unfold hfs_list_restrict_code.
  rewrite !hfs_mem_arithmetize_list_iff.
  apply hfs_list_restrict_In_iff.
Qed.

Lemma hfs_list_restrict_subset : forall relation domain p,
  In p (hfs_list_restrict relation domain) -> In p relation.
Proof.
  intros relation domain p H. now apply hfs_list_restrict_In_iff in H.
Qed.

(** * Mappings *)

Definition hfs_list_is_mapping (relation : list hfs_code) : Prop :=
  forall x y z,
    In (hfs_index_pair x y) relation ->
    In (hfs_index_pair x z) relation ->
    y = z.

Lemma hfs_list_is_mapping_restrict : forall relation domain,
  hfs_list_is_mapping relation ->
  hfs_list_is_mapping (hfs_list_restrict relation domain).
Proof.
  intros relation domain Hmap x y z Hy Hz.
  unfold hfs_list_is_mapping in Hmap.
  apply (@Hmap x y z); [apply hfs_list_restrict_subset in Hy|apply hfs_list_restrict_subset in Hz];
    assumption.
Qed.

Definition hfs_list_domains_disjoint
    (left right : list hfs_code) : Prop :=
  forall x,
    ~ ((exists y, In (hfs_index_pair x y) left) /\
       (exists z, In (hfs_index_pair x z) right)).

Lemma hfs_list_is_mapping_app : forall left right,
  hfs_list_is_mapping left ->
  hfs_list_is_mapping right ->
  hfs_list_domains_disjoint left right ->
  hfs_list_is_mapping (left ++ right).
Proof.
  intros left right Hleft Hright Hdisjoint x y z Hy Hz.
  apply in_app_iff in Hy, Hz.
  destruct Hy as [Hy | Hy], Hz as [Hz | Hz].
  - exact (Hleft x y z Hy Hz).
  - exfalso. apply (Hdisjoint x). split.
    + exists y. exact Hy.
    + exists z. exact Hz.
  - exfalso. apply (Hdisjoint x). split.
    + exists z. exact Hz.
    + exists y. exact Hy.
  - exact (Hright x y z Hy Hz).
Qed.

Lemma hfs_list_is_mapping_empty : hfs_list_is_mapping [].
Proof. intros x y z H; inversion H. Qed.

(** A finite relation with unique fibers is a mapping in the source sense:
    every element of its computed domain has a witness, and that witness is
    unique. *)
Lemma hfs_list_mapping_fiber_existsUnique : forall relation x,
  hfs_list_is_mapping relation ->
  hfs_mem x (hfs_list_domain relation) ->
  exists! y, In (hfs_index_pair x y) relation.
Proof.
  intros relation x Hmap Hx. unfold hfs_list_is_mapping in Hmap.
  apply hfs_mem_list_domain_iff in Hx.
  destruct Hx as [y Hy].
  exists y. split; [exact Hy|].
  intros z Hz. eapply (@Hmap x y z); eassumption.
Qed.

Print Assumptions hfs_mem_list_image_iff.
Print Assumptions hfs_list_image_existsUnique.
Print Assumptions hfs_list_restrict_In_iff.
Print Assumptions hfs_mem_list_restrict_code_iff.
Print Assumptions hfs_list_is_mapping_restrict.
Print Assumptions hfs_list_is_mapping_app.
Print Assumptions hfs_list_mapping_fiber_existsUnique.
