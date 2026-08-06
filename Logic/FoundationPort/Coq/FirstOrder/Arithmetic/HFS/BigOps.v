(** Executable finite-family operations in the standard HFS model.

    Foundation defines big union, big intersection, Cartesian product,
    domain, and range directly on HFS codes inside arbitrary nonstandard
    arithmetic models.  The standard-model membership content is independent
    of that bounded-comprehension layer once a finite family is presented by
    a list.  This module exposes those exact finite-list laws and reuses the
    faithful arithmetic-pair projections from [Seq].
*)

From Stdlib Require Import Lists.List NArith.NArith.
From Foundation.FirstOrder.Arithmetic.HFS Require Import Basic Coding Seq.

Import ListNotations.

Set Implicit Arguments.
Unset Strict Implicit.

(** * Big union and intersection *)

Definition hfs_list_big_union (families : list hfs_code) : hfs_code :=
  fold_right hfs_union hfs_empty families.

Lemma hfs_mem_list_big_union_iff : forall families x,
  hfs_mem x (hfs_list_big_union families) <->
  exists s, In s families /\ hfs_mem x s.
Proof.
  induction families as [|s families IH]; intros x; simpl.
  - rewrite hfs_mem_empty_iff. split; [contradiction|].
    intros [s [Hs _]]. contradiction.
  - rewrite hfs_mem_union_iff, IH. simpl. split.
    + intros [Hs | [u [Hu Hmu]]].
      * exists s. split; [left; reflexivity|exact Hs].
      * exists u. split; [right; exact Hu|exact Hmu].
    + intros [u [[-> | Hu] Hmu]].
      * left. exact Hmu.
      * right. exists u. split; assumption.
Qed.

(** A nonempty finite intersection is represented by its head and tail. *)
Definition hfs_list_big_inter (head : hfs_code)
    (tail : list hfs_code) : hfs_code :=
  fold_right hfs_inter head tail.

Lemma hfs_mem_list_big_inter_iff : forall head tail x,
  hfs_mem x (hfs_list_big_inter head tail) <->
  hfs_mem x head /\ forall s, In s tail -> hfs_mem x s.
Proof.
  induction tail as [|s tail IH]; intros x; simpl.
  - tauto.
  - rewrite hfs_mem_inter_iff, IH. simpl. split.
    + intros [Hs [Hhead Htail]]. split; [exact Hhead|].
      intros u [-> | Hu]; [exact Hs | exact (Htail u Hu)].
    + intros [Hhead Hall]. split.
      * apply Hall. left. reflexivity.
      * split; [exact Hhead|].
        intros u Hu. apply Hall. right. exact Hu.
Qed.

(** * Cartesian products *)

Definition hfs_list_product (left right : list hfs_code) : hfs_code :=
  hfs_arithmetize_list
    (flat_map (fun x => map (fun y => hfs_index_pair x y) right) left).

Lemma hfs_mem_list_product_iff : forall left right p,
  hfs_mem p (hfs_list_product left right) <->
  exists x, In x left /\ exists y, In y right /\
    p = hfs_index_pair x y.
Proof.
  intros left right p. unfold hfs_list_product.
  rewrite hfs_mem_arithmetize_list_iff.
  split.
  - intro Hp. apply in_flat_map in Hp.
    destruct Hp as [x [Hx Hpx]].
    apply in_map_iff in Hpx. destruct Hpx as [y [Hpy Hy]].
    exists x. split; [exact Hx|]. exists y. split; [exact Hy|].
    symmetry. exact Hpy.
  - intros [x [Hx [y [Hy Hp]]]]. apply in_flat_map.
    exists x. split; [exact Hx|].
    apply in_map_iff. exists y. split; [symmetry; exact Hp|exact Hy].
Qed.

(** * Domains and ranges of finite relations *)

Definition hfs_list_domain (relation : list hfs_code) : hfs_code :=
  hfs_arithmetize_list (map hfs_index_fst relation).

Definition hfs_list_range (relation : list hfs_code) : hfs_code :=
  hfs_arithmetize_list (map hfs_index_snd relation).

Lemma hfs_mem_list_domain_iff : forall relation x,
  hfs_mem x (hfs_list_domain relation) <->
  exists y, In (hfs_index_pair x y) relation.
Proof.
  intros relation x. unfold hfs_list_domain.
  rewrite hfs_mem_arithmetize_list_iff. split.
  - intro H. apply in_map_iff in H.
    destruct H as [p [Hfst Hp]].
    exists (hfs_index_snd p).
    rewrite <- Hfst, hfs_index_pair_projections. exact Hp.
  - intros [y Hp]. apply in_map_iff.
    exists (hfs_index_pair x y). split.
    + now rewrite hfs_index_fst_pair.
    + exact Hp.
Qed.

Lemma hfs_mem_list_range_iff : forall relation y,
  hfs_mem y (hfs_list_range relation) <->
  exists x, In (hfs_index_pair x y) relation.
Proof.
  intros relation y. unfold hfs_list_range.
  rewrite hfs_mem_arithmetize_list_iff. split.
  - intro H. apply in_map_iff in H.
    destruct H as [p [Hsnd Hp]].
    exists (hfs_index_fst p).
    rewrite <- Hsnd, hfs_index_pair_projections. exact Hp.
  - intros [x Hp]. apply in_map_iff.
    exists (hfs_index_pair x y). split.
    + now rewrite hfs_index_snd_pair.
    + exact Hp.
Qed.

Print Assumptions hfs_mem_list_big_union_iff.
Print Assumptions hfs_mem_list_big_inter_iff.
Print Assumptions hfs_mem_list_product_iff.
Print Assumptions hfs_mem_list_domain_iff.
Print Assumptions hfs_mem_list_range_iff.
