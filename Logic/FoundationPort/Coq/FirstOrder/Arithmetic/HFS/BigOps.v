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

Lemma hfs_list_big_union_empty :
  hfs_list_big_union [] = hfs_empty.
Proof. reflexivity. Qed.

Lemma hfs_list_big_union_cons : forall family families,
  hfs_list_big_union (family :: families) =
  hfs_union family (hfs_list_big_union families).
Proof. reflexivity. Qed.

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

Theorem hfs_list_big_union_existsUnique : forall families,
  exists! t, forall x,
    hfs_mem x t <->
    exists s, In s families /\ hfs_mem x s.
Proof.
  intros families. exists (hfs_list_big_union families). split.
  - intro x. apply hfs_mem_list_big_union_iff.
  - intros t Ht. apply hfs_extensionality. intro x.
    rewrite Ht, hfs_mem_list_big_union_iff. reflexivity.
Qed.

Lemma hfs_list_big_union_app : forall left right,
  hfs_list_big_union (left ++ right) =
  hfs_union (hfs_list_big_union left) (hfs_list_big_union right).
Proof.
  intros left right. apply hfs_extensionality. intro x.
  rewrite hfs_mem_list_big_union_iff, hfs_mem_union_iff,
    !hfs_mem_list_big_union_iff.
  setoid_rewrite in_app_iff.
  firstorder.
Qed.

Lemma hfs_list_big_union_subset_of_subset : forall left right,
  (forall s, In s left -> In s right) ->
  hfs_subset (hfs_list_big_union left) (hfs_list_big_union right).
Proof.
  intros left right Hsubset x Hx.
  apply hfs_mem_list_big_union_iff in Hx.
  destruct Hx as [s [Hs Hsx]].
  apply hfs_mem_list_big_union_iff.
  exists s. split; [apply Hsubset|exact Hsx]. exact Hs.
Qed.

(** A nonempty finite intersection is represented by its head and tail. *)
Definition hfs_list_big_inter (head : hfs_code)
    (tail : list hfs_code) : hfs_code :=
  fold_right hfs_inter head tail.

Lemma hfs_list_big_inter_singleton : forall head,
  hfs_list_big_inter head [] = head.
Proof. reflexivity. Qed.

Lemma hfs_list_big_inter_cons : forall head family families,
  hfs_list_big_inter head (family :: families) =
  hfs_inter family (hfs_list_big_inter head families).
Proof. reflexivity. Qed.

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

Theorem hfs_list_big_inter_existsUnique : forall head tail,
  exists! t, forall x,
    hfs_mem x t <->
    hfs_mem x head /\ forall s, In s tail -> hfs_mem x s.
Proof.
  intros head tail. exists (hfs_list_big_inter head tail). split.
  - intro x. apply hfs_mem_list_big_inter_iff.
  - intros t Ht. apply hfs_extensionality. intro x.
    rewrite Ht, hfs_mem_list_big_inter_iff. reflexivity.
Qed.

Lemma hfs_list_big_inter_subset_head : forall head tail,
  hfs_subset (hfs_list_big_inter head tail) head.
Proof.
  intros head tail x Hx.
  apply hfs_mem_list_big_inter_iff in Hx. exact (proj1 Hx).
Qed.

Lemma hfs_list_big_inter_subset_member : forall head tail family,
  In family tail ->
  hfs_subset (hfs_list_big_inter head tail) family.
Proof.
  intros head tail family Hfamily x Hx.
  apply hfs_mem_list_big_inter_iff in Hx.
  now apply (proj2 Hx family Hfamily).
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

Theorem hfs_list_product_existsUnique : forall left right,
  exists! t, forall p,
    hfs_mem p t <->
    exists x, In x left /\ exists y, In y right /\
      p = hfs_index_pair x y.
Proof.
  intros left right. exists (hfs_list_product left right). split.
  - intro p. apply hfs_mem_list_product_iff.
  - intros t Ht. apply hfs_extensionality. intro p.
    rewrite Ht, hfs_mem_list_product_iff. reflexivity.
Qed.

Lemma hfs_list_product_empty_left : forall right,
  hfs_list_product [] right = hfs_empty.
Proof. reflexivity. Qed.

Lemma hfs_list_product_empty_right : forall left,
  hfs_list_product left [] = hfs_empty.
Proof.
  intros left. apply hfs_extensionality. intro p.
  rewrite hfs_mem_list_product_iff, hfs_mem_empty_iff.
  split.
  - intros [x [Hx [y [Hy Hp]]]]. simpl in Hy. contradiction.
  - intro H. contradiction.
Qed.

Lemma hfs_list_product_app_left : forall left₁ left₂ right,
  hfs_list_product (left₁ ++ left₂) right =
  hfs_union (hfs_list_product left₁ right)
    (hfs_list_product left₂ right).
Proof.
  intros left₁ left₂ right. apply hfs_extensionality. intro p.
  rewrite hfs_mem_list_product_iff, hfs_mem_union_iff,
    !hfs_mem_list_product_iff.
  setoid_rewrite in_app_iff.
  firstorder.
Qed.

Lemma hfs_list_product_app_right : forall left right₁ right₂,
  hfs_list_product left (right₁ ++ right₂) =
  hfs_union (hfs_list_product left right₁)
    (hfs_list_product left right₂).
Proof.
  intros left right₁ right₂. apply hfs_extensionality. intro p.
  rewrite hfs_mem_list_product_iff, hfs_mem_union_iff,
    !hfs_mem_list_product_iff.
  setoid_rewrite in_app_iff.
  firstorder.
Qed.

Lemma hfs_list_product_singleton : forall x y,
  hfs_list_product [x] [y] = hfs_singleton (hfs_index_pair x y).
Proof.
  intros x y. unfold hfs_list_product, hfs_singleton.
  simpl. reflexivity.
Qed.

(** * Domains and ranges of finite relations *)

Definition hfs_list_domain (relation : list hfs_code) : hfs_code :=
  hfs_arithmetize_list (map hfs_index_fst relation).

Definition hfs_list_range (relation : list hfs_code) : hfs_code :=
  hfs_arithmetize_list (map hfs_index_snd relation).

Lemma hfs_list_domain_empty :
  hfs_list_domain [] = hfs_empty.
Proof. reflexivity. Qed.

Lemma hfs_list_range_empty :
  hfs_list_range [] = hfs_empty.
Proof. reflexivity. Qed.

Lemma hfs_list_domain_app : forall left right,
  hfs_list_domain (left ++ right) =
  hfs_union (hfs_list_domain left) (hfs_list_domain right).
Proof.
  intros left right. unfold hfs_list_domain.
  rewrite map_app, hfs_arithmetize_list_app. reflexivity.
Qed.

Lemma hfs_list_range_app : forall left right,
  hfs_list_range (left ++ right) =
  hfs_union (hfs_list_range left) (hfs_list_range right).
Proof.
  intros left right. unfold hfs_list_range.
  rewrite map_app, hfs_arithmetize_list_app. reflexivity.
Qed.

Lemma hfs_list_domain_singleton : forall x y,
  hfs_list_domain [hfs_index_pair x y] = hfs_singleton x.
Proof.
  intros x y. unfold hfs_list_domain, hfs_singleton.
  simpl. rewrite hfs_index_fst_pair. reflexivity.
Qed.

Lemma hfs_list_range_singleton : forall x y,
  hfs_list_range [hfs_index_pair x y] = hfs_singleton y.
Proof.
  intros x y. unfold hfs_list_range, hfs_singleton.
  simpl. rewrite hfs_index_snd_pair. reflexivity.
Qed.

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

Theorem hfs_list_domain_existsUnique : forall relation,
  exists! t, forall x,
    hfs_mem x t <->
    exists y, In (hfs_index_pair x y) relation.
Proof.
  intros relation. exists (hfs_list_domain relation). split.
  - intro x. apply hfs_mem_list_domain_iff.
  - intros t Ht. apply hfs_extensionality. intro x.
    rewrite Ht, hfs_mem_list_domain_iff. reflexivity.
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

Theorem hfs_list_range_existsUnique : forall relation,
  exists! t, forall y,
    hfs_mem y t <->
    exists x, In (hfs_index_pair x y) relation.
Proof.
  intros relation. exists (hfs_list_range relation). split.
  - intro y. apply hfs_mem_list_range_iff.
  - intros t Ht. apply hfs_extensionality. intro y.
    rewrite Ht, hfs_mem_list_range_iff. reflexivity.
Qed.

Print Assumptions hfs_mem_list_big_union_iff.
Print Assumptions hfs_mem_list_big_inter_iff.
Print Assumptions hfs_list_big_union_empty.
Print Assumptions hfs_list_big_union_cons.
Print Assumptions hfs_list_big_union_app.
Print Assumptions hfs_list_big_union_subset_of_subset.
Print Assumptions hfs_list_big_inter_singleton.
Print Assumptions hfs_list_big_inter_cons.
Print Assumptions hfs_list_big_inter_subset_head.
Print Assumptions hfs_list_big_inter_subset_member.
Print Assumptions hfs_mem_list_product_iff.
Print Assumptions hfs_mem_list_domain_iff.
Print Assumptions hfs_mem_list_range_iff.
Print Assumptions hfs_list_big_union_existsUnique.
Print Assumptions hfs_list_big_inter_existsUnique.
Print Assumptions hfs_list_product_existsUnique.
Print Assumptions hfs_list_product_empty_left.
Print Assumptions hfs_list_product_empty_right.
Print Assumptions hfs_list_product_app_left.
Print Assumptions hfs_list_product_app_right.
Print Assumptions hfs_list_product_singleton.
Print Assumptions hfs_list_domain_existsUnique.
Print Assumptions hfs_list_range_existsUnique.
