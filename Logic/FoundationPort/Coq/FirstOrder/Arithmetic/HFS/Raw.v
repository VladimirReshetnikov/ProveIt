(** Finite enumeration of a raw standard HFS code.

    A Foundation HFS code is a natural number whose set members are the
    positions of its one bits.  The binary representation is finite, but the
    useful bridge to the list-facing development is not merely an existence
    statement: enumerating the bounded prefix below [N.size s] gives exactly
    the members of [s].  This is the standard-model counterpart of the
    bounded comprehension/extraction layer in Foundation.
*)

From Stdlib Require Import Bool.Bool Arith.PeanoNat Lia Lists.List NArith.NArith.
From Foundation.FirstOrder.Arithmetic.Exponential Require Import Bit.
From Foundation.FirstOrder.Arithmetic.HFS Require Import Basic Coding Seq BigOps.

Import ListNotations.

Set Implicit Arguments.
Unset Strict Implicit.

Definition hfs_code_elements (s : hfs_code) : list hfs_code :=
  map N.of_nat
    (filter (fun i => N.testbit s (N.of_nat i))
      (seq 0 (N.to_nat (N.size s)))).

Lemma hfs_mem_code_elements_iff : forall s x,
  In x (hfs_code_elements s) <-> hfs_mem x s.
Proof.
  intros s x. unfold hfs_code_elements.
  rewrite in_map_iff. split.
  - intros [i [Hix Hi]].
    apply filter_In in Hi. destruct Hi as [_ Hbit].
    unfold hfs_mem. rewrite <- Hix. exact Hbit.
  - intro Hmem.
    assert (Hlt : x < N.size s).
    { exact (@nat_bit_lt_size_of_mem x s Hmem). }
    exists (N.to_nat x). split.
    + rewrite N2Nat.id. reflexivity.
    + apply filter_In. split.
      * rewrite in_seq. split; [lia|].
        rewrite Nat.add_0_l.
        apply (proj1 (Nat.compare_lt_iff _ _)).
        rewrite <- N2Nat.inj_compare.
        apply (proj1 (N.compare_lt_iff _ _)).
        exact Hlt.
      * rewrite N2Nat.id. exact Hmem.
Qed.

Lemma hfs_code_elements_arithmetize : forall s,
  hfs_arithmetize_list (hfs_code_elements s) = s.
Proof.
  intro s. apply hfs_extensionality. intro x.
  rewrite hfs_mem_arithmetize_list_iff, hfs_mem_code_elements_iff.
  reflexivity.
Qed.

Lemma hfs_code_elements_nonempty_of_mem : forall s x,
  hfs_mem x s -> In x (hfs_code_elements s).
Proof.
  intros s x H. now apply (proj2 (hfs_mem_code_elements_iff s x)).
Qed.

Lemma hfs_mem_code_elements : forall s x,
  In x (hfs_code_elements s) -> hfs_mem x s.
Proof.
  intros s x H. now apply (proj1 (hfs_mem_code_elements_iff s x)).
Qed.

(** * Raw big operations *)

Definition hfs_code_big_union (s : hfs_code) : hfs_code :=
  hfs_list_big_union (hfs_code_elements s).

Lemma hfs_mem_code_big_union_iff : forall s x,
  hfs_mem x (hfs_code_big_union s) <->
  exists t, hfs_mem t s /\ hfs_mem x t.
Proof.
  intros s x. unfold hfs_code_big_union.
  rewrite hfs_mem_list_big_union_iff. split.
  - intros [t [Ht Hxt]].
    exists t. split.
    + apply (proj1 (hfs_mem_code_elements_iff s t)). exact Ht.
    + exact Hxt.
  - intros [t [Hts Hxt]].
    exists t. split.
    + apply (proj2 (hfs_mem_code_elements_iff s t)). exact Hts.
    + exact Hxt.
Qed.

Theorem hfs_code_big_union_existsUnique : forall s,
  exists! u, forall x,
    hfs_mem x u <-> exists t, hfs_mem t s /\ hfs_mem x t.
Proof.
  intro s. exists (hfs_code_big_union s). split.
  - intro x. apply hfs_mem_code_big_union_iff.
  - intros u Hu. apply hfs_extensionality. intro x.
    rewrite Hu, hfs_mem_code_big_union_iff. reflexivity.
Qed.

Definition hfs_code_big_inter (s : hfs_code) : hfs_code :=
  match hfs_code_elements s with
  | [] => hfs_empty
  | head :: tail => hfs_list_big_inter head tail
  end.

Local Lemma hfs_mem_list_big_inter_cons_iff : forall head tail x,
  hfs_mem x (hfs_list_big_inter head tail) <->
  forall t, In t (head :: tail) -> hfs_mem x t.
Proof.
  intros head tail x. rewrite hfs_mem_list_big_inter_iff. split.
  - intros [Hhead Htail] t Ht. simpl in Ht. destruct Ht as [-> | Ht].
    + exact Hhead.
    + exact (Htail t Ht).
  - intro H. split.
    + apply H. simpl. left. reflexivity.
    + intros t Ht. apply H. simpl. right. exact Ht.
Qed.

Lemma hfs_mem_code_big_inter_iff : forall s x,
  hfs_mem x (hfs_code_big_inter s) <->
  s <> hfs_empty /\ forall t, hfs_mem t s -> hfs_mem x t.
Proof.
  intros s x. unfold hfs_code_big_inter.
  destruct (hfs_code_elements s) as [|head tail] eqn:He.
  - assert (Hs : s = hfs_empty).
    { rewrite <- (hfs_code_elements_arithmetize s), He. reflexivity. }
    subst s. rewrite hfs_mem_empty_iff. tauto.
  - rewrite hfs_mem_list_big_inter_cons_iff. split.
    + intro H. split.
      * intro Hs.
        apply (@hfs_not_mem_empty head).
        apply (proj1 (hfs_mem_code_elements_iff hfs_empty head)).
        rewrite <- Hs, He. simpl. left. reflexivity.
      * intros t Ht. apply H. rewrite <- He.
        apply (proj2 (hfs_mem_code_elements_iff s t)). exact Ht.
    + intros Hpair.
      destruct Hpair as [Hs H_all].
      intro t.
      intro Ht.
      apply H_all.
      apply (proj1 (hfs_mem_code_elements_iff s t)).
      rewrite He. exact Ht.
Qed.

Theorem hfs_code_big_inter_existsUnique : forall s,
  exists! u, forall x,
    hfs_mem x u <->
    s <> hfs_empty /\ forall t, hfs_mem t s -> hfs_mem x t.
Proof.
  intro s. exists (hfs_code_big_inter s). split.
  - intro x. apply hfs_mem_code_big_inter_iff.
  - intros u Hu. apply hfs_extensionality. intro x.
    rewrite Hu, hfs_mem_code_big_inter_iff. reflexivity.
Qed.

Definition hfs_code_product (s t : hfs_code) : hfs_code :=
  hfs_list_product (hfs_code_elements s) (hfs_code_elements t).

Lemma hfs_mem_code_product_iff : forall s t p,
  hfs_mem p (hfs_code_product s t) <->
  exists x, hfs_mem x s /\ exists y, hfs_mem y t /\
      p = hfs_index_pair x y.
Proof.
  intros s t p. unfold hfs_code_product.
  rewrite hfs_mem_list_product_iff. split.
  - intros [x [Hx [y [Hy Hp]]]].
    exists x. split.
    + apply (proj1 (hfs_mem_code_elements_iff s x)). exact Hx.
    + exists y. split.
      * apply (proj1 (hfs_mem_code_elements_iff t y)). exact Hy.
      * exact Hp.
  - intros [x [Hxs [y [Hyt Hp]]]].
    exists x. split.
    + apply (proj2 (hfs_mem_code_elements_iff s x)). exact Hxs.
    + exists y. split.
      * apply (proj2 (hfs_mem_code_elements_iff t y)). exact Hyt.
      * exact Hp.
Qed.

Theorem hfs_code_product_existsUnique : forall s t,
  exists! u, forall p,
    hfs_mem p u <->
    exists x, hfs_mem x s /\ exists y, hfs_mem y t /\
        p = hfs_index_pair x y.
Proof.
  intros s t. exists (hfs_code_product s t). split.
  - intro p. apply hfs_mem_code_product_iff.
  - intros u Hu. apply hfs_extensionality. intro p.
    rewrite Hu, hfs_mem_code_product_iff. reflexivity.
Qed.

Definition hfs_code_domain (relation : hfs_code) : hfs_code :=
  hfs_list_domain (hfs_code_elements relation).

Lemma hfs_mem_code_domain_iff : forall relation x,
  hfs_mem x (hfs_code_domain relation) <->
  exists y, hfs_mem (hfs_index_pair x y) relation.
Proof.
  intros relation x. unfold hfs_code_domain.
  rewrite hfs_mem_list_domain_iff. split.
  - intros [y Hpair].
    exists y. apply (proj1 (hfs_mem_code_elements_iff relation
      (hfs_index_pair x y))). exact Hpair.
  - intros [y Hpair].
    exists y. apply (proj2 (hfs_mem_code_elements_iff relation
      (hfs_index_pair x y))). exact Hpair.
Qed.

Theorem hfs_code_domain_existsUnique : forall relation,
  exists! d, forall x,
    hfs_mem x d <-> exists y,
      hfs_mem (hfs_index_pair x y) relation.
Proof.
  intro relation. exists (hfs_code_domain relation). split.
  - intro x. apply hfs_mem_code_domain_iff.
  - intros d Hd. apply hfs_extensionality. intro x.
    rewrite Hd, hfs_mem_code_domain_iff. reflexivity.
Qed.

Definition hfs_code_range (relation : hfs_code) : hfs_code :=
  hfs_list_range (hfs_code_elements relation).

Lemma hfs_mem_code_range_iff : forall relation y,
  hfs_mem y (hfs_code_range relation) <->
  exists x, hfs_mem (hfs_index_pair x y) relation.
Proof.
  intros relation y. unfold hfs_code_range.
  rewrite hfs_mem_list_range_iff. split.
  - intros [x Hpair].
    exists x. apply (proj1 (hfs_mem_code_elements_iff relation
      (hfs_index_pair x y))). exact Hpair.
  - intros [x Hpair].
    exists x. apply (proj2 (hfs_mem_code_elements_iff relation
      (hfs_index_pair x y))). exact Hpair.
Qed.

Theorem hfs_code_range_existsUnique : forall relation,
  exists! r, forall y,
    hfs_mem y r <-> exists x,
      hfs_mem (hfs_index_pair x y) relation.
Proof.
  intro relation. exists (hfs_code_range relation). split.
  - intro y. apply hfs_mem_code_range_iff.
  - intros r Hr. apply hfs_extensionality. intro y.
    rewrite Hr, hfs_mem_code_range_iff. reflexivity.
Qed.

Print Assumptions hfs_mem_code_elements_iff.
Print Assumptions hfs_code_elements_arithmetize.
Print Assumptions hfs_code_elements_nonempty_of_mem.
Print Assumptions hfs_mem_code_elements.
Print Assumptions hfs_mem_code_big_union_iff.
Print Assumptions hfs_code_big_union_existsUnique.
Print Assumptions hfs_mem_code_big_inter_iff.
Print Assumptions hfs_code_big_inter_existsUnique.
Print Assumptions hfs_mem_code_product_iff.
Print Assumptions hfs_code_product_existsUnique.
Print Assumptions hfs_mem_code_domain_iff.
Print Assumptions hfs_code_domain_existsUnique.
Print Assumptions hfs_mem_code_range_iff.
Print Assumptions hfs_code_range_existsUnique.
