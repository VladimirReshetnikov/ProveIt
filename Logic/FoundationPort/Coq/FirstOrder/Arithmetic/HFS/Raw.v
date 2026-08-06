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
From Foundation.FirstOrder.Arithmetic.HFS Require Import Basic Coding Seq BigOps Relation.

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

Lemma hfs_code_elements_nodup : forall s,
  NoDup (hfs_code_elements s).
Proof.
  intro s. unfold hfs_code_elements.
  apply NoDup_map_NoDup_ForallPairs.
  - intros i j _ _ Hij. apply Nat2N.inj. exact Hij.
  - apply NoDup_filter. apply seq_NoDup.
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

(** * Raw relation restriction, images, and mappings *)

Definition hfs_code_image (f : hfs_code -> hfs_code) (s : hfs_code) : hfs_code :=
  hfs_list_image f (hfs_code_elements s).

Lemma hfs_mem_code_image_iff : forall f s y,
  hfs_mem y (hfs_code_image f s) <->
  exists x, hfs_mem x s /\ y = f x.
Proof.
  intros f s y. unfold hfs_code_image.
  rewrite hfs_mem_list_image_iff. split.
  - intros [x [Hx Hy]]. exists x. split.
    + apply (proj1 (hfs_mem_code_elements_iff s x)). exact Hx.
    + exact Hy.
  - intros [x [Hx Hy]]. exists x. split.
    + apply (proj2 (hfs_mem_code_elements_iff s x)). exact Hx.
    + exact Hy.
Qed.

Theorem hfs_code_image_existsUnique : forall f s,
  exists! t, forall y,
    hfs_mem y t <-> exists x, hfs_mem x s /\ y = f x.
Proof.
  intros f s. exists (hfs_code_image f s). split.
  - intro y. apply hfs_mem_code_image_iff.
  - intros t Ht. apply hfs_extensionality. intro y.
    rewrite Ht, hfs_mem_code_image_iff. reflexivity.
Qed.

Lemma hfs_code_image_empty : forall f,
  hfs_code_image f hfs_empty = hfs_empty.
Proof.
  intro f. apply hfs_extensionality. intro y.
  rewrite hfs_mem_code_image_iff. split.
  - intros [x [Hx _]].
    exfalso. now apply hfs_not_mem_empty in Hx.
  - intro Hy. apply hfs_mem_empty_iff in Hy. contradiction.
Qed.

Lemma hfs_code_image_union : forall f left right,
  hfs_code_image f (hfs_union left right) =
  hfs_union (hfs_code_image f left) (hfs_code_image f right).
Proof.
  intros f left right. apply hfs_extensionality. intro y.
  rewrite hfs_mem_code_image_iff.
  setoid_rewrite hfs_mem_union_iff.
  setoid_rewrite hfs_mem_code_image_iff.
  split.
  - intros [x [Hx Hy]].
    destruct Hx as [Hleft | Hright].
    + left. exists x. split; assumption.
    + right. exists x. split; assumption.
  - intros [Hleft | Hright].
    + destruct Hleft as [x [Hx Hy]]. exists x. split.
      * left. exact Hx.
      * exact Hy.
    + destruct Hright as [x [Hx Hy]]. exists x. split.
      * right. exact Hx.
      * exact Hy.
Qed.

Lemma hfs_code_image_insert : forall f x s,
  hfs_code_image f (hfs_insert x s) =
  hfs_insert (f x) (hfs_code_image f s).
Proof.
  intros f x s. apply hfs_extensionality. intro y.
  rewrite hfs_mem_code_image_iff.
  setoid_rewrite hfs_mem_insert_iff.
  setoid_rewrite hfs_mem_code_image_iff. split.
  - intros [z [[-> | Hz] Hy]].
    + left. exact Hy.
    + right. exists z. split; assumption.
  - intros [Hy | [z [Hz Hy]]].
    + exists x. split; [left; reflexivity|exact Hy].
    + exists z. split; [right; exact Hz|exact Hy].
Qed.

Lemma hfs_code_image_subset_of_subset : forall f s t,
  hfs_subset s t ->
  hfs_subset (hfs_code_image f s) (hfs_code_image f t).
Proof.
  intros f s t Hsub y Hy. apply hfs_mem_code_image_iff in Hy.
  destruct Hy as [x [Hx ->]]. apply hfs_mem_code_image_iff.
  exists x. split; [apply (Hsub x); exact Hx|reflexivity].
Qed.

Definition hfs_code_restrict (relation domain : hfs_code) : hfs_code :=
  hfs_list_restrict_code (hfs_code_elements relation)
    (hfs_code_elements domain).

Lemma hfs_mem_code_restrict_iff : forall relation domain p,
  hfs_mem p (hfs_code_restrict relation domain) <->
  hfs_mem p relation /\ hfs_mem (hfs_index_fst p) domain.
Proof.
  intros relation domain p. unfold hfs_code_restrict.
  rewrite hfs_mem_list_restrict_code_iff, !hfs_code_elements_arithmetize.
  reflexivity.
Qed.

Lemma hfs_code_restrict_subset : forall relation domain,
  hfs_subset (hfs_code_restrict relation domain) relation.
Proof.
  intros relation domain p Hp.
  apply hfs_mem_code_restrict_iff in Hp. exact (proj1 Hp).
Qed.

Lemma hfs_code_restrict_empty : forall relation,
  hfs_code_restrict relation hfs_empty = hfs_empty.
Proof.
  intro relation. apply hfs_extensionality. intro p.
  rewrite hfs_mem_code_restrict_iff. split.
  - intros [_ Hdomain]. now apply hfs_not_mem_empty in Hdomain.
  - intro H. apply hfs_mem_empty_iff in H. contradiction.
Qed.

Lemma hfs_code_domain_restrict : forall relation domain,
  hfs_code_domain (hfs_code_restrict relation domain) =
  hfs_inter (hfs_code_domain relation) domain.
Proof.
  intros relation domain. apply hfs_extensionality. intro x.
  rewrite hfs_mem_code_domain_iff, hfs_mem_inter_iff,
    hfs_mem_code_domain_iff. split.
  - intros [y Hpair].
    apply hfs_mem_code_restrict_iff in Hpair.
    split.
    + exists y. exact (proj1 Hpair).
    + pose proof (proj2 Hpair) as Hdomain.
      rewrite hfs_index_fst_pair in Hdomain. exact Hdomain.
  - intros [[y Hpair] Hdomain]. exists y.
    apply hfs_mem_code_restrict_iff. split; [exact Hpair|].
    rewrite hfs_index_fst_pair. exact Hdomain.
Qed.

Lemma hfs_code_domain_restrict_of_subset : forall relation domain,
  hfs_subset domain (hfs_code_domain relation) ->
  hfs_code_domain (hfs_code_restrict relation domain) = domain.
Proof.
  intros relation domain Hsubset. rewrite hfs_code_domain_restrict.
  rewrite hfs_inter_comm. apply hfs_inter_eq_left_of_subset. exact Hsubset.
Qed.

Definition hfs_code_is_mapping (relation : hfs_code) : Prop :=
  forall x, hfs_mem x (hfs_code_domain relation) ->
    exists! y, hfs_mem (hfs_index_pair x y) relation.

Lemma hfs_code_domain_union : forall left right,
  hfs_code_domain (hfs_union left right) =
  hfs_union (hfs_code_domain left) (hfs_code_domain right).
Proof.
  intros left right. apply hfs_extensionality. intro x.
  rewrite hfs_mem_code_domain_iff, hfs_mem_union_iff,
    hfs_mem_code_domain_iff, hfs_mem_code_domain_iff.
  setoid_rewrite hfs_mem_union_iff.
  split.
  - intros [y [Hy | Hy]].
    + left. exists y. exact Hy.
    + right. exists y. exact Hy.
  - intros [[y Hy] | [y Hy]].
    + exists y. left. exact Hy.
    + exists y. right. exact Hy.
Qed.

Definition hfs_code_domains_disjoint (left right : hfs_code) : Prop :=
  forall x,
    ~ (hfs_mem x (hfs_code_domain left) /\
       hfs_mem x (hfs_code_domain right)).

Lemma hfs_code_is_mapping_union_of_disjoint : forall left right,
  hfs_code_is_mapping left ->
  hfs_code_is_mapping right ->
  hfs_code_domains_disjoint left right ->
  hfs_code_is_mapping (hfs_union left right).
Proof.
  intros left right Hleft Hright Hdisjoint x Hx.
  apply hfs_mem_code_domain_iff in Hx. destruct Hx as [y Hy].
  rewrite hfs_mem_union_iff in Hy.
  destruct Hy as [Hyleft | Hyright].
  - assert (Hxleft : hfs_mem x (hfs_code_domain left)).
    { apply hfs_mem_code_domain_iff. exists y. exact Hyleft. }
    destruct (Hleft x Hxleft) as [z [Hz Huniq]]. exists z. split.
    + apply hfs_mem_union_iff. left. exact Hz.
    + intros w Hw. apply hfs_mem_union_iff in Hw.
      destruct Hw as [Hwleft | Hwright].
      * pose proof (Huniq w Hwleft) as Hzw. congruence.
      * exfalso. apply (Hdisjoint x). split; [exact Hxleft|].
        apply hfs_mem_code_domain_iff. exists w. exact Hwright.
  - assert (Hxright : hfs_mem x (hfs_code_domain right)).
    { apply hfs_mem_code_domain_iff. exists y. exact Hyright. }
    destruct (Hright x Hxright) as [z [Hz Huniq]]. exists z. split.
    + apply hfs_mem_union_iff. right. exact Hz.
    + intros w Hw. apply hfs_mem_union_iff in Hw.
      destruct Hw as [Hwleft | Hwright].
      * exfalso. apply (Hdisjoint x). split.
        -- apply hfs_mem_code_domain_iff. exists w. exact Hwleft.
        -- exact Hxright.
      * pose proof (Huniq w Hwright) as Hzw. congruence.
Qed.

Lemma hfs_code_is_mapping_insert_fresh : forall relation x y,
  hfs_code_is_mapping relation ->
  ~ hfs_mem x (hfs_code_domain relation) ->
  hfs_code_is_mapping (hfs_insert (hfs_index_pair x y) relation).
Proof.
  intros relation x y Hmap Hfresh a Ha.
  apply hfs_mem_code_domain_iff in Ha. destruct Ha as [b Hab].
  rewrite hfs_mem_insert_iff in Hab. destruct Hab as [Habnew | Habold].
  - destruct (hfs_index_pair_injective Habnew) as [Hax Hby].
    subst a. subst b. exists y. split.
    + apply hfs_mem_insert_iff. left. reflexivity.
    + intros z Hz. apply hfs_mem_insert_iff in Hz.
      destruct Hz as [Hznew | Hzold].
      * destruct (hfs_index_pair_injective Hznew) as [_ Hzy]. exact (eq_sym Hzy).
      * exfalso. apply Hfresh. apply hfs_mem_code_domain_iff.
        exists z. exact Hzold.
  - assert (Had : hfs_mem a (hfs_code_domain relation)).
    { apply hfs_mem_code_domain_iff. exists b. exact Habold. }
    destruct (Hmap a Had) as [z [Hz Huniq]]. exists z. split.
    + apply hfs_mem_insert_iff. right. exact Hz.
    + intros w Hw. apply hfs_mem_insert_iff in Hw.
      destruct Hw as [Hwnew | Hwold].
      * destruct (hfs_index_pair_injective Hwnew) as [Hax _].
        exfalso. apply Hfresh. rewrite <- Hax. exact Had.
      * pose proof (Huniq w Hwold) as Hzw. congruence.
Qed.

Lemma hfs_code_is_mapping_empty : hfs_code_is_mapping hfs_empty.
Proof.
  intros x Hx. apply hfs_mem_code_domain_iff in Hx.
  destruct Hx as [y Hy]. exfalso. now apply hfs_not_mem_empty in Hy.
Qed.

Lemma hfs_code_is_mapping_singleton : forall x y,
  hfs_code_is_mapping (hfs_singleton (hfs_index_pair x y)).
Proof.
  intros x y z Hz. apply hfs_mem_code_domain_iff in Hz.
  destruct Hz as [w Hw]. apply hfs_mem_singleton_iff in Hw.
  destruct (hfs_index_pair_injective Hw) as [Hzx Hwy].
  subst z. subst w. exists y. split.
  - apply hfs_mem_singleton_iff. reflexivity.
  - intros z Hz'. apply hfs_mem_singleton_iff in Hz'.
    now apply (proj2 (hfs_index_pair_injective (eq_sym Hz'))).
Qed.

Lemma hfs_code_is_mapping_of_subset : forall relation sub,
  hfs_code_is_mapping relation ->
  hfs_subset sub relation ->
  hfs_code_is_mapping sub.
Proof.
  intros relation sub Hmap Hsub x Hx.
  apply hfs_mem_code_domain_iff in Hx. destruct Hx as [y Hy].
  assert (Hxd : hfs_mem x (hfs_code_domain relation)).
  { apply hfs_mem_code_domain_iff. exists y. apply Hsub. exact Hy. }
  destruct (Hmap x Hxd) as [z [Hz Huniq]]. exists y. split.
  - exact Hy.
  - intros z0 Hz0.
    pose proof (Huniq y (Hsub (hfs_index_pair x y) Hy)) as Hyz.
    pose proof (Huniq z0 (Hsub (hfs_index_pair x z0) Hz0)) as Hz0z.
    congruence.
Qed.

Lemma hfs_code_is_mapping_restrict : forall relation domain,
  hfs_code_is_mapping relation ->
  hfs_code_is_mapping (hfs_code_restrict relation domain).
Proof.
  intros relation domain Hmap.
  apply hfs_code_is_mapping_of_subset with (relation := relation).
  - exact Hmap.
  - apply hfs_code_restrict_subset.
Qed.

Theorem hfs_code_skolem_exists : forall
    (domain : hfs_code)
    (R : hfs_code -> hfs_code -> Prop),
  (forall x, hfs_mem x domain -> exists y, R x y) ->
  exists relation,
    hfs_code_is_mapping relation /\
    hfs_code_domain relation = domain /\
    (forall x y, hfs_mem (hfs_index_pair x y) relation -> R x y).
Proof.
  intros domain R H.
  assert (Hlist : forall x, In x (hfs_code_elements domain) -> exists y, R x y).
  { intros x Hx. apply H.
    apply (proj1 (hfs_mem_code_elements_iff domain x)). exact Hx. }
  destruct (@hfs_list_skolem_exists (hfs_code_elements domain) R
    (hfs_code_elements_nodup domain) Hlist)
    as [relation_list [Hmapping [Hcover Hgraph]]].
  exists (hfs_arithmetize_list relation_list). split.
  - assert (Hmap_code :
      hfs_code_is_mapping (hfs_arithmetize_list relation_list)).
    { intros x Hx.
      apply hfs_mem_code_domain_iff in Hx. destruct Hx as [y Hy].
      apply hfs_mem_arithmetize_list_iff in Hy.
      assert (Hxd : hfs_mem x (hfs_list_domain relation_list)).
      { apply hfs_mem_list_domain_iff. exists y. exact Hy. }
      destruct (@hfs_list_mapping_fiber_existsUnique relation_list x
        Hmapping Hxd) as [z [Hz Huniq]].
      exists z. split.
      - apply hfs_mem_arithmetize_list_iff. exact Hz.
      - intros z0 Hz0.
        apply hfs_mem_arithmetize_list_iff in Hz0.
        exact (Huniq z0 Hz0). }
    exact Hmap_code.
  - split.
    + apply hfs_extensionality. intro x.
      rewrite hfs_mem_code_domain_iff.
      setoid_rewrite hfs_mem_arithmetize_list_iff.
      rewrite <- hfs_mem_code_elements_iff. split.
      * intros [y Hy]. exact (proj1 (Hgraph x y Hy)).
      * intro Hx. destruct (Hcover x Hx) as [y Hy]. exists y. exact Hy.
    + intros x y Hxy. apply hfs_mem_arithmetize_list_iff in Hxy.
      exact (proj2 (Hgraph x y Hxy)).
Qed.

Print Assumptions hfs_mem_code_elements_iff.
Print Assumptions hfs_code_elements_arithmetize.
Print Assumptions hfs_code_elements_nonempty_of_mem.
Print Assumptions hfs_mem_code_elements.
Print Assumptions hfs_code_elements_nodup.
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
Print Assumptions hfs_mem_code_image_iff.
Print Assumptions hfs_code_image_existsUnique.
Print Assumptions hfs_code_image_empty.
Print Assumptions hfs_code_image_union.
Print Assumptions hfs_code_image_insert.
Print Assumptions hfs_code_image_subset_of_subset.
Print Assumptions hfs_mem_code_restrict_iff.
Print Assumptions hfs_code_restrict_subset.
Print Assumptions hfs_code_restrict_empty.
Print Assumptions hfs_code_domain_restrict.
Print Assumptions hfs_code_domain_restrict_of_subset.
Print Assumptions hfs_code_domain_union.
Print Assumptions hfs_code_is_mapping_union_of_disjoint.
Print Assumptions hfs_code_is_mapping_insert_fresh.
Print Assumptions hfs_code_is_mapping_empty.
Print Assumptions hfs_code_is_mapping_singleton.
Print Assumptions hfs_code_is_mapping_of_subset.
Print Assumptions hfs_code_is_mapping_restrict.
Print Assumptions hfs_code_skolem_exists.
