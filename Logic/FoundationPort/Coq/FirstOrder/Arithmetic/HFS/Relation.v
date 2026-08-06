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

(** Finite-list counterpart of Foundation's [sigmaOne_skolem].  [NoDup]
    expresses the fact that an HFS domain is a set rather than a list with
    repeated indices.  The strengthened graph clause records that every pair
    in the constructed mapping has its first coordinate in the domain. *)
Theorem hfs_list_skolem_exists : forall
    (domain : list hfs_code)
    (R : hfs_code -> hfs_code -> Prop),
  NoDup domain ->
  (forall x, In x domain -> exists y, R x y) ->
  exists relation,
    hfs_list_is_mapping relation /\
    (forall x, In x domain ->
      exists y, In (hfs_index_pair x y) relation) /\
    (forall x y, In (hfs_index_pair x y) relation ->
      In x domain /\ R x y).
Proof.
  induction domain as [|a domain IH]; intros R Hnodup H.
  - exists []. split.
    + apply hfs_list_is_mapping_empty.
    + split.
      * intros u Hu. simpl in Hu. contradiction.
      * intros u v Huv. simpl in Huv. contradiction.
  - pose proof (proj1 (@NoDup_cons_iff hfs_code a domain) Hnodup)
      as [Hfresh Hnodup_tail].
    destruct (H a (or_introl eq_refl)) as [b Hb].
    assert (Htail : forall x, In x domain -> exists y, R x y).
    { intros x Hx. apply H. right. exact Hx. }
    destruct (IH R Hnodup_tail Htail) as [relation
      [Hmapping [Hcover Hgraph]]].
    exists (hfs_index_pair a b :: relation). split.
    + unfold hfs_list_is_mapping in Hmapping |-.
      intros x y z Hy Hz. simpl in Hy, Hz.
      destruct Hy as [Hy | Hy], Hz as [Hz | Hz].
      * destruct (hfs_index_pair_injective Hy) as [Hax Hby].
        destruct (hfs_index_pair_injective Hz) as [Hax' Hbz].
        congruence.
      * destruct (hfs_index_pair_injective Hy) as [Hax Hby].
        exfalso. apply Hfresh.
        pose proof (proj1 (Hgraph x z Hz)) as Hxdom.
        rewrite <- Hax in Hxdom. exact Hxdom.
      * destruct (hfs_index_pair_injective Hz) as [Hax Hbz].
        exfalso. apply Hfresh.
        pose proof (proj1 (Hgraph x y Hy)) as Hxdom.
        rewrite <- Hax in Hxdom. exact Hxdom.
      * apply (@Hmapping x y z); assumption.
    + split.
      { intros x Hx. simpl.
        destruct Hx as [-> | Hx].
        - exists b. left. reflexivity.
        - destruct (Hcover x Hx) as [y Hy].
          exists y. right. exact Hy. }
      { intros x y Hxy. simpl in Hxy.
        destruct Hxy as [Hxy | Hxy].
        - destruct (hfs_index_pair_injective Hxy) as [Hax Hby].
          subst x. subst y. split; [left; reflexivity|exact Hb].
        - destruct (Hgraph x y Hxy) as [Hxdom HR].
          split; [right; exact Hxdom|exact HR]. }
Qed.

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

(** * Finite composition and identity relations *)

Definition hfs_list_compose (left right : list hfs_code) : list hfs_code :=
  flat_map
    (fun p =>
      flat_map
        (fun q =>
          if N.eq_dec (hfs_index_snd p) (hfs_index_fst q)
          then [hfs_index_pair (hfs_index_fst p) (hfs_index_snd q)]
          else [])
        right)
    left.

Lemma hfs_list_compose_In_iff : forall left right x z,
  In (hfs_index_pair x z) (hfs_list_compose left right) <->
  exists y,
    In (hfs_index_pair x y) left /\
    In (hfs_index_pair y z) right.
Proof.
  intros left right x z. unfold hfs_list_compose.
  rewrite in_flat_map. split.
  - intros [p [Hp Hpcomp]].
    rewrite in_flat_map in Hpcomp.
    destruct Hpcomp as [q [Hq Hpq]].
    simpl in Hpq.
    destruct (N.eq_dec (hfs_index_snd p) (hfs_index_fst q)) as [Hmatch | Hnomatch].
    + simpl in Hpq. destruct Hpq as [Hpq | Hpq]; [|contradiction].
      apply hfs_index_pair_injective in Hpq.
      destruct Hpq as [Hx Hz].
      exists (hfs_index_snd p). split.
      * rewrite <- Hx. rewrite hfs_index_pair_projections. exact Hp.
      * rewrite Hmatch. rewrite <- Hz.
        rewrite hfs_index_pair_projections. exact Hq.
    + contradiction.
  - intros [y [Hleft Hright]].
    exists (hfs_index_pair x y). split; [exact Hleft|].
    rewrite in_flat_map. exists (hfs_index_pair y z). split; [exact Hright|].
    repeat rewrite hfs_index_snd_pair.
    repeat rewrite hfs_index_fst_pair.
    destruct (N.eq_dec y y) as [Heq | Hneq].
    + apply in_eq.
    + contradiction.
Qed.

Definition hfs_list_identity (domain : list hfs_code) : list hfs_code :=
  map (fun x => hfs_index_pair x x) domain.

Lemma hfs_mem_list_identity_iff : forall domain x y,
  In (hfs_index_pair x y) (hfs_list_identity domain) <->
  In x domain /\ x = y.
Proof.
  intros domain x y. unfold hfs_list_identity.
  rewrite in_map_iff. split.
  - intros [u [Hu Hdom]].
    apply hfs_index_pair_injective in Hu.
    destruct Hu as [Hx Hy].
    split.
    + rewrite <- Hx. exact Hdom.
    + congruence.
  - intros [Hdom Hxy]. subst y.
    exists x. split; [reflexivity|exact Hdom].
Qed.

Lemma hfs_list_is_mapping_identity : forall domain,
  hfs_list_is_mapping (hfs_list_identity domain).
Proof.
  intros domain x y z Hy Hz.
  apply hfs_mem_list_identity_iff in Hy, Hz.
  destruct Hy as [_ ->]. destruct Hz as [_ ->]. reflexivity.
Qed.

Definition hfs_list_is_injective (relation : list hfs_code) : Prop :=
  forall x y z,
    In (hfs_index_pair x z) relation ->
    In (hfs_index_pair y z) relation ->
    x = y.

Lemma hfs_list_is_injective_identity : forall domain,
  hfs_list_is_injective (hfs_list_identity domain).
Proof.
  intros domain x y z Hx Hy.
  apply hfs_mem_list_identity_iff in Hx, Hy.
  now destruct Hx as [_ ->], Hy as [_ ->].
Qed.

Lemma hfs_list_compose_is_mapping : forall left right,
  hfs_list_is_mapping left ->
  hfs_list_is_mapping right ->
  hfs_list_is_mapping (hfs_list_compose left right).
Proof.
  intros left right Hleft Hright x y z Hy Hz.
  apply hfs_list_compose_In_iff in Hy, Hz.
  destruct Hy as [u [Hxu Huy]], Hz as [v [Hxv Hvz]].
  assert (Huv : u = v).
  { exact (Hleft x u v Hxu Hxv). }
  subst v. eapply Hright; eassumption.
Qed.

Lemma hfs_list_compose_is_injective : forall left right,
  hfs_list_is_injective left ->
  hfs_list_is_injective right ->
  hfs_list_is_injective (hfs_list_compose left right).
Proof.
  intros left right Hleft Hright x y z Hxz Hyz.
  apply hfs_list_compose_In_iff in Hxz, Hyz.
  destruct Hxz as [u [Hxu Huz]], Hyz as [v [Hyv Hvz]].
  assert (Huv : u = v).
  { exact (Hright u v z Huz Hvz). }
  subst v. eapply Hleft; eassumption.
Qed.

Print Assumptions hfs_mem_list_image_iff.
Print Assumptions hfs_list_image_existsUnique.
Print Assumptions hfs_list_restrict_In_iff.
Print Assumptions hfs_mem_list_restrict_code_iff.
Print Assumptions hfs_list_is_mapping_restrict.
Print Assumptions hfs_list_is_mapping_app.
Print Assumptions hfs_list_skolem_exists.
Print Assumptions hfs_list_mapping_fiber_existsUnique.
Print Assumptions hfs_list_compose_In_iff.
Print Assumptions hfs_mem_list_identity_iff.
Print Assumptions hfs_list_is_mapping_identity.
Print Assumptions hfs_list_is_injective_identity.
Print Assumptions hfs_list_compose_is_mapping.
Print Assumptions hfs_list_compose_is_injective.
