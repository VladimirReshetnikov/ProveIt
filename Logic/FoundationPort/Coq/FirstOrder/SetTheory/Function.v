(** Set-theoretic relations and functions over chosen Zermelo operations. *)

From Foundation.FirstOrder.SetTheory Require Import Basic Z.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

Definition z_domain {m} (O : zermelo_operations m)
    (R : membership_carrier m) : membership_carrier m :=
  z_separate O
    (fun x => exists y, membership_rel (z_kpair O x y) R)
    (z_sunion O (z_sunion O R)).

Definition z_range {m} (O : zermelo_operations m)
    (R : membership_carrier m) : membership_carrier m :=
  z_separate O
    (fun y => exists x, membership_rel (z_kpair O x y) R)
    (z_sunion O (z_sunion O R)).

Lemma z_mem_sunion_sunion_of_kpair_mem_left :
  forall m (O : zermelo_operations m) (x y R : membership_carrier m),
  membership_rel (z_kpair O x y) R ->
  membership_rel x (z_sunion O (z_sunion O R)).
Proof.
  intros m O x y R Hpair. apply z_sunion_mem_iff.
  exists (z_pair O x y). split.
  - apply z_sunion_mem_iff. exists (z_kpair O x y). split; [exact Hpair |].
    apply z_kpair_mem_iff. now right.
  - apply z_pair_mem_iff. now left.
Qed.

Lemma z_mem_sunion_sunion_of_kpair_mem_right :
  forall m (O : zermelo_operations m) (x y R : membership_carrier m),
  membership_rel (z_kpair O x y) R ->
  membership_rel y (z_sunion O (z_sunion O R)).
Proof.
  intros m O x y R Hpair. apply z_sunion_mem_iff.
  exists (z_pair O x y). split.
  - apply z_sunion_mem_iff. exists (z_kpair O x y). split; [exact Hpair |].
    apply z_kpair_mem_iff. now right.
  - apply z_pair_mem_iff. now right.
Qed.

Lemma z_domain_mem_iff : forall m (O : zermelo_operations m)
    (R x : membership_carrier m),
  membership_rel x (z_domain O R) <->
  exists y, membership_rel (z_kpair O x y) R.
Proof.
  intros m O R x. unfold z_domain. rewrite z_separate_mem_iff. split.
  - now intros [_ H].
  - intros H. split; [|exact H]. destruct H as [y Hy].
    now apply (@z_mem_sunion_sunion_of_kpair_mem_left m O x y R).
Qed.

Lemma z_range_mem_iff : forall m (O : zermelo_operations m)
    (R y : membership_carrier m),
  membership_rel y (z_range O R) <->
  exists x, membership_rel (z_kpair O x y) R.
Proof.
  intros m O R y. unfold z_range. rewrite z_separate_mem_iff. split.
  - now intros [_ H].
  - intros H. split; [|exact H]. destruct H as [x Hx].
    now apply (@z_mem_sunion_sunion_of_kpair_mem_right m O x y R).
Qed.

Lemma z_mem_domain_of_kpair_mem : forall m (O : zermelo_operations m)
    (R x y : membership_carrier m),
  membership_rel (z_kpair O x y) R -> membership_rel x (z_domain O R).
Proof. intros. apply z_domain_mem_iff. now exists y. Qed.

Lemma z_mem_range_of_kpair_mem : forall m (O : zermelo_operations m)
    (R x y : membership_carrier m),
  membership_rel (z_kpair O x y) R -> membership_rel y (z_range O R).
Proof. intros. apply z_range_mem_iff. now exists x. Qed.

Lemma z_domain_empty : forall m (O : zermelo_operations m),
  z_domain O (z_empty O) = z_empty O.
Proof.
  intros m O. apply z_empty_unique. intros x Hx.
  apply z_domain_mem_iff in Hx. destruct Hx as [y Hy].
  now apply (z_not_mem_empty O (z_kpair O x y) Hy).
Qed.

Lemma z_range_empty : forall m (O : zermelo_operations m),
  z_range O (z_empty O) = z_empty O.
Proof.
  intros m O. apply z_empty_unique. intros y Hy.
  apply z_range_mem_iff in Hy. destruct Hy as [x Hx].
  now apply (z_not_mem_empty O (z_kpair O x y) Hx).
Qed.

Lemma z_domain_product : forall m (O : zermelo_operations m)
    (X Y : membership_carrier m),
  set_model_is_nonempty Y -> z_domain O (z_product O X Y) = X.
Proof.
  intros m O X Y [y Hy]. apply (z_extensionality O). intro x. split.
  - intro Hx. apply z_domain_mem_iff in Hx. destruct Hx as [z Hz].
    apply z_kpair_mem_product_iff in Hz. exact (proj1 Hz).
  - intro Hx. apply z_domain_mem_iff. exists y.
    apply z_kpair_mem_product_iff. now split.
Qed.

Lemma z_range_product : forall m (O : zermelo_operations m)
    (X Y : membership_carrier m),
  set_model_is_nonempty X -> z_range O (z_product O X Y) = Y.
Proof.
  intros m O X Y [x Hx]. apply (z_extensionality O). intro y. split.
  - intro Hy. apply z_range_mem_iff in Hy. destruct Hy as [z Hz].
    apply z_kpair_mem_product_iff in Hz. exact (proj2 Hz).
  - intro Hy. apply z_range_mem_iff. exists x.
    apply z_kpair_mem_product_iff. now split.
Qed.

Lemma z_domain_subset_of_subset_product :
  forall m (O : zermelo_operations m) (R X Y : membership_carrier m),
  set_model_subset R (z_product O X Y) -> set_model_subset (z_domain O R) X.
Proof.
  intros m O R X Y H x Hx. apply z_domain_mem_iff in Hx.
  destruct Hx as [y Hy]. apply H in Hy.
  apply z_kpair_mem_product_iff in Hy. exact (proj1 Hy).
Qed.

Lemma z_range_subset_of_subset_product :
  forall m (O : zermelo_operations m) (R X Y : membership_carrier m),
  set_model_subset R (z_product O X Y) -> set_model_subset (z_range O R) Y.
Proof.
  intros m O R X Y H y Hy. apply z_range_mem_iff in Hy.
  destruct Hy as [x Hx]. apply H in Hx.
  apply z_kpair_mem_product_iff in Hx. exact (proj2 Hx).
Qed.

Lemma z_domain_union : forall m (O : zermelo_operations m)
    (R S : membership_carrier m),
  z_domain O (z_union O R S) = z_union O (z_domain O R) (z_domain O S).
Proof.
  intros m O R S. apply (z_extensionality O). intro x. split.
  - intro H. apply z_domain_mem_iff in H. destruct H as [y Hy].
    apply z_union_mem_iff in Hy. apply z_union_mem_iff.
    destruct Hy; [left | right]; apply z_domain_mem_iff; now exists y.
  - intro H. apply z_union_mem_iff in H. apply z_domain_mem_iff.
    destruct H as [H | H]; apply z_domain_mem_iff in H;
      destruct H as [y Hy]; exists y; apply z_union_mem_iff;
      [now left | now right].
Qed.

Lemma z_range_union : forall m (O : zermelo_operations m)
    (R S : membership_carrier m),
  z_range O (z_union O R S) = z_union O (z_range O R) (z_range O S).
Proof.
  intros m O R S. apply (z_extensionality O). intro y. split.
  - intro H. apply z_range_mem_iff in H. destruct H as [x Hx].
    apply z_union_mem_iff in Hx. apply z_union_mem_iff.
    destruct Hx; [left | right]; apply z_range_mem_iff; now exists x.
  - intro H. apply z_union_mem_iff in H. apply z_range_mem_iff.
    destruct H as [H | H]; apply z_range_mem_iff in H;
      destruct H as [x Hx]; exists x; apply z_union_mem_iff;
      [now left | now right].
Qed.

Lemma z_domain_inter_subset : forall m (O : zermelo_operations m)
    (R S : membership_carrier m),
  set_model_subset (z_domain O (z_inter O R S))
    (z_inter O (z_domain O R) (z_domain O S)).
Proof.
  intros m O R S x Hx. apply z_domain_mem_iff in Hx.
  destruct Hx as [y Hy]. apply z_inter_mem_iff in Hy.
  apply z_inter_mem_iff. split; apply z_domain_mem_iff; exists y; tauto.
Qed.

Lemma z_range_inter_subset : forall m (O : zermelo_operations m)
    (R S : membership_carrier m),
  set_model_subset (z_range O (z_inter O R S))
    (z_inter O (z_range O R) (z_range O S)).
Proof.
  intros m O R S y Hy. apply z_range_mem_iff in Hy.
  destruct Hy as [x Hx]. apply z_inter_mem_iff in Hx.
  apply z_inter_mem_iff. split; apply z_range_mem_iff; exists x; tauto.
Qed.

Lemma z_domain_insert_kpair : forall m (O : zermelo_operations m)
    (x y R : membership_carrier m),
  z_domain O (z_insert O (z_kpair O x y) R) = z_insert O x (z_domain O R).
Proof.
  intros m O x y R. apply (z_extensionality O). intro z. split.
  - intro H. apply z_domain_mem_iff in H. destruct H as [w Hw].
    apply z_insert_mem_iff in Hw. apply z_insert_mem_iff.
    destruct Hw as [Heq | Hw].
    + apply z_kpair_injective in Heq. now left; apply (proj1 Heq).
    + right. apply z_domain_mem_iff. now exists w.
  - intro H. apply z_insert_mem_iff in H. apply z_domain_mem_iff.
    destruct H as [-> | H].
    + exists y. apply z_insert_mem_iff. now left.
    + apply z_domain_mem_iff in H. destruct H as [w Hw].
      exists w. apply z_insert_mem_iff. now right.
Qed.

Lemma z_range_insert_kpair : forall m (O : zermelo_operations m)
    (x y R : membership_carrier m),
  z_range O (z_insert O (z_kpair O x y) R) = z_insert O y (z_range O R).
Proof.
  intros m O x y R. apply (z_extensionality O). intro z. split.
  - intro H. apply z_range_mem_iff in H. destruct H as [w Hw].
    apply z_insert_mem_iff in Hw. apply z_insert_mem_iff.
    destruct Hw as [Heq | Hw].
    + apply z_kpair_injective in Heq. now left; apply (proj2 Heq).
    + right. apply z_range_mem_iff. now exists w.
  - intro H. apply z_insert_mem_iff in H. apply z_range_mem_iff.
    destruct H as [-> | H].
    + exists x. apply z_insert_mem_iff. now left.
    + apply z_range_mem_iff in H. destruct H as [w Hw].
      exists w. apply z_insert_mem_iff. now right.
Qed.

Print Assumptions z_domain_mem_iff.
Print Assumptions z_range_mem_iff.
Print Assumptions z_domain_insert_kpair.
Print Assumptions z_range_insert_kpair.
