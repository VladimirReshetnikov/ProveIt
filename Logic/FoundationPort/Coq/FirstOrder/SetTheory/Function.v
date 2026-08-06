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

(** Total single-valued relations. *)
Definition z_function {m} (O : zermelo_operations m)
    (Y X : membership_carrier m) : membership_carrier m :=
  z_separate O
    (fun f => forall x, membership_rel x X ->
      exists y, membership_rel (z_kpair O x y) f /\
        forall y', membership_rel (z_kpair O x y') f -> y' = y)
    (z_power O (z_product O X Y)).

Lemma z_mem_function_iff : forall m (O : zermelo_operations m)
    (f Y X : membership_carrier m),
  membership_rel f (z_function O Y X) <->
  set_model_subset f (z_product O X Y) /\
  forall x, membership_rel x X ->
    exists y, membership_rel (z_kpair O x y) f /\
      forall y', membership_rel (z_kpair O x y') f -> y' = y.
Proof.
  intros m O f Y X. unfold z_function. rewrite z_separate_mem_iff. split.
  - intros [Hbase Htotal]. apply z_power_mem_iff in Hbase. now split.
  - intros [Hsub Htotal]. split.
    + exact (proj2 (@z_power_mem_iff m O (z_product O X Y) f) Hsub).
    + exact Htotal.
Qed.

Lemma z_mem_function_intro : forall m (O : zermelo_operations m)
    (f X Y : membership_carrier m),
  set_model_subset f (z_product O X Y) ->
  (forall x, membership_rel x X ->
    exists y, membership_rel (z_kpair O x y) f /\
      forall y', membership_rel (z_kpair O x y') f -> y' = y) ->
  membership_rel f (z_function O Y X).
Proof. intros. apply z_mem_function_iff. now split. Qed.

Lemma z_subset_product_of_mem_function : forall m (O : zermelo_operations m)
    (f X Y : membership_carrier m),
  membership_rel f (z_function O Y X) ->
  set_model_subset f (z_product O X Y).
Proof. intros. apply z_mem_function_iff in H. exact (proj1 H). Qed.

Lemma z_mem_of_mem_function : forall m (O : zermelo_operations m)
    (f X Y x y : membership_carrier m),
  membership_rel f (z_function O Y X) ->
  membership_rel (z_kpair O x y) f ->
  membership_rel x X /\ membership_rel y Y.
Proof.
  intros m O f X Y x y Hf Hxy.
  pose proof (z_subset_product_of_mem_function Hf) as Hsub.
  apply Hsub in Hxy.
  now apply z_kpair_mem_product_iff in Hxy.
Qed.

Lemma z_function_subset_power_product : forall m (O : zermelo_operations m)
    (X Y : membership_carrier m),
  set_model_subset (z_function O Y X) (z_power O (z_product O X Y)).
Proof.
  intros m O X Y f Hf. apply z_mem_function_iff in Hf.
  apply z_power_mem_iff. exact (proj1 Hf).
Qed.

Lemma z_exists_unique_of_mem_function : forall m (O : zermelo_operations m)
    (f X Y : membership_carrier m),
  membership_rel f (z_function O Y X) ->
  forall x, membership_rel x X ->
    exists y, membership_rel (z_kpair O x y) f /\
      forall y', membership_rel (z_kpair O x y') f -> y' = y.
Proof. intros. apply z_mem_function_iff in H. exact (proj2 H x H0). Qed.

Lemma z_exists_of_mem_function : forall m (O : zermelo_operations m)
    (f X Y x : membership_carrier m),
  membership_rel f (z_function O Y X) -> membership_rel x X ->
  exists y, membership_rel y Y /\ membership_rel (z_kpair O x y) f.
Proof.
  intros m O f X Y x Hf Hx.
  destruct (@z_exists_unique_of_mem_function m O f X Y Hf x Hx)
    as [y [Hy Hunique]].
  exists y. split; [|exact Hy].
  exact (proj2 (@z_mem_of_mem_function m O f X Y x y Hf Hy)).
Qed.

Lemma z_domain_eq_of_mem_function : forall m (O : zermelo_operations m)
    (f X Y : membership_carrier m),
  membership_rel f (z_function O Y X) -> z_domain O f = X.
Proof.
  intros m O f X Y Hf. apply (z_extensionality O). intro x. split.
  - intro Hx. apply z_domain_mem_iff in Hx. destruct Hx as [y Hy].
    exact (proj1 (z_mem_of_mem_function Hf Hy)).
  - intro Hx. apply z_domain_mem_iff. destruct (@z_exists_of_mem_function m O f X Y x Hf Hx)
      as [y [_ Hy]]. now exists y.
Qed.

Lemma z_range_subset_of_mem_function : forall m (O : zermelo_operations m)
    (f X Y : membership_carrier m),
  membership_rel f (z_function O Y X) -> set_model_subset (z_range O f) Y.
Proof.
  intros m O f X Y Hf y Hy. apply z_range_mem_iff in Hy. destruct Hy as [x Hxy].
  exact (proj2 (z_mem_of_mem_function Hf Hxy)).
Qed.

Lemma z_mem_function_range_of_mem_function : forall m (O : zermelo_operations m)
    (f X Y : membership_carrier m),
  membership_rel f (z_function O Y X) ->
  membership_rel f (z_function O (z_range O f) X).
Proof.
  intros m O f X Y Hf. apply z_mem_function_intro.
  - intros p Hpf. pose proof (z_subset_product_of_mem_function Hf) as Hsub.
    pose proof (Hsub p Hpf) as Hp. apply z_product_mem_iff in Hp.
    destruct Hp as [x [Hx [y [Hy Heq]]]]. subst p.
    apply z_kpair_mem_product_iff. split; [exact Hx |].
    exact (@z_mem_range_of_kpair_mem m O f x y Hpf).
  - intros x Hx. destruct (@z_exists_unique_of_mem_function m O f X Y Hf x Hx)
      as [y [Hy Hunique]]. exists y. split; [exact Hy | exact Hunique].
Qed.

Lemma z_mem_function_of_mem_function_of_subset :
  forall m (O : zermelo_operations m) (f X Y1 Y2 : membership_carrier m),
  membership_rel f (z_function O Y1 X) -> set_model_subset Y1 Y2 ->
  membership_rel f (z_function O Y2 X).
Proof.
  intros m O f X Y1 Y2 Hf H12. apply z_mem_function_intro.
  - intros p Hp. pose proof (z_subset_product_of_mem_function Hf) as Hsub.
    apply Hsub in Hp.
    assert (Hprod : set_model_subset (z_product O X Y1)
        (z_product O X Y2)).
    { apply z_product_monotone; [exact (@set_model_subset_refl m X) | exact H12]. }
    exact (Hprod p Hp).
  - intros x Hx. apply (@z_exists_unique_of_mem_function m O f X Y1 Hf x Hx).
Qed.

Lemma z_function_subset_function_of_subset : forall m (O : zermelo_operations m)
    (Y1 Y2 X : membership_carrier m),
  set_model_subset Y1 Y2 ->
  set_model_subset (z_function O Y1 X) (z_function O Y2 X).
Proof.
  intros m O Y1 Y2 X H12 f Hf.
  exact (@z_mem_function_of_mem_function_of_subset m O f X Y1 Y2 Hf H12).
Qed.

Print Assumptions z_mem_function_iff.
Print Assumptions z_domain_eq_of_mem_function.
Print Assumptions z_mem_function_range_of_mem_function.

Definition z_is_function {m} (O : zermelo_operations m)
    (f : membership_carrier m) : Prop :=
  exists X Y, membership_rel f (z_function O Y X).

Lemma z_is_function_iff : forall m (O : zermelo_operations m)
    (f : membership_carrier m),
  z_is_function O f <->
  membership_rel f (z_function O (z_range O f) (z_domain O f)).
Proof.
  intros m O f. split.
  - intros [X [Y Hf]].
    rewrite (z_domain_eq_of_mem_function Hf).
    exact (@z_mem_function_range_of_mem_function m O f X Y Hf).
  - intro Hf. now exists (z_domain O f), (z_range O f).
Qed.

Lemma z_is_function_of_mem : forall m (O : zermelo_operations m)
    (f X Y : membership_carrier m),
  membership_rel f (z_function O Y X) -> z_is_function O f.
Proof. intros. now exists X, Y. Qed.

Lemma z_is_function_mem_function : forall m (O : zermelo_operations m)
    (f : membership_carrier m),
  z_is_function O f ->
  membership_rel f (z_function O (z_range O f) (z_domain O f)).
Proof. intros. apply z_is_function_iff. exact H. Qed.

Lemma z_is_function_mem_kpair : forall m (O : zermelo_operations m)
    (f p : membership_carrier m),
  z_is_function O f -> membership_rel p f ->
  exists x y, p = z_kpair O x y.
Proof.
  intros m O f p Hf Hp. destruct Hf as [X [Y Hf]].
  pose proof (z_subset_product_of_mem_function Hf) as Hsub. apply Hsub in Hp.
  apply z_product_mem_iff in Hp. destruct Hp as [x [_ [y [_ Heq]]]].
  now exists x, y.
Qed.

Lemma z_is_function_unique : forall m (O : zermelo_operations m)
    (f x y1 y2 : membership_carrier m),
  z_is_function O f ->
  membership_rel (z_kpair O x y1) f ->
  membership_rel (z_kpair O x y2) f -> y1 = y2.
Proof.
  intros m O f x y1 y2 Hf H1 H2.
  pose proof (z_is_function_mem_function Hf) as Hrel.
  pose proof (proj1 (@z_mem_function_iff m O f (z_range O f)
    (z_domain O f)) Hrel) as Hmem.
  destruct (proj2 Hmem x (proj1 (z_mem_of_mem_function Hrel H1)))
    as [y [Hy Hunique]].
  now transitivity y; [apply Hunique; exact H1 | symmetry; apply Hunique; exact H2].
Qed.

Lemma z_function_empty_empty : forall m (O : zermelo_operations m),
  z_function O (z_empty O) (z_empty O) = z_singleton O (z_empty O).
Proof.
  intros m O. apply (z_extensionality O). intro f. split.
  - intro Hf. apply z_mem_function_iff in Hf.
    apply z_singleton_mem_iff. apply z_empty_unique.
    intros p Hp. apply (proj1 Hf) in Hp. rewrite z_product_empty_left in Hp.
    now apply (z_not_mem_empty O p Hp).
  - intro Hf. apply z_singleton_mem_iff in Hf. subst f.
    apply z_mem_function_intro.
    + apply z_empty_subset.
    + intros x Hx. exfalso. now apply (z_not_mem_empty O x Hx).
Qed.

Definition z_identity {m} (O : zermelo_operations m)
    (X : membership_carrier m) : membership_carrier m :=
  z_separate O
    (fun p => exists x, membership_rel x X /\ p = z_kpair O x x)
    (z_product O X X).

Lemma z_identity_mem_iff : forall m (O : zermelo_operations m)
    (X p : membership_carrier m),
  membership_rel p (z_identity O X) <->
  exists x, membership_rel x X /\ p = z_kpair O x x.
Proof.
  intros m O X p. unfold z_identity. rewrite z_separate_mem_iff. split.
  - now intros [_ H].
  - intros H. split; [|exact H].
    destruct H as [x [Hx ->]]. apply z_kpair_mem_product_iff. now split.
Qed.

Lemma z_kpair_mem_identity_iff : forall m (O : zermelo_operations m)
    (X x y : membership_carrier m),
  membership_rel (z_kpair O x y) (z_identity O X) <->
  membership_rel x X /\ x = y.
Proof.
  intros m O X x y. split.
  - intro H. apply z_identity_mem_iff in H.
    destruct H as [z [Hz Heq]]. apply z_kpair_injective in Heq.
    now destruct Heq as [-> ->].
  - intros [Hx Heq]. subst y. apply z_identity_mem_iff.
    exists x. now split.
Qed.

Lemma z_identity_mem_function : forall m (O : zermelo_operations m)
    (X : membership_carrier m),
  membership_rel (z_identity O X) (z_function O X X).
Proof.
  intros m O X. apply z_mem_function_intro.
  - intros p Hp. apply z_identity_mem_iff in Hp.
    destruct Hp as [x [Hx ->]]. apply z_kpair_mem_product_iff. now split.
  - intros x Hx. exists x. split; [apply z_identity_mem_iff; now exists x |].
    intros y Hy. apply z_kpair_mem_identity_iff in Hy. now symmetry.
Qed.

Lemma z_identity_is_function : forall m (O : zermelo_operations m)
    (X : membership_carrier m), z_is_function O (z_identity O X).
Proof.
  intros m O X.
  exact (@z_is_function_of_mem m O (z_identity O X) X X
    (@z_identity_mem_function m O X)).
Qed.

Lemma z_identity_injective : forall m (O : zermelo_operations m)
    (X x1 x2 y : membership_carrier m),
  membership_rel (z_kpair O x1 y) (z_identity O X) ->
  membership_rel (z_kpair O x2 y) (z_identity O X) -> x1 = x2.
Proof.
  intros m O X x1 x2 y H1 H2.
  apply z_kpair_mem_identity_iff in H1, H2.
  destruct H1 as [_ H1]. destruct H2 as [_ H2].
  now transitivity y.
Qed.

Print Assumptions z_is_function_iff.
Print Assumptions z_function_empty_empty.
Print Assumptions z_identity_mem_function.
Print Assumptions z_identity_injective.
