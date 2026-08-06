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

Definition z_compose {m} (O : zermelo_operations m)
    (R S : membership_carrier m) : membership_carrier m :=
  z_separate O
    (fun p => exists x y z,
      membership_rel (z_kpair O x y) R /\
      membership_rel (z_kpair O y z) S /\
      p = z_kpair O x z)
    (z_product O (z_domain O R) (z_range O S)).

Lemma z_mem_compose_iff : forall m (O : zermelo_operations m)
    (R S p : membership_carrier m),
  membership_rel p (z_compose O R S) <->
  exists x y z,
    membership_rel (z_kpair O x y) R /\
    membership_rel (z_kpair O y z) S /\
    p = z_kpair O x z.
Proof.
  intros m O R S p. unfold z_compose. rewrite z_separate_mem_iff. split.
  - now intros [_ H].
  - intros H. split; [|exact H].
    destruct H as [x [y [z [Hxy [Hyz ->]]]]].
    apply z_kpair_mem_product_iff. split.
    + exact (@z_mem_domain_of_kpair_mem m O R x y Hxy).
    + exact (@z_mem_range_of_kpair_mem m O S y z Hyz).
Qed.

Lemma z_kpair_mem_compose_iff : forall m (O : zermelo_operations m)
    (R S x z : membership_carrier m),
  membership_rel (z_kpair O x z) (z_compose O R S) <->
  exists y, membership_rel (z_kpair O x y) R /\
    membership_rel (z_kpair O y z) S.
Proof.
  intros m O R S x z. split.
  - intro H. apply z_mem_compose_iff in H.
    destruct H as [x' [y [z' [Hxy [Hyz Heq]]]]].
    apply z_kpair_injective in Heq. destruct Heq as [-> ->]. now exists y.
  - intros [y [Hxy Hyz]]. apply z_mem_compose_iff.
    now exists x, y, z.
Qed.

Lemma z_compose_subset_product : forall m (O : zermelo_operations m)
    (X Y Z R S : membership_carrier m),
  set_model_subset R (z_product O X Y) ->
  set_model_subset S (z_product O Y Z) ->
  set_model_subset (z_compose O R S) (z_product O X Z).
Proof.
  intros m O X Y Z R S HR HS p Hp. apply z_mem_compose_iff in Hp.
  destruct Hp as [x [y [z [Hxy [Hyz ->]]]]].
  apply z_kpair_mem_product_iff. split.
  - exact (proj1 (proj1 (@z_kpair_mem_product_iff m O x y X Y)
      (HR _ Hxy))).
  - exact (proj2 (proj1 (@z_kpair_mem_product_iff m O y z Y Z)
      (HS _ Hyz))).
Qed.

Lemma z_compose_function : forall m (O : zermelo_operations m)
    (X Y Z f g : membership_carrier m),
  membership_rel f (z_function O Y X) ->
  membership_rel g (z_function O Z Y) ->
  membership_rel (z_compose O f g) (z_function O Z X).
Proof.
  intros m O X Y Z f g Hf Hg. apply z_mem_function_intro.
  - exact (@z_compose_subset_product m O X Y Z f g
      (z_subset_product_of_mem_function Hf)
      (z_subset_product_of_mem_function Hg)).
  - intros x Hx.
    destruct (@z_exists_unique_of_mem_function m O f X Y Hf x Hx)
      as [y [Hxy Hfuniq]].
    pose proof (proj2 (@z_mem_of_mem_function m O f X Y x y Hf Hxy)) as HyY.
    pose proof (@z_exists_unique_of_mem_function m O g Y Z Hg y HyY)
      as Hex.
    destruct Hex as [z0 [Hyz Hgunique]].
    exists z0. split; [apply z_kpair_mem_compose_iff; now exists y |].
    intros z' Hz'. apply z_kpair_mem_compose_iff in Hz'.
    destruct Hz' as [y' [Hxy' Hy'z']].
    assert (Hy' : y' = y).
    { apply Hfuniq. exact Hxy'. }
    subst y'.
    exact (Hgunique z' Hy'z').
Qed.

Definition z_injective {m} (O : zermelo_operations m)
    (R : membership_carrier m) : Prop :=
  forall x1 x2 y,
    membership_rel (z_kpair O x1 y) R ->
    membership_rel (z_kpair O x2 y) R -> x1 = x2.

Lemma z_injective_empty : forall m (O : zermelo_operations m),
  z_injective O (z_empty O).
Proof.
  intros m O x1 x2 y H1. exfalso.
  apply (z_not_mem_empty O (z_kpair O x1 y)). exact H1.
Qed.

Lemma z_compose_injective : forall m (O : zermelo_operations m)
    (R S : membership_carrier m),
  z_injective O R -> z_injective O S -> z_injective O (z_compose O R S).
Proof.
  intros m O R S HR HS x1 x2 z H1 H2.
  apply z_kpair_mem_compose_iff in H1, H2.
  destruct H1 as [y1 [Hx1 Hy1]]. destruct H2 as [y2 [Hx2 Hy2]].
  assert (Hy : y1 = y2).
  { apply (HS y1 y2 z); assumption. }
  subst y2.
  exact (HR x1 x2 y1 Hx1 Hx2).
Qed.

Print Assumptions z_mem_compose_iff.
Print Assumptions z_kpair_mem_compose_iff.
Print Assumptions z_compose_function.
Print Assumptions z_compose_injective.

Definition z_value {m} (O : zermelo_operations m)
    (f x : membership_carrier m) : membership_carrier m :=
  z_separate O
    (fun z => exists y, membership_rel z y /\
      membership_rel (z_kpair O x y) f)
    (z_sunion O (z_range O f)).

Lemma z_value_mem_iff : forall m (O : zermelo_operations m)
    (f x z : membership_carrier m),
  membership_rel z (z_value O f x) <->
  membership_rel z (z_sunion O (z_range O f)) /\
  exists y, membership_rel z y /\ membership_rel (z_kpair O x y) f.
Proof.
  intros m O f x z. unfold z_value. apply z_separate_mem_iff.
Qed.

Lemma z_value_eq_of_mem_function : forall m (O : zermelo_operations m)
    (f X Y x : membership_carrier m),
  membership_rel f (z_function O Y X) -> membership_rel x X ->
  exists y, membership_rel (z_kpair O x y) f /\
    z_value O f x = y.
Proof.
  intros m O f X Y x Hf Hx.
  destruct (@z_exists_unique_of_mem_function m O f X Y Hf x Hx)
    as [y [Hxy Hunique]].
  exists y. split; [exact Hxy |]. apply (z_extensionality O). intro z. split.
  - intro Hz. apply z_value_mem_iff in Hz. destruct Hz as [_ [y' [Hzy' Hxy']]].
    assert (Heq : y' = y). { apply Hunique. exact Hxy'. }
    now subst y'.
  - intro Hzy. apply z_value_mem_iff. split.
    + apply z_sunion_mem_iff. exists y. split.
      * exact (@z_mem_range_of_kpair_mem m O f x y Hxy).
      * exact Hzy.
    + now exists y.
Qed.

Lemma z_value_mem_range : forall m (O : zermelo_operations m)
    (f X Y x : membership_carrier m),
  membership_rel f (z_function O Y X) -> membership_rel x X ->
  membership_rel (z_value O f x) (z_range O f).
Proof.
  intros m O f X Y x Hf Hx.
  destruct (z_value_eq_of_mem_function Hf Hx) as [y [Hxy Heq]].
  rewrite Heq. exact (@z_mem_range_of_kpair_mem m O f x y Hxy).
Qed.

Definition z_restrict {m} (O : zermelo_operations m)
    (R A : membership_carrier m) : membership_carrier m :=
  z_inter O R (z_product O A (z_range O R)).

Lemma z_restrict_mem_iff : forall m (O : zermelo_operations m)
    (R A p : membership_carrier m),
  membership_rel p (z_restrict O R A) <->
  membership_rel p R /\
  exists x, membership_rel x A /\ exists y, p = z_kpair O x y.
Proof.
  intros m O R A p. unfold z_restrict. rewrite z_inter_mem_iff. split.
  - intros [HpR HpProd]. apply z_product_mem_iff in HpProd.
    destruct HpProd as [x [Hx [y [Hy Heq]]]].
    split; [exact HpR |]. exists x. split; [exact Hx |]. exists y. exact Heq.
  - intros [HpR [x [Hx [y Heq]]]]. subst p. split; [exact HpR |].
    apply z_kpair_mem_product_iff. split; [exact Hx |].
    exact (@z_mem_range_of_kpair_mem m O R x y HpR).
Qed.

Lemma z_restrict_subset : forall m (O : zermelo_operations m)
    (R A : membership_carrier m),
  set_model_subset (z_restrict O R A) R.
Proof. intros m O R A p Hp. now apply z_restrict_mem_iff in Hp. Qed.

Lemma z_domain_restrict_eq : forall m (O : zermelo_operations m)
    (R A : membership_carrier m),
  z_domain O (z_restrict O R A) =
  z_inter O (z_domain O R) A.
Proof.
  intros m O R A. apply (z_extensionality O). intro x. split.
  - intro Hx. apply z_domain_mem_iff in Hx. destruct Hx as [y Hy].
    apply z_restrict_mem_iff in Hy.
    destruct Hy as [HpR [x' [HxA [y' Heq]]]].
    apply z_kpair_injective in Heq. destruct Heq as [Hxx Hyy].
    apply z_inter_mem_iff. split.
    + exact (@z_mem_domain_of_kpair_mem m O R x y HpR).
    + rewrite <- Hxx in HxA. exact HxA.
  - intro Hx. apply z_inter_mem_iff in Hx. apply z_domain_mem_iff.
    destruct (z_domain_mem_iff O R x) as [Hdom _].
    destruct (Hdom (proj1 Hx)) as [y Hy]. exists y.
    apply z_restrict_mem_iff. split; [exact Hy |].
    exists x. split; [exact (proj2 Hx) |]. exists y. reflexivity.
Qed.

Lemma z_kpair_mem_restrict_iff : forall m (O : zermelo_operations m)
    (R A x y : membership_carrier m),
  membership_rel (z_kpair O x y) (z_restrict O R A) <->
  membership_rel (z_kpair O x y) R /\ membership_rel x A.
Proof.
  intros m O R A x y. split.
  - intro H. apply z_restrict_mem_iff in H. destruct H as [HR [x' [Hx' [y' Heq]]]].
    apply z_kpair_injective in Heq. now destruct Heq as [-> ->].
  - intros [HR Hx]. apply z_restrict_mem_iff. split; [exact HR |].
    exists x. split; [exact Hx |]. exists y. reflexivity.
Qed.

Lemma z_restrict_restrict_eq_restrict_inter : forall m (O : zermelo_operations m)
    (R A B : membership_carrier m),
  z_restrict O (z_restrict O R A) B =
  z_restrict O R (z_inter O A B).
Proof.
  intros m O R A B. apply (z_extensionality O). intro p. split.
  - intro Hp. apply z_restrict_mem_iff in Hp.
    destruct Hp as [HpInner [x [HxB [y Heq]]]].
    apply z_restrict_mem_iff in HpInner.
    destruct HpInner as [HpR [x' [HxA [y' HeqInner]]]].
    assert (Hkp : z_kpair O x y = z_kpair O x' y').
    { rewrite <- Heq. exact HeqInner. }
    apply z_kpair_injective in Hkp. destruct Hkp as [Hxx Hyy].
    subst x'. subst y'.
    subst p. apply z_restrict_mem_iff. split; [exact HpR |].
    exists x. split.
    + apply z_inter_mem_iff. split; [exact HxA | exact HxB].
    + exists y. reflexivity.
  - intro Hp. apply z_restrict_mem_iff in Hp.
    destruct Hp as [HpR [x [HxAB [y Heq]]]].
    apply z_inter_mem_iff in HxAB. destruct HxAB as [HxA HxB].
    subst p. apply z_restrict_mem_iff. split.
    + apply z_restrict_mem_iff. split; [exact HpR |].
      exists x. split; [exact HxA |]. exists y. reflexivity.
    + exists x. split; [exact HxB |]. exists y. reflexivity.
Qed.

Lemma z_restrict_restrict_of_subset : forall m (O : zermelo_operations m)
    (R A B : membership_carrier m),
  set_model_subset B A -> z_restrict O (z_restrict O R A) B = z_restrict O R B.
Proof.
  intros m O R A B HBA. apply (z_extensionality O). intro p. split;
    intro Hp; apply z_restrict_mem_iff in Hp.
  - destruct Hp as [HpInner [x [HxB [y Heq]]]].
    apply z_restrict_mem_iff in HpInner.
    destruct HpInner as [HpR [x' [HxA [y' HeqInner]]]].
    assert (Hkp : z_kpair O x y = z_kpair O x' y').
    { rewrite <- Heq. exact HeqInner. }
    apply z_kpair_injective in Hkp. destruct Hkp as [Hxx Hyy].
    subst x'. subst y'.
    subst p. apply z_restrict_mem_iff. split; [exact HpR |].
    exists x. split; [exact HxB |]. exists y. reflexivity.
  - destruct Hp as [HpR [x [HxB [y Heq]]]]. subst p. apply z_restrict_mem_iff.
    split.
    + apply z_restrict_mem_iff. split; [exact HpR |].
      exists x. split; [exact (HBA x HxB) |]. exists y. reflexivity.
    + exists x. split; [exact HxB |]. exists y. reflexivity.
Qed.

Definition z_image {m} (O : zermelo_operations m)
    (R A : membership_carrier m) : membership_carrier m :=
  z_range O (z_restrict O R A).

Lemma z_image_mem_iff : forall m (O : zermelo_operations m)
    (R A y : membership_carrier m),
  membership_rel y (z_image O R A) <->
  exists x, membership_rel x A /\ membership_rel (z_kpair O x y) R.
Proof.
  intros m O R A y. unfold z_image. rewrite z_range_mem_iff. split.
  - intros [x Hx]. apply z_restrict_mem_iff in Hx.
    destruct Hx as [HpR [x' [HxA [y' Heq]]]]. apply z_kpair_injective in Heq.
    destruct Heq as [Hxx Hyy].
    rewrite <- Hxx in HxA.
    exists x. split; [exact HxA | exact HpR].
  - intros [x [HxA Hxy]]. exists x.
    apply z_restrict_mem_iff. split; [exact Hxy |].
    exists x. split; [exact HxA |]. exists y. reflexivity.
Qed.

Print Assumptions z_value_mem_iff.
Print Assumptions z_value_mem_range.
Print Assumptions z_restrict_mem_iff.
Print Assumptions z_domain_restrict_eq.
Print Assumptions z_restrict_restrict_eq_restrict_inter.
Print Assumptions z_image_mem_iff.
