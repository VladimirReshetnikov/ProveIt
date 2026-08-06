(** Constructive algebra of chosen Zermelo set operations.

    Foundation obtains its operations noncomputably from unique existence in
    a model of Zermelo set theory.  In Coq the useful dependency boundary is
    an explicit operations record: once witnesses and their exact membership
    specifications are supplied, all algebra below is constructive.

    Separation is deliberately available for arbitrary predicates.  A later
    first-order adapter can restrict it to definable predicates without
    changing any proof whose predicate is in that restricted family. *)

From Foundation.FirstOrder.SetTheory Require Import Basic.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

Record zermelo_operations (m : membership_structure) : Type := {
  z_ops_extensional : membership_extensional m;
  z_empty : membership_carrier m;
  z_empty_spec : set_model_is_empty z_empty;
  z_pair : membership_carrier m -> membership_carrier m ->
    membership_carrier m;
  z_pair_spec : forall x y z,
    membership_rel z (z_pair x y) <-> z = x \/ z = y;
  z_sunion : membership_carrier m -> membership_carrier m;
  z_sunion_spec : forall x z,
    membership_rel z (z_sunion x) <->
    exists y, membership_rel y x /\ membership_rel z y;
  z_power : membership_carrier m -> membership_carrier m;
  z_power_spec : forall x z,
    membership_rel z (z_power x) <-> set_model_subset z x;
  z_separate : (membership_carrier m -> Prop) ->
    membership_carrier m -> membership_carrier m;
  z_separate_spec : forall P x z,
    membership_rel z (z_separate P x) <-> membership_rel z x /\ P z;
  z_infinity : membership_carrier m;
  z_infinity_spec :
    (forall e, set_model_is_empty e -> membership_rel e z_infinity) /\
    (forall x, membership_rel x z_infinity ->
      forall successor, set_model_successor successor x ->
        membership_rel successor z_infinity);
  z_foundation_spec :
    forall x : membership_carrier m, @set_model_is_nonempty m x ->
      exists y : membership_carrier m, @membership_rel m y x /\
        forall z : membership_carrier m,
          @membership_rel m z x -> ~ @membership_rel m z y
}.

Arguments z_empty {m} _.
Arguments z_ops_extensional {m} _.
Arguments z_empty_spec {m} _ _.
Arguments z_pair {m} _ _ _.
Arguments z_pair_spec {m} _ _ _ _.
Arguments z_sunion {m} _ _.
Arguments z_sunion_spec {m} _ _ _.
Arguments z_power {m} _ _.
Arguments z_power_spec {m} _ _ _.
Arguments z_separate {m} _ _ _.
Arguments z_separate_spec {m} _ _ _ _.
Arguments z_infinity {m} _.
Arguments z_infinity_spec {m} _.
Arguments z_foundation_spec {m} _ _ _.

Definition z_singleton {m} (O : zermelo_operations m)
    (x : membership_carrier m) : membership_carrier m :=
  z_pair O x x.

Definition z_union {m} (O : zermelo_operations m)
    (x y : membership_carrier m) : membership_carrier m :=
  z_sunion O (z_pair O x y).

Definition z_insert {m} (O : zermelo_operations m)
    (x y : membership_carrier m) : membership_carrier m :=
  z_union O (z_singleton O x) y.

Definition z_sinter {m} (O : zermelo_operations m)
    (x : membership_carrier m) : membership_carrier m :=
  z_separate O
    (fun z => forall y, membership_rel y x -> membership_rel z y)
    (z_sunion O x).

Definition z_inter {m} (O : zermelo_operations m)
    (x y : membership_carrier m) : membership_carrier m :=
  z_separate O (fun z => membership_rel z y) x.

Definition z_sdiff {m} (O : zermelo_operations m)
    (x y : membership_carrier m) : membership_carrier m :=
  z_separate O (fun z => ~ membership_rel z y) x.

Definition z_successor {m} (O : zermelo_operations m)
    (x : membership_carrier m) : membership_carrier m :=
  z_insert O x x.

Lemma z_extensionality : forall m (O : zermelo_operations m)
    (x y : membership_carrier m),
  (forall z : membership_carrier m,
    membership_rel z x <-> membership_rel z y) -> x = y.
Proof. intros m O. exact (z_ops_extensional O). Qed.
Arguments z_extensionality {m} O x y _.

Lemma z_subset_antisym : forall m (O : zermelo_operations m)
    (x y : membership_carrier m),
  set_model_subset x y -> set_model_subset y x -> x = y.
Proof. intros m O. apply set_model_subset_antisym. exact (z_ops_extensional O). Qed.
Arguments z_subset_antisym {m} O x y _ _.

Lemma z_not_mem_empty : forall m (O : zermelo_operations m)
    (x : membership_carrier m),
  ~ membership_rel x (z_empty O).
Proof. intros m O x. exact (z_empty_spec O x). Qed.
Arguments z_not_mem_empty {m} O x _.

Lemma z_empty_unique : forall m (O : zermelo_operations m)
    (x : membership_carrier m),
  set_model_is_empty x -> x = z_empty O.
Proof.
  intros m O x Hempty. apply (z_extensionality O). intro z. split.
  - intro Hz. exact (False_rect _ (Hempty z Hz)).
  - intro Hz. exact (False_rect _ (z_not_mem_empty O z Hz)).
Qed.

Lemma z_eq_empty_or_nonempty :
  (forall P : Prop, P \/ ~ P) ->
  forall m (O : zermelo_operations m) (x : membership_carrier m),
    x = z_empty O \/ set_model_is_nonempty x.
Proof.
  intros Hem m O x.
  destruct (Hem (set_model_is_nonempty x)) as [H | H]; [now right |].
  left. apply z_empty_unique.
  now apply (proj1 (@set_model_not_nonempty_iff_empty m x)).
Qed.

Lemma z_empty_subset : forall m (O : zermelo_operations m)
    (x : membership_carrier m),
  set_model_subset (z_empty O) x.
Proof.
  intros m O x z Hz. now exfalso; apply (z_not_mem_empty O z Hz).
Qed.

Lemma z_subset_empty_iff_eq_empty : forall m (O : zermelo_operations m)
    (x : membership_carrier m),
  set_model_subset x (z_empty O) <-> x = z_empty O.
Proof.
  intros m O x. split.
  - intro H. apply (z_subset_antisym O); [exact H | apply z_empty_subset].
  - intros ->. apply set_model_subset_refl.
Qed.

Lemma z_pair_mem_iff : forall m (O : zermelo_operations m)
    (x y z : membership_carrier m),
  membership_rel z (z_pair O x y) <-> z = x \/ z = y.
Proof. intros. apply z_pair_spec. Qed.

Lemma z_pair_unique : forall m (O : zermelo_operations m)
    (x y p : membership_carrier m),
  (forall z : membership_carrier m,
    membership_rel z p <-> z = x \/ z = y) ->
  p = z_pair O x y.
Proof.
  intros m O x y p Hp. apply (z_extensionality O). intro z.
  rewrite Hp, z_pair_mem_iff. split; trivial.
Qed.

Lemma z_pair_nonempty : forall m (O : zermelo_operations m)
    (x y : membership_carrier m),
  set_model_is_nonempty (z_pair O x y).
Proof.
  intros m O x y. exists x. apply z_pair_mem_iff. now left.
Qed.

Lemma z_singleton_mem_iff : forall m (O : zermelo_operations m)
    (x z : membership_carrier m),
  membership_rel z (z_singleton O x) <-> z = x.
Proof.
  intros. unfold z_singleton. rewrite z_pair_mem_iff. split.
  - intros [H | H]; exact H.
  - intro H. now left.
Qed.

Lemma z_singleton_injective : forall m (O : zermelo_operations m)
    (x y : membership_carrier m),
  z_singleton O x = z_singleton O y -> x = y.
Proof.
  intros m O x y H.
  assert (Hx : membership_rel x (z_singleton O x)).
  { apply z_singleton_mem_iff. reflexivity. }
  rewrite H, z_singleton_mem_iff in Hx. exact Hx.
Qed.

Lemma z_singleton_nonempty : forall m (O : zermelo_operations m)
    (x : membership_carrier m),
  set_model_is_nonempty (z_singleton O x).
Proof.
  intros m O x. exists x. apply z_singleton_mem_iff. reflexivity.
Qed.

Lemma z_singleton_subset_iff_mem : forall m (O : zermelo_operations m)
    (x y : membership_carrier m),
  set_model_subset (z_singleton O x) y <-> membership_rel x y.
Proof.
  intros m O x y. split.
  - intro H. apply H. apply z_singleton_mem_iff. reflexivity.
  - intros Hxy z Hz. apply z_singleton_mem_iff in Hz. now subst.
Qed.

Lemma z_sunion_mem_iff : forall m (O : zermelo_operations m)
    (x z : membership_carrier m),
  membership_rel z (z_sunion O x) <->
  exists y, membership_rel y x /\ membership_rel z y.
Proof. intros. apply z_sunion_spec. Qed.

Lemma z_subset_sunion_of_mem : forall m (O : zermelo_operations m)
    (x y : membership_carrier m),
  membership_rel x y -> set_model_subset x (z_sunion O y).
Proof.
  intros m O x y Hxy z Hz. apply z_sunion_mem_iff.
  exists x. now split.
Qed.

Lemma z_sunion_empty : forall m (O : zermelo_operations m),
  z_sunion O (z_empty O) = z_empty O.
Proof.
  intros m O. apply (z_extensionality O). intro z. split.
  - intros Hz. apply z_sunion_mem_iff in Hz.
    destruct Hz as [y [Hy _]]. now exfalso; apply (z_not_mem_empty O y Hy).
  - intro Hz. now exfalso; apply (z_not_mem_empty O z Hz).
Qed.

Lemma z_sunion_singleton : forall m (O : zermelo_operations m)
    (x : membership_carrier m),
  z_sunion O (z_singleton O x) = x.
Proof.
  intros m O x. apply (z_extensionality O). intro z.
  rewrite z_sunion_mem_iff. split.
  - intros [y [Hy Hz]]. apply z_singleton_mem_iff in Hy. now subst.
  - intro Hz. exists x. split; [apply z_singleton_mem_iff; reflexivity | exact Hz].
Qed.

Lemma z_sunion_nonempty_iff : forall m (O : zermelo_operations m)
    (x : membership_carrier m),
  set_model_is_nonempty (z_sunion O x) <->
  exists y, membership_rel y x /\ set_model_is_nonempty y.
Proof.
  intros m O x. split.
  - intros [z Hz]. apply z_sunion_mem_iff in Hz.
    destruct Hz as [y [Hyx Hzy]]. exists y. split; [exact Hyx | now exists z].
  - intros [y [Hyx [z Hzy]]]. exists z. apply z_sunion_mem_iff.
    exists y. now split.
Qed.

Lemma z_union_mem_iff : forall m (O : zermelo_operations m)
    (x y z : membership_carrier m),
  membership_rel z (z_union O x y) <->
  membership_rel z x \/ membership_rel z y.
Proof.
  intros m O x y z. unfold z_union. rewrite z_sunion_mem_iff.
  split.
  - intros [w [Hw Hzw]]. apply z_pair_mem_iff in Hw.
    destruct Hw as [-> | ->]; [now left | now right].
  - intros [Hz | Hz].
    + exists x. split; [apply z_pair_mem_iff; now left | exact Hz].
    + exists y. split; [apply z_pair_mem_iff; now right | exact Hz].
Qed.

Lemma z_union_comm : forall m (O : zermelo_operations m)
    (x y : membership_carrier m),
  z_union O x y = z_union O y x.
Proof.
  intros. apply (z_extensionality O). intro z.
  rewrite !z_union_mem_iff. tauto.
Qed.

Lemma z_union_assoc : forall m (O : zermelo_operations m)
    (x y z : membership_carrier m),
  z_union O (z_union O x y) z = z_union O x (z_union O y z).
Proof.
  intros. apply (z_extensionality O). intro w.
  rewrite !z_union_mem_iff. tauto.
Qed.

Lemma z_union_self : forall m (O : zermelo_operations m)
    (x : membership_carrier m),
  z_union O x x = x.
Proof.
  intros m O x. apply (z_extensionality O). intro z.
  rewrite z_union_mem_iff. tauto.
Qed.

Lemma z_union_empty_left : forall m (O : zermelo_operations m)
    (x : membership_carrier m),
  z_union O (z_empty O) x = x.
Proof.
  intros. apply (z_extensionality O). intro z.
  rewrite z_union_mem_iff. split.
  - intros [Hz | Hz];
      [now exfalso; apply (z_not_mem_empty O z) | exact Hz].
  - intro Hz. now right.
Qed.

Lemma z_union_empty_right : forall m (O : zermelo_operations m)
    (x : membership_carrier m),
  z_union O x (z_empty O) = x.
Proof. intros. rewrite z_union_comm. apply z_union_empty_left. Qed.

Lemma z_union_nonempty_iff : forall m (O : zermelo_operations m)
    (x y : membership_carrier m),
  set_model_is_nonempty (z_union O x y) <->
  set_model_is_nonempty x \/ set_model_is_nonempty y.
Proof.
  intros m O x y. split.
  - intros [z Hz]. apply z_union_mem_iff in Hz.
    destruct Hz as [Hz | Hz]; [left | right]; now exists z.
  - intros [[z Hz] | [z Hz]]; exists z; apply z_union_mem_iff;
      [now left | now right].
Qed.

Lemma z_subset_union_left : forall m (O : zermelo_operations m)
    (x y : membership_carrier m),
  set_model_subset x (z_union O x y).
Proof. intros m O x y z Hz. apply z_union_mem_iff. now left. Qed.

Lemma z_subset_union_right : forall m (O : zermelo_operations m)
    (x y : membership_carrier m),
  set_model_subset y (z_union O x y).
Proof. intros m O x y z Hz. apply z_union_mem_iff. now right. Qed.

Lemma z_union_eq_iff_right_subset : forall m (O : zermelo_operations m)
    (x y : membership_carrier m),
  z_union O x y = x <-> set_model_subset y x.
Proof.
  intros m O x y. split.
  - intros H z Hz.
    pose proof (@z_subset_union_right m O x y z Hz) as Hunion.
    now rewrite H in Hunion.
  - intro Hyx. apply (z_subset_antisym O).
    + intros z Hz. apply z_union_mem_iff in Hz. destruct Hz; auto.
    + apply z_subset_union_left.
Qed.

Lemma z_union_eq_iff_left_subset : forall m (O : zermelo_operations m)
    (x y : membership_carrier m),
  z_union O x y = y <-> set_model_subset x y.
Proof.
  intros m O x y. rewrite z_union_comm.
  apply z_union_eq_iff_right_subset.
Qed.

Lemma z_insert_mem_iff : forall m (O : zermelo_operations m)
    (x y z : membership_carrier m),
  membership_rel z (z_insert O x y) <-> z = x \/ membership_rel z y.
Proof.
  intros. unfold z_insert. rewrite z_union_mem_iff, z_singleton_mem_iff.
  split; trivial.
Qed.

Lemma z_union_insert : forall m (O : zermelo_operations m)
    (x y z : membership_carrier m),
  z_union O x (z_insert O y z) = z_insert O y (z_union O x z).
Proof.
  intros. apply (z_extensionality O). intro w.
  rewrite z_union_mem_iff, z_insert_mem_iff,
    z_insert_mem_iff, z_union_mem_iff. split.
  - intros [Hwx | [Hwy | Hwz]].
    + right. now left.
    + now left.
    + right. now right.
  - intros [Hwy | [Hwx | Hwz]].
    + right. now left.
    + now left.
    + right. now right.
Qed.

Lemma z_insert_empty : forall m (O : zermelo_operations m)
    (x : membership_carrier m),
  z_insert O x (z_empty O) = z_singleton O x.
Proof. intros. unfold z_insert. apply z_union_empty_right. Qed.

Lemma z_insert_nonempty : forall m (O : zermelo_operations m)
    (x y : membership_carrier m),
  set_model_is_nonempty (z_insert O x y).
Proof.
  intros m O x y. exists x. apply z_insert_mem_iff. now left.
Qed.

Lemma z_subset_insert : forall m (O : zermelo_operations m)
    (x y : membership_carrier m),
  set_model_subset y (z_insert O x y).
Proof. intros m O x y z Hz. apply z_insert_mem_iff. now right. Qed.

Lemma z_sunion_insert : forall m (O : zermelo_operations m)
    (x y : membership_carrier m),
  z_sunion O (z_insert O x y) = z_union O x (z_sunion O y).
Proof.
  intros m O x y. apply (z_extensionality O). intro z.
  rewrite z_sunion_mem_iff, z_union_mem_iff. split.
  - intros [w [Hw Hzw]]. apply z_insert_mem_iff in Hw.
    destruct Hw as [-> | Hw]; [now left | right].
    apply z_sunion_mem_iff. exists w. now split.
  - intros [Hzx | Hz].
    + exists x. split; [apply z_insert_mem_iff; now left | exact Hzx].
    + apply z_sunion_mem_iff in Hz. destruct Hz as [w [Hw Hzw]].
      exists w. split; [apply z_insert_mem_iff; now right | exact Hzw].
Qed.

Lemma z_insert_union : forall m (O : zermelo_operations m)
    (x y z : membership_carrier m),
  z_union O (z_insert O x y) z = z_insert O x (z_union O y z).
Proof.
  intros m O x y z. apply (z_extensionality O). intro w.
  rewrite z_union_mem_iff, z_insert_mem_iff,
    z_insert_mem_iff, z_union_mem_iff. tauto.
Qed.

Lemma z_power_mem_iff : forall m (O : zermelo_operations m)
    (x z : membership_carrier m),
  membership_rel z (z_power O x) <-> set_model_subset z x.
Proof. intros. apply z_power_spec. Qed.

Lemma z_power_unique : forall m (O : zermelo_operations m)
    (x p : membership_carrier m),
  (forall z : membership_carrier m,
    membership_rel z p <-> set_model_subset z x) ->
  p = z_power O x.
Proof.
  intros m O x p Hp. apply (z_extensionality O). intro z.
  rewrite Hp, z_power_mem_iff. split; trivial.
Qed.

Lemma z_separate_mem_iff : forall m (O : zermelo_operations m)
    (P : membership_carrier m -> Prop) (x z : membership_carrier m),
  membership_rel z (z_separate O P x) <-> membership_rel z x /\ P z.
Proof. intros. apply z_separate_spec. Qed.

Lemma z_separate_subset : forall m (O : zermelo_operations m)
    (P : membership_carrier m -> Prop) (x : membership_carrier m),
  set_model_subset (z_separate O P x) x.
Proof. intros m O P x z Hz. now apply z_separate_mem_iff in Hz. Qed.

Lemma z_sinter_mem_iff : forall m (O : zermelo_operations m)
    (x z : membership_carrier m),
  membership_rel z (z_sinter O x) <->
  set_model_is_nonempty x /\
  forall y, membership_rel y x -> membership_rel z y.
Proof.
  intros m O x z. unfold z_sinter. rewrite z_separate_mem_iff,
    z_sunion_mem_iff. split.
  - intros [[y [Hyx Hzy]] Hall]. split.
    + now exists y.
    + exact Hall.
  - intros [[y Hyx] Hall]. split.
    + exists y. split; [exact Hyx | now apply Hall].
    + exact Hall.
Qed.

Lemma z_sinter_subset_of_mem : forall m (O : zermelo_operations m)
    (x y : membership_carrier m),
  membership_rel x y -> set_model_subset (z_sinter O y) x.
Proof.
  intros m O x y Hxy z Hz. apply z_sinter_mem_iff in Hz.
  now apply (proj2 Hz x).
Qed.

Lemma z_inter_mem_iff : forall m (O : zermelo_operations m)
    (x y z : membership_carrier m),
  membership_rel z (z_inter O x y) <->
  membership_rel z x /\ membership_rel z y.
Proof.
  intros m O x y z. unfold z_inter.
  exact (z_separate_spec O (fun w => membership_rel w y) x z).
Qed.

Lemma z_inter_comm : forall m (O : zermelo_operations m)
    (x y : membership_carrier m),
  z_inter O x y = z_inter O y x.
Proof.
  intros. apply (z_extensionality O). intro z.
  rewrite !z_inter_mem_iff. tauto.
Qed.

Lemma z_inter_assoc : forall m (O : zermelo_operations m)
    (x y z : membership_carrier m),
  z_inter O (z_inter O x y) z = z_inter O x (z_inter O y z).
Proof.
  intros. apply (z_extensionality O). intro w.
  rewrite !z_inter_mem_iff. tauto.
Qed.

Lemma z_inter_subset_left : forall m (O : zermelo_operations m)
    (x y : membership_carrier m),
  set_model_subset (z_inter O x y) x.
Proof. intros m O x y z Hz. now apply z_inter_mem_iff in Hz. Qed.

Lemma z_inter_subset_right : forall m (O : zermelo_operations m)
    (x y : membership_carrier m),
  set_model_subset (z_inter O x y) y.
Proof. intros m O x y z Hz. now apply z_inter_mem_iff in Hz. Qed.

Lemma z_sdiff_mem_iff : forall m (O : zermelo_operations m)
    (x y z : membership_carrier m),
  membership_rel z (z_sdiff O x y) <->
  membership_rel z x /\ ~ membership_rel z y.
Proof.
  intros m O x y z. unfold z_sdiff.
  exact (z_separate_spec O (fun w => ~ membership_rel w y) x z).
Qed.

Lemma z_sdiff_subset : forall m (O : zermelo_operations m)
    (x y : membership_carrier m),
  set_model_subset (z_sdiff O x y) x.
Proof. intros m O x y z Hz. now apply z_sdiff_mem_iff in Hz. Qed.

Lemma z_strict_subset_iff_difference_witness :
  (forall P : Prop, P \/ ~ P) ->
  forall m (O : zermelo_operations m)
    (x y : membership_carrier m),
  set_model_strict_subset x y <->
  set_model_subset x y /\
  exists z, membership_rel z y /\ ~ membership_rel z x.
Proof.
  intros Hem m O x y. split.
  - intros [Hxy Hneq]. split; [exact Hxy |].
    destruct (Hem (exists z, membership_rel z y /\ ~ membership_rel z x))
      as [H | H]; [exact H |].
    exfalso. apply Hneq. apply (z_subset_antisym O); [exact Hxy |].
    intros z Hzy.
    destruct (Hem (membership_rel z x)) as [Hzx | Hzx]; [exact Hzx |].
    exfalso. apply H. exists z. now split.
  - intros [Hxy [z [Hzy Hnzx]]]. split; [exact Hxy |].
    intro H. apply Hnzx. now rewrite H.
Qed.

Lemma z_sdiff_nonempty_of_strict_subset :
  (forall P : Prop, P \/ ~ P) ->
  forall m (O : zermelo_operations m)
    (x y : membership_carrier m),
  set_model_strict_subset x y ->
  set_model_is_nonempty (z_sdiff O y x).
Proof.
  intros Hem m O x y Hstrict.
  apply (proj1 (z_strict_subset_iff_difference_witness Hem O x y)) in Hstrict.
  destruct Hstrict as [_ [z [Hzy Hnzx]]]. exists z.
  apply z_sdiff_mem_iff. now split.
Qed.

Lemma z_successor_mem_iff : forall m (O : zermelo_operations m)
    (x y : membership_carrier m),
  membership_rel y (z_successor O x) <-> y = x \/ membership_rel y x.
Proof. intros. unfold z_successor. apply z_insert_mem_iff. Qed.

Lemma z_successor_is_successor : forall m (O : zermelo_operations m)
    (x : membership_carrier m),
  set_model_successor (z_successor O x) x.
Proof. intros m O x y. apply z_successor_mem_iff. Qed.

(** The operations record realizes the semantic Zermelo axiom family. *)
Theorem zermelo_operations_model : forall m (O : zermelo_operations m),
  @set_theory_model m zermelo_axiom.
Proof.
  intros m O a Ha. destruct Ha; simpl.
  - exact I.
  - exists (z_empty O). exact (z_empty_spec O).
  - exact (z_ops_extensional O).
  - intros x y. exists (z_pair O x y). apply z_pair_spec.
  - intro x. exists (z_sunion O x). apply z_sunion_spec.
  - intro x. exists (z_power O x). apply z_power_spec.
  - exists (z_infinity O). exact (z_infinity_spec O).
  - exact (z_foundation_spec O).
  - intro x. exists (z_separate O P x). apply z_separate_spec.
Qed.

Print Assumptions z_union_assoc.
Print Assumptions z_sinter_mem_iff.
Print Assumptions z_strict_subset_iff_difference_witness.
Print Assumptions zermelo_operations_model.
