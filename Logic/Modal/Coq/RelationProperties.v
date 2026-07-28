(**
  Generic relation iteration, closures, and elementary properties.

  This module ports the complete active mathematical surface of the pinned
  Foundation modules

    Vorspiel/Rel/{Basic,Coreflexive,Serial,Euclidean,Convergent,Connected,
                  Equality,Isolated,Universal}.lean.

  Foundation presents relation properties twice: first as predicates and then
  as one-field classes, with most implications registered as type-class
  instances.  In Rocq the predicate is the useful mathematical interface, so
  each predicate/class pair is represented once and every substantive
  instance becomes an ordinary named lemma.  Positive naturals are represented
  by a natural number together with a strict-positivity premise.

  [rel_iter] is the existing Foundation-modal path relation.  Likewise,
  [relation_reflexive_closure], [relation_positive_closure], and
  [relation_reflexive_transitive_closure] are reused from [FrameProperties].
  This avoids parallel closure encodings while retaining the exact pointwise
  theorem content of the source.
*)

From Stdlib Require Import Arith.PeanoNat Lia.
From Stdlib Require Import Relations.Relation_Definitions.
From FoundationModal Require Import Kripke FrameProperties.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

(** * Iterated relations *)

(** Foundation's [Rel.Iterate.iff_zero] and [iff_succ] are already
    [rel_iter_zero] and [rel_iter_succ]. *)

Lemma rel_iter_positive_succ_iff :
  forall (A : Type) (R : A -> A -> Prop) n x y,
    0 < n ->
    (rel_iter R n x y <->
     exists z, R x z /\ rel_iter R (Nat.pred n) z y).
Proof.
  intros A R [|n] x y Hpos; [lia |].
  simpl. reflexivity.
Qed.

Lemma rel_iter_succ_left :
  forall (A : Type) (R : A -> A -> Prop) n x z y,
    R x z -> rel_iter R n z y -> rel_iter R (S n) x y.
Proof. exact rel_iter_step_left. Qed.

(** Foundation states this as equality of relation-valued functions.  The
    pointwise iff is the extensional Coq presentation. *)
Lemma rel_iter_equality_iff :
  forall (A : Type) n (x y : A),
    rel_iter (@eq A) n x y <-> x = y.
Proof.
  intros A n; induction n as [|n IH]; intros x y; simpl.
  - reflexivity.
  - split.
    + intros [z [Hxz Hzy]]. subst z. now apply IH in Hzy.
    + intro Hxy. subst y. exists x; split; [reflexivity |].
      now apply IH.
Qed.

Lemma rel_iter_succ_right_iff :
  forall (A : Type) (R : A -> A -> Prop) n x y,
    rel_iter R (S n) x y <->
    exists z, rel_iter R n x z /\ R z y.
Proof.
  intros A R n x y.
  replace (S n) with (n + 1) by lia.
  rewrite rel_iter_plus.
  split.
  - intros [z [Hxz Hzy]].
    exists z; split; [exact Hxz |].
    now apply (proj1 (rel_iter_one R z y)).
  - intros [z [Hxz Rzy]].
    exists z; split; [exact Hxz |].
    now apply (proj2 (rel_iter_one R z y)).
Qed.

Lemma rel_iter_true_of_eq :
  forall (A : Type) n (x y : A),
    x = y -> rel_iter (fun _ _ : A => True) n x y.
Proof.
  intros A n; induction n as [|n IH]; intros x y Hxy; subst y; simpl.
  - reflexivity.
  - exists x; split; [constructor |]. now apply IH.
Qed.

Lemma rel_iter_congr_index :
  forall (A : Type) (R : A -> A -> Prop) n m x y,
    rel_iter R n x y -> n = m -> rel_iter R m x y.
Proof. intros A R n m x y H ->; exact H. Qed.

Lemma rel_iter_comp_iff :
  forall (A : Type) (R : A -> A -> Prop) n m x y,
    (exists z, rel_iter R n x z /\ rel_iter R m z y) <->
    rel_iter R (n + m) x y.
Proof.
  intros A R n m x y. symmetry. apply rel_iter_plus.
Qed.

(** This is the positive-natural version of Foundation's
    [Iterate.unwrap_of_trans]. *)
Lemma rel_iter_unwrap_transitive_succ :
  forall (A : Type) (R : A -> A -> Prop),
    transitive A R ->
    forall n x y, rel_iter R (S n) x y -> R x y.
Proof.
  intros A R Htrans n x y Hxy.
  exact (@rel_iter_collapse_of_transitive A R Htrans
    (S n) x y (Nat.lt_0_succ n) Hxy).
Qed.

Lemma rel_iter_unwrap_transitive_positive :
  forall (A : Type) (R : A -> A -> Prop),
    transitive A R ->
    forall n x y, 0 < n -> rel_iter R n x y -> R x y.
Proof. exact rel_iter_collapse_of_transitive. Qed.

Lemma rel_iter_unwrap_reflexive_transitive :
  forall (A : Type) (R : A -> A -> Prop),
    reflexive A R -> transitive A R ->
    forall n x y, rel_iter R n x y -> R x y.
Proof.
  intros A R Hrefl Htrans [|n] x y Hxy.
  - simpl in Hxy. subst y. apply Hrefl.
  - exact (@rel_iter_unwrap_transitive_succ A R Htrans n x y Hxy).
Qed.

Lemma rel_iter_prefix_transitive_positive :
  forall (A : Type) (R : A -> A -> Prop),
    transitive A R ->
    forall n z x y,
      0 < n -> R z x -> rel_iter R n x y -> rel_iter R n z y.
Proof.
  intros A R Htrans [|n] z x y Hpos Rzx Hxy; [lia |].
  simpl in Hxy |- *.
  destruct Hxy as [w [Rxw Hwy]].
  exists w; split; [exact (Htrans z x w Rzx Rxw) | exact Hwy].
Qed.

(** * Reflexive closure *)

Lemma relation_refl_gen_reflexive :
  forall (A : Type) (R : A -> A -> Prop),
    reflexive A (relation_reflexive_closure R).
Proof. intros A R x; apply reflexive_closure_refl. Qed.

Lemma relation_refl_gen_transitive :
  forall (A : Type) (R : A -> A -> Prop),
    transitive A R ->
    transitive A (relation_reflexive_closure R).
Proof. exact reflexive_closure_transitive. Qed.

Lemma relation_refl_gen_symmetric :
  forall (A : Type) (R : A -> A -> Prop),
    symmetric A R ->
    symmetric A (relation_reflexive_closure R).
Proof. exact reflexive_closure_symmetric. Qed.

Definition relation_irreflexive {A : Type}
    (R : A -> A -> Prop) : Prop :=
  forall x, ~ R x x.

Lemma relation_refl_gen_antisymmetric :
  forall (A : Type) (R : A -> A -> Prop),
    relation_irreflexive R -> transitive A R ->
    antisymmetric A (relation_reflexive_closure R).
Proof.
  intros A R Hirrefl Htrans x y Hxy Hyx.
  destruct Hxy as [Hxy | Rxy]; [exact Hxy |].
  destruct Hyx as [Hyx | Ryx]; [now symmetry |].
  exfalso. exact (Hirrefl x (Htrans x y x Rxy Ryx)).
Qed.

Definition relation_partial_order {A : Type}
    (R : A -> A -> Prop) : Prop :=
  reflexive A R /\ antisymmetric A R /\ transitive A R.

Lemma relation_refl_gen_partial_order :
  forall (A : Type) (R : A -> A -> Prop),
    relation_irreflexive R -> transitive A R ->
    relation_partial_order (relation_reflexive_closure R).
Proof.
  intros A R Hirrefl Htrans.
  split; [apply relation_refl_gen_reflexive |].
  split.
  - now apply relation_refl_gen_antisymmetric.
  - now apply relation_refl_gen_transitive.
Qed.

(** * Positive/transitive closure *)

Lemma relation_trans_gen_transitive :
  forall (A : Type) (R : A -> A -> Prop),
    transitive A (relation_positive_closure R).
Proof. exact positive_closure_transitive. Qed.

Lemma relation_trans_gen_trans :
  forall (A : Type) (R : A -> A -> Prop) x y z,
    relation_positive_closure R x y ->
    relation_positive_closure R y z ->
    relation_positive_closure R x z.
Proof. exact positive_closure_transitive. Qed.

Lemma relation_trans_gen_single :
  forall (A : Type) (R : A -> A -> Prop) x y,
    R x y -> relation_positive_closure R x y.
Proof. exact positive_closure_base. Qed.

Lemma relation_trans_gen_head :
  forall (A : Type) (R : A -> A -> Prop) x y z,
    R x y -> relation_positive_closure R y z ->
    relation_positive_closure R x z.
Proof.
  intros A R x y z Rxy Hyz.
  exact (@positive_closure_transitive A R x y z
    (@positive_closure_base A R x y Rxy) Hyz).
Qed.

Lemma relation_trans_gen_tail :
  forall (A : Type) (R : A -> A -> Prop) x y z,
    relation_positive_closure R x y -> R y z ->
    relation_positive_closure R x z.
Proof.
  intros A R x y z Hxy Ryz.
  exact (@positive_closure_transitive A R x y z Hxy
    (@positive_closure_base A R y z Ryz)).
Qed.

Lemma relation_trans_gen_exists_iterate :
  forall (A : Type) (R : A -> A -> Prop) x y,
    relation_positive_closure R x y <->
    exists n, 0 < n /\ rel_iter R n x y.
Proof. reflexivity. Qed.

Lemma relation_trans_gen_remove_iterate :
  forall (A : Type) (R : A -> A -> Prop) n x y,
    0 < n ->
    rel_iter (relation_positive_closure R) n x y ->
    relation_positive_closure R x y.
Proof.
  intros A R n x y Hpos Hxy.
  eapply rel_iter_collapse_of_transitive; eauto.
  apply positive_closure_transitive.
Qed.

Lemma relation_trans_gen_unwrap :
  forall (A : Type) (R : A -> A -> Prop),
    transitive A R ->
    forall x y, relation_positive_closure R x y -> R x y.
Proof.
  intros A R Htrans x y Hxy.
  now apply (proj1 (positive_closure_of_transitive_iff Htrans x y)).
Qed.

Lemma relation_trans_gen_unwrap_iff :
  forall (A : Type) (R : A -> A -> Prop),
    transitive A R ->
    forall x y, relation_positive_closure R x y <-> R x y.
Proof. exact positive_closure_of_transitive_iff. Qed.

Lemma relation_trans_gen_reflexive :
  forall (A : Type) (R : A -> A -> Prop),
    reflexive A R -> reflexive A (relation_positive_closure R).
Proof. intros A R Hrefl x; apply positive_closure_base, Hrefl. Qed.

Lemma relation_trans_gen_symmetric :
  forall (A : Type) (R : A -> A -> Prop),
    symmetric A R -> symmetric A (relation_positive_closure R).
Proof. exact positive_closure_symmetric. Qed.

Lemma relation_trans_gen_antisymmetric :
  forall (A : Type) (R : A -> A -> Prop),
    transitive A R -> antisymmetric A R ->
    antisymmetric A (relation_positive_closure R).
Proof.
  intros A R Htrans Hanti x y Hxy Hyx.
  apply Hanti.
  - now apply (relation_trans_gen_unwrap Htrans).
  - now apply (relation_trans_gen_unwrap Htrans).
Qed.

(** * Reflexive-transitive closure *)

Lemma relation_refl_trans_gen_reflexive :
  forall (A : Type) (R : A -> A -> Prop),
    reflexive A (relation_reflexive_transitive_closure R).
Proof. intros A R x; apply rtc_refl. Qed.

Lemma relation_refl_trans_gen_transitive :
  forall (A : Type) (R : A -> A -> Prop),
    transitive A (relation_reflexive_transitive_closure R).
Proof. exact rtc_transitive. Qed.

Lemma relation_refl_trans_gen_exists_iterate :
  forall (A : Type) (R : A -> A -> Prop) x y,
    relation_reflexive_transitive_closure R x y <->
    exists n, rel_iter R n x y.
Proof. reflexivity. Qed.

Lemma relation_refl_trans_gen_remove_iterate :
  forall (A : Type) (R : A -> A -> Prop) n x y,
    rel_iter (relation_reflexive_transitive_closure R) n x y ->
    relation_reflexive_transitive_closure R x y.
Proof.
  intros A R n x y Hxy.
  eapply rel_iter_unwrap_reflexive_transitive; eauto.
  - apply relation_refl_trans_gen_reflexive.
  - apply relation_refl_trans_gen_transitive.
Qed.

Lemma relation_refl_trans_gen_unwrap :
  forall (A : Type) (R : A -> A -> Prop),
    reflexive A R -> transitive A R ->
    forall x y, relation_reflexive_transitive_closure R x y -> R x y.
Proof.
  intros A R Hrefl Htrans x y [n Hxy].
  exact (@rel_iter_unwrap_reflexive_transitive A R Hrefl Htrans
    n x y Hxy).
Qed.

Lemma relation_refl_trans_gen_symmetric :
  forall (A : Type) (R : A -> A -> Prop),
    symmetric A R ->
    symmetric A (relation_reflexive_transitive_closure R).
Proof. exact rtc_symmetric. Qed.

(** * Irreflexive generator *)

Definition relation_irreflexive_generator {A : Type}
    (R : A -> A -> Prop) : A -> A -> Prop :=
  fun x y => R x y /\ x <> y.

Lemma relation_irreflexive_generator_irreflexive :
  forall (A : Type) (R : A -> A -> Prop),
    relation_irreflexive (relation_irreflexive_generator R).
Proof. intros A R x [_ Hneq]; exact (Hneq eq_refl). Qed.

Lemma relation_irreflexive_generator_transitive :
  forall (A : Type) (R : A -> A -> Prop),
    transitive A R -> antisymmetric A R ->
    transitive A (relation_irreflexive_generator R).
Proof.
  intros A R Htrans Hanti x y z [Rxy Hxy] [Ryz Hyz].
  split; [exact (Htrans x y z Rxy Ryz) |].
  intro Hxz; subst z.
  apply Hxy. now apply (Hanti x y Rxy Ryz).
Qed.

Definition relation_strict_order {A : Type}
    (R : A -> A -> Prop) : Prop :=
  relation_irreflexive R /\ transitive A R.

Lemma relation_irreflexive_generator_strict_order :
  forall (A : Type) (R : A -> A -> Prop),
    relation_partial_order R ->
    relation_strict_order (relation_irreflexive_generator R).
Proof.
  intros A R [_ [Hanti Htrans]]. split.
  - apply relation_irreflexive_generator_irreflexive.
  - now apply relation_irreflexive_generator_transitive.
Qed.

(** * Coreflexive and equality relations *)

Definition relation_coreflexive {A : Type}
    (R : A -> A -> Prop) : Prop :=
  forall x y, R x y -> x = y.

Lemma relation_coreflexive_of_symmetric_antisymmetric :
  forall (A : Type) (R : A -> A -> Prop),
    symmetric A R -> antisymmetric A R -> relation_coreflexive R.
Proof.
  intros A R Hsym Hanti x y Rxy.
  exact (Hanti x y Rxy (Hsym x y Rxy)).
Qed.

Lemma relation_coreflexive_transitive :
  forall (A : Type) (R : A -> A -> Prop),
    relation_coreflexive R -> transitive A R.
Proof.
  intros A R Hcore x y z Rxy Ryz.
  pose proof (Hcore x y Rxy) as Hxy.
  pose proof (Hcore y z Ryz) as Hyz.
  subst y; subst z. exact Rxy.
Qed.

Lemma relation_coreflexive_symmetric :
  forall (A : Type) (R : A -> A -> Prop),
    relation_coreflexive R -> symmetric A R.
Proof.
  intros A R Hcore x y Rxy.
  destruct (Hcore x y Rxy). exact Rxy.
Qed.

Lemma relation_eq_coreflexive :
  forall A : Type, relation_coreflexive (@eq A).
Proof. intros A x y Hxy; exact Hxy. Qed.

Definition relation_equality {A : Type}
    (R : A -> A -> Prop) : Prop :=
  reflexive A R /\ relation_coreflexive R.

Lemma relation_equality_iff :
  forall (A : Type) (R : A -> A -> Prop),
    relation_equality R -> forall x y, R x y <-> x = y.
Proof.
  intros A R [Hrefl Hcore] x y; split.
  - apply Hcore.
  - intro Hxy; subst y; apply Hrefl.
Qed.

Lemma relation_equality_symmetric :
  forall (A : Type) (R : A -> A -> Prop),
    relation_equality R -> symmetric A R.
Proof. intros A R [_ Hcore]; now apply relation_coreflexive_symmetric. Qed.

Lemma relation_equality_antisymmetric :
  forall (A : Type) (R : A -> A -> Prop),
    relation_equality R -> antisymmetric A R.
Proof. intros A R [_ Hcore] x y Rxy _; now apply Hcore in Rxy. Qed.

Lemma relation_equality_transitive :
  forall (A : Type) (R : A -> A -> Prop),
    relation_equality R -> transitive A R.
Proof. intros A R [_ Hcore]; now apply relation_coreflexive_transitive. Qed.

Definition relation_piecewise_strongly_connected {A : Type}
    (R : A -> A -> Prop) : Prop :=
  forall x y z, R x y -> R x z -> R y z \/ R z y.

Lemma relation_equality_piecewise_strongly_connected :
  forall (A : Type) (R : A -> A -> Prop),
    relation_equality R -> relation_piecewise_strongly_connected R.
Proof.
  intros A R Heq x y z Rxy Rxz.
  apply (relation_equality_iff Heq) in Rxy.
  apply (relation_equality_iff Heq) in Rxz.
  subst y; subst z. left.
  apply (proj2 (relation_equality_iff Heq x x)). reflexivity.
Qed.

Lemma relation_eq_is_equality :
  forall A : Type, relation_equality (@eq A).
Proof.
  intro A; split.
  - intro x; reflexivity.
  - apply relation_eq_coreflexive.
Qed.

(** * Serial and Euclidean relations *)

Definition relation_serial {A : Type}
    (R : A -> A -> Prop) : Prop :=
  forall x, exists y, R x y.

Lemma relation_reflexive_serial :
  forall (A : Type) (R : A -> A -> Prop),
    reflexive A R -> relation_serial R.
Proof. intros A R Hrefl x; exists x; apply Hrefl. Qed.

Lemma relation_reflexive_of_symmetric_transitive_serial :
  forall (A : Type) (R : A -> A -> Prop),
    symmetric A R -> transitive A R -> relation_serial R ->
    reflexive A R.
Proof.
  intros A R Hsym Htrans Hserial x.
  destruct (Hserial x) as [y Rxy].
  exact (Htrans x y x Rxy (Hsym x y Rxy)).
Qed.

Definition relation_right_euclidean {A : Type}
    (R : A -> A -> Prop) : Prop :=
  forall x y z, R x y -> R x z -> R y z.

Definition relation_left_euclidean {A : Type}
    (R : A -> A -> Prop) : Prop :=
  forall x y z, R y x -> R z x -> R y z.

Lemma relation_right_euclidean_of_symmetric_transitive :
  forall (A : Type) (R : A -> A -> Prop),
    symmetric A R -> transitive A R -> relation_right_euclidean R.
Proof.
  intros A R Hsym Htrans x y z Rxy Rxz.
  exact (Htrans y x z (Hsym x y Rxy) Rxz).
Qed.

Lemma relation_symmetric_of_reflexive_right_euclidean :
  forall (A : Type) (R : A -> A -> Prop),
    reflexive A R -> relation_right_euclidean R -> symmetric A R.
Proof.
  intros A R Hrefl Heucl x y Rxy.
  exact (Heucl x y x Rxy (Hrefl x)).
Qed.

Lemma relation_transitive_of_symmetric_right_euclidean :
  forall (A : Type) (R : A -> A -> Prop),
    symmetric A R -> relation_right_euclidean R -> transitive A R.
Proof.
  intros A R Hsym Heucl x y z Rxy Ryz.
  apply Hsym. exact (Heucl y z x Ryz (Hsym x y Rxy)).
Qed.

Lemma relation_transitive_of_reflexive_right_euclidean :
  forall (A : Type) (R : A -> A -> Prop),
    reflexive A R -> relation_right_euclidean R -> transitive A R.
Proof.
  intros A R Hrefl Heucl.
  apply relation_transitive_of_symmetric_right_euclidean; [|exact Heucl].
  now apply relation_symmetric_of_reflexive_right_euclidean.
Qed.

(** * Convergence *)

Definition relation_convergent {A : Type}
    (R : A -> A -> Prop) : Prop :=
  forall x y, x <> y -> exists u, R x u /\ R y u.

Definition relation_strongly_convergent {A : Type}
    (R : A -> A -> Prop) : Prop :=
  forall x y, exists u, R x u /\ R y u.

Lemma relation_strongly_convergent_convergent :
  forall (A : Type) (R : A -> A -> Prop),
    relation_strongly_convergent R -> relation_convergent R.
Proof. intros A R H x y _; apply H. Qed.

Definition relation_piecewise_convergent {A : Type}
    (R : A -> A -> Prop) : Prop :=
  forall x y z,
    R x y -> R x z -> y <> z ->
    exists u, R y u /\ R z u.

Definition relation_piecewise_strongly_convergent {A : Type}
    (R : A -> A -> Prop) : Prop :=
  forall x y z,
    R x y -> R x z -> exists u, R y u /\ R z u.

Lemma relation_piecewise_strongly_convergent_convergent :
  forall (A : Type) (R : A -> A -> Prop),
    relation_piecewise_strongly_convergent R ->
    relation_piecewise_convergent R.
Proof. intros A R H x y z Rxy Rxz _; now apply (H x y z). Qed.

(** * Connectedness *)

Definition relation_piecewise_connected {A : Type}
    (R : A -> A -> Prop) : Prop :=
  forall x y z,
    R x y -> R x z -> R y z \/ y = z \/ R z y.

Lemma relation_piecewise_connected_distinct :
  forall (A : Type) (R : A -> A -> Prop),
    relation_piecewise_connected R ->
    forall x y z,
      R x y -> R x z -> y <> z -> R y z \/ R z y.
Proof.
  intros A R H x y z Rxy Rxz Hneq.
  destruct (H x y z Rxy Rxz) as [Ryz | [Hyz | Rzy]]; auto.
  contradiction.
Qed.

Lemma relation_piecewise_connected_of_trichotomous :
  forall (A : Type) (R : A -> A -> Prop),
    (forall y z, R y z \/ y = z \/ R z y) ->
    relation_piecewise_connected R.
Proof. intros A R H x y z _ _; apply H. Qed.

Lemma relation_piecewise_connected_of_right_euclidean :
  forall (A : Type) (R : A -> A -> Prop),
    relation_right_euclidean R -> relation_piecewise_connected R.
Proof.
  intros A R Heucl x y z Rxy Rxz. left.
  now apply (Heucl x y z).
Qed.

Lemma relation_piecewise_strongly_connected_of_total :
  forall (A : Type) (R : A -> A -> Prop),
    (forall y z, R y z \/ R z y) ->
    relation_piecewise_strongly_connected R.
Proof. intros A R H x y z _ _; apply H. Qed.

Lemma relation_piecewise_strongly_connected_of_reflexive_connected :
  forall (A : Type) (R : A -> A -> Prop),
    reflexive A R -> relation_piecewise_connected R ->
    relation_piecewise_strongly_connected R.
Proof.
  intros A R Hrefl Hconnected x y z Rxy Rxz.
  destruct (Hconnected x y z Rxy Rxz) as [Ryz | [Hyz | Rzy]].
  - now left.
  - subst z. left. apply Hrefl.
  - now right.
Qed.

Lemma relation_piecewise_connected_of_strongly_connected :
  forall (A : Type) (R : A -> A -> Prop),
    relation_piecewise_strongly_connected R ->
    relation_piecewise_connected R.
Proof.
  intros A R H x y z Rxy Rxz.
  destruct (H x y z Rxy Rxz); auto.
Qed.

Lemma relation_piecewise_strongly_convergent_of_reflexive_connected :
  forall (A : Type) (R : A -> A -> Prop),
    reflexive A R -> relation_piecewise_strongly_connected R ->
    relation_piecewise_strongly_convergent R.
Proof.
  intros A R Hrefl Hconnected x y z Rxy Rxz.
  destruct (Hconnected x y z Rxy Rxz) as [Ryz | Rzy].
  - exists z; split; [exact Ryz | apply Hrefl].
  - exists y; split; [apply Hrefl | exact Rzy].
Qed.

(** * Isolated and universal relations *)

Definition relation_isolated {A : Type}
    (R : A -> A -> Prop) : Prop :=
  forall x y, ~ R x y.

Lemma relation_isolated_elim :
  forall (A : Type) (R : A -> A -> Prop),
    relation_isolated R -> forall x y, ~ R x y.
Proof. intros A R H; exact H. Qed.

Lemma relation_isolated_coreflexive :
  forall (A : Type) (R : A -> A -> Prop),
    relation_isolated R -> relation_coreflexive R.
Proof. intros A R H x y Rxy; exfalso; exact (H x y Rxy). Qed.

Lemma relation_isolated_irreflexive :
  forall (A : Type) (R : A -> A -> Prop),
    relation_isolated R -> relation_irreflexive R.
Proof. intros A R H x; apply H. Qed.

Lemma relation_isolated_transitive :
  forall (A : Type) (R : A -> A -> Prop),
    relation_isolated R -> transitive A R.
Proof. intros A R H x y z Rxy _; exfalso; exact (H x y Rxy). Qed.

Definition relation_universal {A : Type}
    (R : A -> A -> Prop) : Prop :=
  forall x y, R x y.

Lemma relation_universal_reflexive :
  forall (A : Type) (R : A -> A -> Prop),
    relation_universal R -> reflexive A R.
Proof. intros A R H x; apply H. Qed.

Lemma relation_universal_right_euclidean :
  forall (A : Type) (R : A -> A -> Prop),
    relation_universal R -> relation_right_euclidean R.
Proof. intros A R H x y z _ _; apply H. Qed.
