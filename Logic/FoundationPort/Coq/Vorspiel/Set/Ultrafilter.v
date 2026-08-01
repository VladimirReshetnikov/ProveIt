(** Ultrafilters on predicate sets.

    The interface records exactly the Boolean-prime filter laws used by
    first-order ultraproducts.  Keeping existence separate lets Łoś's theorem
    depend only on the algebraic laws, while maximal-extension constructions
    can be audited independently. *)

From Stdlib Require Import Logic.Classical_Prop.
From Foundation.Vorspiel.Set Require Import Basic.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

Definition set_intersection {A} (s t : pred_set A) : pred_set A :=
  fun x => s x /\ t x.

Definition set_union {A} (s t : pred_set A) : pred_set A :=
  fun x => s x \/ t x.

Definition set_complement {A} (s : pred_set A) : pred_set A :=
  fun x => ~ s x.

Definition set_universal {A} : pred_set A := fun _ => True.
Definition set_void {A} : pred_set A := fun _ => False.

Record set_ultrafilter (A : Type) : Type := {
  ultrafilter_member : pred_set A -> Prop;
  ultrafilter_universal_mem : ultrafilter_member set_universal;
  ultrafilter_void_not_mem : ~ ultrafilter_member set_void;
  ultrafilter_mem_of_superset : forall s t,
    set_subset s t -> ultrafilter_member s -> ultrafilter_member t;
  ultrafilter_intersection_mem_iff : forall s t,
    ultrafilter_member (set_intersection s t) <->
    ultrafilter_member s /\ ultrafilter_member t;
  ultrafilter_union_mem_iff : forall s t,
    ultrafilter_member (set_union s t) <->
    ultrafilter_member s \/ ultrafilter_member t;
  ultrafilter_complement_mem_iff : forall s,
    ultrafilter_member (set_complement s) <->
    ~ ultrafilter_member s
}.

Arguments ultrafilter_member {A} _ _.

Lemma ultrafilter_member_equiv : forall A (U : set_ultrafilter A) s t,
  set_equiv s t ->
  (ultrafilter_member U s <-> ultrafilter_member U t).
Proof.
  intros A U s t Heq. split; intro H.
  - eapply ultrafilter_mem_of_superset; [|exact H].
    intros x Hx. exact (proj1 (Heq x) Hx).
  - eapply ultrafilter_mem_of_superset; [|exact H].
    intros x Hx. exact (proj2 (Heq x) Hx).
Qed.

Lemma ultrafilter_intersection_mem : forall A (U : set_ultrafilter A) s t,
  ultrafilter_member U s -> ultrafilter_member U t ->
  ultrafilter_member U (set_intersection s t).
Proof.
  intros A U s t Hs Ht.
  apply (proj2 (ultrafilter_intersection_mem_iff U s t)). now split.
Qed.

Lemma ultrafilter_member_intersection_left : forall A
    (U : set_ultrafilter A) s t,
  ultrafilter_member U (set_intersection s t) ->
  ultrafilter_member U s.
Proof.
  intros A U s t H. exact (proj1
    (proj1 (ultrafilter_intersection_mem_iff U s t) H)).
Qed.

Lemma ultrafilter_member_intersection_right : forall A
    (U : set_ultrafilter A) s t,
  ultrafilter_member U (set_intersection s t) ->
  ultrafilter_member U t.
Proof.
  intros A U s t H. exact (proj2
    (proj1 (ultrafilter_intersection_mem_iff U s t) H)).
Qed.

Lemma ultrafilter_member_decides : forall A (U : set_ultrafilter A) s,
  ultrafilter_member U s \/
  ultrafilter_member U (set_complement s).
Proof.
  intros A U s. destruct (classic (ultrafilter_member U s)) as [Hs | Hs].
  - now left.
  - right. now apply (proj2 (ultrafilter_complement_mem_iff U s)).
Qed.
