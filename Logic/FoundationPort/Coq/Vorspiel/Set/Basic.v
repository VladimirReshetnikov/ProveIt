(** Predicate sets, strict inclusion, and finite subsets of chains. *)

From Stdlib Require Import Lists.List.

Set Implicit Arguments.
Unset Strict Implicit.

Definition pred_set (A : Type) := A -> Prop.

Definition set_subset {A} (s t : pred_set A) : Prop :=
  forall x, s x -> t x.

Definition set_equiv {A} (s t : pred_set A) : Prop :=
  forall x, s x <-> t x.

Definition set_strict_subset {A} (s t : pred_set A) : Prop :=
  set_subset s t /\ ~ set_subset t s.

Definition set_family_union {A} (C : pred_set (pred_set A)) : pred_set A :=
  fun x => exists s, C s /\ s x.

Definition set_chain {A} (C : pred_set (pred_set A)) : Prop :=
  forall s t, C s -> C t -> set_subset s t \/ set_subset t s.

Lemma set_doubleton_subset_iff : forall A (a b : A) s,
  set_subset (fun x => x = a \/ x = b) s <-> s a /\ s b.
Proof.
  intros A a b s. split.
  - intro H. split; apply H; [now left | now right].
  - intros [Ha Hb] x [-> | ->]; assumption.
Qed.

Lemma set_subset_insert_iff_remove : forall A (a : A) s t,
  (forall x, x = a \/ x <> a) ->
  (set_subset s (fun x => x = a \/ t x) <->
    set_subset (fun x => s x /\ x <> a) t).
Proof.
  intros A a s t Hdec. split.
  - intros H x [Hsx Hneq]. destruct (H x Hsx); [contradiction | assumption].
  - intros H x Hsx. destruct (Hdec x) as [-> | Hneq].
    + now left.
    + right. now apply H.
Qed.

Lemma set_strict_subset_of_subset_not_equiv : forall A
    (s t : pred_set A),
  set_subset s t -> ~ set_equiv s t -> set_strict_subset s t.
Proof.
  intros A s t Hst Hneq. split; [exact Hst |].
  intro Hts. apply Hneq. intro x. split; [apply Hst | apply Hts].
Qed.

Theorem finite_list_subset_chain_union : forall A
    (C : pred_set (pred_set A)),
  (exists t, C t) -> set_chain C ->
  forall xs : list A,
  set_subset (fun x => List.In x xs) (set_family_union C) ->
  exists t, C t /\ set_subset (fun x => List.In x xs) t.
Proof.
  intros A C Hnonempty Hchain xs.
  induction xs as [|a xs IH]; intro Hcover.
  - destruct Hnonempty as [t Ht]. exists t. split; [exact Ht |].
    intros x Hx. inversion Hx.
  - assert (Htail : set_subset (fun x => List.In x xs) (set_family_union C)).
    { intros x Hx. apply Hcover. now right. }
    destruct (IH Htail) as [t [Ht Hall]].
    destruct (Hcover a (or_introl eq_refl)) as [u [Hu Hau]].
    destruct (Hchain t u Ht Hu) as [Htu | Hut].
    + exists u. split; [exact Hu |]. intros x [<- | Hx].
      * exact Hau.
      * apply Htu, Hall, Hx.
    + exists t. split; [exact Ht |]. intros x [<- | Hx].
      * apply Hut, Hau.
      * apply Hall, Hx.
Qed.

Corollary finite_family_subset_chain_union : forall A
    (C : pred_set (pred_set A)),
  (exists t, C t) -> set_chain C ->
  forall I (cover : list I),
  (forall i, List.In i cover) ->
  forall f : I -> A,
  (forall i, set_family_union C (f i)) ->
  exists t, C t /\ forall i, t (f i).
Proof.
  intros A C Hnonempty Hchain I cover Hcover f Hf.
  destruct (@finite_list_subset_chain_union A C Hnonempty Hchain
    (List.map f cover)) as [t [Ht Hall]].
  - intros x Hx. apply List.in_map_iff in Hx.
    destruct Hx as [i [<- _]]. apply Hf.
  - exists t. split; [exact Ht |]. intro i. apply Hall.
    apply List.in_map. apply Hcover.
Qed.
