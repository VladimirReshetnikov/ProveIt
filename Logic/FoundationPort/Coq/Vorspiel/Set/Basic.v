(** Predicate sets, strict inclusion, and finite subsets of chains. *)

From Stdlib Require Import Arith.PeanoNat Lia Lists.List.
From Foundation.Vorspiel.Fin Require Import Basic.

Import ListNotations.

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

Record pointed_set_enumeration {A} (s : pred_set A) (a : A) := {
  pointed_enum : nat -> A;
  pointed_enum_member : forall n, s (pointed_enum n);
  pointed_enum_not_base : forall n, pointed_enum n <> a;
  pointed_enum_injective : forall i j,
    pointed_enum i = pointed_enum j -> i = j;
  pointed_enum_complete : forall x, s x ->
    x = a \/ exists n, pointed_enum n = x
}.

Arguments pointed_enum {A s a} _ _.

Definition set_finite_approximation {A} {s : pred_set A} {a}
    (E : pointed_set_enumeration s a) (n : nat) : list A :=
  a :: map (pointed_enum E) (seq 0 n).

Lemma set_finite_approximation_member_iff : forall A
    (s : pred_set A) a (E : pointed_set_enumeration s a) n x,
  In x (set_finite_approximation E n) <->
  x = a \/ exists i, i < n /\ pointed_enum E i = x.
Proof.
  intros A s a E n x. unfold set_finite_approximation. simpl. split.
  - intros [Hx | Hx]; [now left |]. right.
    apply in_map_iff in Hx. destruct Hx as [i [Hix Hi]].
    exists i. split; [apply in_seq in Hi; lia | exact Hix].
  - intros [-> | [i [Hi Hix]]]; [now left |]. right.
    apply in_map_iff. exists i. split; [exact Hix |].
    apply in_seq. lia.
Qed.

Lemma set_finite_approximation_nodup : forall A
    (s : pred_set A) a (E : pointed_set_enumeration s a) n,
  NoDup (set_finite_approximation E n).
Proof.
  intros A s a E n. unfold set_finite_approximation. constructor.
  - intro Hmem. apply in_map_iff in Hmem.
    destruct Hmem as [i [Hi _]].
    exact (@pointed_enum_not_base A s a E i Hi).
  - apply list_map_nodup_of_injective.
    + intros i j Hij. now apply (@pointed_enum_injective A s a E i j).
    + apply seq_NoDup.
Qed.

Theorem set_finite_approximation_strict : forall A
    (s : pred_set A) a (E : pointed_set_enumeration s a) n,
  set_strict_subset
    (fun x => In x (set_finite_approximation E n))
    (fun x => In x (set_finite_approximation E (S n))).
Proof.
  intros A s a E n. split.
  - intros x Hx. apply set_finite_approximation_member_iff in Hx.
    apply set_finite_approximation_member_iff. destruct Hx as [Hx | [i [Hi Hix]]].
    + now left.
    + right. exists i. split; [lia | exact Hix].
  - intro Hback.
    assert (Hnew : In (pointed_enum E n)
      (set_finite_approximation E (S n))).
    { apply set_finite_approximation_member_iff. right.
      exists n. split; [lia | reflexivity]. }
    specialize (Hback (pointed_enum E n) Hnew).
    apply set_finite_approximation_member_iff in Hback.
    destruct Hback as [Hbase | [i [Hi Heq]]].
    + exact (@pointed_enum_not_base A s a E n Hbase).
    + apply (@pointed_enum_injective A s a E i n) in Heq. lia.
Qed.

Lemma set_finite_approximation_subset : forall A
    (s : pred_set A) a (E : pointed_set_enumeration s a),
  s a -> forall n,
  set_subset (fun x => In x (set_finite_approximation E n)) s.
Proof.
  intros A s a E Ha n x Hx.
  apply set_finite_approximation_member_iff in Hx.
  destruct Hx as [-> | [i [_ <-]]];
    [exact Ha | apply (@pointed_enum_member A s a E i)].
Qed.

Lemma set_finite_approximation_complete : forall A
    (s : pred_set A) a (E : pointed_set_enumeration s a) x,
  s x -> exists n, In x (set_finite_approximation E n).
Proof.
  intros A s a E x Hx.
  destruct (@pointed_enum_complete A s a E x Hx) as [-> | [i Hi]].
  - exists 0. apply set_finite_approximation_member_iff. now left.
  - exists (S i). apply set_finite_approximation_member_iff. right.
    exists i. split; [lia | exact Hi].
Qed.

Theorem infinitely_finite_approximate : forall A
    (s : pred_set A) a (E : pointed_set_enumeration s a),
  s a -> exists f : nat -> list A,
    f 0 = [a] /\
    (forall n, NoDup (f n)) /\
    (forall n, set_strict_subset
      (fun x => In x (f n)) (fun x => In x (f (S n)))) /\
    (forall n, set_subset (fun x => In x (f n)) s) /\
    (forall x, s x -> exists n, In x (f n)).
Proof.
  intros A s a E Ha. exists (set_finite_approximation E).
  split; [reflexivity |]. split.
  - apply set_finite_approximation_nodup.
  - split.
    + apply set_finite_approximation_strict.
    + split.
      * now apply set_finite_approximation_subset.
      * now apply set_finite_approximation_complete.
Qed.
