(** Dense subsets, descending-chain filters, and countable generic filters. *)

From Stdlib Require Import Arith.PeanoNat Lia Logic.ClassicalEpsilon.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

Record preorder_data (A : Type) := {
  preorder_le : A -> A -> Prop;
  preorder_refl : forall x, preorder_le x x;
  preorder_trans : forall x y z,
    preorder_le x y -> preorder_le y z -> preorder_le x z
}.

Arguments preorder_le {A} _ _ _.

Definition order_compatible {A} (O : preorder_data A) (a b : A) : Prop :=
  exists c, preorder_le O c a /\ preorder_le O c b.

Definition order_incompatible {A} (O : preorder_data A) (a b : A) : Prop :=
  ~ order_compatible O a b.

Lemma order_compatible_refl : forall A (O : preorder_data A) a,
  order_compatible O a a.
Proof. intros A O a. exists a. split; apply preorder_refl. Qed.

Lemma order_compatible_sym_iff : forall A (O : preorder_data A) a b,
  order_compatible O a b <-> order_compatible O b a.
Proof.
  intros A O a b. split; intros [c [Hca Hcb]];
    exists c; now split.
Qed.

Lemma order_compatible_of_le : forall A (O : preorder_data A) a b,
  preorder_le O a b -> order_compatible O a b.
Proof.
  intros A O a b Hab. exists a. split; [apply preorder_refl | exact Hab].
Qed.

Lemma order_incompatible_iff : forall A (O : preorder_data A) a b,
  order_incompatible O a b <->
  forall c, preorder_le O c a -> ~ preorder_le O c b.
Proof.
  intros A O a b. unfold order_incompatible, order_compatible. split.
  - intros H c Hca Hcb. apply H. exists c. now split.
  - intros H [c [Hca Hcb]]. exact (H c Hca Hcb).
Qed.

Lemma order_incompatible_irrefl : forall A (O : preorder_data A) a,
  ~ order_incompatible O a a.
Proof.
  intros A O a H. apply H. apply order_compatible_refl.
Qed.

Lemma order_incompatible_sym_iff : forall A (O : preorder_data A) a b,
  order_incompatible O a b <-> order_incompatible O b a.
Proof.
  intros A O a b. unfold order_incompatible.
  rewrite (order_compatible_sym_iff O a b). tauto.
Qed.

Lemma order_incompatible_lower : forall A (O : preorder_data A)
    a a' b b',
  order_incompatible O a b ->
  preorder_le O a' a -> preorder_le O b' b ->
  order_incompatible O a' b'.
Proof.
  intros A O a a' b b' Hab Ha Hb [c [Hca Hcb]]. apply Hab.
  exists c. split.
  - exact (@preorder_trans A O _ _ _ Hca Ha).
  - exact (@preorder_trans A O _ _ _ Hcb Hb).
Qed.

Definition order_dense {A} (O : preorder_data A) (D : A -> Prop) : Prop :=
  forall p, exists q, preorder_le O q p /\ D q.

Definition order_dense_below {A} (O : preorder_data A)
    (D : A -> Prop) (a : A) : Prop :=
  forall p, preorder_le O p a ->
    exists q, preorder_le O q p /\ D q.

Record dense_set {A} (O : preorder_data A) := {
  dense_member : A -> Prop;
  dense_set_dense : order_dense O dense_member
}.

Arguments dense_member {A O} _ _.

Definition dense_choose {A} {O : preorder_data A}
    (d : dense_set O) (a : A) : A :=
  proj1_sig (constructive_indefinite_description
    (fun q => preorder_le O q a /\ dense_member d q)
    (dense_set_dense d a)).

Lemma dense_choose_le : forall A (O : preorder_data A)
    (d : dense_set O) a,
  preorder_le O (dense_choose d a) a.
Proof.
  intros A O d a. unfold dense_choose.
  exact (proj1 (proj2_sig (constructive_indefinite_description
    (fun q => preorder_le O q a /\ dense_member d q)
    (dense_set_dense d a)))).
Qed.

Lemma dense_choose_member : forall A (O : preorder_data A)
    (d : dense_set O) a,
  dense_member d (dense_choose d a).
Proof.
  intros A O d a. unfold dense_choose.
  exact (proj2 (proj2_sig (constructive_indefinite_description
    (fun q => preorder_le O q a /\ dense_member d q)
    (dense_set_dense d a)))).
Qed.

Record order_pfilter {A} (O : preorder_data A) := {
  pfilter_member : A -> Prop;
  pfilter_nonempty : exists x, pfilter_member x;
  pfilter_directed : forall x y,
    pfilter_member x -> pfilter_member y ->
    exists z, pfilter_member z /\
      preorder_le O z x /\ preorder_le O z y;
  pfilter_upward : forall x y,
    preorder_le O x y -> pfilter_member x -> pfilter_member y
}.

Arguments pfilter_member {A O} _ _.

Definition principal_pfilter {A} (O : preorder_data A) (a : A) :
    order_pfilter O.
Proof.
  refine {| pfilter_member := fun x => preorder_le O a x |}.
  - exists a. apply preorder_refl.
  - intros x y Hx Hy. exists a. repeat split; try apply preorder_refl;
      assumption.
  - intros x y Hxy Hax. exact (@preorder_trans A O _ _ _ Hax Hxy).
Defined.

Definition descending_chain {A} (O : preorder_data A)
    (s : nat -> A) : Prop :=
  forall i j, i <= j -> preorder_le O (s j) (s i).

Definition pfilter_of_descending_chain {A} (O : preorder_data A)
    (s : nat -> A) (Hs : descending_chain O s) : order_pfilter O.
Proof.
  refine {| pfilter_member := fun x => exists i, preorder_le O (s i) x |}.
  - exists (s 0), 0. apply preorder_refl.
  - intros x y [i Hix] [j Hjy].
    destruct (Nat.le_ge_cases i j) as [Hij | Hji].
    + exists (s j). repeat split.
      * exists j. apply preorder_refl.
      * exact (@preorder_trans A O _ _ _ (Hs i j Hij) Hix).
      * exact Hjy.
    + exists (s i). repeat split.
      * exists i. apply preorder_refl.
      * exact Hix.
      * exact (@preorder_trans A O _ _ _ (Hs j i Hji) Hjy).
  - intros x y Hxy [i Hix]. exists i.
    exact (@preorder_trans A O _ _ _ Hix Hxy).
Defined.

Lemma pfilter_of_descending_chain_member_iff : forall A
    (O : preorder_data A) s Hs x,
  pfilter_member (@pfilter_of_descending_chain A O s Hs) x <->
  exists i, preorder_le O (s i) x.
Proof. reflexivity. Qed.

Definition pfilter_generic {A} {O : preorder_data A}
    (F : order_pfilter O) (family : dense_set O -> Prop) : Prop :=
  forall d, family d ->
    exists a, pfilter_member F a /\ dense_member d a.

Definition dense_family_countable {A} {O : preorder_data A}
    (family : dense_set O -> Prop) : Prop :=
  (forall d, ~ family d) \/
  exists enum : nat -> dense_set O,
    (forall n, family (enum n)) /\
    forall d, family d ->
      exists n, forall x, dense_member d x <-> dense_member (enum n) x.

Fixpoint generic_descending_chain {A} {O : preorder_data A}
    (a : A) (enum : nat -> dense_set O) (n : nat) : A :=
  match n with
  | 0 => a
  | S k => dense_choose (enum k) (generic_descending_chain a enum k)
  end.

Lemma nat_relation_of_successors : forall (R : nat -> nat -> Prop),
  (forall n, R n n) ->
  (forall i j k, R i j -> R j k -> R i k) ->
  (forall n, R n (S n)) ->
  forall n m, n <= m -> R n m.
Proof.
  intros R Hr Ht Hs n m Hnm. induction Hnm.
  - apply Hr.
  - eapply Ht; [exact IHHnm | apply Hs].
Qed.

Lemma generic_descending_chain_is_descending : forall A
    (O : preorder_data A) (a : A) (enum : nat -> dense_set O),
  descending_chain O (generic_descending_chain a enum).
Proof.
  intros A O a enum i j Hij.
  apply (nat_relation_of_successors
    (R := fun i j => preorder_le O
      (generic_descending_chain a enum j)
      (generic_descending_chain a enum i))); try assumption.
  - intro n. apply preorder_refl.
  - intros x y z Hxy Hyz. exact (@preorder_trans A O _ _ _ Hyz Hxy).
  - intro n. simpl. apply dense_choose_le.
Qed.

Theorem exists_generic_pfilter_of_countable : forall A
    (O : preorder_data A) (family : dense_set O -> Prop),
  dense_family_countable family -> forall a,
  exists G : order_pfilter O,
    pfilter_generic G family /\ pfilter_member G a.
Proof.
  intros A O family Hcount a. destruct Hcount as [Hempty | Henum].
  - exists (@principal_pfilter A O a). split.
    + intros d Hd. exfalso. exact (Hempty d Hd).
    + apply preorder_refl.
  - destruct Henum as [enum [Hmem Hcover]].
    pose (s := generic_descending_chain a enum).
    pose proof (@generic_descending_chain_is_descending A O a enum) as Hdesc.
    exists (@pfilter_of_descending_chain A O s Hdesc). split.
    + intros d Hd. destruct (Hcover d Hd) as [n Hn].
      exists (s (S n)). split.
      * exists (S n). apply preorder_refl.
      * apply (proj2 (Hn (s (S n)))).
        unfold s. simpl. apply dense_choose_member.
    + exists 0. apply preorder_refl.
Qed.
