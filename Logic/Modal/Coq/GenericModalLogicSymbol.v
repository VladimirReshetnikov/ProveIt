(**
  Generic modal operations and finite iteration.

  This module ports the representation-independent core of the pinned
  Foundation module [Modal/LogicSymbol.lean].  Box and diamond are arbitrary
  endomaps on an arbitrary carrier.  Shared iteration, image, and preimage
  lemmas are proved once and then exposed through the two modal names.

  Predicate-valued sets replace Lean [Set] values extensionally.  The
  subsequent list-backed finite-set layer can reuse the same iteration core
  without decidable equality.
*)

From Stdlib Require Import Lists.List Arith.PeanoNat.
From FoundationModal Require Import GenericSemantics GenericLogicSymbol.

Import ListNotations.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

(** * Iterated modalities and bounded folds *)

Fixpoint generic_modal_iter {F : Type}
    (op : F -> F) (n : nat) (p : F) : F :=
  match n with
  | 0 => p
  | S k => op (generic_modal_iter op k p)
  end.

Lemma generic_modal_iter_zero :
  forall (F : Type) (op : F -> F) (p : F),
    generic_modal_iter op 0 p = p.
Proof. reflexivity. Qed.

Lemma generic_modal_iter_succ :
  forall (F : Type) (op : F -> F) (n : nat) (p : F),
    generic_modal_iter op (S n) p =
    op (generic_modal_iter op n p).
Proof. reflexivity. Qed.

Lemma generic_modal_iter_add :
  forall (F : Type) (op : F -> F) (n m : nat) (p : F),
    generic_modal_iter op n (generic_modal_iter op m p) =
    generic_modal_iter op (n + m) p.
Proof.
  intros F op n; induction n as [|n IH]; intros m p; simpl.
  - reflexivity.
  - now rewrite IH.
Qed.

Definition generic_box_iter := @generic_modal_iter.
Definition generic_dia_iter := @generic_modal_iter.

Lemma generic_box_iter_zero :
  forall (F : Type) (box : F -> F) (p : F),
    generic_box_iter box 0 p = p.
Proof. exact generic_modal_iter_zero. Qed.

Lemma generic_box_iter_succ :
  forall (F : Type) (box : F -> F) (n : nat) (p : F),
    generic_box_iter box (S n) p = box (generic_box_iter box n p).
Proof. exact generic_modal_iter_succ. Qed.

Lemma generic_box_iter_add :
  forall (F : Type) (box : F -> F) (n m : nat) (p : F),
    generic_box_iter box n (generic_box_iter box m p) =
    generic_box_iter box (n + m) p.
Proof. exact generic_modal_iter_add. Qed.

Lemma generic_dia_iter_zero :
  forall (F : Type) (dia : F -> F) (p : F),
    generic_dia_iter dia 0 p = p.
Proof. exact generic_modal_iter_zero. Qed.

Lemma generic_dia_iter_succ :
  forall (F : Type) (dia : F -> F) (n : nat) (p : F),
    generic_dia_iter dia (S n) p = dia (generic_dia_iter dia n p).
Proof. exact generic_modal_iter_succ. Qed.

Lemma generic_dia_iter_add :
  forall (F : Type) (dia : F -> F) (n m : nat) (p : F),
    generic_dia_iter dia n (generic_dia_iter dia m p) =
    generic_dia_iter dia (n + m) p.
Proof. exact generic_modal_iter_add. Qed.

(** Foundation [boxLe]/[diaLe].  An explicit list enumeration removes the
    source [Finset.image] and [DecidableEq] machinery. *)
Definition generic_box_le {F : Type}
    (C : generic_connectives F) (box : F -> F)
    (n : nat) (p : F) : F :=
  generic_finset_conj_map C (seq 0 (S n))
    (fun j => generic_box_iter box j p).

Definition generic_dia_le {F : Type}
    (C : generic_connectives F) (dia : F -> F)
    (n : nat) (p : F) : F :=
  generic_finset_conj_map C (seq 0 (S n))
    (fun j => generic_dia_iter dia j p).

Lemma generic_box_le_zero :
  forall (F : Type) (C : generic_connectives F)
         (box : F -> F) (p : F),
    generic_box_le C box 0 p = p.
Proof. reflexivity. Qed.

Lemma generic_dia_le_zero :
  forall (F : Type) (C : generic_connectives F)
         (dia : F -> F) (p : F),
    generic_dia_le C dia 0 p = p.
Proof. reflexivity. Qed.

Definition generic_boxdot {F : Type}
    (C : generic_connectives F) (box : F -> F) (p : F) : F :=
  generic_and C p (box p).

Definition generic_diadot {F : Type}
    (C : generic_connectives F) (dia : F -> F) (p : F) : F :=
  generic_or C p (dia p).

(** * Modal connective interfaces *)

Record generic_modal_connectives (F : Type) : Type := {
  generic_modal_propositional : generic_connectives F;
  generic_modal_box : F -> F;
  generic_modal_dia : F -> F
}.

Definition generic_dia_by_box_law {F : Type}
    (C : generic_connectives F) (box dia : F -> F) : Prop :=
  forall p, dia p = generic_neg C (box (generic_neg C p)).

Definition generic_box_by_dia_law {F : Type}
    (C : generic_connectives F) (box dia : F -> F) : Prop :=
  forall p, box p = generic_neg C (dia (generic_neg C p)).

Record generic_modal_de_morgan_laws {F : Type}
    (C : generic_connectives F) (box dia : F -> F) : Prop := {
  generic_modal_de_morgan_propositional : generic_de_morgan_laws C;
  generic_neg_dia_law :
    forall p, generic_neg C (dia p) = box (generic_neg C p);
  generic_neg_box_law :
    forall p, generic_neg C (box p) = dia (generic_neg C p)
}.

Definition generic_injective {F : Type} (op : F -> F) : Prop :=
  forall p q, op p = op q -> p = q.

Lemma generic_modal_iter_injective :
  forall (F : Type) (op : F -> F),
    generic_injective op ->
    forall n, generic_injective (generic_modal_iter op n).
Proof.
  intros F op Hop n; induction n as [|n IH]; intros p q Hpq; simpl in *.
  - exact Hpq.
  - apply IH. now apply Hop.
Qed.

Lemma generic_box_iter_injective :
  forall (F : Type) (box : F -> F),
    generic_injective box ->
    forall n, generic_injective (generic_box_iter box n).
Proof. exact generic_modal_iter_injective. Qed.

Lemma generic_dia_iter_injective :
  forall (F : Type) (dia : F -> F),
    generic_injective dia ->
    forall n, generic_injective (generic_dia_iter dia n).
Proof. exact generic_modal_iter_injective. Qed.

(** * Images and preimages of predicate-valued sets *)

Definition generic_set_subset {F : Type}
    (s t : F -> Prop) : Prop :=
  forall p, s p -> t p.

Definition generic_iter_image {F : Type}
    (op : F -> F) (n : nat) (s : F -> Prop) : F -> Prop :=
  fun p => exists q, s q /\ generic_modal_iter op n q = p.

Definition generic_iter_preimage {F : Type}
    (op : F -> F) (n : nat) (s : F -> Prop) : F -> Prop :=
  fun p => s (generic_modal_iter op n p).

Lemma generic_iter_image_subset_mono :
  forall (F : Type) (op : F -> F) (n : nat)
         (s t : F -> Prop),
    generic_set_subset s t ->
    generic_set_subset (generic_iter_image op n s)
      (generic_iter_image op n t).
Proof.
  unfold generic_set_subset, generic_iter_image.
  intros F op n s t Hsub p [q [Hq Heq]].
  exists q. split; [now apply Hsub | exact Heq].
Qed.

Lemma generic_iter_preimage_subset_mono :
  forall (F : Type) (op : F -> F) (n : nat)
         (s t : F -> Prop),
    generic_set_subset s t ->
    generic_set_subset (generic_iter_preimage op n s)
      (generic_iter_preimage op n t).
Proof.
  unfold generic_set_subset, generic_iter_preimage.
  intros F op n s t Hsub p Hp. now apply Hsub.
Qed.

Lemma generic_iter_image_intro :
  forall (F : Type) (op : F -> F) (n : nat)
         (s : F -> Prop) (p : F),
    s p -> generic_iter_image op n s (generic_modal_iter op n p).
Proof.
  unfold generic_iter_image.
  intros F op n s p Hp. exists p. now split.
Qed.

Lemma generic_iter_image_elim :
  forall (F : Type) (op : F -> F) (n : nat)
         (s : F -> Prop) (p : F),
    generic_iter_image op n s p ->
    exists q, s q /\ generic_modal_iter op n q = p.
Proof. unfold generic_iter_image. intros F op n s p Hp. exact Hp. Qed.

Lemma generic_iter_preimage_member_iff :
  forall (F : Type) (op : F -> F) (n : nat)
         (s : F -> Prop) (p : F),
    generic_iter_preimage op n s p <->
    s (generic_modal_iter op n p).
Proof. reflexivity. Qed.

Lemma generic_iter_image_reflect :
  forall (F : Type) (op : F -> F),
    generic_injective op ->
    forall (n : nat) (s : F -> Prop) (p : F),
      generic_iter_image op n s (generic_modal_iter op n p) -> s p.
Proof.
  unfold generic_iter_image.
  intros F op Hop n s p [q [Hq Heq]].
  pose proof (@generic_modal_iter_injective F op Hop n q p Heq) as Hqp.
  now rewrite <- Hqp.
Qed.

Lemma generic_iter_image_change_depth :
  forall (F : Type) (op : F -> F),
    generic_injective op ->
    forall (n m : nat) (s : F -> Prop) (p : F),
      generic_iter_image op n s (generic_modal_iter op n p) ->
      generic_iter_image op m s (generic_modal_iter op m p).
Proof.
  intros F op Hop n m s p Hp.
  apply generic_iter_image_intro.
  exact (@generic_iter_image_reflect F op Hop n s p Hp).
Qed.

(** Box-named wrappers corresponding to Foundation [Set.LO]. *)
Definition generic_set_box_iter_image := @generic_iter_image.
Definition generic_set_box_iter_preimage := @generic_iter_preimage.

Definition generic_set_box_image {F : Type}
    (box : F -> F) : (F -> Prop) -> F -> Prop :=
  generic_set_box_iter_image box 1.

Definition generic_set_box_preimage {F : Type}
    (box : F -> F) : (F -> Prop) -> F -> Prop :=
  generic_set_box_iter_preimage box 1.

Lemma generic_set_box_iter_image_subset_mono :
  forall (F : Type) (box : F -> F) (n : nat)
         (s t : F -> Prop),
    generic_set_subset s t ->
    generic_set_subset (generic_set_box_iter_image box n s)
      (generic_set_box_iter_image box n t).
Proof. exact generic_iter_image_subset_mono. Qed.

Lemma generic_set_box_iter_preimage_subset_mono :
  forall (F : Type) (box : F -> F) (n : nat)
         (s t : F -> Prop),
    generic_set_subset s t ->
    generic_set_subset (generic_set_box_iter_preimage box n s)
      (generic_set_box_iter_preimage box n t).
Proof. exact generic_iter_preimage_subset_mono. Qed.

Lemma generic_set_box_iter_image_intro :
  forall (F : Type) (box : F -> F) (n : nat)
         (s : F -> Prop) (p : F),
    s p ->
    generic_set_box_iter_image box n s (generic_box_iter box n p).
Proof. exact generic_iter_image_intro. Qed.

Lemma generic_set_box_iter_image_elim :
  forall (F : Type) (box : F -> F) (n : nat)
         (s : F -> Prop) (p : F),
    generic_set_box_iter_image box n s p ->
    exists q, s q /\ generic_box_iter box n q = p.
Proof. exact generic_iter_image_elim. Qed.

Lemma generic_set_box_iter_preimage_member_iff :
  forall (F : Type) (box : F -> F) (n : nat)
         (s : F -> Prop) (p : F),
    generic_set_box_iter_preimage box n s p <->
    s (generic_box_iter box n p).
Proof. reflexivity. Qed.

Lemma generic_set_box_iter_image_reflect :
  forall (F : Type) (box : F -> F),
    generic_injective box ->
    forall (n : nat) (s : F -> Prop) (p : F),
      generic_set_box_iter_image box n s (generic_box_iter box n p) ->
      s p.
Proof. exact generic_iter_image_reflect. Qed.

Lemma generic_set_box_iter_image_change_depth :
  forall (F : Type) (box : F -> F),
    generic_injective box ->
    forall (n m : nat) (s : F -> Prop) (p : F),
      generic_set_box_iter_image box n s (generic_box_iter box n p) ->
      generic_set_box_iter_image box m s (generic_box_iter box m p).
Proof. exact generic_iter_image_change_depth. Qed.

(** Diamond-named wrappers share exactly the same proofs. *)
Definition generic_set_dia_iter_image := @generic_iter_image.
Definition generic_set_dia_iter_preimage := @generic_iter_preimage.

Definition generic_set_dia_image {F : Type}
    (dia : F -> F) : (F -> Prop) -> F -> Prop :=
  generic_set_dia_iter_image dia 1.

Definition generic_set_dia_preimage {F : Type}
    (dia : F -> F) : (F -> Prop) -> F -> Prop :=
  generic_set_dia_iter_preimage dia 1.

Lemma generic_set_dia_iter_image_subset_mono :
  forall (F : Type) (dia : F -> F) (n : nat)
         (s t : F -> Prop),
    generic_set_subset s t ->
    generic_set_subset (generic_set_dia_iter_image dia n s)
      (generic_set_dia_iter_image dia n t).
Proof. exact generic_iter_image_subset_mono. Qed.

Lemma generic_set_dia_iter_preimage_subset_mono :
  forall (F : Type) (dia : F -> F) (n : nat)
         (s t : F -> Prop),
    generic_set_subset s t ->
    generic_set_subset (generic_set_dia_iter_preimage dia n s)
      (generic_set_dia_iter_preimage dia n t).
Proof. exact generic_iter_preimage_subset_mono. Qed.

Lemma generic_set_dia_iter_image_intro :
  forall (F : Type) (dia : F -> F) (n : nat)
         (s : F -> Prop) (p : F),
    s p -> generic_set_dia_iter_image dia n s (generic_dia_iter dia n p).
Proof. exact generic_iter_image_intro. Qed.

Lemma generic_set_dia_iter_image_elim :
  forall (F : Type) (dia : F -> F) (n : nat)
         (s : F -> Prop) (p : F),
    generic_set_dia_iter_image dia n s p ->
    exists q, s q /\ generic_dia_iter dia n q = p.
Proof. exact generic_iter_image_elim. Qed.

Lemma generic_set_dia_iter_preimage_member_iff :
  forall (F : Type) (dia : F -> F) (n : nat)
         (s : F -> Prop) (p : F),
    generic_set_dia_iter_preimage dia n s p <->
    s (generic_dia_iter dia n p).
Proof. reflexivity. Qed.

(** * List-backed finite collection images *)

Definition generic_list_collection_subset {F : Type}
    (s t : list F) : Prop :=
  forall p, In p s -> In p t.

Definition generic_list_iter_image {F : Type}
    (op : F -> F) (n : nat) (s : list F) : list F :=
  map (generic_modal_iter op n) s.

Definition generic_list_image {F : Type}
    (op : F -> F) (s : list F) : list F :=
  generic_list_iter_image op 1 s.

Lemma generic_list_iter_image_zero :
  forall (F : Type) (op : F -> F) (s : list F),
    generic_list_iter_image op 0 s = s.
Proof.
  intros F op s; induction s as [|p s IH]; simpl; [reflexivity |].
  now rewrite IH.
Qed.

Lemma generic_list_iter_image_nil :
  forall (F : Type) (op : F -> F) (n : nat),
    generic_list_iter_image op n [] = [].
Proof. reflexivity. Qed.

Lemma generic_list_iter_image_singleton :
  forall (F : Type) (op : F -> F) (n : nat) (p : F),
    generic_list_iter_image op n [p] = [generic_modal_iter op n p].
Proof. reflexivity. Qed.

Lemma generic_list_iter_image_cons :
  forall (F : Type) (op : F -> F) (n : nat)
         (p : F) (s : list F),
    generic_list_iter_image op n (p :: s) =
    generic_modal_iter op n p :: generic_list_iter_image op n s.
Proof. reflexivity. Qed.

Lemma generic_list_iter_image_nonempty :
  forall (F : Type) (op : F -> F) (n : nat) (s : list F),
    s <> [] -> generic_list_iter_image op n s <> [].
Proof.
  intros F op n [|p s] H; [now exfalso; apply H | discriminate].
Qed.

Lemma generic_list_iter_image_cons_member_iff :
  forall (F : Type) (op : F -> F) (n : nat)
         (p q : F) (s : list F),
    In p (generic_list_iter_image op n (q :: s)) <->
    p = generic_modal_iter op n q \/
    In p (generic_list_iter_image op n s).
Proof.
  intros F op n p q s. unfold generic_list_iter_image. simpl.
  split.
  - intros [H | H]; [left; now symmetry | now right].
  - intros [H | H]; [left; now symmetry | now right].
Qed.

Lemma generic_list_iter_image_add :
  forall (F : Type) (op : F -> F) (m n : nat) (s : list F),
    generic_list_iter_image op (m + n) s =
    generic_list_iter_image op n (generic_list_iter_image op m s).
Proof.
  intros F op m n s; induction s as [|p s IH]; simpl.
  - reflexivity.
  - rewrite IH, (generic_modal_iter_add op n m p), Nat.add_comm.
    reflexivity.
Qed.

Lemma generic_list_iter_image_intro :
  forall (F : Type) (op : F -> F) (n : nat)
         (s : list F) (p : F),
    In p s ->
    In (generic_modal_iter op n p) (generic_list_iter_image op n s).
Proof.
  intros F op n s p Hp. unfold generic_list_iter_image.
  now apply in_map.
Qed.

Lemma generic_list_iter_image_elim :
  forall (F : Type) (op : F -> F) (n : nat)
         (s : list F) (p : F),
    In p (generic_list_iter_image op n s) ->
    exists q, In q s /\ generic_modal_iter op n q = p.
Proof.
  intros F op n s p Hp. unfold generic_list_iter_image in Hp.
  apply in_map_iff in Hp. destruct Hp as [q [Heq Hq]].
  exists q. split; [exact Hq | exact Heq].
Qed.

Lemma generic_list_iter_image_subset_mono :
  forall (F : Type) (op : F -> F) (n : nat)
         (s t : list F),
    generic_list_collection_subset s t ->
    generic_list_collection_subset
      (generic_list_iter_image op n s)
      (generic_list_iter_image op n t).
Proof.
  unfold generic_list_collection_subset.
  intros F op n s t Hsub p Hp.
  destruct (generic_list_iter_image_elim Hp) as [q [Hq Heq]].
  rewrite <- Heq.
  apply generic_list_iter_image_intro. now apply Hsub.
Qed.

(** Box list API. *)
Definition generic_list_box_iter_image := @generic_list_iter_image.
Definition generic_list_box_image := @generic_list_image.

Lemma generic_list_box_iter_image_zero :
  forall (F : Type) (box : F -> F) (s : list F),
    generic_list_box_iter_image box 0 s = s.
Proof. exact generic_list_iter_image_zero. Qed.

Lemma generic_list_box_iter_image_nonempty :
  forall (F : Type) (box : F -> F) (n : nat) (s : list F),
    s <> [] -> generic_list_box_iter_image box n s <> [].
Proof. exact generic_list_iter_image_nonempty. Qed.

Lemma generic_list_box_iter_image_nil :
  forall (F : Type) (box : F -> F) (n : nat),
    generic_list_box_iter_image box n [] = [].
Proof. reflexivity. Qed.

Lemma generic_list_box_iter_image_singleton :
  forall (F : Type) (box : F -> F) (n : nat) (p : F),
    generic_list_box_iter_image box n [p] = [generic_box_iter box n p].
Proof. reflexivity. Qed.

Lemma generic_list_box_iter_image_cons :
  forall (F : Type) (box : F -> F) (n : nat)
         (p : F) (s : list F),
    generic_list_box_iter_image box n (p :: s) =
    generic_box_iter box n p :: generic_list_box_iter_image box n s.
Proof. reflexivity. Qed.

Lemma generic_list_box_iter_image_cons_member_iff :
  forall (F : Type) (box : F -> F) (n : nat)
         (p q : F) (s : list F),
    In p (generic_list_box_iter_image box n (q :: s)) <->
    p = generic_box_iter box n q \/
    In p (generic_list_box_iter_image box n s).
Proof. exact generic_list_iter_image_cons_member_iff. Qed.

Lemma generic_list_box_iter_image_add :
  forall (F : Type) (box : F -> F) (m n : nat) (s : list F),
    generic_list_box_iter_image box (m + n) s =
    generic_list_box_iter_image box n
      (generic_list_box_iter_image box m s).
Proof. exact generic_list_iter_image_add. Qed.

Lemma generic_list_box_iter_image_intro :
  forall (F : Type) (box : F -> F) (n : nat)
         (s : list F) (p : F),
    In p s ->
    In (generic_box_iter box n p)
      (generic_list_box_iter_image box n s).
Proof. exact generic_list_iter_image_intro. Qed.

Lemma generic_list_box_iter_image_elim :
  forall (F : Type) (box : F -> F) (n : nat)
         (s : list F) (p : F),
    In p (generic_list_box_iter_image box n s) ->
    exists q, In q s /\ generic_box_iter box n q = p.
Proof. exact generic_list_iter_image_elim. Qed.

Lemma generic_list_box_iter_image_subset_mono :
  forall (F : Type) (box : F -> F) (n : nat)
         (s t : list F),
    generic_list_collection_subset s t ->
    generic_list_collection_subset
      (generic_list_box_iter_image box n s)
      (generic_list_box_iter_image box n t).
Proof. exact generic_list_iter_image_subset_mono. Qed.

(** Diamond list API. *)
Definition generic_list_dia_iter_image := @generic_list_iter_image.
Definition generic_list_dia_image := @generic_list_image.

Lemma generic_list_dia_iter_image_zero :
  forall (F : Type) (dia : F -> F) (s : list F),
    generic_list_dia_iter_image dia 0 s = s.
Proof. exact generic_list_iter_image_zero. Qed.

Lemma generic_list_dia_iter_image_nonempty :
  forall (F : Type) (dia : F -> F) (n : nat) (s : list F),
    s <> [] -> generic_list_dia_iter_image dia n s <> [].
Proof. exact generic_list_iter_image_nonempty. Qed.

Lemma generic_list_dia_iter_image_nil :
  forall (F : Type) (dia : F -> F) (n : nat),
    generic_list_dia_iter_image dia n [] = [].
Proof. reflexivity. Qed.

Lemma generic_list_dia_iter_image_singleton :
  forall (F : Type) (dia : F -> F) (n : nat) (p : F),
    generic_list_dia_iter_image dia n [p] = [generic_dia_iter dia n p].
Proof. reflexivity. Qed.

Lemma generic_list_dia_iter_image_cons :
  forall (F : Type) (dia : F -> F) (n : nat)
         (p : F) (s : list F),
    generic_list_dia_iter_image dia n (p :: s) =
    generic_dia_iter dia n p :: generic_list_dia_iter_image dia n s.
Proof. reflexivity. Qed.

Lemma generic_list_dia_iter_image_cons_member_iff :
  forall (F : Type) (dia : F -> F) (n : nat)
         (p q : F) (s : list F),
    In p (generic_list_dia_iter_image dia n (q :: s)) <->
    p = generic_dia_iter dia n q \/
    In p (generic_list_dia_iter_image dia n s).
Proof. exact generic_list_iter_image_cons_member_iff. Qed.

Lemma generic_list_dia_iter_image_add :
  forall (F : Type) (dia : F -> F) (m n : nat) (s : list F),
    generic_list_dia_iter_image dia (m + n) s =
    generic_list_dia_iter_image dia n
      (generic_list_dia_iter_image dia m s).
Proof. exact generic_list_iter_image_add. Qed.

Lemma generic_list_dia_iter_image_intro :
  forall (F : Type) (dia : F -> F) (n : nat)
         (s : list F) (p : F),
    In p s ->
    In (generic_dia_iter dia n p)
      (generic_list_dia_iter_image dia n s).
Proof. exact generic_list_iter_image_intro. Qed.

Lemma generic_list_dia_iter_image_elim :
  forall (F : Type) (dia : F -> F) (n : nat)
         (s : list F) (p : F),
    In p (generic_list_dia_iter_image dia n s) ->
    exists q, In q s /\ generic_dia_iter dia n q = p.
Proof. exact generic_list_iter_image_elim. Qed.

Lemma generic_list_dia_iter_image_subset_mono :
  forall (F : Type) (dia : F -> F) (n : nat)
         (s t : list F),
    generic_list_collection_subset s t ->
    generic_list_collection_subset
      (generic_list_dia_iter_image dia n s)
      (generic_list_dia_iter_image dia n t).
Proof. exact generic_list_iter_image_subset_mono. Qed.
