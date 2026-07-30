(** Finite list bounds, deletion, custom induction, and suffix divergence. *)

From Stdlib Require Import Arith.PeanoNat Bool.Bool Lia Lists.List Logic.Classical.

Import ListNotations.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

Fixpoint list_subset_bool {A} (keep : A -> bool) (xs : list A) : bool :=
  match xs with
  | [] => true
  | x :: rest => andb (keep x) (list_subset_bool keep rest)
  end.

Lemma list_subset_bool_true_iff : forall A (keep : A -> bool) xs,
  list_subset_bool keep xs = true <->
  forall x, In x xs -> keep x = true.
Proof.
  intros A keep xs. induction xs as [|x xs IH]; simpl.
  - split; [intros _ y Hy; inversion Hy | reflexivity].
  - rewrite andb_true_iff, IH. split.
    + intros [Hx Hall] y [-> | Hy]; [exact Hx | now apply Hall].
    + intro Hall. split; [apply Hall; now left |].
      intros y Hy. apply Hall. now right.
Qed.

Fixpoint list_upper (xs : list nat) : nat :=
  match xs with
  | [] => 0
  | x :: rest => Nat.max (S x) (list_upper rest)
  end.

Lemma list_upper_nil : list_upper [] = 0.
Proof. reflexivity. Qed.

Lemma list_upper_cons : forall x xs,
  list_upper (x :: xs) = Nat.max (S x) (list_upper xs).
Proof. reflexivity. Qed.

Theorem list_member_lt_upper : forall xs x,
  In x xs -> x < list_upper xs.
Proof.
  induction xs as [|y xs IH]; intros x Hx; [inversion Hx |].
  change (x < Nat.max (S y) (list_upper xs)).
  destruct Hx as [-> | Hx].
  - eapply Nat.lt_le_trans; [apply Nat.lt_succ_diag_r | apply Nat.le_max_l].
  - eapply Nat.lt_le_trans; [apply IH; exact Hx | apply Nat.le_max_r].
Qed.

Lemma list_append_incl : forall A (xs ys tail : list A),
  incl xs ys -> incl (xs ++ tail) (ys ++ tail).
Proof.
  intros A xs ys tail H x Hx. apply in_app_iff in Hx.
  apply in_app_iff. destruct Hx as [Hx | Hx]; [left; now apply H | now right].
Qed.

Lemma list_incl_of_eq : forall A (xs ys : list A),
  xs = ys -> incl xs ys.
Proof. intros A xs ys -> x Hx; exact Hx. Qed.

Fixpoint list_remove_all {A}
    (eq_dec : forall x y : A, {x = y} + {x <> y})
    (a : A) (xs : list A) : list A :=
  match xs with
  | [] => []
  | x :: rest =>
      if eq_dec x a then list_remove_all eq_dec a rest
      else x :: list_remove_all eq_dec a rest
  end.

Lemma list_remove_all_nil : forall A eq_dec (a : A),
  list_remove_all eq_dec a [] = [].
Proof. reflexivity. Qed.

Lemma list_remove_all_cons_self : forall A eq_dec (a : A) xs,
  list_remove_all eq_dec a (a :: xs) = list_remove_all eq_dec a xs.
Proof. intros. simpl. destruct (eq_dec a a); [reflexivity | contradiction]. Qed.

Lemma list_remove_all_cons_other : forall A eq_dec (a b : A) xs,
  a <> b ->
  list_remove_all eq_dec b (a :: xs) =
  a :: list_remove_all eq_dec b xs.
Proof.
  intros A eq_dec a b xs Hab. simpl.
  destruct (eq_dec a b); [contradiction | reflexivity].
Qed.

Theorem list_remove_all_member_iff : forall A eq_dec (a b : A) xs,
  In b (list_remove_all eq_dec a xs) <-> In b xs /\ b <> a.
Proof.
  intros A eq_dec a b xs. induction xs as [|x xs IH]; simpl.
  - tauto.
  - destruct (eq_dec x a) as [-> | Hxa].
    + rewrite IH. split.
      * intros [Hb Hne]. split; [now right | exact Hne].
      * intros [[Hab | Hb] Hne].
        { exfalso. apply Hne. now symmetry. }
        now split.
    + simpl. rewrite IH. split.
      * intros [-> | [Hb Hne]]; [now split; [left |] |].
        split; [now right | exact Hne].
      * intros [[-> | Hb] Hne]; [now left | right; now split].
Qed.

Lemma list_remove_all_member : forall A eq_dec (a b : A) xs,
  In b (list_remove_all eq_dec a xs) -> In b xs.
Proof.
  intros A eq_dec a b xs H.
  apply (proj1 (@list_remove_all_member_iff A eq_dec a b xs)) in H.
  exact (proj1 H).
Qed.

Lemma list_remove_all_incl : forall A eq_dec (a : A) xs,
  incl (list_remove_all eq_dec a xs) xs.
Proof.
  intros A eq_dec a xs b Hb.
  exact (@list_remove_all_member A eq_dec a b xs Hb).
Qed.

Lemma list_incl_cons_remove_all : forall A eq_dec (a : A) xs,
  incl xs (a :: list_remove_all eq_dec a xs).
Proof.
  intros A eq_dec a xs b Hb. destruct (eq_dec b a) as [-> | Hba]; [now left |].
  right. apply (proj2 (@list_remove_all_member_iff A eq_dec a b xs)).
  now split.
Qed.

Lemma list_remove_all_mono : forall A eq_dec (a : A) xs ys,
  incl xs ys ->
  incl (list_remove_all eq_dec a xs) (list_remove_all eq_dec a ys).
Proof.
  intros A eq_dec a xs ys Hsub b Hb.
  apply (proj1 (@list_remove_all_member_iff A eq_dec a b xs)) in Hb.
  apply (proj2 (@list_remove_all_member_iff A eq_dec a b ys)).
  split; [now apply Hsub | exact (proj2 Hb)].
Qed.

Lemma list_remove_all_cons_incl : forall A eq_dec (a b : A) xs,
  incl (list_remove_all eq_dec b (a :: xs))
    (a :: list_remove_all eq_dec b xs).
Proof.
  intros A eq_dec a b xs x Hx.
  apply (proj1 (@list_remove_all_member_iff A eq_dec b x (a :: xs))) in Hx.
  destruct Hx as [[-> | Hx] Hne]; [now left |].
  right. apply (proj2 (@list_remove_all_member_iff A eq_dec b x xs)).
  now split.
Qed.

Lemma list_remove_all_map_incl : forall A B eqA eqB
    (f : A -> B) xs a,
  incl (list_remove_all eqB (f a) (map f xs))
    (map f (list_remove_all eqA a xs)).
Proof.
  intros A B eqA eqB f xs a y Hy.
  apply (proj1 (@list_remove_all_member_iff B eqB (f a) y (map f xs))) in Hy.
  destruct Hy as [Hy Hneq]. apply in_map_iff in Hy.
  destruct Hy as [x [Hfx Hx]]. subst y. apply in_map.
  apply (proj2 (@list_remove_all_member_iff A eqA a x xs)).
  split; [exact Hx |].
  intro Hxa. subst. contradiction.
Qed.

Lemma list_induction_with_singleton : forall A (P : list A -> Prop),
  P [] ->
  (forall a, P [a]) ->
  (forall a xs, xs <> [] -> P xs -> P (a :: xs)) ->
  forall xs, P xs.
Proof.
  intros A P Hnil Hsingle Hcons xs. induction xs as [|a xs IH].
  - exact Hnil.
  - destruct xs as [|b xs].
    + apply Hsingle.
    + apply Hcons; [discriminate | exact IH].
Qed.

Fixpoint list_rec_with_singleton {A} (P : list A -> Type)
    (Hnil : P [])
    (Hsingle : forall a, P [a])
    (Hcons : forall a b xs, P (b :: xs) -> P (a :: b :: xs))
    (xs : list A) {struct xs} : P xs :=
  match xs as l return P l with
  | [] => Hnil
  | a :: rest =>
      match rest as r return P r -> P (a :: r) with
      | [] => fun _ => Hsingle a
      | b :: tail => fun Hr => Hcons a b tail Hr
      end (@list_rec_with_singleton A P Hnil Hsingle Hcons rest)
  end.

Definition list_suffix {A} (xs ys : list A) : Prop :=
  exists prefix, ys = prefix ++ xs.

Lemma list_suffix_refl : forall A (xs : list A), list_suffix xs xs.
Proof. intros A xs. exists []. reflexivity. Qed.

Lemma list_suffix_of_cons_suffix : forall A (a : A) xs ys,
  list_suffix (a :: xs) ys -> list_suffix xs ys.
Proof.
  intros A a xs ys [prefix ->]. exists (prefix ++ [a]).
  change (prefix ++ ([a] ++ xs) = (prefix ++ [a]) ++ xs).
  apply app_assoc.
Qed.

Lemma list_suffix_under_cons : forall A (a : A) xs ys,
  list_suffix xs ys -> list_suffix xs (a :: ys).
Proof.
  intros A a xs ys [prefix ->]. exists (a :: prefix). reflexivity.
Qed.

Theorem list_boundary_of_not_suffix : forall A (xs ys : list A),
  ~ list_suffix xs ys ->
  exists common a,
    list_suffix (a :: common) xs /\
    list_suffix common ys /\
    ~ list_suffix (a :: common) ys.
Proof.
  intros A xs. induction xs as [|a xs IH]; intro ys; intro Hnot.
  - exfalso. apply Hnot. exists ys. now rewrite app_nil_r.
  - destruct (classic (list_suffix xs ys)) as [Hs | Hs].
    + exists xs, a. repeat split; try apply list_suffix_refl; assumption.
    + destruct (IH ys Hs) as [common [b [Hb [Hcommon Hnb]]]].
      exists common, b. split.
      * now apply list_suffix_under_cons.
      * now split.
Qed.

Lemma list_suffix_eq_or_cons : forall A (xs ys : list A),
  list_suffix xs ys ->
  xs = ys \/ exists a, list_suffix (a :: xs) ys.
Proof.
  intros A xs ys [prefix Hprefix]. destruct prefix as [|p prefix].
  - left. simpl in Hprefix. now symmetry.
  - right.
    destruct (@exists_last A (p :: prefix) ltac:(discriminate))
      as [front [a Hlast]].
    exists a, front. rewrite Hprefix, Hlast.
    change ((front ++ [a]) ++ xs = front ++ ([a] ++ xs)).
    symmetry. apply app_assoc.
Qed.

Theorem list_suffix_trichotomy : forall A (xs ys : list A),
  ~ list_suffix xs ys -> ~ list_suffix ys xs ->
  exists common a b,
    a <> b /\ list_suffix (a :: common) xs /\
    list_suffix (b :: common) ys.
Proof.
  intros A xs ys Hxy Hyx.
  destruct (@list_boundary_of_not_suffix A xs ys Hxy)
    as [common [a [Ha [Hcommon Hna]]]].
  destruct (@list_suffix_eq_or_cons A common ys Hcommon)
    as [Heq | [b Hb]].
  - subst. exfalso. apply Hyx. now apply list_suffix_of_cons_suffix in Ha.
  - exists common, a, b. repeat split; try assumption.
    intro Hab. subst. contradiction.
Qed.

Lemma list_exists_member_of_nonempty : forall A (xs : list A),
  xs <> [] -> exists x, In x xs.
Proof. intros A [|x xs] H; [contradiction | exists x; now left]. Qed.

Lemma list_nil_iff_all_members_impossible : forall A (xs : list A),
  xs = [] <-> forall x, In x xs -> False.
Proof.
  intros A xs. split; [intros -> x H; inversion H |].
  intro H. destruct xs as [|x xs]; [reflexivity |]. exfalso. apply (H x). now left.
Qed.

Lemma list_exists_of_map_seq : forall A (f : nat -> A) n a,
  In a (map f (seq 0 n)) -> exists i, i < n /\ a = f i.
Proof.
  intros A f n a H. apply in_map_iff in H.
  destruct H as [i [Hfi Hi]]. exists i. split.
  - apply in_seq in Hi. lia.
  - now symmetry.
Qed.

Lemma list_singleton_suffix_unique : forall A (a b : A) xs,
  list_suffix [a] xs -> list_suffix [b] xs -> a = b.
Proof.
  intros A a b xs [left Hleft] [right Hright].
  assert (Heq : left ++ [a] = right ++ [b]).
  { now rewrite <- Hleft, <- Hright. }
  exact (proj2 (app_inj_tail left right a b Heq)).
Qed.
