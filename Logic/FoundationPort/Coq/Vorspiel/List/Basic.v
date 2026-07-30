(** Finite list bounds, deletion, custom induction, and suffix divergence. *)

From Stdlib Require Import Arith.PeanoNat Bool.Bool Lia Lists.List Logic.Classical.
From Foundation.Vorspiel.Fin Require Import Basic.

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

Lemma list_nth_map_seq : forall A (default : A) (f : nat -> A) n i,
  i < n -> nth i (map f (seq 0 n)) default = f i.
Proof.
  intros A default f n i Hi. apply nth_error_nth with (x := f i).
  rewrite nth_error_map, nth_error_seq.
  assert (Hltb : Nat.ltb i n = true) by now apply Nat.ltb_lt.
  rewrite Hltb. reflexivity.
Qed.

Fixpoint list_join {A} (join : A -> A -> A) (bottom : A)
    (xs : list A) : A :=
  match xs with
  | [] => bottom
  | x :: rest => join x (list_join join bottom rest)
  end.

Lemma list_join_nil : forall A join (bottom : A),
  list_join join bottom [] = bottom.
Proof. reflexivity. Qed.

Lemma list_join_cons : forall A join (bottom : A) x xs,
  list_join join bottom (x :: xs) = join x (list_join join bottom xs).
Proof. reflexivity. Qed.

Theorem list_member_le_join : forall A (le : A -> A -> Prop)
    join bottom,
  (forall x y z, le x y -> le y z -> le x z) ->
  (forall x y, le x (join x y)) ->
  (forall x y, le y (join x y)) ->
  forall xs x, In x xs -> le x (list_join join bottom xs).
Proof.
  intros A le join bottom Htrans Hleft Hright xs.
  induction xs as [|y xs IH]; intros x Hx; [inversion Hx |].
  destruct Hx as [-> | Hx].
  - apply Hleft.
  - eapply Htrans; [apply IH; exact Hx | apply Hright].
Qed.

Definition list_of_fin {A n} (f : Fin.t n -> A) : list A :=
  map f (vorspiel_fin_enum n).

Lemma list_of_fin_length : forall A n (f : Fin.t n -> A),
  length (list_of_fin f) = n.
Proof.
  intros A n f. unfold list_of_fin.
  now rewrite length_map, vorspiel_fin_enum_length.
Qed.

Lemma list_of_fin_member_iff : forall A n (f : Fin.t n -> A) x,
  In x (list_of_fin f) <-> exists i, f i = x.
Proof.
  intros A n f x. unfold list_of_fin. rewrite in_map_iff. split.
  - intros [i [Hix _]]. now exists i.
  - intros [i Hix]. exists i. split; [exact Hix | apply vorspiel_fin_enum_complete].
Qed.

Lemma list_of_fin_map : forall A B n (g : A -> B) (f : Fin.t n -> A),
  map g (list_of_fin f) = list_of_fin (fun i => g (f i)).
Proof. intros. unfold list_of_fin. now rewrite map_map. Qed.

Corollary list_fin_member_le_join : forall A (le : A -> A -> Prop)
    join bottom,
  (forall x y z, le x y -> le y z -> le x z) ->
  (forall x y, le x (join x y)) ->
  (forall x y, le y (join x y)) ->
  forall n (f : Fin.t n -> A) i,
    le (f i) (list_join join bottom (list_of_fin f)).
Proof.
  intros A le join bottom Htrans Hleft Hright n f i.
  apply (@list_member_le_join A le join bottom Htrans Hleft Hright
           (list_of_fin f) (f i)).
  apply (proj2 (@list_of_fin_member_iff A n f (f i))). now exists i.
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

Theorem list_nodup_iff_indexed_distinct : forall A (xs : list A),
  NoDup xs <->
  forall i j x,
    i < j -> j < length xs ->
    nth_error xs i = Some x -> nth_error xs j <> Some x.
Proof.
  intros A xs. split.
  - intros Hnodup i j x Hij Hj Hi Hjeq.
    pose proof (proj1 (@NoDup_nth_error A xs) Hnodup i j) as Hindex.
    assert (HiLen : i < length xs) by lia.
    specialize (Hindex HiLen).
    assert (i = j).
    { apply Hindex. now rewrite Hi, Hjeq. }
    lia.
  - intro Hdistinct. apply (proj2 (@NoDup_nth_error A xs)).
    intros i j HiLen Heq.
    destruct (nth_error xs i) as [x |] eqn:Hi.
    + assert (Hj : nth_error xs j = Some x) by now rewrite <- Heq.
      assert (HjLen : j < length xs).
      { apply (proj1 (@nth_error_Some A xs j)). now rewrite Hj. }
      destruct (Nat.lt_trichotomy i j) as [Hij | [Hij | Hij]].
      * exfalso. exact (Hdistinct i j x Hij HjLen Hi Hj).
      * exact Hij.
      * exfalso. exact (Hdistinct j i x Hij HiLen Hj Hi).
    + exfalso. apply (proj2 (@nth_error_Some A xs i) HiLen). exact Hi.
Qed.

Fixpoint list_words_up_to {A} (alphabet : list A) (n : nat) :
    list (list A) :=
  match n with
  | 0 => [[]]
  | S k =>
      list_words_up_to alphabet k ++
      flat_map (fun a => map (cons a) (list_words_up_to alphabet k)) alphabet
  end.

Lemma list_words_up_to_complete : forall A (alphabet : list A) n xs,
  length xs <= n ->
  (forall x, In x xs -> In x alphabet) ->
  In xs (list_words_up_to alphabet n).
Proof.
  intros A alphabet n. induction n as [|n IH]; intros xs Hlen Hall.
  - assert (xs = []) by (apply length_zero_iff_nil; lia).
    subst. simpl. now left.
  - simpl. destruct xs as [|x xs].
    + apply in_app_iff. left.
      apply IH; [simpl; lia | intros y Hy; inversion Hy].
    + apply in_app_iff. right. apply in_flat_map. exists x. split.
      * apply Hall. now left.
      * apply in_map. apply IH.
        { simpl in Hlen. lia. }
        { intros y Hy. apply Hall. now right. }
Qed.

Theorem nodup_lists_explicit_finite_cover : forall A (alphabet : list A),
  (forall x : A, In x alphabet) ->
  forall xs, NoDup xs ->
    In xs (list_words_up_to alphabet (length alphabet)).
Proof.
  intros A alphabet Hcover xs Hnodup.
  apply list_words_up_to_complete.
  - apply NoDup_incl_length with (l := xs); [exact Hnodup |].
    intros x Hx. apply Hcover.
  - intros x Hx. apply Hcover.
Qed.

Lemma list_singleton_suffix_unique : forall A (a b : A) xs,
  list_suffix [a] xs -> list_suffix [b] xs -> a = b.
Proof.
  intros A a b xs [left Hleft] [right Hright].
  assert (Heq : left ++ [a] = right ++ [b]).
  { now rewrite <- Hleft, <- Hright. }
  exact (proj2 (app_inj_tail left right a b Heq)).
Qed.
