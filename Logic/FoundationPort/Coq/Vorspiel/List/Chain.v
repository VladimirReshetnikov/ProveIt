(** Chains represented by ordered list positions. *)

From Stdlib Require Import Arith.PeanoNat Lia Lists.List.
From Foundation.Vorspiel.Fin Require Import Basic.
From Foundation.Vorspiel.List Require Import Basic.

Import ListNotations.

Set Implicit Arguments.
Unset Strict Implicit.

Definition list_chain {A} (R : A -> A -> Prop) (xs : list A) : Prop :=
  forall i j x y,
    i < j ->
    nth_error xs i = Some x ->
    nth_error xs j = Some y ->
    R x y.

Lemma list_member_index : forall A (xs : list A) x,
  In x xs -> exists i,
    i < length xs /\ nth_error xs i = Some x.
Proof.
  intros A xs x Hx. destruct (@In_nth_error A xs x Hx) as [i Hi].
  exists i. split; [|exact Hi].
  apply (proj1 (@nth_error_Some A xs i)). rewrite Hi. discriminate.
Qed.

Lemma list_member_indices_distinct : forall A (xs : list A)
    i j x y,
  nth_error xs i = Some x ->
  nth_error xs j = Some y ->
  x <> y -> i <> j.
Proof.
  intros A xs i j x y Hi Hj Hneq ->.
  rewrite Hi in Hj. inversion Hj. contradiction.
Qed.

Lemma list_chain_map : forall A B (R : A -> A -> Prop)
    (S : B -> B -> Prop) (f : A -> B) xs,
  (forall x y, R x y -> S (f x) (f y)) ->
  list_chain R xs ->
  list_chain S (map f xs).
Proof.
  intros A B R S f xs Hf Hchain i j x y Hij Hi Hj.
  rewrite nth_error_map in Hi, Hj.
  destruct (nth_error xs i) as [u |] eqn:Hui; simpl in Hi; try discriminate.
  destruct (nth_error xs j) as [v |] eqn:Hvj; simpl in Hj; try discriminate.
  inversion Hi; inversion Hj; subst.
  apply Hf. exact (Hchain i j u v Hij Hui Hvj).
Qed.

Theorem list_chain_map_seq : forall A (R : A -> A -> Prop)
    (f : nat -> A) start n,
  (forall i j, i < j -> R (f (start + i)) (f (start + j))) ->
  list_chain R (map f (seq start n)).
Proof.
  intros A R f start n Hmono i j x y Hij Hi Hj.
  rewrite nth_error_map, nth_error_seq in Hi, Hj.
  destruct (Nat.ltb i n) eqn:Hib; simpl in Hi; try discriminate.
  destruct (Nat.ltb j n) eqn:Hjb; simpl in Hj; try discriminate.
  inversion Hi; inversion Hj; subst. now apply Hmono.
Qed.

Corollary list_chain_range_strict_mono : forall A
    (R : A -> A -> Prop) (f : nat -> A) n,
  (forall i j, i < j -> R (f i) (f j)) ->
  list_chain R (map f (seq 0 n)).
Proof.
  intros A R f n Hmono. apply list_chain_map_seq.
  intros i j Hij. now apply Hmono.
Qed.

Corollary list_chain_range_strict_anti : forall A
    (R : A -> A -> Prop) (f : nat -> A) n,
  (forall i j, i < j -> R (f j) (f i)) ->
  list_chain (fun x y => R y x) (map f (seq 0 n)).
Proof.
  intros A R f n Hanti. apply list_chain_map_seq.
  intros i j Hij. now apply Hanti.
Qed.

Lemma list_chain_seq : forall start n,
  list_chain Nat.lt (seq start n).
Proof.
  intros start n i j x y Hij Hi Hj.
  rewrite !nth_error_seq in Hi, Hj.
  destruct (Nat.ltb i n) eqn:Hib; simpl in Hi; try discriminate.
  destruct (Nat.ltb j n) eqn:Hjb; simpl in Hj; try discriminate.
  inversion Hi; inversion Hj; subst. lia.
Qed.

Lemma fin_value_FS : forall n (i : Fin.t n),
  vorspiel_fin_value (Fin.FS i) = S (vorspiel_fin_value i).
Proof.
  intros n i. unfold vorspiel_fin_value. cbn [Fin.to_nat].
  now destruct (Fin.to_nat i).
Qed.

Lemma fin_enum_nth_error_value : forall n k (i : Fin.t n),
  nth_error (vorspiel_fin_enum n) k = Some i ->
  vorspiel_fin_value i = k.
Proof.
  induction n as [|n IH]; intros k i Hi; [inversion i |].
  destruct k as [|k].
  - simpl in Hi. inversion Hi. reflexivity.
  - simpl in Hi. rewrite nth_error_map in Hi.
    destruct (nth_error (vorspiel_fin_enum n) k) as [j |] eqn:Hj;
      simpl in Hi; try discriminate.
    inversion Hi; subst. specialize (IH k j Hj).
    rewrite fin_value_FS. lia.
Qed.

Lemma list_chain_fin_enum : forall n,
  list_chain
    (fun i j : Fin.t n => vorspiel_fin_value i < vorspiel_fin_value j)
    (vorspiel_fin_enum n).
Proof.
  intros n i j x y Hij Hi Hj.
  rewrite (fin_enum_nth_error_value Hi), (fin_enum_nth_error_value Hj).
  exact Hij.
Qed.

Corollary list_chain_fin_enum_strict_mono : forall A n
    (R : A -> A -> Prop) (f : Fin.t n -> A),
  (forall i j, vorspiel_fin_value i < vorspiel_fin_value j -> R (f i) (f j)) ->
  list_chain R (map f (vorspiel_fin_enum n)).
Proof.
  intros A n R f Hmono.
  eapply (@list_chain_map (Fin.t n) A
    (fun i j => vorspiel_fin_value i < vorspiel_fin_value j)
    R f (vorspiel_fin_enum n)); [exact Hmono |].
  apply list_chain_fin_enum.
Qed.

Corollary list_chain_fin_enum_strict_anti : forall A n
    (R : A -> A -> Prop) (f : Fin.t n -> A),
  (forall i j, vorspiel_fin_value i < vorspiel_fin_value j -> R (f j) (f i)) ->
  list_chain (fun x y => R y x) (map f (vorspiel_fin_enum n)).
Proof.
  intros A n R f Hanti.
  eapply (@list_chain_map (Fin.t n) A
    (fun i j => vorspiel_fin_value i < vorspiel_fin_value j)
    (fun x y => R y x) f (vorspiel_fin_enum n)); [exact Hanti |].
  apply list_chain_fin_enum.
Qed.

Lemma list_chain_at : forall A (R : A -> A -> Prop) xs i j x y,
  list_chain R xs ->
  i < j ->
  nth_error xs i = Some x ->
  nth_error xs j = Some y ->
  R x y.
Proof. intros A R xs i j x y H; now apply (H i j x y). Qed.

Theorem list_chain_connected : forall A (R : A -> A -> Prop) xs x y,
  list_chain R xs ->
  In x xs -> In y xs -> x <> y ->
  R x y \/ R y x.
Proof.
  intros A R xs x y Hchain Hx Hy Hneq.
  destruct (@In_nth_error A xs x Hx) as [i Hi].
  destruct (@In_nth_error A xs y Hy) as [j Hj].
  destruct (Nat.lt_trichotomy i j) as [Hij | [Hij | Hij]].
  - left. exact (Hchain i j x y Hij Hi Hj).
  - subst j. rewrite Hi in Hj. inversion Hj. contradiction.
  - right. exact (Hchain j i y x Hij Hj Hi).
Qed.

Theorem list_chain_nodup : forall A (R : A -> A -> Prop) xs,
  (forall x, ~ R x x) ->
  list_chain R xs -> NoDup xs.
Proof.
  intros A R xs Hirrefl Hchain.
  apply (proj2 (@list_nodup_iff_indexed_distinct A xs)).
  intros i j x Hij Hj Hi Hjeq.
  exact (Hirrefl x (Hchain i j x x Hij Hi Hjeq)).
Qed.

Theorem chain_lists_explicit_finite_cover : forall A
    (R : A -> A -> Prop) (alphabet : list A),
  (forall x : A, In x alphabet) ->
  (forall x, ~ R x x) ->
  forall xs, list_chain R xs ->
    In xs (list_words_up_to alphabet (length alphabet)).
Proof.
  intros A R alphabet Hcover Hirrefl xs Hchain.
  apply nodup_lists_explicit_finite_cover; [exact Hcover |].
  now apply (list_chain_nodup Hirrefl).
Qed.

Lemma list_chain_rev : forall A (R : A -> A -> Prop) xs,
  list_chain R xs ->
  list_chain (fun x y => R y x) (rev xs).
Proof.
  intros A R xs Hchain i j x y Hij Hi Hj.
  rewrite !nth_error_rev in Hi, Hj.
  destruct (Nat.ltb i (length xs)) eqn:Hilen; try discriminate.
  destruct (Nat.ltb j (length xs)) eqn:Hjlen; try discriminate.
  apply Nat.ltb_lt in Hilen. apply Nat.ltb_lt in Hjlen.
  exact (Hchain (length xs - S j) (length xs - S i)
    y x ltac:(lia) Hj Hi).
Qed.

Corollary list_chain_fin_enum_rev : forall n,
  list_chain
    (fun i j : Fin.t n => vorspiel_fin_value j < vorspiel_fin_value i)
    (rev (vorspiel_fin_enum n)).
Proof. intro n. now apply list_chain_rev, list_chain_fin_enum. Qed.

Lemma nth_error_app_singleton_last : forall A (xs : list A) a,
  nth_error (xs ++ [a]) (length xs) = Some a.
Proof.
  intros A xs a. rewrite nth_error_app2 by lia.
  replace (length xs - length xs) with 0 by lia. reflexivity.
Qed.

Theorem list_chain_app_singleton_iff : forall A
    (R : A -> A -> Prop) xs a,
  list_chain R (xs ++ [a]) <->
  list_chain R xs /\ forall x, In x xs -> R x a.
Proof.
  intros A R xs a. split.
  - intro Hchain. split.
    + intros i j x y Hij Hi Hj.
      apply (Hchain i j x y Hij).
      * now rewrite nth_error_app1 by
          (apply (proj1 (@nth_error_Some A xs i)); rewrite Hi; discriminate).
      * now rewrite nth_error_app1 by
          (apply (proj1 (@nth_error_Some A xs j)); rewrite Hj; discriminate).
    + intros x Hx. destruct (@In_nth_error A xs x Hx) as [i Hi].
      apply (Hchain i (length xs) x a).
      * apply (proj1 (@nth_error_Some A xs i)). rewrite Hi. discriminate.
      * now rewrite nth_error_app1 by
          (apply (proj1 (@nth_error_Some A xs i)); rewrite Hi; discriminate).
      * apply nth_error_app_singleton_last.
  - intros [Hchain Hall] i j x y Hij Hi Hj.
    assert (HjLen : j < length (xs ++ [a])).
    { apply (proj1 (@nth_error_Some A (xs ++ [a]) j)).
      rewrite Hj. discriminate. }
    rewrite length_app in HjLen. simpl in HjLen.
    destruct (Nat.lt_ge_cases j (length xs)) as [Hjxs | Hjlast].
    + apply (Hchain i j x y Hij).
      * now rewrite nth_error_app1 in Hi by lia.
      * now rewrite nth_error_app1 in Hj by lia.
    + assert (j = length xs) by lia. subst j.
      assert (Hixs : nth_error xs i = Some x).
      { now rewrite nth_error_app1 in Hi by lia. }
      assert (y = a).
      { rewrite nth_error_app_singleton_last in Hj. now inversion Hj. }
      subst y. apply Hall. now apply (@nth_error_In A xs i x).
Qed.

Theorem list_chain_head_relation : forall A
    (R : A -> A -> Prop) a xs x,
  list_chain R (a :: xs) ->
  In x (a :: xs) -> x <> a -> R a x.
Proof.
  intros A R a xs x Hchain Hx Hneq.
  destruct Hx as [Hx | Hx].
  - exfalso. apply Hneq. now symmetry.
  - destruct (@In_nth_error A xs x Hx) as [i Hi].
    exact (Hchain 0 (S i) a x ltac:(lia) eq_refl Hi).
Qed.

Corollary list_chain_head_lower : forall A
    (R : A -> A -> Prop) a xs,
  (forall x, R x x) ->
  list_chain R (a :: xs) ->
  forall x, In x (a :: xs) -> R a x.
Proof.
  intros A R a xs Hrefl Hchain x Hx.
  destruct Hx as [<- | Hx]; [apply Hrefl |].
  destruct (@In_nth_error A xs x Hx) as [i Hi].
  exact (Hchain 0 (S i) a x ltac:(lia) eq_refl Hi).
Qed.

Theorem list_chain_last_relation : forall A
    (R : A -> A -> Prop) xs default,
  xs <> [] -> list_chain R xs ->
  forall x, In x xs -> x <> last xs default -> R x (last xs default).
Proof.
  intros A R xs default Hnonempty Hchain x Hx Hneq.
  pose proof (@app_removelast_last A xs default Hnonempty) as Hsplit.
  rewrite Hsplit in Hchain, Hx, Hneq |- *.
  rewrite last_last in Hneq |- *.
  apply (proj1 (list_chain_app_singleton_iff R
    (removelast xs) (last xs default))) in Hchain.
  destruct Hchain as [_ Hlast]. apply in_app_iff in Hx.
  destruct Hx as [Hx | Hx]; [now apply Hlast |].
  simpl in Hx. destruct Hx as [Hx | Hx].
  - exfalso. apply Hneq. now symmetry.
  - inversion Hx.
Qed.

Corollary list_chain_last_upper : forall A
    (R : A -> A -> Prop) xs default,
  (forall x, R x x) ->
  xs <> [] -> list_chain R xs ->
  forall x, In x xs -> R x (last xs default).
Proof.
  intros A R xs default Hrefl Hnonempty Hchain x Hx.
  pose proof (@app_removelast_last A xs default Hnonempty) as Hsplit.
  rewrite Hsplit in Hchain, Hx |- *.
  rewrite last_last.
  apply (proj1 (list_chain_app_singleton_iff R
    (removelast xs) (last xs default))) in Hchain.
  destruct Hchain as [_ Hlast]. apply in_app_iff in Hx.
  destruct Hx as [Hx | Hx]; [now apply Hlast |].
  simpl in Hx. destruct Hx as [Hx | Hx]; [now subst | inversion Hx].
Qed.

Theorem list_chain_app_singleton_last_iff : forall A
    (R : A -> A -> Prop) xs default a,
  (forall x, R x x) ->
  (forall x y z, R x y -> R y z -> R x z) ->
  xs <> [] ->
  (list_chain R (xs ++ [a]) <->
    list_chain R xs /\ R (last xs default) a).
Proof.
  intros A R xs default a Hrefl Htrans Hnonempty. split.
  - intro Happ.
    apply (proj1 (list_chain_app_singleton_iff R xs a)) in Happ.
    destruct Happ as [Hchain Hall]. split; [exact Hchain |].
    apply Hall. pose proof (@app_removelast_last A xs default Hnonempty) as Hsplit.
    rewrite Hsplit, last_last. apply in_app_iff. right. now left.
  - intros [Hchain Hlast].
    apply (proj2 (list_chain_app_singleton_iff R xs a)).
    split; [exact Hchain |]. intros x Hx.
    eapply Htrans; [|exact Hlast].
    exact (@list_chain_last_upper A R xs default
      Hrefl Hnonempty Hchain x Hx).
Qed.

Fixpoint chain_list_index {A} (xs : list A) : Fin.t (length xs) -> A :=
  match xs as ys return Fin.t (length ys) -> A with
  | [] => fun i => match i with end
  | x :: rest => fun i =>
      @Fin.caseS' (length rest) i (fun _ => A) x (@chain_list_index A rest)
  end.

Lemma chain_list_index_member : forall A (xs : list A) (i : Fin.t (length xs)),
  In (@chain_list_index A xs i) xs.
Proof.
  intros A xs. induction xs as [|x xs IH]; intro i; [inversion i |].
  refine (@Fin.caseS' (length xs) i
    (fun j => In (@chain_list_index A (x :: xs) j) (x :: xs)) _ _).
  - now left.
  - intro j. right. apply IH.
Qed.

Theorem chain_list_index_injective_of_nodup : forall A (xs : list A),
  NoDup xs ->
  forall i j : Fin.t (length xs),
    @chain_list_index A xs i = @chain_list_index A xs j -> i = j.
Proof.
  intros A xs Hnodup. induction Hnodup as [|x xs Hnotin Hnodup IH].
  - intros i. inversion i.
  - intros i. refine (@Fin.caseS' (length xs) i
      (fun i => forall j,
        @chain_list_index A (x :: xs) i =
        @chain_list_index A (x :: xs) j -> i = j)
      _ _).
    + intro j. refine (@Fin.caseS' (length xs) j
        (fun j => @chain_list_index A (x :: xs) Fin.F1 =
          @chain_list_index A (x :: xs) j -> Fin.F1 = j) _ _).
      * intro. reflexivity.
      * intros k Heq. change (x = @chain_list_index A xs k) in Heq.
        exfalso. apply Hnotin. rewrite Heq.
        apply chain_list_index_member.
    + intros k j. refine (@Fin.caseS' (length xs) j
        (fun j => @chain_list_index A (x :: xs) (Fin.FS k) =
          @chain_list_index A (x :: xs) j -> Fin.FS k = j) _ _).
      * intro Heq. change (@chain_list_index A xs k = x) in Heq.
        exfalso. apply Hnotin. rewrite <- Heq.
        apply chain_list_index_member.
      * intros l Heq.
        change (@chain_list_index A xs k = @chain_list_index A xs l) in Heq.
        f_equal. now apply IH.
Qed.

Record type_embedding (I A : Type) := {
  type_embedding_fun : I -> A;
  type_embedding_injective : forall i j,
    type_embedding_fun i = type_embedding_fun j -> i = j
}.

Definition list_embedding_of_nodup_length : forall A (xs : list A) n,
  NoDup xs -> length xs = n -> type_embedding (Fin.t n) A.
Proof.
  intros A xs n Hnodup Hlength. subst n.
  refine {| type_embedding_fun := @chain_list_index A xs |}.
  now apply (@chain_list_index_injective_of_nodup A xs).
Defined.
