(** Permutations and contraction-complete list inclusion. *)

From Stdlib Require Import Lia Lists.List Sorting.Permutation.

Import ListNotations.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

Theorem list_permutation_two_iff : forall A (a b : A) l,
  Permutation l [a; b] <-> l = [a; b] \/ l = [b; a].
Proof.
  intros A a b l. split.
  - intro H. pose proof (Permutation_length H) as Hlength.
    destruct l as [|x [|y tail]]; simpl in Hlength; try discriminate.
    destruct tail; [| discriminate].
    apply Permutation_sym in H.
    apply Permutation_length_2 in H.
    destruct H as [[-> ->] | [-> ->]]; [now left | now right].
  - intros [-> | ->]; [apply Permutation_refl | apply perm_swap].
Qed.

Inductive list_comp_subset {A} : list A -> list A -> Type :=
| comp_subset_refl : forall xs, list_comp_subset xs xs
| comp_subset_perm : forall xs ys zs,
    list_comp_subset xs ys -> Permutation ys zs -> list_comp_subset xs zs
| comp_subset_add : forall xs ys a,
    list_comp_subset xs ys -> list_comp_subset xs (a :: ys)
| comp_subset_double : forall xs ys a,
    list_comp_subset xs (a :: a :: ys) -> list_comp_subset xs (a :: ys).

Arguments comp_subset_refl {A} xs.
Arguments comp_subset_perm {A xs ys zs} _ _.
Arguments comp_subset_add {A xs ys} a _.
Arguments comp_subset_double {A xs ys a} _.

Theorem list_permutation_normalize : forall A
    (eq_dec : forall x y : A, {x = y} + {x <> y})
    (xs : list A) a,
  Permutation xs
    (repeat a (count_occ eq_dec xs a) ++ remove eq_dec a xs).
Proof.
  intros A eq_dec xs. induction xs as [|b xs IH]; intro a; simpl.
  - apply Permutation_refl.
  - destruct (eq_dec b a) as [Hab | Hab].
    + subst b. destruct (eq_dec a a) as [_ | Hneq]; [| contradiction].
      simpl. apply perm_skip. apply IH.
    + destruct (eq_dec a b) as [Hba | Hba]; [congruence |].
      eapply Permutation_trans.
      * apply perm_skip. apply IH.
      * apply Permutation_middle.
Qed.

Theorem list_comp_subset_contract : forall A k (a : A) xs ys,
  0 < k ->
  list_comp_subset xs (repeat a k ++ ys) ->
  list_comp_subset xs (a :: ys).
Proof.
  intros A k. induction k as [|k IH]; intros a xs ys Hpos Hcomp;
    [lia |].
  destruct k as [|k].
  - exact Hcomp.
  - simpl in Hcomp. apply IH; [lia |].
    exact (comp_subset_double Hcomp).
Qed.

Theorem list_comp_subset_trans : forall A (xs ys zs : list A),
  list_comp_subset xs ys -> list_comp_subset ys zs ->
  list_comp_subset xs zs.
Proof.
  intros A xs ys zs Hxy Hyz. induction Hyz.
  - exact Hxy.
  - exact (comp_subset_perm (IHHyz Hxy) p).
  - exact (comp_subset_add a (IHHyz Hxy)).
  - exact (comp_subset_double (IHHyz Hxy)).
Qed.

Theorem list_comp_subset_cons : forall A (xs ys : list A),
  list_comp_subset xs ys -> forall a,
  list_comp_subset (a :: xs) (a :: ys).
Proof.
  intros A xs ys H.
  induction H as [xs | xs ys zs Hsub IH Hperm |
    xs ys added Hsub IH | xs ys doubled Hsub IH]; intro head.
  - apply comp_subset_refl.
  - apply (comp_subset_perm (IH head) (perm_skip head Hperm)).
  - eapply comp_subset_perm.
    + exact (comp_subset_add added (IH head)).
    + apply perm_swap.
  - eapply comp_subset_perm.
    + apply (@comp_subset_double A (head :: xs) (head :: ys) doubled).
      eapply comp_subset_perm.
      * exact (IH head).
      * exact (@Permutation_middle A [doubled; doubled] ys head).
    + apply perm_swap.
Qed.

Theorem list_incl_to_comp_subset : forall A
    (eq_dec : forall x y : A, {x = y} + {x <> y})
    (xs ys : list A),
  incl xs ys -> list_comp_subset xs ys.
Proof.
  intros A eq_dec xs ys. revert xs.
  induction ys as [|a ys IH]; intros xs Hincl.
  - destruct xs as [|x xs].
    + apply comp_subset_refl.
    + exfalso. specialize (Hincl x (or_introl eq_refl)). exact Hincl.
  - destruct (in_dec eq_dec a xs) as [Ha | Ha].
    + pose proof (list_permutation_normalize eq_dec xs a) as Hperm.
      pose (Hnormalized := comp_subset_perm (comp_subset_refl xs) Hperm).
      pose proof (proj1 (count_occ_In eq_dec xs a) Ha) as Hcount.
      pose (Hcontracted := list_comp_subset_contract Hcount Hnormalized).
      assert (Hremove : incl (remove eq_dec a xs) ys).
      { intros x Hx. destruct (in_remove eq_dec xs x a Hx) as [Hxin Hne].
        specialize (Hincl x Hxin). simpl in Hincl.
        destruct Hincl as [Hxa | Htailin]; [congruence | exact Htailin]. }
      pose proof (IH _ Hremove) as Htail.
      exact (list_comp_subset_trans Hcontracted
        (list_comp_subset_cons Htail a)).
    + apply comp_subset_add. apply IH.
      intros x Hx. specialize (Hincl x Hx). simpl in Hincl.
      destruct Hincl as [Hxa | Hxin]; [subst x; contradiction | exact Hxin].
Qed.
