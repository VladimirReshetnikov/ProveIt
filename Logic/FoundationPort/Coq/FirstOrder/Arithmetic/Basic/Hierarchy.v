(**
  The arithmetical hierarchy over the ordered-ring language.

  Foundation states the hierarchy for every language carrying a distinguished
  strict-order operator.  The port specializes it to the canonical arithmetic
  language used by every downstream arithmetic theorem, avoiding an otherwise
  pervasive explicit operator parameter while retaining the exact grammar.
*)

From Stdlib Require Import Bool.Bool Arith.PeanoNat Lia Lists.List.
From FoundationModal Require Import GenericEntailment GenericSemantics.
From Foundation.Syntax.Predicate Require Import Language Term Rew.
From Foundation.FirstOrder.Basic.Syntax Require Import Formula.
From Foundation.FirstOrder.Basic Require Import Calculus Operator.
From Foundation.FirstOrder.Basic.Semantics Require Import ModelTheory.
From Foundation.FirstOrder Require Import Polarity.
From Foundation.FirstOrder.Arithmetic.Basic Require Import Model.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

Import ListNotations.

Definition arithmetic_sigma : bool := true.
Definition arithmetic_pi : bool := false.
Definition arithmetic_polarity_alt (pol : bool) : bool := negb pol.

Definition arithmetic_lt_operator :
    semiformula_has_lt_operator oring_language :=
  semiformula_lt_operator_of_language
    (language_oring_lt oring_language_structure).

Definition arithmetic_lt_guard {X n}
    (t : semiterm oring_language X (S n)) :
    semiformula oring_language X (S n) :=
  semiformula_operator_apply
    (semiformula_lt_operator arithmetic_lt_operator)
    (fin_two (Semiterm_bvar Fin.F1) t).

Definition arithmetic_bounded_all {X n}
    (t : semiterm oring_language X (S n))
    (p : semiformula oring_language X (S n)) :
    semiformula oring_language X n :=
  semiformula_bounded_all (arithmetic_lt_guard t) p.

Definition arithmetic_bounded_exists {X n}
    (t : semiterm oring_language X (S n))
    (p : semiformula oring_language X (S n)) :
    semiformula oring_language X n :=
  semiformula_bounded_exists (arithmetic_lt_guard t) p.

Unset Implicit Arguments.
Inductive arithmetic_hierarchy (X : Type) :
    bool -> nat -> forall n,
      semiformula oring_language X n -> Prop :=
| AH_verum : forall pol s n,
    arithmetic_hierarchy X pol s n (Semiformula_verum n)
| AH_falsum : forall pol s n,
    arithmetic_hierarchy X pol s n (Semiformula_falsum n)
| AH_rel : forall pol s n k (r : language_rel oring_language k)
                  (v : Fin.t k -> semiterm oring_language X n),
    arithmetic_hierarchy X pol s n (Semiformula_rel r v)
| AH_nrel : forall pol s n k (r : language_rel oring_language k)
                   (v : Fin.t k -> semiterm oring_language X n),
    arithmetic_hierarchy X pol s n (Semiformula_nrel r v)
| AH_and : forall pol s n (p q : semiformula oring_language X n),
    arithmetic_hierarchy X pol s n p ->
    arithmetic_hierarchy X pol s n q ->
    arithmetic_hierarchy X pol s n (Semiformula_and p q)
| AH_or : forall pol s n (p q : semiformula oring_language X n),
    arithmetic_hierarchy X pol s n p ->
    arithmetic_hierarchy X pol s n q ->
    arithmetic_hierarchy X pol s n (Semiformula_or p q)
| AH_ball : forall pol s n
    (t : semiterm oring_language X (S n))
    (p : semiformula oring_language X (S n)),
    semiterm_positive t ->
    arithmetic_hierarchy X pol s (S n) p ->
    arithmetic_hierarchy X pol s n (arithmetic_bounded_all t p)
| AH_bex : forall pol s n
    (t : semiterm oring_language X (S n))
    (p : semiformula oring_language X (S n)),
    semiterm_positive t ->
    arithmetic_hierarchy X pol s (S n) p ->
    arithmetic_hierarchy X pol s n (arithmetic_bounded_exists t p)
| AH_exists : forall s n (p : semiformula oring_language X (S n)),
    arithmetic_hierarchy X arithmetic_sigma (S s) (S n) p ->
    arithmetic_hierarchy X arithmetic_sigma (S s) n
      (Semiformula_exists p)
| AH_all : forall s n (p : semiformula oring_language X (S n)),
    arithmetic_hierarchy X arithmetic_pi (S s) (S n) p ->
    arithmetic_hierarchy X arithmetic_pi (S s) n (Semiformula_all p)
| AH_sigma : forall s n (p : semiformula oring_language X (S n)),
    arithmetic_hierarchy X arithmetic_pi s (S n) p ->
    arithmetic_hierarchy X arithmetic_sigma (S s) n
      (Semiformula_exists p)
| AH_pi : forall s n (p : semiformula oring_language X (S n)),
    arithmetic_hierarchy X arithmetic_sigma s (S n) p ->
    arithmetic_hierarchy X arithmetic_pi (S s) n (Semiformula_all p)
| AH_dummy_sigma : forall s n
    (p : semiformula oring_language X (S n)),
    arithmetic_hierarchy X arithmetic_pi (S s) (S n) p ->
    arithmetic_hierarchy X arithmetic_sigma (S (S s)) n
      (Semiformula_all p)
| AH_dummy_pi : forall s n
    (p : semiformula oring_language X (S n)),
    arithmetic_hierarchy X arithmetic_sigma (S s) (S n) p ->
    arithmetic_hierarchy X arithmetic_pi (S (S s)) n
      (Semiformula_exists p).
Set Implicit Arguments.

Arguments AH_verum {X} pol s n.
Arguments AH_falsum {X} pol s n.
Arguments AH_rel {X} pol s n k r v.
Arguments AH_nrel {X} pol s n k r v.
Arguments AH_and {X pol s n p q} _ _.
Arguments AH_or {X pol s n p q} _ _.
Arguments AH_ball {X pol s n t p} _ _.
Arguments AH_bex {X pol s n t p} _ _.
Arguments AH_exists {X s n p} _.
Arguments AH_all {X s n p} _.
Arguments AH_sigma {X s n p} _.
Arguments AH_pi {X s n p} _.
Arguments AH_dummy_sigma {X s n p} _.
Arguments AH_dummy_pi {X s n p} _.

Definition arithmetic_delta_zero {X n}
    (p : semiformula oring_language X n) : Prop :=
  arithmetic_hierarchy X arithmetic_sigma 0 n p.

Theorem arithmetic_hierarchy_accum : forall X pol s n
    (p : semiformula oring_language X n),
  arithmetic_hierarchy X pol s n p ->
  forall pol', arithmetic_hierarchy X pol' (S s) n p.
Proof.
  intros X pol s n p H; induction H; intro pol';
    try solve [constructor]; try solve [constructor; eauto].
  - destruct pol'.
    + apply AH_exists. apply IHarithmetic_hierarchy.
    + apply AH_dummy_pi. exact H.
  - destruct pol'.
    + apply AH_dummy_sigma. exact H.
    + apply AH_all. apply IHarithmetic_hierarchy.
  - destruct pol'.
    + apply AH_sigma. apply IHarithmetic_hierarchy.
    + apply AH_dummy_pi. apply IHarithmetic_hierarchy.
  - destruct pol'.
    + apply AH_dummy_sigma. apply IHarithmetic_hierarchy.
    + apply AH_pi. apply IHarithmetic_hierarchy.
  - destruct pol'.
    + apply AH_dummy_sigma. apply IHarithmetic_hierarchy.
    + apply AH_pi. apply IHarithmetic_hierarchy.
  - destruct pol'.
    + apply AH_sigma. apply IHarithmetic_hierarchy.
    + apply AH_dummy_pi. apply IHarithmetic_hierarchy.
Qed.

Lemma arithmetic_hierarchy_accum_iter : forall X pol s n
    (p : semiformula oring_language X n),
  arithmetic_hierarchy X pol s n p ->
  forall d pol', arithmetic_hierarchy X pol' (S s + d) n p.
Proof.
  intros X pol s n p H d; induction d as [|d IH]; intro pol'.
  - rewrite Nat.add_0_r. exact (arithmetic_hierarchy_accum H pol').
  - replace (S s + S d) with (S (S s + d)) by lia.
    exact (arithmetic_hierarchy_accum (IH pol') pol').
Qed.

Theorem arithmetic_hierarchy_strict_mono : forall X pol s n
    (p : semiformula oring_language X n),
  arithmetic_hierarchy X pol s n p ->
  forall pol' s', s < s' -> arithmetic_hierarchy X pol' s' n p.
Proof.
  intros X pol s n p H pol' s' Hlt.
  assert (Hd : exists d, s' = S s + d).
  { exists (s' - S s). lia. }
  destruct Hd as [d ->].
  now apply arithmetic_hierarchy_accum_iter with (pol := pol).
Qed.

Theorem arithmetic_hierarchy_mono : forall X pol s n
    (p : semiformula oring_language X n),
  arithmetic_hierarchy X pol s n p ->
  forall s', s <= s' -> arithmetic_hierarchy X pol s' n p.
Proof.
  intros X pol s n p H s' Hle.
  destruct (Nat.eq_dec s s') as [-> | Hne]; [exact H |].
  apply arithmetic_hierarchy_strict_mono with (pol := pol) (s := s);
    [exact H | lia].
Qed.

Theorem arithmetic_hierarchy_zero_alt : forall X pol n
    (p : semiformula oring_language X n),
  arithmetic_hierarchy X pol 0 n p ->
  arithmetic_hierarchy X (arithmetic_polarity_alt pol) 0 n p.
Proof.
  intros X pol n p H. remember 0 as level eqn:Hlevel.
  induction H; inversion Hlevel; subst; try constructor; eauto.
Qed.

Corollary arithmetic_hierarchy_zero_iff : forall X pol pol' n
    (p : semiformula oring_language X n),
  arithmetic_hierarchy X pol 0 n p <->
  arithmetic_hierarchy X pol' 0 n p.
Proof.
  intros X pol pol' n p. destruct pol, pol'; simpl; try tauto;
    split; apply arithmetic_hierarchy_zero_alt.
Qed.

Theorem arithmetic_hierarchy_and_iff : forall X pol s n
    (p q : semiformula oring_language X n),
  arithmetic_hierarchy X pol s n (Semiformula_and p q) <->
  arithmetic_hierarchy X pol s n p /\
  arithmetic_hierarchy X pol s n q.
Proof.
  intros X pol s n p q; split.
  - intro H. inversion H; subst.
    match goal with
    | E1 : existT _ n ?a = existT _ n p,
      E2 : existT _ n ?b = existT _ n q |- _ =>
        apply existT_nat_injective in E1;
        apply existT_nat_injective in E2; subst; auto
    end.
  - intros [Hp Hq]. now apply AH_and.
Qed.

Theorem arithmetic_hierarchy_or_iff : forall X pol s n
    (p q : semiformula oring_language X n),
  arithmetic_hierarchy X pol s n (Semiformula_or p q) <->
  arithmetic_hierarchy X pol s n p /\
  arithmetic_hierarchy X pol s n q.
Proof.
  intros X pol s n p q; split.
  - intro H. inversion H; subst.
    match goal with
    | E1 : existT _ n ?a = existT _ n p,
      E2 : existT _ n ?b = existT _ n q |- _ =>
        apply existT_nat_injective in E1;
        apply existT_nat_injective in E2; subst; auto
    end.
  - intros [Hp Hq]. now apply AH_or.
Qed.

Theorem arithmetic_hierarchy_neg : forall X pol s n
    (p : semiformula oring_language X n),
  arithmetic_hierarchy X pol s n p ->
  arithmetic_hierarchy X (arithmetic_polarity_alt pol) s n
    (semiformula_neg p).
Proof.
  intros X pol s n p H; induction H.
  - simpl. apply AH_falsum.
  - simpl. apply AH_verum.
  - simpl. apply AH_nrel.
  - simpl. apply AH_rel.
  - simpl. apply AH_or; assumption.
  - simpl. apply AH_and; assumption.
  - unfold arithmetic_bounded_all.
    rewrite semiformula_neg_bounded_all.
    apply AH_bex; assumption.
  - unfold arithmetic_bounded_exists.
    rewrite semiformula_neg_bounded_exists.
    apply AH_ball; assumption.
  - simpl. apply AH_all. exact IHarithmetic_hierarchy.
  - simpl. apply AH_exists. exact IHarithmetic_hierarchy.
  - simpl. apply AH_pi. exact IHarithmetic_hierarchy.
  - simpl. apply AH_sigma. exact IHarithmetic_hierarchy.
  - simpl. apply AH_dummy_pi. exact IHarithmetic_hierarchy.
  - simpl. apply AH_dummy_sigma. exact IHarithmetic_hierarchy.
Qed.

Corollary arithmetic_hierarchy_neg_iff : forall X pol s n
    (p : semiformula oring_language X n),
  arithmetic_hierarchy X pol s n (semiformula_neg p) <->
  arithmetic_hierarchy X (arithmetic_polarity_alt pol) s n p.
Proof.
  intros. split; intro H.
  - pose proof (arithmetic_hierarchy_neg H) as Hneg.
    rewrite semiformula_neg_involutive in Hneg.
    destruct pol; exact Hneg.
  - pose proof (arithmetic_hierarchy_neg H) as Hneg.
    destruct pol; exact Hneg.
Qed.

Corollary arithmetic_hierarchy_imp_iff : forall X pol s n
    (p q : semiformula oring_language X n),
  arithmetic_hierarchy X pol s n (semiformula_imp p q) <->
  arithmetic_hierarchy X (arithmetic_polarity_alt pol) s n p /\
  arithmetic_hierarchy X pol s n q.
Proof.
  intros. unfold semiformula_imp.
  rewrite arithmetic_hierarchy_or_iff,
    arithmetic_hierarchy_neg_iff. reflexivity.
Qed.

Corollary arithmetic_hierarchy_iff_iff : forall X pol s n
    (p q : semiformula oring_language X n),
  arithmetic_hierarchy X pol s n (semiformula_iff p q) <->
  arithmetic_hierarchy X pol s n p /\
  arithmetic_hierarchy X (arithmetic_polarity_alt pol) s n p /\
  arithmetic_hierarchy X pol s n q /\
  arithmetic_hierarchy X (arithmetic_polarity_alt pol) s n q.
Proof.
  intros. unfold semiformula_iff.
  rewrite arithmetic_hierarchy_and_iff,
    !arithmetic_hierarchy_imp_iff.
  destruct pol; simpl; tauto.
Qed.

Corollary arithmetic_hierarchy_zero_iff_iff : forall X pol n
    (p q : semiformula oring_language X n),
  arithmetic_hierarchy X pol 0 n (semiformula_iff p q) <->
  arithmetic_hierarchy X pol 0 n p /\
  arithmetic_hierarchy X pol 0 n q.
Proof.
  intros. rewrite arithmetic_hierarchy_iff_iff.
  split.
  - intros [Hp [_ [Hq _]]]. now split.
  - intros [Hp Hq]. repeat split; try assumption;
      now apply arithmetic_hierarchy_zero_alt.
Qed.

Theorem arithmetic_hierarchy_of_open : forall X n
    (p : semiformula oring_language X n),
  semiformula_open p ->
  forall pol s, arithmetic_hierarchy X pol s n p.
Proof.
  intros X n p; induction p; intros Hopen pol level.
  - apply AH_verum.
  - apply AH_falsum.
  - apply AH_rel.
  - apply AH_nrel.
  - apply (proj1 (semiformula_open_and p1 p2)) in Hopen.
    apply AH_and; [apply IHp1 | apply IHp2]; tauto.
  - apply (proj1 (semiformula_open_or p1 p2)) in Hopen.
    apply AH_or; [apply IHp1 | apply IHp2]; tauto.
  - exfalso. exact (@semiformula_not_open_all
      oring_language X n p Hopen).
  - exfalso. exact (@semiformula_not_open_exists
      oring_language X n p Hopen).
Qed.

Lemma arithmetic_lt_guard_open : forall X n
    (t : semiterm oring_language X (S n)),
  semiformula_open (arithmetic_lt_guard t).
Proof.
  intros. unfold arithmetic_lt_guard, arithmetic_lt_operator.
  apply semiformula_lt_operator_open.
Qed.

Theorem arithmetic_hierarchy_remove_all : forall X pol s n
    (p : semiformula oring_language X (S n)),
  arithmetic_hierarchy X pol s n (Semiformula_all p) ->
  arithmetic_hierarchy X pol s (S n) p.
Proof.
  intros X pol s n p H. inversion H; subst.
  all: match goal with
  | E : @existT nat _ _ _ = @existT nat _ _ _ |- _ =>
      apply existT_nat_injective in E; subst
  end.
  - apply (proj2 (@arithmetic_hierarchy_imp_iff
      X pol s (S n) (arithmetic_lt_guard t) p0)). split.
    + apply arithmetic_hierarchy_of_open. apply arithmetic_lt_guard_open.
    + assumption.
  - assumption.
  - eapply arithmetic_hierarchy_strict_mono; eauto; lia.
  - eapply arithmetic_hierarchy_strict_mono; eauto; lia.
Qed.

Theorem arithmetic_hierarchy_remove_exists : forall X pol s n
    (p : semiformula oring_language X (S n)),
  arithmetic_hierarchy X pol s n (Semiformula_exists p) ->
  arithmetic_hierarchy X pol s (S n) p.
Proof.
  intros X pol s n p H. inversion H; subst.
  all: match goal with
  | E : @existT nat _ _ _ = @existT nat _ _ _ |- _ =>
      apply existT_nat_injective in E; subst
  end.
  - apply (proj2 (@arithmetic_hierarchy_and_iff
      X pol s (S n) (arithmetic_lt_guard t) p0)). split.
    + apply arithmetic_hierarchy_of_open. apply arithmetic_lt_guard_open.
    + assumption.
  - assumption.
  - eapply arithmetic_hierarchy_strict_mono; eauto; lia.
  - eapply arithmetic_hierarchy_strict_mono; eauto; lia.
Qed.

Theorem arithmetic_hierarchy_bounded_all_iff : forall X pol s n
    (t : semiterm oring_language X (S n))
    (p : semiformula oring_language X (S n)),
  semiterm_positive t ->
  (arithmetic_hierarchy X pol s n (arithmetic_bounded_all t p) <->
   arithmetic_hierarchy X pol s (S n) p).
Proof.
  intros X pol s n t p Hpositive; split.
  - intro H. unfold arithmetic_bounded_all in H.
    apply arithmetic_hierarchy_remove_all in H.
    apply (proj1 (@arithmetic_hierarchy_imp_iff
      X pol s (S n) (arithmetic_lt_guard t) p)) in H. tauto.
  - intro H. now apply AH_ball.
Qed.

Theorem arithmetic_hierarchy_bounded_exists_iff : forall X pol s n
    (t : semiterm oring_language X (S n))
    (p : semiformula oring_language X (S n)),
  semiterm_positive t ->
  (arithmetic_hierarchy X pol s n (arithmetic_bounded_exists t p) <->
   arithmetic_hierarchy X pol s (S n) p).
Proof.
  intros X pol s n t p Hpositive; split.
  - intro H. unfold arithmetic_bounded_exists in H.
    apply arithmetic_hierarchy_remove_exists in H.
    apply (proj1 (@arithmetic_hierarchy_and_iff
      X pol s (S n) (arithmetic_lt_guard t) p)) in H. tauto.
  - intro H. now apply AH_bex.
Qed.

Corollary arithmetic_hierarchy_ball_lt_iff : forall X pol s n
    (t : semiterm oring_language X n)
    (p : semiformula oring_language X (S n)),
  arithmetic_hierarchy X pol s n
      (semiformula_ball_lt arithmetic_lt_operator t p) <->
  arithmetic_hierarchy X pol s (S n) p.
Proof.
  intros. unfold semiformula_ball_lt, arithmetic_bounded_all,
    arithmetic_lt_guard.
  apply arithmetic_hierarchy_bounded_all_iff.
  apply rew_bshift_positive.
Qed.

Corollary arithmetic_hierarchy_bex_lt_iff : forall X pol s n
    (t : semiterm oring_language X n)
    (p : semiformula oring_language X (S n)),
  arithmetic_hierarchy X pol s n
      (semiformula_bex_lt arithmetic_lt_operator t p) <->
  arithmetic_hierarchy X pol s (S n) p.
Proof.
  intros. unfold semiformula_bex_lt, arithmetic_bounded_exists,
    arithmetic_lt_guard.
  apply arithmetic_hierarchy_bounded_exists_iff.
  apply rew_bshift_positive.
Qed.

Corollary arithmetic_hierarchy_all_iff : forall X s n
    (p : semiformula oring_language X (S n)),
  arithmetic_hierarchy X arithmetic_pi (S s) n (Semiformula_all p) <->
  arithmetic_hierarchy X arithmetic_pi (S s) (S n) p.
Proof.
  split.
  - apply arithmetic_hierarchy_remove_all.
  - apply AH_all.
Qed.

Corollary arithmetic_hierarchy_exists_iff : forall X s n
    (p : semiformula oring_language X (S n)),
  arithmetic_hierarchy X arithmetic_sigma (S s) n
      (Semiformula_exists p) <->
  arithmetic_hierarchy X arithmetic_sigma (S s) (S n) p.
Proof.
  split.
  - apply arithmetic_hierarchy_remove_exists.
  - apply AH_exists.
Qed.

Theorem arithmetic_hierarchy_list_conj_iff : forall X pol s n
    (xs : list (semiformula oring_language X n)),
  arithmetic_hierarchy X pol s n
      (generic_list_conj2 (semiformula_connectives oring_language X n) xs) <->
  forall p, In p xs -> arithmetic_hierarchy X pol s n p.
Proof.
  intros X pol s n xs; induction xs as [|p xs IH].
  - simpl. split.
    + intros _ q Hq. contradiction.
    + intros _. apply AH_verum.
  - destruct xs as [|q xs].
    + simpl. split.
      * intros Hp r [Hr | []]. now subst r.
      * intro Hall. apply Hall. now left.
    + simpl generic_list_conj2.
      rewrite arithmetic_hierarchy_and_iff, IH.
      split.
      * intros [Hp Hrest] r [-> | Hr]; [exact Hp | now apply Hrest].
      * intro Hall. split.
        -- apply Hall. now left.
        -- intros r Hr. apply Hall. now right.
Qed.

Theorem arithmetic_hierarchy_list_disj_iff : forall X pol s n
    (xs : list (semiformula oring_language X n)),
  arithmetic_hierarchy X pol s n
      (generic_list_disj2 (semiformula_connectives oring_language X n) xs) <->
  forall p, In p xs -> arithmetic_hierarchy X pol s n p.
Proof.
  intros X pol s n xs; induction xs as [|p xs IH].
  - simpl. split.
    + intros _ q Hq. contradiction.
    + intros _. apply AH_falsum.
  - destruct xs as [|q xs].
    + simpl. split.
      * intros Hp r [Hr | []]. now subst r.
      * intro Hall. apply Hall. now left.
    + simpl generic_list_disj2.
      rewrite arithmetic_hierarchy_or_iff, IH.
      split.
      * intros [Hp Hrest] r [-> | Hr]; [exact Hp | now apply Hrest].
      * intro Hall. split.
        -- apply Hall. now left.
        -- intros r Hr. apply Hall. now right.
Qed.

Definition arithmetic_theory_sound_on_hierarchy
    (T : theory oring_language) (pol : bool) (k : nat) : Prop :=
  arithmetic_theory_sound_on T
    (fun sigma => arithmetic_hierarchy Empty_set pol k 0 sigma).

Lemma arithmetic_theory_sound_on_hierarchy_elim :
  forall (T : theory oring_language) pol k
         (sigma : sentence oring_language),
    arithmetic_theory_sound_on_hierarchy T pol k ->
    first_order_theory_provable T sigma ->
    arithmetic_hierarchy Empty_set pol k 0 sigma ->
    first_order_model_realize nat_standard_model sigma.
Proof.
  intros T pol k sigma Hsound Hproof Hsigma.
  exact (arithmetic_theory_sound_on_elim Hsound Hproof Hsigma).
Qed.

Theorem arithmetic_theory_consistent_of_sigma_one_sound :
  forall T : theory oring_language,
    arithmetic_theory_sound_on_hierarchy T arithmetic_sigma 1 ->
    generic_consistent (first_order_theory_entailment oring_language) T.
Proof.
  intros T Hsound.
  apply arithmetic_theory_consistent_of_sound_on with
    (F := fun sigma => arithmetic_hierarchy Empty_set arithmetic_sigma 1 0 sigma).
  - exact Hsound.
  - apply AH_falsum.
Qed.

Theorem arithmetic_theory_consistent_of_pi_two_sound :
  forall T : theory oring_language,
    arithmetic_theory_sound_on_hierarchy T arithmetic_pi 2 ->
    generic_consistent (first_order_theory_entailment oring_language) T.
Proof.
  intros T Hsound.
  apply arithmetic_theory_consistent_of_sound_on with
    (F := fun sigma => arithmetic_hierarchy Empty_set arithmetic_pi 2 0 sigma).
  - exact Hsound.
  - apply AH_falsum.
Qed.
