(**
  The arithmetical hierarchy over the ordered-ring language.

  Foundation states the hierarchy for every language carrying a distinguished
  strict-order operator.  The port specializes it to the canonical arithmetic
  language used by every downstream arithmetic theorem, avoiding an otherwise
  pervasive explicit operator parameter while retaining the exact grammar.
*)

From Stdlib Require Import Bool.Bool Arith.PeanoNat Lia.
From FoundationModal Require Import GenericEntailment.
From Foundation.Syntax.Predicate Require Import Language Term Rew.
From Foundation.FirstOrder.Basic.Syntax Require Import Formula.
From Foundation.FirstOrder.Basic Require Import Calculus Operator.
From Foundation.FirstOrder.Basic.Semantics Require Import ModelTheory.
From Foundation.FirstOrder Require Import Polarity.
From Foundation.FirstOrder.Arithmetic.Basic Require Import Model.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

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
