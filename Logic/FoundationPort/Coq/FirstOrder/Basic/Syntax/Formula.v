(**
  Generic first-order formulas in negation normal form.

  This ports [Foundation/FirstOrder/Basic/Syntax/Formula.lean].  As in the
  semiterm layer, free occurrence is predicate-valued, so structural and
  functorial theorems do not require decidable equality.  Duplicate-tolerant
  lists provide the executable indexing interface separately.
*)

From Stdlib Require Import Arith.PeanoNat Lia Lists.List Vectors.Fin.
From Stdlib Require Import Logic.Eqdep_dec Logic.FunctionalExtensionality.
From FoundationModal Require Import GenericSemantics GenericLogicSymbol.
From Foundation.Syntax.Predicate Require Import Language Term Quantifier.

Import ListNotations.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

Inductive semiformula (L : language) (X : Type) : nat -> Type :=
| Semiformula_verum : forall n, semiformula L X n
| Semiformula_falsum : forall n, semiformula L X n
| Semiformula_rel : forall n k,
    language_rel L k -> (Fin.t k -> semiterm L X n) -> semiformula L X n
| Semiformula_nrel : forall n k,
    language_rel L k -> (Fin.t k -> semiterm L X n) -> semiformula L X n
| Semiformula_and : forall n,
    semiformula L X n -> semiformula L X n -> semiformula L X n
| Semiformula_or : forall n,
    semiformula L X n -> semiformula L X n -> semiformula L X n
| Semiformula_all : forall n,
    semiformula L X (S n) -> semiformula L X n
| Semiformula_exists : forall n,
    semiformula L X (S n) -> semiformula L X n.

Arguments Semiformula_verum {L X} n.
Arguments Semiformula_falsum {L X} n.
Arguments Semiformula_rel {L X n k} _ _.
Arguments Semiformula_nrel {L X n k} _ _.
Arguments Semiformula_and {L X n} _ _.
Arguments Semiformula_or {L X n} _ _.
Arguments Semiformula_all {L X n} _.
Arguments Semiformula_exists {L X n} _.

Definition formula L X := semiformula L X 0.
Definition sentence L := formula L Empty_set.
Definition semisentence L n := semiformula L Empty_set n.
Definition semiproposition L n := semiformula L nat n.
Definition proposition L := semiproposition L 0.

(** * Primitive connectives and quantifiers *)

Fixpoint semiformula_neg {L X n} (p : semiformula L X n) :
    semiformula L X n :=
  match p with
  | Semiformula_verum n => Semiformula_falsum n
  | Semiformula_falsum n => Semiformula_verum n
  | Semiformula_rel r v => Semiformula_nrel r v
  | Semiformula_nrel r v => Semiformula_rel r v
  | Semiformula_and p q => Semiformula_or (semiformula_neg p) (semiformula_neg q)
  | Semiformula_or p q => Semiformula_and (semiformula_neg p) (semiformula_neg q)
  | Semiformula_all p => Semiformula_exists (semiformula_neg p)
  | Semiformula_exists p => Semiformula_all (semiformula_neg p)
  end.

Definition semiformula_imp {L X n} (p q : semiformula L X n) :=
  Semiformula_or (semiformula_neg p) q.

Definition semiformula_iff {L X n} (p q : semiformula L X n) :=
  Semiformula_and (semiformula_imp p q) (semiformula_imp q p).

Definition semiformula_connectives L X n :
    generic_connectives (semiformula L X n) :=
  {| generic_top := Semiformula_verum n;
     generic_bottom := Semiformula_falsum n;
     generic_and := Semiformula_and;
     generic_or := Semiformula_or;
     generic_imp := semiformula_imp;
     generic_neg := semiformula_neg |}.

Definition semiformula_universal_quantifier L X :
    first_universal_quantifier (semiformula L X) :=
  {| first_all := fun n => @Semiformula_all L X n |}.

Definition semiformula_existential_quantifier L X :
    first_existential_quantifier (semiformula L X) :=
  {| first_exists := fun n => @Semiformula_exists L X n |}.

Definition semiformula_quantifiers L X :
    first_quantifiers (semiformula L X) :=
  {| first_quantifier_all := semiformula_universal_quantifier L X;
     first_quantifier_exists := semiformula_existential_quantifier L X |}.

Definition semiformula_lcwq L X :
    first_connectives_with_quantifiers (semiformula L X) :=
  {| first_lcwq_quantifiers := semiformula_quantifiers L X;
     first_lcwq_connectives := semiformula_connectives L X |}.

Definition semiformula_bounded_all {L X n}
    (p q : semiformula L X (S n)) : semiformula L X n :=
  Semiformula_all (semiformula_imp p q).

Definition semiformula_bounded_exists {L X n}
    (p q : semiformula L X (S n)) : semiformula L X n :=
  Semiformula_exists (Semiformula_and p q).

Lemma semiformula_neg_involutive :
  forall L X n (p : semiformula L X n),
    semiformula_neg (semiformula_neg p) = p.
Proof.
  intros L X n p; induction p; simpl; try reflexivity;
    f_equal; assumption.
Qed.

Lemma semiformula_neg_injective :
  forall L X n (p q : semiformula L X n),
    semiformula_neg p = semiformula_neg q <-> p = q.
Proof.
  split; [intro H | now intros ->].
  apply (f_equal semiformula_neg) in H.
  now rewrite !semiformula_neg_involutive in H.
Qed.

Lemma semiformula_neg_all :
  forall L X n (p : semiformula L X (S n)),
    semiformula_neg (Semiformula_all p) =
    Semiformula_exists (semiformula_neg p).
Proof. reflexivity. Qed.

Lemma semiformula_neg_exists :
  forall L X n (p : semiformula L X (S n)),
    semiformula_neg (Semiformula_exists p) =
    Semiformula_all (semiformula_neg p).
Proof. reflexivity. Qed.

Lemma semiformula_neg_all_closure :
  forall L X n (p : semiformula L X n),
    semiformula_neg
      (first_all_closure (semiformula_universal_quantifier L X) n p) =
    first_exists_closure (semiformula_existential_quantifier L X) n
      (semiformula_neg p).
Proof.
  intros L X n; induction n as [|n IH]; intro p; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

Lemma semiformula_neg_exists_closure :
  forall L X n (p : semiformula L X n),
    semiformula_neg
      (first_exists_closure (semiformula_existential_quantifier L X) n p) =
    first_all_closure (semiformula_universal_quantifier L X) n
      (semiformula_neg p).
Proof.
  intros L X n; induction n as [|n IH]; intro p; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

Lemma semiformula_neg_bounded_all :
  forall L X n (p q : semiformula L X (S n)),
    semiformula_neg (semiformula_bounded_all p q) =
    semiformula_bounded_exists p (semiformula_neg q).
Proof.
  intros; unfold semiformula_bounded_all, semiformula_bounded_exists,
    semiformula_imp; simpl.
  now rewrite semiformula_neg_involutive.
Qed.

Lemma semiformula_neg_bounded_exists :
  forall L X n (p q : semiformula L X (S n)),
    semiformula_neg (semiformula_bounded_exists p q) =
    semiformula_bounded_all p (semiformula_neg q).
Proof.
  intros; unfold semiformula_bounded_all, semiformula_bounded_exists,
    semiformula_imp; simpl.
  reflexivity.
Qed.

(** * Constructor injectivity *)

Lemma existT_nat_injective :
  forall (P : nat -> Type) n (x y : P n),
    existT P n x = existT P n y -> x = y.
Proof.
  intros P n x y H.
  exact (@inj_pair2_eq_dec nat Nat.eq_dec P n x y H).
Qed.

Lemma semiformula_and_injective :
  forall L X n (p q r s : semiformula L X n),
    Semiformula_and p q = Semiformula_and r s <-> p = r /\ q = s.
Proof.
  intros; split.
  - intro H. inversion H.
    apply existT_nat_injective in H1.
    apply existT_nat_injective in H2. auto.
  - intros [-> ->]; reflexivity.
Qed.

Lemma semiformula_or_injective :
  forall L X n (p q r s : semiformula L X n),
    Semiformula_or p q = Semiformula_or r s <-> p = r /\ q = s.
Proof.
  intros; split.
  - intro H. inversion H.
    apply existT_nat_injective in H1.
    apply existT_nat_injective in H2. auto.
  - intros [-> ->]; reflexivity.
Qed.

Lemma semiformula_all_injective :
  forall L X n (p q : semiformula L X (S n)),
    Semiformula_all p = Semiformula_all q <-> p = q.
Proof.
  intros; split; [intro H | now intros ->].
  inversion H. now apply existT_nat_injective in H1.
Qed.

Lemma semiformula_exists_injective :
  forall L X n (p q : semiformula L X (S n)),
    Semiformula_exists p = Semiformula_exists q <-> p = q.
Proof.
  intros; split; [intro H | now intros ->].
  inversion H. now apply existT_nat_injective in H1.
Qed.

Lemma semiformula_imp_injective :
  forall L X n (p q r s : semiformula L X n),
    semiformula_imp p q = semiformula_imp r s <-> p = r /\ q = s.
Proof.
  intros; unfold semiformula_imp; rewrite semiformula_or_injective.
  split.
  - intros [H1 H2]; split; [|exact H2].
    now apply (proj1 (semiformula_neg_injective p r)).
  - intros [-> ->]; split; reflexivity.
Qed.

Lemma semiformula_all_closure_injective :
  forall L X n (p q : semiformula L X n),
    first_all_closure (semiformula_universal_quantifier L X) n p =
    first_all_closure (semiformula_universal_quantifier L X) n q <-> p = q.
Proof.
  intros L X n; induction n as [|n IH]; intros p q; simpl.
  - reflexivity.
  - rewrite IH. apply semiformula_all_injective.
Qed.

Lemma semiformula_exists_closure_injective :
  forall L X n (p q : semiformula L X n),
    first_exists_closure (semiformula_existential_quantifier L X) n p =
    first_exists_closure (semiformula_existential_quantifier L X) n q <-> p = q.
Proof.
  intros L X n; induction n as [|n IH]; intros p q; simpl.
  - reflexivity.
  - rewrite IH. apply semiformula_exists_injective.
Qed.

Lemma semiformula_all_iter_injective :
  forall L X k n (p q : semiformula L X (k + n)),
    first_all_iter (semiformula_universal_quantifier L X) k n p =
    first_all_iter (semiformula_universal_quantifier L X) k n q <-> p = q.
Proof.
  intros L X k; induction k as [|k IH]; intros n p q; simpl.
  - reflexivity.
  - rewrite IH. apply semiformula_all_injective.
Qed.

Lemma semiformula_exists_iter_injective :
  forall L X k n (p q : semiformula L X (k + n)),
    first_exists_iter (semiformula_existential_quantifier L X) k n p =
    first_exists_iter (semiformula_existential_quantifier L X) k n q <-> p = q.
Proof.
  intros L X k; induction k as [|k IH]; intros n p q; simpl.
  - reflexivity.
  - rewrite IH. apply semiformula_exists_injective.
Qed.

(** * Complexity and quantifier rank *)

Fixpoint semiformula_complexity {L X n} (p : semiformula L X n) : nat :=
  match p with
  | Semiformula_verum _ | Semiformula_falsum _ => 0
  | Semiformula_rel _ _ | Semiformula_nrel _ _ => 0
  | Semiformula_and p q | Semiformula_or p q =>
      S (Nat.max (semiformula_complexity p) (semiformula_complexity q))
  | Semiformula_all p | Semiformula_exists p => S (semiformula_complexity p)
  end.

Fixpoint semiformula_quantifier_rank {L X n} (p : semiformula L X n) : nat :=
  match p with
  | Semiformula_verum _ | Semiformula_falsum _ => 0
  | Semiformula_rel _ _ | Semiformula_nrel _ _ => 0
  | Semiformula_and p q | Semiformula_or p q =>
      Nat.max (semiformula_quantifier_rank p) (semiformula_quantifier_rank q)
  | Semiformula_all p | Semiformula_exists p =>
      S (semiformula_quantifier_rank p)
  end.

Definition semiformula_open {L X n} (p : semiformula L X n) : Prop :=
  semiformula_quantifier_rank p = 0.

Lemma semiformula_complexity_neg :
  forall L X n (p : semiformula L X n),
    semiformula_complexity (semiformula_neg p) = semiformula_complexity p.
Proof.
  intros L X n p; induction p; simpl; try reflexivity;
    now rewrite ?IHp, ?IHp1, ?IHp2.
Qed.

Lemma semiformula_quantifier_rank_neg :
  forall L X n (p : semiformula L X n),
    semiformula_quantifier_rank (semiformula_neg p) =
    semiformula_quantifier_rank p.
Proof.
  intros L X n p; induction p; simpl; try reflexivity;
    now rewrite ?IHp, ?IHp1, ?IHp2.
Qed.

Lemma semiformula_quantifier_rank_imp :
  forall L X n (p q : semiformula L X n),
    semiformula_quantifier_rank (semiformula_imp p q) =
    Nat.max (semiformula_quantifier_rank p) (semiformula_quantifier_rank q).
Proof.
  intros; unfold semiformula_imp; simpl.
  now rewrite semiformula_quantifier_rank_neg.
Qed.

Lemma semiformula_quantifier_rank_iff :
  forall L X n (p q : semiformula L X n),
    semiformula_quantifier_rank (semiformula_iff p q) =
    Nat.max (semiformula_quantifier_rank p) (semiformula_quantifier_rank q).
Proof.
  intros; unfold semiformula_iff, semiformula_imp; simpl.
  rewrite !semiformula_quantifier_rank_neg.
  rewrite (Nat.max_comm (semiformula_quantifier_rank q)
    (semiformula_quantifier_rank p)).
  apply Nat.max_id.
Qed.

Lemma semiformula_open_and :
  forall L X n (p q : semiformula L X n),
    semiformula_open (Semiformula_and p q) <->
    semiformula_open p /\ semiformula_open q.
Proof.
  intros; unfold semiformula_open; simpl.
  split.
  - intro H; split; apply Nat.le_0_r.
    + rewrite <- H. apply Nat.le_max_l.
    + rewrite <- H. apply Nat.le_max_r.
  - intros [-> ->]; reflexivity.
Qed.

Lemma semiformula_open_or :
  forall L X n (p q : semiformula L X n),
    semiformula_open (Semiformula_or p q) <->
    semiformula_open p /\ semiformula_open q.
Proof. apply semiformula_open_and. Qed.

Lemma semiformula_open_neg :
  forall L X n (p : semiformula L X n),
    semiformula_open (semiformula_neg p) <-> semiformula_open p.
Proof. intros; unfold semiformula_open; now rewrite semiformula_quantifier_rank_neg. Qed.

Lemma semiformula_not_open_all :
  forall L X n (p : semiformula L X (S n)),
    ~ semiformula_open (Semiformula_all p).
Proof. intros; unfold semiformula_open; simpl; lia. Qed.

Lemma semiformula_not_open_exists :
  forall L X n (p : semiformula L X (S n)),
    ~ semiformula_open (Semiformula_exists p).
Proof. intros; unfold semiformula_open; simpl; lia. Qed.

Lemma semiformula_ne_of_ne_complexity :
  forall L X n (p q : semiformula L X n),
    semiformula_complexity p <> semiformula_complexity q -> p <> q.
Proof. intros L X n p q Hneq ->; contradiction. Qed.

Lemma semiformula_ne_or_left :
  forall L X n (p q : semiformula L X n), p <> Semiformula_or p q.
Proof.
  intros; apply semiformula_ne_of_ne_complexity; simpl.
  pose proof (Nat.le_max_l (semiformula_complexity p) (semiformula_complexity q)); lia.
Qed.

Lemma semiformula_open_imp :
  forall L X n (p q : semiformula L X n),
    semiformula_open (semiformula_imp p q) <->
    semiformula_open p /\ semiformula_open q.
Proof.
  intros; unfold semiformula_open.
  rewrite semiformula_quantifier_rank_imp.
  apply semiformula_open_and.
Qed.

Lemma semiformula_open_iff :
  forall L X n (p q : semiformula L X n),
    semiformula_open (semiformula_iff p q) <->
    semiformula_open p /\ semiformula_open q.
Proof.
  intros; unfold semiformula_open.
  rewrite semiformula_quantifier_rank_iff.
  apply semiformula_open_and.
Qed.

Lemma semiformula_ne_or_right :
  forall L X n (p q : semiformula L X n), q <> Semiformula_or p q.
Proof.
  intros; apply semiformula_ne_of_ne_complexity; simpl.
  pose proof (Nat.le_max_r (semiformula_complexity p) (semiformula_complexity q)); lia.
Qed.

(** * Equality decision *)

Definition semiformula_rel_payload (L : language) (X : Type) (n : nat) :=
  {k : nat & (language_rel L k * (Fin.t k -> semiterm L X n))%type}.

Definition semiformula_outer_rel_payload {L X n} (p : semiformula L X n) :
    option (semiformula_rel_payload L X n) :=
  match p with
  | @Semiformula_rel _ _ _ k r v => Some (existT _ k (r, v))
  | _ => None
  end.

Definition semiformula_outer_nrel_payload {L X n} (p : semiformula L X n) :
    option (semiformula_rel_payload L X n) :=
  match p with
  | @Semiformula_nrel _ _ _ k r v => Some (existT _ k (r, v))
  | _ => None
  end.

Lemma semiformula_rel_injective_same_arity :
  forall L X n k (r s : language_rel L k)
         (v w : Fin.t k -> semiterm L X n),
    Semiformula_rel r v = Semiformula_rel s w -> r = s /\ v = w.
Proof.
  intros L X n k r s v w H.
  pose proof (f_equal semiformula_outer_rel_payload H) as Hp; simpl in Hp.
  apply option_some_injective in Hp.
  apply (@inj_pair2_eq_dec nat Nat.eq_dec
    (fun j => (language_rel L j * (Fin.t j -> semiterm L X n))%type)
    k (r, v) (s, w)) in Hp.
  now injection Hp.
Qed.

Lemma semiformula_nrel_injective_same_arity :
  forall L X n k (r s : language_rel L k)
         (v w : Fin.t k -> semiterm L X n),
    Semiformula_nrel r v = Semiformula_nrel s w -> r = s /\ v = w.
Proof.
  intros L X n k r s v w H.
  pose proof (f_equal semiformula_outer_nrel_payload H) as Hp; simpl in Hp.
  apply option_some_injective in Hp.
  apply (@inj_pair2_eq_dec nat Nat.eq_dec
    (fun j => (language_rel L j * (Fin.t j -> semiterm L X n))%type)
    k (r, v) (s, w)) in Hp.
  now injection Hp.
Qed.

Definition semiformula_eq_dec {L X n}
    (D : language_decidable_eq L)
    (free_eq_dec : forall x y : X, {x = y} + {x <> y})
    (p q : semiformula L X n) : {p = q} + {p <> q}.
Proof.
  revert q.
  refine (@semiformula_rect L X
    (fun n p => forall q : semiformula L X n, {p = q} + {p <> q})
    _ _ _ _ _ _ _ _ n p); clear p n.
  - intros n q; destruct q; try (right; discriminate); left; reflexivity.
  - intros n q; destruct q; try (right; discriminate); left; reflexivity.
  - intros n k r v q; destruct q as [| |n l s w| | | | |];
      try (right; discriminate).
    destruct (Nat.eq_dec k l) as [Hkl | Hkl].
    + subst l. destruct (@language_rel_eq_dec L D k r s) as [-> | Hrs].
      * destruct (@fin_function_pointwise_eq_dec k (semiterm L X n) v w
          (fun i => semiterm_eq_dec (language_func_eq_dec D) free_eq_dec
            (v i) (w i))) as [-> | Hvw].
        { left; reflexivity. }
        { right; intro H; apply Hvw.
          exact (proj2 (semiformula_rel_injective_same_arity H)). }
      * right; intro H; apply Hrs.
        exact (proj1 (semiformula_rel_injective_same_arity H)).
    + right; intro H. apply Hkl.
      pose proof (f_equal semiformula_outer_rel_payload H) as Hp; simpl in Hp.
      apply option_some_injective in Hp. now injection Hp.
  - intros n k r v q; destruct q as [| | |n l s w| | | |];
      try (right; discriminate).
    destruct (Nat.eq_dec k l) as [Hkl | Hkl].
    + subst l. destruct (@language_rel_eq_dec L D k r s) as [-> | Hrs].
      * destruct (@fin_function_pointwise_eq_dec k (semiterm L X n) v w
          (fun i => semiterm_eq_dec (language_func_eq_dec D) free_eq_dec
            (v i) (w i))) as [-> | Hvw].
        { left; reflexivity. }
        { right; intro H; apply Hvw.
          exact (proj2 (semiformula_nrel_injective_same_arity H)). }
      * right; intro H; apply Hrs.
        exact (proj1 (semiformula_nrel_injective_same_arity H)).
    + right; intro H. apply Hkl.
      pose proof (f_equal semiformula_outer_nrel_payload H) as Hp; simpl in Hp.
      apply option_some_injective in Hp. now injection Hp.
  - intros n a IHa b IHb q; destruct q; try (right; discriminate).
    destruct (IHa q1) as [-> | Ha].
    2: { right; intro H; apply Ha.
         exact (proj1 (proj1 (semiformula_and_injective a b q1 q2) H)). }
    destruct (IHb q2) as [-> | Hb]; [left; reflexivity|].
    right; intro H; apply Hb.
    exact (proj2 (proj1 (semiformula_and_injective q1 b q1 q2) H)).
  - intros n a IHa b IHb q; destruct q; try (right; discriminate).
    destruct (IHa q1) as [-> | Ha].
    2: { right; intro H; apply Ha.
         exact (proj1 (proj1 (semiformula_or_injective a b q1 q2) H)). }
    destruct (IHb q2) as [-> | Hb]; [left; reflexivity|].
    right; intro H; apply Hb.
    exact (proj2 (proj1 (semiformula_or_injective q1 b q1 q2) H)).
  - intros n a IHa q; destruct q; try (right; discriminate).
    destruct (IHa q) as [-> | Ha]; [left; reflexivity|].
    right; intro H; apply Ha.
    now apply (proj1 (semiformula_all_injective a q)).
  - intros n a IHa q; destruct q; try (right; discriminate).
    destruct (IHa q) as [-> | Ha]; [left; reflexivity|].
    right; intro H; apply Ha.
    now apply (proj1 (semiformula_exists_injective a q)).
Defined.

(** * Free occurrence and an executable list view *)

Fixpoint semiformula_free_occurs {L X n}
    (x : X) (p : semiformula L X n) : Prop :=
  match p with
  | Semiformula_verum _ | Semiformula_falsum _ => False
  | @Semiformula_rel _ _ _ k _ v | @Semiformula_nrel _ _ _ k _ v =>
      exists i : Fin.t k, semiterm_free_occurs x (v i)
  | Semiformula_and p q | Semiformula_or p q =>
      semiformula_free_occurs x p \/ semiformula_free_occurs x q
  | Semiformula_all p | Semiformula_exists p => semiformula_free_occurs x p
  end.

Lemma semiformula_free_occurs_neg :
  forall L X n x (p : semiformula L X n),
    semiformula_free_occurs x (semiformula_neg p) <->
    semiformula_free_occurs x p.
Proof.
  intros L X n x p; induction p; simpl; try reflexivity;
    now rewrite ?IHp, ?IHp1, ?IHp2.
Qed.

Lemma semiformula_free_occurs_imp :
  forall L X n x (p q : semiformula L X n),
    semiformula_free_occurs x (semiformula_imp p q) <->
    semiformula_free_occurs x p \/ semiformula_free_occurs x q.
Proof. intros; unfold semiformula_imp; simpl; now rewrite semiformula_free_occurs_neg. Qed.

Lemma semiformula_free_occurs_all_closure :
  forall L X n x (p : semiformula L X n),
    semiformula_free_occurs x
      (first_all_closure (semiformula_universal_quantifier L X) n p) <->
    semiformula_free_occurs x p.
Proof.
  intros L X n; induction n as [|n IH]; intros x p; simpl; [reflexivity|apply IH].
Qed.

Lemma semiformula_no_free_occurs_empty :
  forall L n (p : semiformula L Empty_set n) x,
    ~ semiformula_free_occurs x p.
Proof. intros L n p x; inversion x. Qed.

Fixpoint semiformula_free_variable_list {L X n}
    (p : semiformula L X n) : list X :=
  match p with
  | Semiformula_verum _ | Semiformula_falsum _ => []
  | @Semiformula_rel _ _ _ k _ v | @Semiformula_nrel _ _ _ k _ v =>
      flat_map (fun i => semiterm_free_variable_list (v i)) (fin_enum k)
  | Semiformula_and p q | Semiformula_or p q =>
      semiformula_free_variable_list p ++ semiformula_free_variable_list q
  | Semiformula_all p | Semiformula_exists p => semiformula_free_variable_list p
  end.

Lemma semiformula_free_variable_list_spec :
  forall L X n (p : semiformula L X n) x,
    In x (semiformula_free_variable_list p) <-> semiformula_free_occurs x p.
Proof.
  intros L X n p; induction p; intro x; simpl; try tauto.
  - rewrite in_flat_map; split.
    + intros [i [_ Hi]]. exists i.
      now apply (proj1 (semiterm_free_variable_list_spec (s i) x)).
    + intros [i Hi]. exists i; split; [apply fin_enum_complete|].
      now apply (proj2 (semiterm_free_variable_list_spec (s i) x)).
  - rewrite in_flat_map; split.
    + intros [i [_ Hi]]. exists i.
      now apply (proj1 (semiterm_free_variable_list_spec (s i) x)).
    + intros [i Hi]. exists i; split; [apply fin_enum_complete|].
      now apply (proj2 (semiterm_free_variable_list_spec (s i) x)).
  - now rewrite in_app_iff, IHp1, IHp2.
  - now rewrite in_app_iff, IHp1, IHp2.
  - apply IHp.
  - apply IHp.
Qed.

Definition semiformula_index_of_free_variable {L X n}
    (eq_dec : forall x y : X, {x = y} + {x <> y})
    (p : semiformula L X n) (x : X) : nat :=
  list_index eq_dec x (semiformula_free_variable_list p).

Definition semiformula_enumerate_free_variable {L X n}
    (default : X) (p : semiformula L X n) (i : nat) : X :=
  nth i (semiformula_free_variable_list p) default.

Theorem semiformula_enumerate_index_of_free_variable :
  forall L X n (eq_dec : forall x y : X, {x = y} + {x <> y})
         (default : X) (p : semiformula L X n) x,
    semiformula_free_occurs x p ->
    semiformula_enumerate_free_variable default p
      (semiformula_index_of_free_variable eq_dec p x) = x.
Proof.
  intros. apply nth_list_index.
  now apply (proj2 (semiformula_free_variable_list_spec p x)).
Qed.

Fixpoint list_nat_max (xs : list nat) : nat :=
  match xs with [] => 0 | x :: ys => Nat.max x (list_nat_max ys) end.

Lemma in_list_nat_max : forall x xs, In x xs -> x <= list_nat_max xs.
Proof.
  intros x xs; induction xs as [|y ys IH]; simpl; [tauto|].
  intros [-> | Hin]; [apply Nat.le_max_l|].
  eapply Nat.le_trans; [apply IH, Hin|apply Nat.le_max_r].
Qed.

Definition semiformula_fv_sup {L n} (p : semiproposition L n) : nat :=
  S (list_nat_max (semiformula_free_variable_list p)).

Lemma semiformula_lt_fv_sup_of_free_occurs :
  forall L n (p : semiproposition L n) x,
    semiformula_free_occurs x p -> x < semiformula_fv_sup p.
Proof.
  intros; unfold semiformula_fv_sup.
  apply Nat.lt_succ_r, in_list_nat_max.
  now apply (proj2 (semiformula_free_variable_list_spec p x)).
Qed.

Lemma semiformula_fv_sup_fresh :
  forall L n (p : semiproposition L n),
    ~ semiformula_free_occurs (semiformula_fv_sup p) p.
Proof.
  intros L n p H.
  pose proof (@semiformula_lt_fv_sup_of_free_occurs
    L n p (semiformula_fv_sup p) H); lia.
Qed.

Lemma semiformula_no_free_occurs_above_fv_sup :
  forall L n (p : semiproposition L n) m,
    semiformula_fv_sup p <= m -> ~ semiformula_free_occurs m p.
Proof.
  intros L n p m Hle Hocc.
  pose proof (@semiformula_lt_fv_sup_of_free_occurs L n p m Hocc); lia.
Qed.

(** * Functorial language maps *)

Fixpoint semiformula_language_map {L M X n}
    (h : language_hom L M) (p : semiformula L X n) : semiformula M X n :=
  match p with
  | Semiformula_verum n => Semiformula_verum n
  | Semiformula_falsum n => Semiformula_falsum n
  | Semiformula_rel r v =>
      Semiformula_rel (hom_rel h r) (fun i => semiterm_language_map h (v i))
  | Semiformula_nrel r v =>
      Semiformula_nrel (hom_rel h r) (fun i => semiterm_language_map h (v i))
  | Semiformula_and p q =>
      Semiformula_and (semiformula_language_map h p) (semiformula_language_map h q)
  | Semiformula_or p q =>
      Semiformula_or (semiformula_language_map h p) (semiformula_language_map h q)
  | Semiformula_all p => Semiformula_all (semiformula_language_map h p)
  | Semiformula_exists p => Semiformula_exists (semiformula_language_map h p)
  end.

Lemma semiformula_language_map_neg :
  forall L M X n (h : language_hom L M) (p : semiformula L X n),
    semiformula_language_map h (semiformula_neg p) =
    semiformula_neg (semiformula_language_map h p).
Proof.
  intros L M X n h p; induction p; simpl; try reflexivity;
    now rewrite ?IHp, ?IHp1, ?IHp2.
Qed.

Definition semiformula_language_connective_hom {L M X n}
    (h : language_hom L M) :
    generic_connective_hom (semiformula_connectives L X n)
      (semiformula_connectives M X n).
Proof.
  refine {| generic_connective_hom_apply := semiformula_language_map h |}.
  - reflexivity.
  - reflexivity.
  - apply semiformula_language_map_neg.
  - intros p q; unfold semiformula_imp; simpl.
    now rewrite semiformula_language_map_neg.
  - reflexivity.
  - reflexivity.
Defined.

Lemma semiformula_language_map_free_occurs :
  forall L M X n (h : language_hom L M) (p : semiformula L X n) x,
    semiformula_free_occurs x (semiformula_language_map h p) <->
    semiformula_free_occurs x p.
Proof.
  intros L M X n h p; induction p; intro x; simpl; try reflexivity.
  - split; intros [i Hi]; exists i;
      [apply (proj1 (semiterm_language_map_free_occurs h (s i) x))|
       apply (proj2 (semiterm_language_map_free_occurs h (s i) x))]; exact Hi.
  - split; intros [i Hi]; exists i;
      [apply (proj1 (semiterm_language_map_free_occurs h (s i) x))|
       apply (proj2 (semiterm_language_map_free_occurs h (s i) x))]; exact Hi.
  - now rewrite IHp1, IHp2.
  - now rewrite IHp1, IHp2.
  - apply IHp.
  - apply IHp.
Qed.

Lemma semiformula_language_map_id :
  forall L X n (p : semiformula L X n),
    semiformula_language_map (language_hom_id L) p = p.
Proof.
  intros L X n p; induction p; simpl; try (f_equal; assumption); try reflexivity.
  - f_equal. apply functional_extensionality; intro i.
    apply semiterm_language_map_id.
  - f_equal. apply functional_extensionality; intro i.
    apply semiterm_language_map_id.
Qed.

Lemma semiformula_language_map_comp :
  forall L M N X n (g : language_hom M N) (f : language_hom L M)
         (p : semiformula L X n),
    semiformula_language_map g (semiformula_language_map f p) =
    semiformula_language_map (language_hom_comp g f) p.
Proof.
  intros L M N X n g f p; induction p; simpl;
    try (f_equal; assumption); try reflexivity.
  - f_equal. apply functional_extensionality; intro i.
    apply semiterm_language_map_comp.
  - f_equal. apply functional_extensionality; intro i.
    apply semiterm_language_map_comp.
Qed.

Lemma semiformula_language_map_all_closure :
  forall L M X n (h : language_hom L M) (p : semiformula L X n),
    semiformula_language_map h
      (first_all_closure (semiformula_universal_quantifier L X) n p) =
    first_all_closure (semiformula_universal_quantifier M X) n
      (semiformula_language_map h p).
Proof.
  intros L M X n; induction n as [|n IH]; intros h p; simpl;
    [reflexivity|apply IH].
Qed.

Lemma semiformula_language_map_exists_closure :
  forall L M X n (h : language_hom L M) (p : semiformula L X n),
    semiformula_language_map h
      (first_exists_closure (semiformula_existential_quantifier L X) n p) =
    first_exists_closure (semiformula_existential_quantifier M X) n
      (semiformula_language_map h p).
Proof.
  intros L M X n; induction n as [|n IH]; intros h p; simpl;
    [reflexivity|apply IH].
Qed.

Lemma semiformula_language_map_all_iter :
  forall L M X k n (h : language_hom L M)
         (p : semiformula L X (k + n)),
    semiformula_language_map h
      (first_all_iter (semiformula_universal_quantifier L X) k n p) =
    first_all_iter (semiformula_universal_quantifier M X) k n
      (semiformula_language_map h p).
Proof.
  intros L M X k; induction k as [|k IH]; intros n h p; simpl;
    [reflexivity|apply IH].
Qed.

Lemma semiformula_language_map_exists_iter :
  forall L M X k n (h : language_hom L M)
         (p : semiformula L X (k + n)),
    semiformula_language_map h
      (first_exists_iter (semiformula_existential_quantifier L X) k n p) =
    first_exists_iter (semiformula_existential_quantifier M X) k n
      (semiformula_language_map h p).
Proof.
  intros L M X k; induction k as [|k IH]; intros n h p; simpl;
    [reflexivity|apply IH].
Qed.

Lemma semiformula_language_map_bounded_all :
  forall L M X n (h : language_hom L M) (p q : semiformula L X (S n)),
    semiformula_language_map h (semiformula_bounded_all p q) =
    semiformula_bounded_all (semiformula_language_map h p)
      (semiformula_language_map h q).
Proof.
  intros; unfold semiformula_bounded_all, semiformula_imp; simpl.
  now rewrite semiformula_language_map_neg.
Qed.

Lemma semiformula_language_map_bounded_exists :
  forall L M X n (h : language_hom L M) (p q : semiformula L X (S n)),
    semiformula_language_map h (semiformula_bounded_exists p q) =
    semiformula_bounded_exists (semiformula_language_map h p)
      (semiformula_language_map h q).
Proof. reflexivity. Qed.

Lemma semiformula_language_map_free_variable_list :
  forall L M X n (h : language_hom L M) (p : semiformula L X n),
    semiformula_free_variable_list (semiformula_language_map h p) =
    semiformula_free_variable_list p.
Proof.
  intros L M X n h p; induction p; simpl; try reflexivity;
    try now rewrite ?IHp, ?IHp1, ?IHp2.
  - assert (Hfunctions :
      (fun i => semiterm_free_variable_list
        (semiterm_language_map h (s i))) =
      (fun i => semiterm_free_variable_list (s i))).
    { apply functional_extensionality; intro i.
      apply semiterm_language_map_free_variable_list. }
    now rewrite Hfunctions.
  - assert (Hfunctions :
      (fun i => semiterm_free_variable_list
        (semiterm_language_map h (s i))) =
      (fun i => semiterm_free_variable_list (s i))).
    { apply functional_extensionality; intro i.
      apply semiterm_language_map_free_variable_list. }
    now rewrite Hfunctions.
Qed.

Definition theory (L : language) : Type := sentence L -> Prop.

Definition theory_language_map {L M} (h : language_hom L M)
    (T : theory L) : theory M :=
  fun q => exists p, T p /\ semiformula_language_map h p = q.
