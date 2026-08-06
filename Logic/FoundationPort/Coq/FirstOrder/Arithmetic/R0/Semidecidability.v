(** Semidecidability of Sigma-one arithmetic formulas.

    This is the standard-model content of the source theorem [sigma1_re].
    The recognizer for a bounded universal formula stores one successful
    recognizer fuel for each member of the finite initial segment. *)

From Stdlib Require Import Arith.Cantor Arith.Compare_dec Arith.PeanoNat
  Bool.Bool Lia Vectors.Fin.
From Foundation.Vorspiel Require Import Computability.
From Foundation.Syntax.Predicate Require Import Language Term.
From Foundation.FirstOrder.Basic.Syntax Require Import Formula.
From Foundation.FirstOrder.Basic Require Import Operator.
From Foundation.FirstOrder.Basic.Semantics Require Import Semantics.
From Foundation.FirstOrder.Arithmetic.Basic Require Import Hierarchy Misc Model.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

(** Transport a recognizer across a pointwise logical equivalence. *)
Lemma semidecidable_ext : forall A (p q : A -> Prop),
  (forall a, p a <-> q a) -> semidecidable p -> semidecidable q.
Proof.
  intros A p q Hequiv [recognize Hrecognize].
  exists recognize. intro a. rewrite <- Hequiv. apply Hrecognize.
Qed.

(** A code is a right-nested Cantor tuple.  At stage [S k], its first
    component is fuel witnessing the [k]-th instance, while its second
    component recursively witnesses all earlier instances. *)
Fixpoint semidecidable_prefix_recognizer {A}
    (recognize : (nat * A) -> nat -> bool)
    (a : A) (k code : nat) : bool :=
  match k with
  | 0 => true
  | S k' =>
      let '(head_fuel, tail_code) := Cantor.of_nat code in
      andb (recognize (k', a) head_fuel)
           (semidecidable_prefix_recognizer
              recognize a k' tail_code)
  end.

Lemma semidecidable_prefix_recognizer_spec : forall A
    (p : nat * A -> Prop) (recognize : (nat * A) -> nat -> bool),
  (forall xa, p xa <-> exists fuel, recognize xa fuel = true) ->
  forall a k,
    (forall x, x < k -> p (x, a)) <->
    exists code,
      semidecidable_prefix_recognizer recognize a k code = true.
Proof.
  intros A p recognize Hrecognize a k. revert a.
  induction k as [|k IH]; intro a; split.
  - intro. exists 0. reflexivity.
  - intros [code _] x Hx. lia.
  - intro Hall.
    destruct (proj1 (Hrecognize (k, a))
      (Hall k (Nat.lt_succ_diag_r k))) as [head_fuel Hhead].
    assert (Hprefix : forall x, x < k -> p (x, a)).
    { intros x Hx. apply Hall. lia. }
    destruct (proj1 (IH a) Hprefix) as [tail_code Htail].
    exists (Cantor.to_nat (head_fuel, tail_code)).
    cbn [semidecidable_prefix_recognizer].
    rewrite Cantor.cancel_of_to. simpl. now rewrite Hhead, Htail.
  - intros [code Hcode] x Hx.
    destruct (Cantor.of_nat code) as [head_fuel tail_code] eqn:Htuple.
    cbn [semidecidable_prefix_recognizer] in Hcode.
    rewrite Htuple in Hcode.
    apply Bool.andb_true_iff in Hcode.
    destruct Hcode as [Hhead Htail].
    destruct (Nat.eq_dec x k) as [-> | Hne].
    + apply (proj2 (Hrecognize (k, a))). now exists head_fuel.
    + apply (proj2 (IH a)).
      * now exists tail_code.
      * lia.
Qed.

(** Semidecidability is closed under a finite universal quantifier whose
    bound may depend on the input. *)
Lemma semidecidable_bounded_forall_nat : forall A
    (bound : A -> nat) (p : nat * A -> Prop),
  semidecidable p ->
  semidecidable (fun a => forall x, x < bound a -> p (x, a)).
Proof.
  intros A bound p [recognize Hrecognize].
  exists (fun a code =>
    semidecidable_prefix_recognizer recognize a (bound a) code).
  intro a. now apply semidecidable_prefix_recognizer_spec.
Qed.

(** The generic bounded-quantifier semantics uses classical logic for an
    arbitrary guard.  Natural-number order is decidable, so this specialized
    equivalence is constructive. *)
Lemma r0_semiformula_eval_ball_lt : forall X n (fv : X -> nat)
    (bv : Fin.t n -> nat) (t : semiterm oring_language X n)
    (p : semiformula oring_language X (S n)),
  semiformula_eval nat_standard_structure bv fv
      (semiformula_ball_lt arithmetic_lt_operator t p) <->
  forall x,
    x < semiterm_val nat_standard_structure bv fv t ->
    semiformula_eval nat_standard_structure (fin_env_cons x bv) fv p.
Proof.
  intros X n fv bv t p.
  unfold semiformula_ball_lt, semiformula_bounded_all, semiformula_imp,
    arithmetic_lt_operator.
  rewrite semiformula_lt_operator_apply.
  cbn [semiformula_neg semiformula_eval].
  setoid_rewrite semiterm_val_fin_two.
  setoid_rewrite semiterm_val_bshift.
  split.
  - intros Hall x Hx. destruct (Hall x) as [Hnot | Hp].
    + contradiction.
    + exact Hp.
  - intros Hall x.
    destruct (lt_dec x (semiterm_val nat_standard_structure bv fv t)).
    + right. now apply Hall.
    + now left.
Qed.

(** Source theorem [sigma1_re].  A fixed interpretation of free variables
    is treated as a parameter; the finite bound-variable environment is the
    input recognized by the resulting semidecision procedure. *)
Theorem r0_sigma_one_semidecidable : forall X (fv : X -> nat) n
    (p : semiformula oring_language X n),
  arithmetic_hierarchy X arithmetic_sigma 1 n p ->
  semidecidable
    (fun bv => semiformula_eval nat_standard_structure bv fv p).
Proof.
  intros X fv.
  set (P := fun n (p : semiformula oring_language X n) =>
    semidecidable
      (fun bv => semiformula_eval nat_standard_structure bv fv p)).
  assert (Hverum : forall n, P n (Semiformula_verum n)).
  { intro n. unfold P. apply semidecidable_true. }
  assert (Hfalsum : forall n, P n (Semiformula_falsum n)).
  { intro n. unfold P. apply semidecidable_false. }
  assert (Hrel : forall n k (r : language_rel oring_language k)
      (v : Fin.t k -> semiterm oring_language X n),
      P n (Semiformula_rel r v)).
  { intros n k r v. unfold P.
    apply decidable_predicate_semidecidable. intro bv.
    destruct r; cbn [semiformula_eval nat_standard_structure
      oring_standard_structure].
    - apply Nat.eq_dec.
    - apply lt_dec. }
  assert (Hnrel : forall n k (r : language_rel oring_language k)
      (v : Fin.t k -> semiterm oring_language X n),
      P n (Semiformula_nrel r v)).
  { intros n k r v. unfold P.
    apply decidable_predicate_semidecidable. intro bv.
    destruct r; cbn [semiformula_eval nat_standard_structure
      oring_standard_structure].
    - destruct (Nat.eq_dec
        (semiterm_val nat_standard_structure bv fv (v Fin.F1))
        (semiterm_val nat_standard_structure bv fv
          (v (Fin.FS Fin.F1)))); firstorder.
    - destruct (lt_dec
        (semiterm_val nat_standard_structure bv fv (v Fin.F1))
        (semiterm_val nat_standard_structure bv fv
          (v (Fin.FS Fin.F1)))); firstorder. }
  assert (Hand : forall n (p q : semiformula oring_language X n),
      arithmetic_hierarchy X arithmetic_sigma 1 n p ->
      arithmetic_hierarchy X arithmetic_sigma 1 n q ->
      P n p -> P n q -> P n (Semiformula_and p q)).
  { intros n p q _ _ IHp IHq. unfold P in *.
    apply semidecidable_and; assumption. }
  assert (Hor : forall n (p q : semiformula oring_language X n),
      arithmetic_hierarchy X arithmetic_sigma 1 n p ->
      arithmetic_hierarchy X arithmetic_sigma 1 n q ->
      P n p -> P n q -> P n (Semiformula_or p q)).
  { intros n p q _ _ IHp IHq. unfold P in *.
    apply semidecidable_or; assumption. }
  assert (Hball : forall n (t : semiterm oring_language X n)
      (p : semiformula oring_language X (S n)),
      arithmetic_hierarchy X arithmetic_sigma 1 (S n) p ->
      P (S n) p ->
      P n (semiformula_ball_lt arithmetic_lt_operator t p)).
  { intros n t p _ IHp. unfold P in *.
    apply (semidecidable_ext
      (p := fun bv =>
        forall x,
          x < semiterm_val nat_standard_structure bv fv t ->
          semiformula_eval nat_standard_structure
            (fin_env_cons x bv) fv p)).
    - intro bv. symmetry. apply r0_semiformula_eval_ball_lt.
    - apply (@semidecidable_bounded_forall_nat
        (Fin.t n -> nat)
        (fun bv => semiterm_val nat_standard_structure bv fv t)
        (fun xb => semiformula_eval nat_standard_structure
          (fin_env_cons (fst xb) (snd xb)) fv p)).
      apply (semidecidable_comp
        (fun xb : nat * (Fin.t n -> nat) =>
          fin_env_cons (fst xb) (snd xb))
        (p := fun bv =>
          semiformula_eval nat_standard_structure bv fv p)).
      exact IHp. }
  assert (Hexists : forall n
      (p : semiformula oring_language X (S n)),
      arithmetic_hierarchy X arithmetic_sigma 1 (S n) p ->
      P (S n) p -> P n (Semiformula_exists p)).
  { intros n p _ IHp. unfold P in *.
    apply (semidecidable_ext
      (p := fun bv => exists x,
        semiformula_eval nat_standard_structure
          (fin_env_cons x bv) fv p)).
    - intro bv. reflexivity.
    - apply (@semidecidable_projection
        (Fin.t n -> nat) nat nat_enumerable_decoder
        (fun bx => semiformula_eval nat_standard_structure
          (fin_env_cons (snd bx) (fst bx)) fv p)).
      apply (semidecidable_comp
        (fun bx : (Fin.t n -> nat) * nat =>
          fin_env_cons (snd bx) (fst bx))
        (p := fun bv =>
          semiformula_eval nat_standard_structure bv fv p)).
      exact IHp. }
  intros n p Hp.
  exact (arithmetic_sigma_one_induction Hverum Hfalsum Hrel Hnrel
    Hand Hor Hball Hexists Hp).
Qed.
