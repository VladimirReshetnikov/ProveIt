(**
  Generic first- and second-order quantifier operations.

  This ports the complete mathematical surface of
  [Foundation/Syntax/Predicate/Quantifier.lean].  The connective component is
  reused from the already audited Foundation [LogicSymbol] port.  Iterators
  index their input by [k + n], rather than [n + k], so recursion is
  judgmental in Coq; [Nat.add_comm] identifies the two presentations.
*)

From Stdlib Require Import Arith.PeanoNat.
From FoundationModal Require Import GenericSemantics.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

Inductive polarity : Type := Polarity_sigma | Polarity_pi.

Definition polarity_alt (p : polarity) : polarity :=
  match p with
  | Polarity_sigma => Polarity_pi
  | Polarity_pi => Polarity_sigma
  end.

Lemma polarity_alt_involutive : forall p, polarity_alt (polarity_alt p) = p.
Proof. intros []; reflexivity. Qed.

Inductive sigma_pi_delta : Type :=
| SigmaPiDelta_sigma | SigmaPiDelta_pi | SigmaPiDelta_delta.

Definition sigma_pi_delta_alt (p : sigma_pi_delta) : sigma_pi_delta :=
  match p with
  | SigmaPiDelta_sigma => SigmaPiDelta_pi
  | SigmaPiDelta_pi => SigmaPiDelta_sigma
  | SigmaPiDelta_delta => SigmaPiDelta_delta
  end.

Lemma sigma_pi_delta_alt_involutive :
  forall p, sigma_pi_delta_alt (sigma_pi_delta_alt p) = p.
Proof. intros []; reflexivity. Qed.

Definition polarity_to_sigma_pi_delta (p : polarity) : sigma_pi_delta :=
  match p with
  | Polarity_sigma => SigmaPiDelta_sigma
  | Polarity_pi => SigmaPiDelta_pi
  end.

Lemma sigma_pi_delta_alt_polarity :
  forall p,
    sigma_pi_delta_alt (polarity_to_sigma_pi_delta p) =
    polarity_to_sigma_pi_delta (polarity_alt p).
Proof. intros []; reflexivity. Qed.

(** * First-order quantifiers *)

Record first_universal_quantifier (A : nat -> Type) : Type := {
  first_all : forall n, A (S n) -> A n
}.

Record first_existential_quantifier (A : nat -> Type) : Type := {
  first_exists : forall n, A (S n) -> A n
}.

Arguments first_all {A} _ _ _.
Arguments first_exists {A} _ _ _.

Record first_quantifiers (A : nat -> Type) : Type := {
  first_quantifier_all : first_universal_quantifier A;
  first_quantifier_exists : first_existential_quantifier A
}.

Record first_connectives_with_quantifiers (A : nat -> Type) : Type := {
  first_lcwq_quantifiers : first_quantifiers A;
  first_lcwq_connectives : forall n, generic_connectives (A n)
}.

Fixpoint first_all_closure {A} (Q : first_universal_quantifier A)
    (n : nat) : A n -> A 0 :=
  match n as k return A k -> A 0 with
  | 0 => fun a => a
  | S k => fun a =>
      @first_all_closure A Q k (@first_all A Q k a)
  end.

Arguments first_all_closure {A} _ _ _.

Lemma first_all_closure_zero :
  forall A (Q : first_universal_quantifier A) (a : A 0),
    first_all_closure Q 0 a = a.
Proof. reflexivity. Qed.

Lemma first_all_closure_succ :
  forall A (Q : first_universal_quantifier A) n (a : A (S n)),
    first_all_closure Q (S n) a =
    first_all_closure Q n (first_all Q n a).
Proof. reflexivity. Qed.

Fixpoint first_all_iter {A} (Q : first_universal_quantifier A)
    (k n : nat) : A (k + n) -> A n :=
  match k as j return A (j + n) -> A n with
  | 0 => fun a => a
  | S j => fun a =>
      @first_all_iter A Q j n (@first_all A Q (j + n) a)
  end.

Arguments first_all_iter {A} _ _ _ _.

Lemma first_all_iter_zero :
  forall A (Q : first_universal_quantifier A) n (a : A n),
    first_all_iter Q 0 n a = a.
Proof. reflexivity. Qed.

Lemma first_all_iter_one :
  forall A (Q : first_universal_quantifier A) n (a : A (S n)),
    first_all_iter Q 1 n a = first_all Q n a.
Proof. reflexivity. Qed.

Lemma first_all_iter_succ :
  forall A (Q : first_universal_quantifier A) k n (a : A (S (k + n))),
    first_all_iter Q (S k) n a =
    first_all_iter Q k n (first_all Q (k + n) a).
Proof. reflexivity. Qed.

Fixpoint first_exists_closure {A} (Q : first_existential_quantifier A)
    (n : nat) : A n -> A 0 :=
  match n as k return A k -> A 0 with
  | 0 => fun a => a
  | S k => fun a =>
      @first_exists_closure A Q k (@first_exists A Q k a)
  end.

Arguments first_exists_closure {A} _ _ _.

Lemma first_exists_closure_zero :
  forall A (Q : first_existential_quantifier A) (a : A 0),
    first_exists_closure Q 0 a = a.
Proof. reflexivity. Qed.

Lemma first_exists_closure_succ :
  forall A (Q : first_existential_quantifier A) n (a : A (S n)),
    first_exists_closure Q (S n) a =
    first_exists_closure Q n (first_exists Q n a).
Proof. reflexivity. Qed.

Fixpoint first_exists_iter {A} (Q : first_existential_quantifier A)
    (k n : nat) : A (k + n) -> A n :=
  match k as j return A (j + n) -> A n with
  | 0 => fun a => a
  | S j => fun a =>
      @first_exists_iter A Q j n (@first_exists A Q (j + n) a)
  end.

Arguments first_exists_iter {A} _ _ _ _.

Lemma first_exists_iter_zero :
  forall A (Q : first_existential_quantifier A) n (a : A n),
    first_exists_iter Q 0 n a = a.
Proof. reflexivity. Qed.

Lemma first_exists_iter_one :
  forall A (Q : first_existential_quantifier A) n (a : A (S n)),
    first_exists_iter Q 1 n a = first_exists Q n a.
Proof. reflexivity. Qed.

Lemma first_exists_iter_succ :
  forall A (Q : first_existential_quantifier A) k n (a : A (S (k + n))),
    first_exists_iter Q (S k) n a =
    first_exists_iter Q k n (first_exists Q (k + n) a).
Proof. reflexivity. Qed.

Definition first_bounded_all {A n} (Q : first_universal_quantifier A)
    (C : generic_connectives (A (S n))) (p q : A (S n)) : A n :=
  first_all Q n (generic_imp C p q).

Definition first_bounded_exists {A n} (Q : first_existential_quantifier A)
    (C : generic_connectives (A (S n))) (p q : A (S n)) : A n :=
  first_exists Q n (generic_and C p q).

(** * Second-order quantifiers *)

Record second_universal_quantifier (A : nat -> nat -> Type) : Type := {
  second_all : forall m n, A (S m) n -> A m n
}.

Record second_existential_quantifier (A : nat -> nat -> Type) : Type := {
  second_exists : forall m n, A (S m) n -> A m n
}.

Arguments second_all {A} _ _ _ _.
Arguments second_exists {A} _ _ _ _.

Record second_quantifiers (A : nat -> nat -> Type) : Type := {
  second_quantifier_all : second_universal_quantifier A;
  second_quantifier_exists : second_existential_quantifier A
}.

Record second_connectives_with_quantifiers (A : nat -> nat -> Type) : Type := {
  second_lcwq_quantifiers : second_quantifiers A;
  second_lcwq_first_order : forall m, first_connectives_with_quantifiers (A m)
}.

Fixpoint second_all_closure {A} (Q : second_universal_quantifier A)
    (m n : nat) : A m n -> A 0 n :=
  match m as k return A k n -> A 0 n with
  | 0 => fun a => a
  | S k => fun a =>
      @second_all_closure A Q k n (@second_all A Q k n a)
  end.

Arguments second_all_closure {A} _ _ _ _.

Lemma second_all_closure_zero :
  forall A (Q : second_universal_quantifier A) n (a : A 0 n),
    second_all_closure Q 0 n a = a.
Proof. reflexivity. Qed.

Lemma second_all_closure_succ :
  forall A (Q : second_universal_quantifier A) m n (a : A (S m) n),
    second_all_closure Q (S m) n a =
    second_all_closure Q m n (second_all Q m n a).
Proof. reflexivity. Qed.

Fixpoint second_all_iter {A} (Q : second_universal_quantifier A)
    (k m n : nat) : A (k + m) n -> A m n :=
  match k as j return A (j + m) n -> A m n with
  | 0 => fun a => a
  | S j => fun a =>
      @second_all_iter A Q j m n (@second_all A Q (j + m) n a)
  end.

Arguments second_all_iter {A} _ _ _ _ _.

Lemma second_all_iter_zero :
  forall A (Q : second_universal_quantifier A) m n (a : A m n),
    second_all_iter Q 0 m n a = a.
Proof. reflexivity. Qed.

Lemma second_all_iter_one :
  forall A (Q : second_universal_quantifier A) m n (a : A (S m) n),
    second_all_iter Q 1 m n a = second_all Q m n a.
Proof. reflexivity. Qed.

Lemma second_all_iter_succ :
  forall A (Q : second_universal_quantifier A) k m n
         (a : A (S (k + m)) n),
    second_all_iter Q (S k) m n a =
    second_all_iter Q k m n (second_all Q (k + m) n a).
Proof. reflexivity. Qed.

Fixpoint second_exists_closure {A} (Q : second_existential_quantifier A)
    (m n : nat) : A m n -> A 0 n :=
  match m as k return A k n -> A 0 n with
  | 0 => fun a => a
  | S k => fun a =>
      @second_exists_closure A Q k n (@second_exists A Q k n a)
  end.

Arguments second_exists_closure {A} _ _ _ _.

Lemma second_exists_closure_zero :
  forall A (Q : second_existential_quantifier A) n (a : A 0 n),
    second_exists_closure Q 0 n a = a.
Proof. reflexivity. Qed.

Lemma second_exists_closure_succ :
  forall A (Q : second_existential_quantifier A) m n (a : A (S m) n),
    second_exists_closure Q (S m) n a =
    second_exists_closure Q m n (second_exists Q m n a).
Proof. reflexivity. Qed.

Fixpoint second_exists_iter {A} (Q : second_existential_quantifier A)
    (k m n : nat) : A (k + m) n -> A m n :=
  match k as j return A (j + m) n -> A m n with
  | 0 => fun a => a
  | S j => fun a =>
      @second_exists_iter A Q j m n (@second_exists A Q (j + m) n a)
  end.

Arguments second_exists_iter {A} _ _ _ _ _.

Lemma second_exists_iter_zero :
  forall A (Q : second_existential_quantifier A) m n (a : A m n),
    second_exists_iter Q 0 m n a = a.
Proof. reflexivity. Qed.

Lemma second_exists_iter_one :
  forall A (Q : second_existential_quantifier A) m n (a : A (S m) n),
    second_exists_iter Q 1 m n a = second_exists Q m n a.
Proof. reflexivity. Qed.

Lemma second_exists_iter_succ :
  forall A (Q : second_existential_quantifier A) k m n
         (a : A (S (k + m)) n),
    second_exists_iter Q (S k) m n a =
    second_exists_iter Q k m n (second_exists Q (k + m) n a).
Proof. reflexivity. Qed.

Definition second_bounded_all {A m n} (Q : second_universal_quantifier A)
    (C : generic_connectives (A (S m) n)) (p q : A (S m) n) : A m n :=
  second_all Q m n (generic_imp C p q).

Definition second_bounded_exists {A m n} (Q : second_existential_quantifier A)
    (C : generic_connectives (A (S m) n)) (p q : A (S m) n) : A m n :=
  second_exists Q m n (generic_and C p q).
