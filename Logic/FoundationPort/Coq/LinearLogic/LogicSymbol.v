(** Capability-driven linear-logic connective interfaces. *)

From Stdlib Require Import Lists.List.

Import ListNotations.

Definition binary_injective {A} (op : A -> A -> A) : Prop :=
  forall a b c d, op a b = op c d -> a = c /\ b = d.

Record multiplicative_connective (A : Type) := {
  linear_tensor : A -> A -> A;
  linear_par : A -> A -> A;
  linear_tensor_injective : binary_injective linear_tensor;
  linear_par_injective : binary_injective linear_par
}.

Record multiplicative_neutral (A : Type) := {
  linear_one : A;
  linear_bottom : A
}.

Record additive_connective (A : Type) := {
  linear_with : A -> A -> A;
  linear_plus : A -> A -> A;
  linear_with_injective : binary_injective linear_with;
  linear_plus_injective : binary_injective linear_plus
}.

Record additive_neutral (A : Type) := {
  linear_top : A;
  linear_zero : A
}.

Record exponential_connective (A : Type) := {
  linear_bang : A -> A;
  linear_quest : A -> A;
  linear_bang_injective : forall a b,
    linear_bang a = linear_bang b -> a = b;
  linear_quest_injective : forall a b,
    linear_quest a = linear_quest b -> a = b
}.

Arguments linear_tensor {A} _ _ _.
Arguments linear_par {A} _ _ _.
Arguments linear_one {A} _.
Arguments linear_bottom {A} _.
Arguments linear_with {A} _ _ _.
Arguments linear_plus {A} _ _ _.
Arguments linear_top {A} _.
Arguments linear_zero {A} _.
Arguments linear_bang {A} _ _.
Arguments linear_quest {A} _ _.

Record multiplicative_de_morgan {A}
    (C : multiplicative_connective A) (neg : A -> A) : Prop := {
  linear_neg_tensor : forall phi psi,
    neg (linear_tensor C phi psi) =
    linear_par C (neg phi) (neg psi);
  linear_neg_par : forall phi psi,
    neg (linear_par C phi psi) =
    linear_tensor C (neg phi) (neg psi)
}.

Record multiplicative_neutral_de_morgan {A}
    (N : multiplicative_neutral A) (neg : A -> A) : Prop := {
  linear_neg_one : neg (linear_one N) = linear_bottom N;
  linear_neg_bottom : neg (linear_bottom N) = linear_one N
}.

Record additive_de_morgan {A}
    (C : additive_connective A) (neg : A -> A) : Prop := {
  linear_neg_with : forall phi psi,
    neg (linear_with C phi psi) =
    linear_plus C (neg phi) (neg psi);
  linear_neg_plus : forall phi psi,
    neg (linear_plus C phi psi) =
    linear_with C (neg phi) (neg psi)
}.

Record additive_neutral_de_morgan {A}
    (N : additive_neutral A) (neg : A -> A) : Prop := {
  linear_neg_top : neg (linear_top N) = linear_zero N;
  linear_neg_zero : neg (linear_zero N) = linear_top N
}.

Record exponential_de_morgan {A}
    (C : exponential_connective A) (neg : A -> A) : Prop := {
  linear_neg_bang : forall phi,
    neg (linear_bang C phi) = linear_quest C (neg phi);
  linear_neg_quest : forall phi,
    neg (linear_quest C phi) = linear_bang C (neg phi)
}.

Definition linear_lolli {A} (C : multiplicative_connective A)
    (neg : A -> A) (phi psi : A) : A :=
  linear_par C (neg phi) psi.

Lemma linear_lolli_def : forall A (C : multiplicative_connective A)
    neg phi psi,
  linear_lolli C neg phi psi = linear_par C (neg phi) psi.
Proof. reflexivity. Qed.

Lemma linear_tensor_eq_iff : forall A (C : multiplicative_connective A)
    a b c d,
  linear_tensor C a b = linear_tensor C c d <-> a = c /\ b = d.
Proof.
  intros A C a b c d. split.
  - apply (linear_tensor_injective A C).
  - intros [-> ->]. reflexivity.
Qed.

Lemma linear_par_eq_iff : forall A (C : multiplicative_connective A)
    a b c d,
  linear_par C a b = linear_par C c d <-> a = c /\ b = d.
Proof.
  intros A C a b c d. split.
  - apply (linear_par_injective A C).
  - intros [-> ->]. reflexivity.
Qed.

Lemma involutive_injective : forall A (neg : A -> A),
  (forall x, neg (neg x) = x) ->
  forall x y, neg x = neg y -> x = y.
Proof.
  intros A neg Hinv x y Hxy.
  apply (f_equal neg) in Hxy.
  now rewrite !Hinv in Hxy.
Qed.

Lemma linear_lolli_eq_iff : forall A (C : multiplicative_connective A)
    (neg : A -> A),
  (forall x, neg (neg x) = x) ->
  forall a b c d,
  linear_lolli C neg a b = linear_lolli C neg c d <->
  a = c /\ b = d.
Proof.
  intros A C neg Hinv a b c d. unfold linear_lolli.
  rewrite linear_par_eq_iff. split.
  - intros [Hneg Hb]. split.
    + exact (@involutive_injective A neg Hinv a c Hneg).
    + exact Hb.
  - intros [-> ->]. split; reflexivity.
Qed.

Lemma linear_with_eq_iff : forall A (C : additive_connective A)
    a b c d,
  linear_with C a b = linear_with C c d <-> a = c /\ b = d.
Proof.
  intros A C a b c d. split.
  - apply (linear_with_injective A C).
  - intros [-> ->]. reflexivity.
Qed.

Lemma linear_plus_eq_iff : forall A (C : additive_connective A)
    a b c d,
  linear_plus C a b = linear_plus C c d <-> a = c /\ b = d.
Proof.
  intros A C a b c d. split.
  - apply (linear_plus_injective A C).
  - intros [-> ->]. reflexivity.
Qed.

Lemma linear_bang_eq_iff : forall A (C : exponential_connective A) a b,
  linear_bang C a = linear_bang C b <-> a = b.
Proof.
  intros A C a b. split.
  - apply (linear_bang_injective A C).
  - now intros ->.
Qed.

Lemma linear_quest_eq_iff : forall A (C : exponential_connective A) a b,
  linear_quest C a = linear_quest C b <-> a = b.
Proof.
  intros A C a b. split.
  - apply (linear_quest_injective A C).
  - now intros ->.
Qed.

Definition linear_list_quest {A} (C : exponential_connective A)
    (Gamma : list A) : list A :=
  map (linear_quest C) Gamma.

Lemma linear_list_quest_def : forall A (C : exponential_connective A) Gamma,
  linear_list_quest C Gamma = map (linear_quest C) Gamma.
Proof. reflexivity. Qed.

Lemma linear_list_quest_nil : forall A (C : exponential_connective A),
  linear_list_quest C [] = [].
Proof. reflexivity. Qed.

Lemma linear_list_quest_cons : forall A (C : exponential_connective A)
    phi Gamma,
  linear_list_quest C (phi :: Gamma) =
  linear_quest C phi :: linear_list_quest C Gamma.
Proof. reflexivity. Qed.

Lemma linear_list_quest_append : forall A (C : exponential_connective A)
    Gamma Delta,
  linear_list_quest C (Gamma ++ Delta) =
  linear_list_quest C Gamma ++ linear_list_quest C Delta.
Proof.
  intros A C Gamma Delta. unfold linear_list_quest.
  apply map_app.
Qed.
