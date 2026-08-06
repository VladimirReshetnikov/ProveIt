(**
  Structural recognition of bootstrapped first-order proof codes.

  The source realizes the least fixed point of ten proof rules inside an
  arbitrary arithmetic model.  This standard-natural core keeps the same ten
  rules but represents finite sequents by duplicate-tolerant lists.  The
  recognizer is inductive, so recursive premises and the formula/term arity
  invariants are enforced directly instead of recovered from an untyped
  numerical fixed point.
*)

From Stdlib Require Import Arith.PeanoNat Bool Cantor Lists.List Lia Vectors.Fin.
From Foundation.Syntax.Predicate Require Import Language Term Rew.
From Foundation.FirstOrder.Basic.Syntax Require Import Formula.
From Foundation.FirstOrder.Basic Require Import Calculus Coding.
From Foundation.FirstOrder.Bootstrapping.Syntax.Term Require Import Basic.
From Foundation.FirstOrder.Bootstrapping.Syntax.Formula Require Import
  Basic Functions Coding.
From Foundation.FirstOrder.Bootstrapping.Syntax Require Import Theory.

Import ListNotations.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

Lemma boot_list_in_of_generic_list_member : forall (A : Type) (x : A) xs,
  GenericAdjunctiveSet.generic_list_member x xs -> In x xs.
Proof.
  intros A x xs. induction xs as [|y ys IH]; simpl; [tauto|].
  intros [Hxy | Hx].
  - left. now symmetry.
  - right. now apply IH.
Qed.

(** * Injective finite-list and sequent coding *)

Fixpoint boot_nat_list_code (xs : list nat) : nat :=
  match xs with
  | [] => Cantor.to_nat (0, 0)
  | x :: rest =>
      Cantor.to_nat (1, Cantor.to_nat (x, boot_nat_list_code rest))
  end.

Local Opaque Cantor.to_nat.

Theorem boot_nat_list_code_injective : forall xs ys,
  boot_nat_list_code xs = boot_nat_list_code ys -> xs = ys.
Proof.
  induction xs as [|x xs IH]; destruct ys as [|y ys]; intro H.
  - reflexivity.
  - cbn [boot_nat_list_code] in H. apply Cantor.to_nat_inj in H.
    discriminate H.
  - cbn [boot_nat_list_code] in H. apply Cantor.to_nat_inj in H.
    discriminate H.
  - cbn [boot_nat_list_code] in H. apply Cantor.to_nat_inj in H.
    injection H as Hpayload. apply Cantor.to_nat_inj in Hpayload.
    injection Hpayload as Hxy Htail. f_equal; [exact Hxy|now apply IH].
Qed.

Lemma boot_nat_list_code_member_le : forall xs x,
  In x xs -> x <= boot_nat_list_code xs.
Proof.
  induction xs as [|y ys IH]; intros x Hx; [contradiction|].
  cbn [boot_nat_list_code].
  pose proof (Cantor.to_nat_non_decreasing
    y (boot_nat_list_code ys)) as Hinner.
  pose proof (Cantor.to_nat_non_decreasing 1
    (Cantor.to_nat (y, boot_nat_list_code ys))) as Houter.
  destruct Hx as [->|Hx].
  - lia.
  - specialize (IH x Hx). lia.
Qed.

Definition boot_sequent_quote {L} (EL : language_encodable L)
    (Gamma : first_order_sequent L) : nat :=
  boot_nat_list_code (map (boot_typed_formula_quote EL) Gamma).

Theorem boot_sequent_quote_injective : forall L EL
    (Gamma Delta : first_order_sequent L),
  boot_sequent_quote EL Gamma = boot_sequent_quote EL Delta -> Gamma = Delta.
Proof.
  intros L EL Gamma; induction Gamma as [|p Gamma IH];
    destruct Delta as [|q Delta]; intro H.
  - reflexivity.
  - unfold boot_sequent_quote in H.
    apply boot_nat_list_code_injective in H. discriminate.
  - unfold boot_sequent_quote in H.
    apply boot_nat_list_code_injective in H. discriminate.
  - unfold boot_sequent_quote in H.
    apply boot_nat_list_code_injective in H. injection H as Hpq Htail.
    f_equal.
    + now apply boot_typed_formula_quote_injective in Hpq.
    + apply IH. unfold boot_sequent_quote. now rewrite Htail.
Qed.

Lemma boot_sequent_quote_member_iff : forall L EL
    (Gamma : first_order_sequent L) (p : proposition L),
  In (boot_typed_formula_quote EL p)
      (map (boot_typed_formula_quote EL) Gamma) <-> In p Gamma.
Proof.
  intros L EL Gamma; induction Gamma as [|q Gamma IH]; intro p; simpl.
  - tauto.
  - rewrite IH. split.
    + intros [H | H]; [left|now right].
      now apply boot_typed_formula_quote_injective in H.
    + intros [-> | H]; [now left|now right].
Qed.

(** * Formula sets and code-level shifts *)

Definition boot_is_formula_set {L} (EL : language_encodable L)
    (Gamma : list nat) : Prop := Forall (boot_is_formula EL) Gamma.

Lemma boot_is_formula_set_nil : forall L EL,
  @boot_is_formula_set L EL [].
Proof. constructor. Qed.

Lemma boot_is_formula_set_cons_iff : forall L EL p Gamma,
  @boot_is_formula_set L EL (p :: Gamma) <->
  boot_is_formula EL p /\ boot_is_formula_set EL Gamma.
Proof.
  intros; split; intro H; inversion H; subst; now split || constructor.
Qed.

Lemma boot_is_formula_set_app_iff : forall L EL Gamma Delta,
  @boot_is_formula_set L EL (Gamma ++ Delta) <->
  boot_is_formula_set EL Gamma /\ boot_is_formula_set EL Delta.
Proof. intros. unfold boot_is_formula_set. apply Forall_app. Qed.

Lemma boot_is_formula_set_quote : forall L EL
    (Gamma : first_order_sequent L),
  boot_is_formula_set EL (map (boot_typed_formula_quote EL) Gamma).
Proof.
  intros. induction Gamma as [|p Gamma IH]; simpl; constructor; auto.
  apply boot_typed_formula_quote_recognized.
Qed.

Definition boot_sequent_shift_code {L} (EL : language_encodable L)
    (Gamma : list nat) : list nat :=
  map (boot_formula_shift_code EL 0) Gamma.

Lemma boot_is_formula_set_shift : forall L EL Gamma,
  @boot_is_formula_set L EL Gamma ->
  boot_is_formula_set EL (boot_sequent_shift_code EL Gamma).
Proof.
  intros L EL Gamma H. induction H; simpl; constructor; auto.
  now apply boot_formula_shift_code_preserves.
Qed.

Lemma boot_sequent_shift_quote : forall L EL
    (Gamma : first_order_sequent L),
  map (boot_typed_formula_quote EL) (first_order_sequent_shift Gamma) =
  boot_sequent_shift_code EL
    (map (boot_typed_formula_quote EL) Gamma).
Proof.
  intros. induction Gamma as [|p Gamma IH]; simpl; [reflexivity|].
  f_equal; [apply boot_typed_formula_quote_shift|assumption].
Qed.

Definition boot_formula_free_code {L} (EL : language_encodable L)
    (code : nat) : nat :=
  boot_formula_subst_code EL
    (fun _ : Fin.t 1 => @Semiterm_fvar L nat 0 0)
    (boot_formula_shift_code EL 1 code).

Lemma boot_formula_free_code_quote : forall L EL
    (p : semiproposition L 1),
  boot_formula_free_code EL (boot_typed_formula_quote EL p) =
  boot_typed_formula_quote EL (@semiformula_free L 0 p).
Proof.
  intros. symmetry. apply boot_typed_formula_quote_free.
Qed.

Lemma boot_formula_free_code_preserves : forall L EL code,
  @boot_is_semiformula L EL 1 code ->
  boot_is_formula EL (boot_formula_free_code EL code).
Proof.
  intros. unfold boot_formula_free_code.
  apply boot_formula_subst_code_preserves.
  now apply boot_formula_shift_code_preserves.
Qed.

(** * Ten raw proof constructors *)

Definition boot_proof_node (sequent tag : nat) (fields : list nat) : nat :=
  S (Cantor.to_nat
    (sequent, Cantor.to_nat (tag, boot_nat_list_code fields))).

Definition boot_proof_conseq (code : nat) : nat :=
  fst (Cantor.of_nat (Nat.pred code)).

Lemma boot_proof_node_nonzero : forall s tag fields,
  boot_proof_node s tag fields <> 0.
Proof. discriminate. Qed.

Lemma boot_proof_conseq_node : forall s tag fields,
  boot_proof_conseq (boot_proof_node s tag fields) = s.
Proof.
  intros. unfold boot_proof_conseq, boot_proof_node. simpl.
  rewrite Cantor.cancel_of_to. reflexivity.
Qed.

Definition boot_axL (s p : nat) : nat := boot_proof_node s 0 [p].
Definition boot_verum_intro (s : nat) : nat := boot_proof_node s 1 [].
Definition boot_and_intro (s p q dp dq : nat) : nat :=
  boot_proof_node s 2 [p; q; dp; dq].
Definition boot_or_intro (s p q d : nat) : nat :=
  boot_proof_node s 3 [p; q; d].
Definition boot_all_intro (s p d : nat) : nat :=
  boot_proof_node s 4 [p; d].
Definition boot_exists_intro (s p t d : nat) : nat :=
  boot_proof_node s 5 [p; t; d].
Definition boot_weakening_rule (s d : nat) : nat :=
  boot_proof_node s 6 [d].
Definition boot_shift_rule (s d : nat) : nat :=
  boot_proof_node s 7 [d].
Definition boot_cut_rule (s p d1 d2 : nat) : nat :=
  boot_proof_node s 8 [p; d1; d2].
Definition boot_axiom_rule (s p : nat) : nat :=
  boot_proof_node s 9 [p].

Lemma boot_proof_conseq_axL : forall s p,
  boot_proof_conseq (boot_axL s p) = s.
Proof. intros. apply boot_proof_conseq_node. Qed.

Lemma boot_proof_conseq_verum_intro : forall s,
  boot_proof_conseq (boot_verum_intro s) = s.
Proof. intros. apply boot_proof_conseq_node. Qed.

Lemma boot_proof_conseq_and_intro : forall s p q dp dq,
  boot_proof_conseq (boot_and_intro s p q dp dq) = s.
Proof. intros. apply boot_proof_conseq_node. Qed.

Lemma boot_proof_conseq_or_intro : forall s p q d,
  boot_proof_conseq (boot_or_intro s p q d) = s.
Proof. intros. apply boot_proof_conseq_node. Qed.

Lemma boot_proof_conseq_all_intro : forall s p d,
  boot_proof_conseq (boot_all_intro s p d) = s.
Proof. intros. apply boot_proof_conseq_node. Qed.

Lemma boot_proof_conseq_exists_intro : forall s p t d,
  boot_proof_conseq (boot_exists_intro s p t d) = s.
Proof. intros. apply boot_proof_conseq_node. Qed.

Lemma boot_proof_conseq_weakening_rule : forall s d,
  boot_proof_conseq (boot_weakening_rule s d) = s.
Proof. intros. apply boot_proof_conseq_node. Qed.

Lemma boot_proof_conseq_shift_rule : forall s d,
  boot_proof_conseq (boot_shift_rule s d) = s.
Proof. intros. apply boot_proof_conseq_node. Qed.

Lemma boot_proof_conseq_cut_rule : forall s p d1 d2,
  boot_proof_conseq (boot_cut_rule s p d1 d2) = s.
Proof. intros. apply boot_proof_conseq_node. Qed.

Lemma boot_proof_conseq_axiom_rule : forall s p,
  boot_proof_conseq (boot_axiom_rule s p) = s.
Proof. intros. apply boot_proof_conseq_node. Qed.

(** * Structural derivation recognition *)

Inductive boot_derivation_code {L : language}
    (EL : language_encodable L) (T : theory L)
    (ET : boot_theory_encoding EL T) : list nat -> nat -> Prop :=
| Boot_derivation_axL : forall Gamma p,
    boot_is_formula_set EL Gamma ->
    In p Gamma -> In (boot_formula_neg_code EL 0 p) Gamma ->
    @boot_derivation_code L EL T ET Gamma
      (boot_axL (boot_nat_list_code Gamma) p)
| Boot_derivation_verum : forall Gamma,
    boot_is_formula_set EL Gamma -> In boot_qq_verum Gamma ->
    @boot_derivation_code L EL T ET Gamma
      (boot_verum_intro (boot_nat_list_code Gamma))
| Boot_derivation_and : forall Gamma p q dp dq,
    boot_is_formula_set EL Gamma -> In (boot_qq_and p q) Gamma ->
    @boot_derivation_code L EL T ET (p :: Gamma) dp ->
    @boot_derivation_code L EL T ET (q :: Gamma) dq ->
    @boot_derivation_code L EL T ET Gamma
      (boot_and_intro (boot_nat_list_code Gamma) p q dp dq)
| Boot_derivation_or : forall Gamma p q d,
    boot_is_formula_set EL Gamma -> In (boot_qq_or p q) Gamma ->
    @boot_derivation_code L EL T ET (p :: q :: Gamma) d ->
    @boot_derivation_code L EL T ET Gamma
      (boot_or_intro (boot_nat_list_code Gamma) p q d)
| Boot_derivation_all : forall Gamma p d,
    boot_is_formula_set EL Gamma -> In (boot_qq_all p) Gamma ->
    boot_is_semiformula EL 1 p ->
    @boot_derivation_code L EL T ET
      (boot_formula_free_code EL p :: boot_sequent_shift_code EL Gamma) d ->
    @boot_derivation_code L EL T ET Gamma
      (boot_all_intro (boot_nat_list_code Gamma) p d)
| Boot_derivation_exists : forall Gamma p t d,
    boot_is_formula_set EL Gamma -> In (boot_qq_exists p) Gamma ->
    boot_is_semiformula EL 1 p -> boot_is_semiterm EL 0 t ->
    @boot_derivation_code L EL T ET
      (boot_formula_subst_code EL
        (fun _ : Fin.t 1 =>
          match semiterm_decode EL boot_nat_encoding 0 t with
          | Some term => term
          | None => @Semiterm_fvar L nat 0 0
          end) p :: Gamma) d ->
    @boot_derivation_code L EL T ET Gamma
      (boot_exists_intro (boot_nat_list_code Gamma) p t d)
| Boot_derivation_weakening : forall Delta Gamma d,
    boot_is_formula_set EL Gamma ->
    (forall p, In p Delta -> In p Gamma) ->
    @boot_derivation_code L EL T ET Delta d ->
    @boot_derivation_code L EL T ET Gamma
      (boot_weakening_rule (boot_nat_list_code Gamma) d)
| Boot_derivation_shift : forall Gamma d,
    boot_is_formula_set EL (boot_sequent_shift_code EL Gamma) ->
    @boot_derivation_code L EL T ET Gamma d ->
    @boot_derivation_code L EL T ET (boot_sequent_shift_code EL Gamma)
      (boot_shift_rule
        (boot_nat_list_code (boot_sequent_shift_code EL Gamma)) d)
| Boot_derivation_cut : forall Gamma p d1 d2,
    boot_is_formula_set EL Gamma -> boot_is_formula EL p ->
    @boot_derivation_code L EL T ET (p :: Gamma) d1 ->
    @boot_derivation_code L EL T ET
      (boot_formula_neg_code EL 0 p :: Gamma) d2 ->
    @boot_derivation_code L EL T ET Gamma
      (boot_cut_rule (boot_nat_list_code Gamma) p d1 d2)
| Boot_derivation_axiom : forall Gamma p,
    boot_is_formula_set EL Gamma -> In p Gamma ->
    boot_theory_classifier ET p = true ->
    @boot_derivation_code L EL T ET Gamma
      (boot_axiom_rule (boot_nat_list_code Gamma) p).

Definition boot_derivation {L} (EL : language_encodable L)
    (T : theory L) (ET : boot_theory_encoding EL T) (code : nat) : Prop :=
  exists Gamma, @boot_derivation_code L EL T ET Gamma code.

Definition boot_derivation_of {L} (EL : language_encodable L)
    (T : theory L) (ET : boot_theory_encoding EL T)
    (code : nat) (Gamma : list nat) : Prop :=
  @boot_derivation_code L EL T ET Gamma code.

Definition boot_proof {L} (EL : language_encodable L)
    (T : theory L) (ET : boot_theory_encoding EL T)
    (code formula : nat) : Prop :=
  @boot_derivation_code L EL T ET [formula] code.

Definition boot_provable {L} (EL : language_encodable L)
    (T : theory L) (ET : boot_theory_encoding EL T)
    (formula : nat) : Prop :=
  exists code, @boot_proof L EL T ET code formula.

Lemma boot_derivation_code_formula_set : forall L EL T ET Gamma code,
  @boot_derivation_code L EL T ET Gamma code ->
  boot_is_formula_set EL Gamma.
Proof. intros L EL T ET Gamma code H; inversion H; assumption. Qed.

Lemma boot_derivation_code_conseq : forall L EL T ET Gamma code,
  @boot_derivation_code L EL T ET Gamma code ->
  boot_proof_conseq code = boot_nat_list_code Gamma.
Proof.
  intros L EL T ET Gamma code H; inversion H; subst;
    apply boot_proof_conseq_node.
Qed.

Lemma boot_derivation_code_nonzero : forall L EL T ET Gamma code,
  @boot_derivation_code L EL T ET Gamma code -> code <> 0.
Proof.
  intros L EL T ET Gamma code H; inversion H; subst;
    apply boot_proof_node_nonzero.
Qed.
