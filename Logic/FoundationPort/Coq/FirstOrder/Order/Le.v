(**
  The weak-order operator and its logical completeness interface.

  Foundation defines weak order from equality and strict order, then proves
  its defining biconditional by a restricted completeness theorem.  The Coq
  formulation keeps the operators abstract and observes that the
  biconditional is a pure logical theorem, so no equality axioms are needed.
*)

From Stdlib Require Import Vectors.Fin.
From Foundation.Syntax.Predicate Require Import Language Term.
From Foundation.FirstOrder.Basic.Syntax Require Import Formula.
From Foundation.FirstOrder.Basic Require Import Operator Calculus.
From Foundation.FirstOrder.Basic.Semantics Require Import Semantics ModelTheory.
From Foundation.FirstOrder.Completeness Require Import CounterModel.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

Definition first_order_order_le_operator {L}
    (Heq : semiformula_has_eq_operator L)
    (Hlt : semiformula_has_lt_operator L) : semiformula_has_le_operator L :=
  semiformula_le_operator_of_eq_lt Heq Hlt.

Lemma first_order_order_le_apply : forall L X n
    (Heq : semiformula_has_eq_operator L)
    (Hlt : semiformula_has_lt_operator L)
    (t u : semiterm L X n),
  semiformula_operator_apply
      (semiformula_le_operator (first_order_order_le_operator Heq Hlt))
      (fin_two t u) =
  Semiformula_or
    (semiformula_operator_apply (semiformula_eq_operator Heq) (fin_two t u))
    (semiformula_operator_apply (semiformula_lt_operator Hlt) (fin_two t u)).
Proof.
  intros. unfold first_order_order_le_operator,
    semiformula_le_operator_of_eq_lt. simpl.
  apply semiformula_operator_or_apply.
Qed.

Definition first_order_order_le_atom {L}
    (Heq : semiformula_has_eq_operator L)
    (Hlt : semiformula_has_lt_operator L) : semisentence L 2 :=
  semiformula_operator_apply
    (semiformula_le_operator (first_order_order_le_operator Heq Hlt))
    (fin_two
      (@Semiterm_bvar L Empty_set 2 Fin.F1)
      (@Semiterm_bvar L Empty_set 2 (Fin.FS Fin.F1))).

Definition first_order_order_eq_or_lt_atom {L}
    (Heq : semiformula_has_eq_operator L)
    (Hlt : semiformula_has_lt_operator L) : semisentence L 2 :=
  Semiformula_or
    (semiformula_operator_apply (semiformula_eq_operator Heq)
      (fin_two
        (@Semiterm_bvar L Empty_set 2 Fin.F1)
        (@Semiterm_bvar L Empty_set 2 (Fin.FS Fin.F1))))
    (semiformula_operator_apply (semiformula_lt_operator Hlt)
      (fin_two
        (@Semiterm_bvar L Empty_set 2 Fin.F1)
        (@Semiterm_bvar L Empty_set 2 (Fin.FS Fin.F1)))).

Lemma first_order_order_le_atom_eq : forall L
    (Heq : semiformula_has_eq_operator L)
    (Hlt : semiformula_has_lt_operator L),
  first_order_order_le_atom Heq Hlt =
  first_order_order_eq_or_lt_atom Heq Hlt.
Proof.
  intros. unfold first_order_order_le_atom,
    first_order_order_eq_or_lt_atom.
  apply first_order_order_le_apply.
Qed.

Definition first_order_order_le_iff_sentence {L}
    (Heq : semiformula_has_eq_operator L)
    (Hlt : semiformula_has_lt_operator L) : sentence L :=
  Semiformula_all (Semiformula_all
    (semiformula_iff
      (first_order_order_le_atom Heq Hlt)
      (first_order_order_eq_or_lt_atom Heq Hlt))).

Lemma first_order_order_le_iff_sentence_realize : forall L M
    (Str : first_order_structure L M)
    (Heq : semiformula_has_eq_operator L)
    (Hlt : semiformula_has_lt_operator L),
  sentence_realize Str (first_order_order_le_iff_sentence Heq Hlt).
Proof.
  intros L M Str Heq Hlt.
  change (forall x y : M,
    semiformula_eval Str
      (fin_env_cons y (fin_env_cons x
        (fun i : Fin.t 0 => match i with end)))
      (fun z : Empty_set => match z with end)
      (semiformula_iff
        (first_order_order_le_atom Heq Hlt)
        (first_order_order_eq_or_lt_atom Heq Hlt))).
  intros x y. rewrite semiformula_eval_iff,
    first_order_order_le_atom_eq. reflexivity.
Qed.

Theorem first_order_order_le_iff_provable : forall L
    (T : theory L)
    (Heq : semiformula_has_eq_operator L)
    (Hlt : semiformula_has_lt_operator L),
  first_order_theory_provable T
    (first_order_order_le_iff_sentence Heq Hlt).
Proof.
  intros L T Heq Hlt.
  apply first_order_theory_proof_complete.
  intros m _. apply first_order_order_le_iff_sentence_realize.
Qed.

Theorem first_order_order_complete : forall L
    (T : theory L) (sigma : sentence L),
  (forall m, first_order_models_theory m T ->
    first_order_model_realize m sigma) ->
  first_order_theory_provable T sigma.
Proof.
  intros L T sigma Hmodels.
  apply first_order_theory_proof_complete. exact Hmodels.
Qed.
