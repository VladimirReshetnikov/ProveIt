(** Exact conversion between modal-degree-zero formulas and propositional
    formulas.  The source exposes this as a proof-indexed conversion; the Coq
    version retains that dependency and proves both round trips. *)

From Stdlib Require Import Lia.
From FoundationModal Require Import Syntax PropositionalFormula.

Set Implicit Arguments.
Unset Strict Implicit.

Fixpoint pformula_to_modal {A} (p : pformula A) : formula A :=
  match p with
  | PAtom a => Atom a
  | PFalsum => Bottom
  | PAnd q r => And (pformula_to_modal q) (pformula_to_modal r)
  | POr q r => Or (pformula_to_modal q) (pformula_to_modal r)
  | PImp q r => Imp (pformula_to_modal q) (pformula_to_modal r)
  end.

Lemma pformula_to_modal_degree_zero : forall A (p : pformula A),
  modal_degree (pformula_to_modal p) = 0.
Proof.
  intros A p; induction p; simpl in *; try rewrite IHp1, IHp2;
    reflexivity.
Qed.

Lemma pformula_to_modal_letterless : forall A (p : pformula A),
  formula_letterless (pformula_to_modal p) <-> pformula_letterless p.
Proof.
  intros A p; induction p; simpl in *; tauto.
Qed.

Lemma modal_degree_imp_left_zero : forall A (p q : formula A),
  modal_degree (Imp p q) = 0 -> modal_degree p = 0.
Proof. intros; simpl in H. lia. Qed.

Lemma modal_degree_imp_right_zero : forall A (p q : formula A),
  modal_degree (Imp p q) = 0 -> modal_degree q = 0.
Proof. intros; simpl in H. lia. Qed.

Lemma modal_degree_successor_not_zero : forall n, S n <> 0.
Proof. discriminate. Qed.

Fixpoint modal_to_pformula {A} (p : formula A) :
    modal_degree p = 0 -> pformula A :=
  match p as p0 return modal_degree p0 = 0 -> pformula A with
  | Atom a => fun _ => PAtom a
  | Bottom => fun _ => PFalsum
  | Imp q r => fun H =>
      PImp
        (@modal_to_pformula A q (modal_degree_imp_left_zero H))
        (@modal_to_pformula A r (modal_degree_imp_right_zero H))
  | Box q => fun H => False_rect _
      ((@modal_degree_successor_not_zero (modal_degree q)) H)
  end.

Arguments modal_to_pformula {A} p _.

Lemma modal_to_pformula_to_modal : forall A (p : formula A)
    (H : modal_degree p = 0),
  pformula_to_modal (modal_to_pformula p H) = p.
Proof.
  intros A p; induction p as [a | | q IHq r IHr | q IHq]; intro H;
    simpl in *.
  - reflexivity.
  - reflexivity.
  - rewrite (IHq (modal_degree_imp_left_zero H)),
      (IHr (modal_degree_imp_right_zero H)). reflexivity.
  - discriminate.
Qed.

Theorem modal_degree_zero_iff_propositional : forall A (p : formula A),
  modal_degree p = 0 <-> exists q : pformula A, pformula_to_modal q = p.
Proof.
  intros A p. split.
  - intro H. exists (modal_to_pformula p H).
    apply modal_to_pformula_to_modal.
  - intros [q <-]. apply pformula_to_modal_degree_zero.
Qed.
