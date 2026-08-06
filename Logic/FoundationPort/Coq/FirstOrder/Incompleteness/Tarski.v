(** Tarski undefinability from abstract diagonalization.

    Foundation states these results for substitution into quoted arithmetic
    semisentences.  The proof uses none of that representation: a fixed point
    for every formula endomorphism is sufficient. *)

From FoundationModal Require Import Syntax LogicInfrastructure.
From Foundation.FirstOrder.Incompleteness Require Import
  ProvabilityAbstraction.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

(** No formula endomorphism can internally classify all theorems by a
    biconditional.  This strictly generalizes the source's unary predicate,
    whose endomorphism is induced by substitution of a sentence code. *)
Theorem pa_not_exists_tarski_predicate : forall (A : Type)
    (L0 L : modal_logic_set A) (Hclass : classical_logic L)
    (Hweak : logic_subset L0 L) (D : pa_diagonalization L0),
  logic_consistent L ->
  ~ exists tau : formula A -> formula A,
      forall sigma, L (Iff sigma (tau sigma)).
Proof.
  intros A L0 L Hclass Hweak D Hconsistent [tau Htau].
  set (liar := pa_fixedpoint D (fun p => Neg (tau p))).
  assert (Hliar0 : L0 (Iff liar (Neg (tau liar)))).
  { unfold liar. exact (pa_diagonal D (fun p => Neg (tau p))). }
  pose proof (Hweak _ Hliar0) as Hliar.
  pose proof (Htau liar) as Htruth.
  apply (logic_no_bot Hclass Hconsistent).
  eapply pa_tautology2;
    [exact Hclass | | exact Htruth | exact Hliar].
  intro rho. unfold Iff, And, Neg. simpl. tauto.
Qed.

(** Tarski's semantic theorem needs only the completeness direction from
    truth to theoremhood and the introduction direction for truth of a
    biconditional.  Neither the converse completeness direction nor a full
    semantic model interface is used. *)
Theorem pa_undefinability_of_truth : forall (A : Type)
    (L0 L : modal_logic_set A) (Hclass : classical_logic L)
    (Hweak : logic_subset L0 L) (D : pa_diagonalization L0)
    (truth : formula A -> Prop),
  logic_consistent L ->
  (forall p, truth p -> L p) ->
  (forall p q, (truth p <-> truth q) -> truth (Iff p q)) ->
  ~ exists tau : formula A -> formula A,
      forall sigma, truth sigma <-> truth (tau sigma).
Proof.
  intros A L0 L Hclass Hweak D truth Hconsistent
    Hcomplete Hiff [tau Htau].
  apply (pa_not_exists_tarski_predicate
    Hclass Hweak D Hconsistent).
  exists tau. intro sigma.
  apply Hcomplete, Hiff, Htau.
Qed.
