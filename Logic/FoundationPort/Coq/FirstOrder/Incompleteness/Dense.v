(** Incompleteness makes the Lindenbaum order dense.

    The source phrases extension through an adjunctive context type and then
    quotients formulas by provable equivalence.  The Coq Lindenbaum algebra
    already uses formula representatives with an explicit setoid, so only
    the theorem predicate of a one-formula extension and its deduction law
    are operationally relevant. *)

From FoundationModal Require Import
  Syntax LogicInfrastructure LindenbaumAlgebra.
From Foundation.FirstOrder.Incompleteness Require Import
  ProvabilityAbstraction.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

Record pa_adjoin {A : Type} (L : modal_logic_set A) : Type := {
  pa_adjoin_logic : formula A -> modal_logic_set A;
  pa_adjoin_deduction : forall added conclusion,
    pa_adjoin_logic added conclusion <->
    L (Imp added conclusion)
}.

Arguments pa_adjoin_logic {A L} _ _ _.
Arguments pa_adjoin_deduction {A L} _ _ _.

(** Foundation's [consistent_cons_of_unprovable_neg].  No classical-logic
    law is needed for this direction. *)
Lemma pa_consistent_adjoin_of_unprovable_neg : forall (A : Type)
    (L : modal_logic_set A) (J : pa_adjoin L) p,
  ~ L (Neg p) -> logic_consistent (pa_adjoin_logic J p).
Proof.
  intros A L J p Hnot Hinc. apply Hnot.
  change (L (Imp p Bottom)).
  apply (proj1 (pa_adjoin_deduction J p Bottom)).
  exact (Hinc Bottom).
Qed.

(** Foundation's [consistent_cons_of_unprovable].  Only double-negation
    elimination in the base theorem predicate is additionally required. *)
Lemma pa_consistent_adjoin_neg_of_unprovable : forall (A : Type)
    (L : modal_logic_set A) (Hclass : classical_logic L)
    (J : pa_adjoin L) p,
  ~ L p -> logic_consistent (pa_adjoin_logic J (Neg p)).
Proof.
  intros A L Hclass J p Hnot.
  apply pa_consistent_adjoin_of_unprovable_neg.
  intro Hnn. apply Hnot.
  eapply pa_tautology1; [exact Hclass | | exact Hnn].
  intro rho. unfold Neg. simpl. tauto.
Qed.

(** Strict order in the explicit-setoid Lindenbaum presentation. *)
Definition pa_lindenbaum_lt {A : Type} (L : modal_logic_set A)
    (p q : formula A) : Prop :=
  lindenbaum_le L p q /\ ~ lindenbaum_le L q p.

(** Foundation's [dense_of_finite_extend_incomplete].  The source name says
    "finite" because a single adjoined formula is finitely axiomatized; the
    proof consumes only deduction for that single extension. *)
Theorem pa_dense_of_adjoin_incomplete : forall (A : Type)
    (L : modal_logic_set A) (Hclass : classical_logic L)
    (J : pa_adjoin L),
  (forall added,
    logic_consistent (pa_adjoin_logic J added) ->
    pa_incomplete (pa_adjoin_logic J added)) ->
  forall p q, pa_lindenbaum_lt L p q ->
  exists middle,
    pa_lindenbaum_lt L p middle /\
    pa_lindenbaum_lt L middle q.
Proof.
  intros A L Hclass J Hall p q [Hpq Hnotqp].
  unfold lindenbaum_le in Hpq, Hnotqp.
  set (added := And (Neg p) q).
  assert (Hconsistent : logic_consistent (pa_adjoin_logic J added)).
  { apply pa_consistent_adjoin_of_unprovable_neg.
    intro Hneg_added. apply Hnotqp.
    eapply pa_tautology1; [exact Hclass | | exact Hneg_added].
    intro rho. unfold added, And, Neg. simpl. tauto. }
  destruct (Hall added Hconsistent) as [rho [Hrho Hneg_rho]].
  set (middle := Or p (And q (Neg rho))).
  exists middle. unfold pa_lindenbaum_lt, lindenbaum_le. split; split.
  - apply (logic_classical_tautology Hclass).
    intro valuation. unfold middle, Or, And, Neg. simpl. tauto.
  - intro Hmiddle_p. apply Hrho.
    apply (proj2 (pa_adjoin_deduction J added rho)).
    eapply pa_tautology1; [exact Hclass | | exact Hmiddle_p].
    intro valuation.
    unfold added, middle, Or, And, Neg. simpl. tauto.
  - eapply pa_tautology1; [exact Hclass | | exact Hpq].
    intro valuation. unfold middle, Or, And, Neg. simpl. tauto.
  - intro Hq_middle. apply Hneg_rho.
    apply (proj2 (pa_adjoin_deduction J added (Neg rho))).
    eapply pa_tautology1; [exact Hclass | | exact Hq_middle].
    intro valuation.
    unfold added, middle, Or, And, Neg. simpl. tauto.
Qed.
