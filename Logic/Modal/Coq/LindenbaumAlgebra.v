(**
  The Lindenbaum algebra of a classical predicate-valued logic.

  This module is a reusable Coq counterpart of the pinned Foundation module
  [Logic/LindenbaumAlgebra.lean].  Foundation forms a quotient of formulas by
  provable biconditional.  The Boolean-algebra interface in this repository
  already carries an explicit setoid equality, so the carrier remains the
  formula type itself and [lindenbaum_equiv] is its equality relation.  This
  avoids quotient representatives and the source's implementation-only
  [DecidableEq] assumption without changing the mathematics.

  The exported readback lemmas correspond to Foundation's
  [of_eq_of], [le_def], [top_def], [bot_def], [inf_def], [sup_def],
  [himp_def], and [compl_def].  The final metatheorems port
  [provable_iff_eq_top], [inconsistent_iff_trivial],
  [consistent_iff_nontrivial], and [nontrivial_of_consistent], translating
  quotient equality and [Nontrivial] to the explicit relation [ba_equiv].
*)

From FoundationModal Require Import
  Syntax LogicInfrastructure EntailmentExtensions ModalAlgebra.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

(** * Provable equivalence and order *)

(** Foundation's [Entailment.ProvablyEquivalent]. *)
Definition lindenbaum_equiv {AtomType : Type}
    (L : modal_logic_set AtomType)
    (p q : formula AtomType) : Prop :=
  L (Iff p q).

(** The implication order underlying Foundation's [LE] instance. *)
Definition lindenbaum_le {AtomType : Type}
    (L : modal_logic_set AtomType)
    (p q : formula AtomType) : Prop :=
  L (Imp p q).

(** Source [ProvablyEquivalent.refl]. *)
Lemma lindenbaum_equiv_refl :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    classical_logic L -> forall p, lindenbaum_equiv L p p.
Proof.
  intros AtomType L Hclass p.
  unfold lindenbaum_equiv.
  apply logic_iff_intro; [exact Hclass | |];
    now apply logic_identity.
Qed.

(** Source [ProvablyEquivalent.symm]. *)
Lemma lindenbaum_equiv_sym :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    classical_logic L -> forall p q,
    lindenbaum_equiv L p q -> lindenbaum_equiv L q p.
Proof.
  intros AtomType L Hclass p q Hpq.
  unfold lindenbaum_equiv in *.
  now apply (logic_iff_sym Hclass).
Qed.

(** Source [ProvablyEquivalent.trans]. *)
Lemma lindenbaum_equiv_trans :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    classical_logic L -> forall p q r,
    lindenbaum_equiv L p q ->
    lindenbaum_equiv L q r ->
    lindenbaum_equiv L p r.
Proof.
  intros AtomType L Hclass p q r Hpq Hqr.
  unfold lindenbaum_equiv in *.
  eapply logic_iff_trans; eauto.
Qed.

Local Ltac solve_lindenbaum_classical Hclass :=
  apply (logic_classical_tautology Hclass);
  intro rho; unfold Iff, And, Or, Neg, Top; simpl; tauto.

Lemma lindenbaum_imp_respects_equiv :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    classical_logic L -> forall p p' q q',
    lindenbaum_equiv L p p' ->
    lindenbaum_equiv L q q' ->
    lindenbaum_equiv L (Imp p q) (Imp p' q').
Proof.
  intros AtomType L Hclass p p' q q' Hpp Hqq.
  unfold lindenbaum_equiv in *.
  eapply (logic_modus_ponens Hclass); [|exact Hqq].
  eapply (logic_modus_ponens Hclass); [|exact Hpp].
  solve_lindenbaum_classical Hclass.
Qed.

Lemma lindenbaum_and_respects_equiv :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    classical_logic L -> forall p p' q q',
    lindenbaum_equiv L p p' ->
    lindenbaum_equiv L q q' ->
    lindenbaum_equiv L (And p q) (And p' q').
Proof.
  intros AtomType L Hclass p p' q q' Hpp Hqq.
  unfold lindenbaum_equiv in *.
  eapply (logic_modus_ponens Hclass); [|exact Hqq].
  eapply (logic_modus_ponens Hclass); [|exact Hpp].
  solve_lindenbaum_classical Hclass.
Qed.

Lemma lindenbaum_or_respects_equiv :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    classical_logic L -> forall p p' q q',
    lindenbaum_equiv L p p' ->
    lindenbaum_equiv L q q' ->
    lindenbaum_equiv L (Or p q) (Or p' q').
Proof.
  intros AtomType L Hclass p p' q q' Hpp Hqq.
  unfold lindenbaum_equiv in *.
  eapply (logic_modus_ponens Hclass); [|exact Hqq].
  eapply (logic_modus_ponens Hclass); [|exact Hpp].
  solve_lindenbaum_classical Hclass.
Qed.

(** * The Boolean algebra *)

(** This is specifically Foundation's classical [BooleanAlgebra] instance.
    The repository's [boolean_algebra] record subsumes the order and operation
    laws used by that instance.  Foundation's weaker generalized-Heyting and
    intuitionistic boundaries remain outside this classical API: modal
    conjunction and disjunction in [formula] are themselves classically
    encoded. *)
Definition lindenbaum_boolean_algebra
    (AtomType : Type) (L : modal_logic_set AtomType)
    (Hclass : classical_logic L) :
    boolean_algebra (formula AtomType).
Proof.
  refine
    {| ba_equiv := lindenbaum_equiv L;
       ba_le := lindenbaum_le L;
       ba_top := Top;
       ba_bottom := Bottom;
       ba_meet := And;
       ba_join := Or;
       ba_compl := Neg;
       ba_imp := Imp |}.
  - split.
    + intro p.
      exact (@lindenbaum_equiv_refl AtomType L Hclass p).
    + intros p q Hpq.
      exact (@lindenbaum_equiv_sym AtomType L Hclass p q Hpq).
    + intros p q r Hpq Hqr.
      exact (@lindenbaum_equiv_trans AtomType L Hclass p q r Hpq Hqr).
  - split.
    + intro p. unfold lindenbaum_le. now apply logic_identity.
    + intros p q r Hpq Hqr. unfold lindenbaum_le in *.
      eapply logic_imp_trans; eauto.
  - intros p q Hpq Hqp. unfold lindenbaum_equiv, lindenbaum_le in *.
    now apply (logic_iff_intro Hclass).
  - intros p p' Hpp q q' Hqq; split; intro Hpq;
      unfold lindenbaum_equiv, lindenbaum_le in *.
    + eapply logic_imp_trans; [exact Hclass | |].
      * exact (@logic_iff_elim_right AtomType L Hclass p p' Hpp).
      * eapply logic_imp_trans; [exact Hclass | exact Hpq |].
        exact (@logic_iff_elim_left AtomType L Hclass q q' Hqq).
    + eapply logic_imp_trans; [exact Hclass | |].
      * exact (@logic_iff_elim_left AtomType L Hclass p p' Hpp).
      * eapply logic_imp_trans; [exact Hclass | exact Hpq |].
        exact (@logic_iff_elim_right AtomType L Hclass q q' Hqq).
  - intros p p' Hpp q q' Hqq.
    now apply (lindenbaum_and_respects_equiv Hclass).
  - intros p p' Hpp q q' Hqq.
    now apply (lindenbaum_or_respects_equiv Hclass).
  - intros p q Hpq. unfold lindenbaum_equiv in *.
    now apply (logic_neg_iff Hclass).
  - intros p p' Hpp q q' Hqq.
    now apply (lindenbaum_imp_respects_equiv Hclass).
  - intro p. unfold lindenbaum_le. solve_lindenbaum_classical Hclass.
  - intro p. unfold lindenbaum_le. solve_lindenbaum_classical Hclass.
  - intros p q. unfold lindenbaum_le. solve_lindenbaum_classical Hclass.
  - intros p q. unfold lindenbaum_le. solve_lindenbaum_classical Hclass.
  - intros p q r Hpq Hpr. unfold lindenbaum_le in *.
    now apply (logic_imp_and_intro Hclass).
  - intros p q. unfold lindenbaum_le. solve_lindenbaum_classical Hclass.
  - intros p q. unfold lindenbaum_le. solve_lindenbaum_classical Hclass.
  - intros p q r Hpr Hqr. unfold lindenbaum_le in *.
    eapply (logic_modus_ponens Hclass); [|exact Hqr].
    eapply (logic_modus_ponens Hclass); [|exact Hpr].
    solve_lindenbaum_classical Hclass.
  - intros p q. unfold lindenbaum_equiv.
    solve_lindenbaum_classical Hclass.
  - intros p q. unfold lindenbaum_equiv.
    solve_lindenbaum_classical Hclass.
  - intros p q r. unfold lindenbaum_equiv.
    solve_lindenbaum_classical Hclass.
  - intro p. unfold lindenbaum_equiv.
    solve_lindenbaum_classical Hclass.
  - intros p q Hpq. unfold lindenbaum_le in *.
    now apply (logic_contraposition Hclass).
  - unfold lindenbaum_equiv. solve_lindenbaum_classical Hclass.
  - unfold lindenbaum_equiv. solve_lindenbaum_classical Hclass.
  - intro p. unfold lindenbaum_equiv.
    solve_lindenbaum_classical Hclass.
  - intro p. unfold lindenbaum_equiv.
    solve_lindenbaum_classical Hclass.
  - intros p q. unfold lindenbaum_equiv.
    solve_lindenbaum_classical Hclass.
  - intros p q. unfold lindenbaum_equiv.
    solve_lindenbaum_classical Hclass.
  - intros p q. unfold lindenbaum_equiv.
    solve_lindenbaum_classical Hclass.
  - intros x p q; split; intro H; unfold lindenbaum_le in *.
    + now apply (logic_curry Hclass).
    + eapply (logic_modus_ponens Hclass); [|exact H].
      solve_lindenbaum_classical Hclass.
Defined.

(** * Readback and beta laws *)

(** Setoid counterpart of source [of_eq_of]. *)
Lemma lindenbaum_equiv_readback :
  forall (AtomType : Type) (L : modal_logic_set AtomType)
         (Hclass : classical_logic L) p q,
    ba_equiv (lindenbaum_boolean_algebra Hclass) p q <->
    L (Iff p q).
Proof. reflexivity. Qed.

(** Source [le_def]. *)
Lemma lindenbaum_order_readback :
  forall (AtomType : Type) (L : modal_logic_set AtomType)
         (Hclass : classical_logic L) p q,
    ba_le (lindenbaum_boolean_algebra Hclass) p q <->
    L (Imp p q).
Proof. reflexivity. Qed.

(** Source [top_def]. *)
Lemma lindenbaum_top_beta :
  forall (AtomType : Type) (L : modal_logic_set AtomType)
         (Hclass : classical_logic L),
    ba_top (lindenbaum_boolean_algebra Hclass) = Top.
Proof. reflexivity. Qed.

(** Source [bot_def]. *)
Lemma lindenbaum_bottom_beta :
  forall (AtomType : Type) (L : modal_logic_set AtomType)
         (Hclass : classical_logic L),
    ba_bottom (lindenbaum_boolean_algebra Hclass) = Bottom.
Proof. reflexivity. Qed.

(** Source [inf_def]. *)
Lemma lindenbaum_meet_beta :
  forall (AtomType : Type) (L : modal_logic_set AtomType)
         (Hclass : classical_logic L) p q,
    ba_meet (lindenbaum_boolean_algebra Hclass) p q = And p q.
Proof. reflexivity. Qed.

(** Source [sup_def]. *)
Lemma lindenbaum_join_beta :
  forall (AtomType : Type) (L : modal_logic_set AtomType)
         (Hclass : classical_logic L) p q,
    ba_join (lindenbaum_boolean_algebra Hclass) p q = Or p q.
Proof. reflexivity. Qed.

(** Source [himp_def]. *)
Lemma lindenbaum_imp_beta :
  forall (AtomType : Type) (L : modal_logic_set AtomType)
         (Hclass : classical_logic L) p q,
    ba_imp (lindenbaum_boolean_algebra Hclass) p q = Imp p q.
Proof. reflexivity. Qed.

(** Source [compl_def]. *)
Lemma lindenbaum_compl_beta :
  forall (AtomType : Type) (L : modal_logic_set AtomType)
         (Hclass : classical_logic L) p,
    ba_compl (lindenbaum_boolean_algebra Hclass) p = Neg p.
Proof. reflexivity. Qed.

(** * Provability, consistency, and nontriviality *)

(** Source [provable_iff_provablyEquivalent_verum] and
    [provable_iff_eq_top], combined for the setoid presentation. *)
Lemma lindenbaum_provable_iff_top :
  forall (AtomType : Type) (L : modal_logic_set AtomType)
         (Hclass : classical_logic L) p,
    L p <->
    ba_equiv (lindenbaum_boolean_algebra Hclass) p
      (ba_top (lindenbaum_boolean_algebra Hclass)).
Proof.
  intros AtomType L Hclass p.
  change (L p <-> L (Iff p Top)).
  split.
  - now apply logic_iff_top_left_from.
  - intro Hiff.
    eapply (logic_modus_ponens Hclass).
    + exact (@logic_iff_elim_right AtomType L Hclass p Top Hiff).
    + now apply logic_mem_top.
Qed.

Definition lindenbaum_trivial
    (AtomType : Type) (L : modal_logic_set AtomType)
    (Hclass : classical_logic L) : Prop :=
  forall p : formula AtomType,
    ba_equiv (lindenbaum_boolean_algebra Hclass) p
      (ba_top (lindenbaum_boolean_algebra Hclass)).

Definition lindenbaum_nontrivial
    (AtomType : Type) (L : modal_logic_set AtomType)
    (Hclass : classical_logic L) : Prop :=
  exists p q : formula AtomType,
    ~ ba_equiv (lindenbaum_boolean_algebra Hclass) p q.

(** Source [inconsistent_iff_trivial]. *)
Lemma lindenbaum_inconsistent_iff_trivial :
  forall (AtomType : Type) (L : modal_logic_set AtomType)
         (Hclass : classical_logic L),
    logic_inconsistent L <->
    lindenbaum_trivial Hclass.
Proof.
  intros AtomType L Hclass; split.
  - intros Hinconsistent p.
    apply (proj1 (lindenbaum_provable_iff_top Hclass p)).
    exact (Hinconsistent p).
  - intros Htrivial p.
    apply (proj2 (lindenbaum_provable_iff_top Hclass p)).
    exact (Htrivial p).
Qed.

(** Source [consistent_iff_nontrivial]. *)
Lemma lindenbaum_consistent_iff_nontrivial :
  forall (AtomType : Type) (L : modal_logic_set AtomType)
         (Hclass : classical_logic L),
    logic_consistent L <->
    lindenbaum_nontrivial Hclass.
Proof.
  intros AtomType L Hclass; split.
  - intro Hconsistent.
    destruct (logic_exists_unprovable Hconsistent) as [p Hp].
    exists p, Top. intro Hequiv.
    apply Hp.
    apply (proj2 (lindenbaum_provable_iff_top Hclass p)).
    exact Hequiv.
  - intros [p [q Hneq]] Hinconsistent.
    apply Hneq. exact (Hinconsistent (Iff p q)).
Qed.

(** Source [nontrivial_of_consistent]. *)
Lemma lindenbaum_nontrivial_of_consistent :
  forall (AtomType : Type) (L : modal_logic_set AtomType)
         (Hclass : classical_logic L),
    logic_consistent L -> lindenbaum_nontrivial Hclass.
Proof.
  intros AtomType L Hclass Hconsistent.
  now apply (proj1 (lindenbaum_consistent_iff_nontrivial Hclass)).
Qed.
