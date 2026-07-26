(**
  The quasinormal modal logic D: its proof-theoretic core and finite
  reduction context.

  This module ports the syntactic half of Foundation's pinned
  [Modal/Logic/D/Basic.lean].  Foundation defines D as the least
  quasinormal sum of GL and two distinguished formulas:

    - [~ box bottom], and
    - [box (box p \/ box q) -> box p \/ box q] at atoms 0 and 1.

  Substitution generates every instance of the second formula.  As in the
  source, a substitution-free presentation then gives a compact recursor
  with just GL, P, Dz, and modus-ponens cases.

  Finite sets are represented by lists.  The list of all subsets needed by
  [dzSubformula] is [finite_powerset]; repetitions in the source subformula
  list are harmless because every theorem below is extensional in list
  membership.  The semantic tail model and the final reduction to GL are
  deliberately left to a subsequent module tranche.
*)

From Stdlib Require Import Lists.List.
From Stdlib Require Import Logic.Classical_Prop.
From FoundationModal Require Import
  Syntax Axioms NormalHilbert LogicInfrastructure GLGrzDerivations
  GLIndependence FiniteMaximalContext FiniteCanonicalSupport.

Import ListNotations.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

(** * Definition and primitive generators *)

(** Foundation's binary axiom [Dz]. *)
Definition Dz {AtomType : Type} (p q : formula AtomType)
    : formula AtomType :=
  Imp (Box (Or (Box p) (Box q))) (Or (Box p) (Box q)).

(** The exact two-element right summand used by Foundation's definition.
    Closure under substitution belongs to the generated quasinormal sum,
    rather than to this atomic predicate. *)
Definition D_atomic_axiom : modal_logic_set nat :=
  fun p =>
    p = P \/
    p = Dz (Atom 0) (Atom 1).

(** Foundation [Modal.D].  This is unrelated to the normal serial logic
    [KD_proves]; the short name D here follows the pinned quasinormal source. *)
Definition D_proves : modal_logic_set nat :=
  logic_sum_quasi_normal (@GL_proves nat) D_atomic_axiom.

(** Foundation's [Modal.D.IsQuasiNormal] instance. *)
Theorem D_quasi_normal : quasi_normal_logic D_proves.
Proof.
  unfold D_proves.
  apply logic_sum_quasi_normal_quasi_left.
  exact (normal_quasi GL_normal_logic).
Qed.

Definition D_classical_logic : classical_logic D_proves :=
  quasi_classical D_quasi_normal.

(** The canonical inclusion [GL <= D]. *)
Theorem GL_weaker_than_D : logic_subset (@GL_proves nat) D_proves.
Proof.
  intros p Hp. now apply LSQ_mem_left.
Qed.

(** Foundation's P instance. *)
Theorem D_proves_P : D_proves (@P nat).
Proof.
  apply LSQ_mem_right. unfold D_atomic_axiom. now left.
Qed.

(** The distinguished atomic Dz generator. *)
Theorem D_proves_atomic_Dz :
  D_proves (Dz (Atom 0) (Atom 1)).
Proof.
  apply LSQ_mem_right. unfold D_atomic_axiom. now right.
Qed.

(** Foundation [D.mem_axiomDz].  Every Dz instance is obtained by one
    substitution from the distinguished atoms. *)
Theorem D_proves_Dz :
  forall p q : formula nat, D_proves (Dz p q).
Proof.
  intros p q.
  pose proof
    (LSQ_substitute
      (fun n : nat => match n with 0 => p | _ => q end)
      D_proves_atomic_Dz) as Hsub.
  change (D_proves (Dz p q)) in Hsub.
  exact Hsub.
Qed.

(** A named form of D's structural substitution rule. *)
Theorem D_proves_substitute :
  forall (sigma : nat -> formula nat) p,
    D_proves p -> D_proves (substitute sigma p).
Proof.
  intros sigma p Hp. now apply LSQ_substitute.
Qed.

(** The first strict inclusion in Foundation's hierarchy. *)
Theorem GL_strictly_weaker_D :
  logic_strictly_weaker (@GL_proves nat) D_proves.
Proof.
  split.
  - exact GL_weaker_than_D.
  - exists (@P nat); split.
    + exact D_proves_P.
    + exact (GL_unprovable_notbox (p := @Bottom nat)).
Qed.

(** * A substitution-free presentation and recursor *)

Module DDerivationInternal.

Inductive derives : formula nat -> Prop :=
| derives_GL : forall p, GL_proves p -> derives p
| derives_P : derives P
| derives_Dz : forall p q, derives (Dz p q)
| derives_mp : forall p q,
    derives (Imp p q) -> derives p -> derives q.

Lemma derives_substitute :
  forall p, derives p ->
  forall sigma : nat -> formula nat, derives (substitute sigma p).
Proof.
  intros p Hp; induction Hp; intro sigma.
  - apply derives_GL.
    eapply (@normal_proves_substitute schema_L
      schema_L_substitution_closed nat nat sigma p).
    exact H.
  - change (derives P). apply derives_P.
  - change (derives (Dz (substitute sigma p) (substitute sigma q))).
    apply derives_Dz.
  - simpl. eapply derives_mp; eauto.
Qed.

Lemma derives_to_D : forall p, derives p -> D_proves p.
Proof.
  intros p Hp; induction Hp.
  - now apply GL_weaker_than_D.
  - exact D_proves_P.
  - now apply D_proves_Dz.
  - eapply LSQ_mp; eassumption.
Qed.

Lemma D_to_derives : forall p, D_proves p -> derives p.
Proof.
  intros p Hp; induction Hp.
  - now apply derives_GL.
  - unfold D_atomic_axiom in H. destruct H as [-> | ->].
    + apply derives_P.
    + apply derives_Dz.
  - eapply derives_mp; eassumption.
  - now apply derives_substitute.
Qed.

End DDerivationInternal.

(** The source-equivalent derivation characterization. *)
Theorem D_derivation_iff :
  forall p, D_proves p <-> DDerivationInternal.derives p.
Proof.
  intro p; split.
  - apply DDerivationInternal.D_to_derives.
  - apply DDerivationInternal.derives_to_D.
Qed.

(** Foundation [Modal.D.rec'].  Substitution has been normalized into the
    GL and arbitrary-Dz cases. *)
Theorem D_proves_induction :
  forall (Q : formula nat -> Prop),
    (forall p, GL_proves p -> Q p) ->
    Q P ->
    (forall p q, Q (Dz p q)) ->
    (forall p q, Q (Imp p q) -> Q p -> Q q) ->
    forall p, D_proves p -> Q p.
Proof.
  intros Q HGL HP HDz Hmp p Hp.
  apply DDerivationInternal.D_to_derives in Hp.
  induction Hp.
  - now apply HGL.
  - exact HP.
  - now apply HDz.
  - eapply Hmp; eassumption.
Qed.

Definition D_rec := D_proves_induction.

(** * Finite disjunction support *)

(** The standard right-associated finite disjunction, with falsity at the
    empty list.  It is the list presentation of Foundation's [List.disj]. *)
Fixpoint D_list_disj (Gamma : list (formula nat)) : formula nat :=
  match Gamma with
  | [] => Bottom
  | p :: rest => Or p (D_list_disj rest)
  end.

Definition D_boxed_list_disj (Gamma : list (formula nat)) : formula nat :=
  D_list_disj (map Box Gamma).

(** The finite/list instance of Dz used throughout the reduction. *)
Definition D_list_Dz (Gamma : list (formula nat)) : formula nat :=
  Imp (Box (D_boxed_list_disj Gamma)) (D_boxed_list_disj Gamma).

(** Two elementary classical rules kept local to this development. *)
Lemma D_logic_or_mono :
  forall (L : modal_logic_set nat), classical_logic L ->
  forall p p' q q',
    L (Imp p p') -> L (Imp q q') ->
    L (Imp (Or p q) (Or p' q')).
Proof.
  intros L Hclass p p' q q' Hpp Hqq.
  eapply (logic_modus_ponens Hclass); [|exact Hqq].
  eapply (logic_modus_ponens Hclass); [|exact Hpp].
  apply (logic_classical_tautology Hclass).
  intro rho. unfold Or, Neg; simpl; tauto.
Qed.

Lemma D_logic_or_cases :
  forall (L : modal_logic_set nat), classical_logic L ->
  forall p q r,
    L (Imp p r) -> L (Imp q r) -> L (Imp (Or p q) r).
Proof.
  intros L Hclass p q r Hpr Hqr.
  eapply (logic_modus_ponens Hclass); [|exact Hqr].
  eapply (logic_modus_ponens Hclass); [|exact Hpr].
  apply (logic_classical_tautology Hclass).
  intro rho. unfold Or, Neg; simpl; tauto.
Qed.

(** Normal box collects a disjunction of boxes into the box of a
    disjunction. *)
Lemma D_logic_box_or_collect :
  forall (L : modal_logic_set nat), normal_logic L ->
  forall p q,
    L (Imp (Or (Box p) (Box q)) (Box (Or p q))).
Proof.
  intros L Hnormal p q.
  pose proof (quasi_classical (normal_quasi Hnormal)) as Hclass.
  apply D_logic_or_cases; [exact Hclass | |].
  - apply logic_box_regularity; [exact Hnormal |].
    apply (logic_classical_tautology Hclass).
    intro rho. unfold Or, Neg; simpl; tauto.
  - apply logic_box_regularity; [exact Hnormal |].
    apply (logic_classical_tautology Hclass).
    intro rho. unfold Or, Neg; simpl; tauto.
Qed.

(** Foundation [GL.box_disj_Tc].  Transitivity turns every boxed disjunct
    into its doubly boxed form, after which normality collects the finite
    disjunction. *)
Theorem GL_proves_boxed_list_disj_Four :
  forall Gamma,
    GL_proves
      (Imp (D_boxed_list_disj Gamma)
           (Box (D_boxed_list_disj Gamma))).
Proof.
  intro Gamma; induction Gamma as [|p Gamma IH].
  - cbn [D_boxed_list_disj D_list_disj].
    apply (logic_classical_tautology GL_classical_logic).
    intro rho; simpl; tauto.
  - cbn [D_boxed_list_disj D_list_disj] in IH |- *.
    set (A := D_list_disj (map Box Gamma)) in IH |- *.
    assert (Hmono :
      GL_proves
        (Imp (Or (Box p) A) (Or (Box (Box p)) (Box A)))).
    { apply D_logic_or_mono; [exact GL_classical_logic | |].
      - apply GL_proves_Four.
      - exact IH. }
    exact
      (logic_imp_trans GL_classical_logic Hmono
        (D_logic_box_or_collect GL_normal_logic (Box p) A)).
Qed.

(** Foundation [D.ldisj_axiomDz], with lists serving for both the source's
    list and finite-set variants.  The proof uses GL only for the step that
    must be necessitated; the induction hypothesis is used propositionally
    inside quasinormal D. *)
Theorem D_proves_list_Dz :
  forall Gamma, D_proves (D_list_Dz Gamma).
Proof.
  intro Gamma; induction Gamma as [|p Gamma IH].
  - cbn [D_list_Dz D_boxed_list_disj D_list_disj].
    exact D_proves_P.
  - cbn [D_list_Dz D_boxed_list_disj D_list_disj] in IH |- *.
    set (A := D_list_disj (map Box Gamma)) in *.
    assert (Hlift : GL_proves (Imp A (Box A))).
    { subst A. exact (GL_proves_boxed_list_disj_Four Gamma). }
    assert (Hinside :
      GL_proves (Imp (Or (Box p) A) (Or (Box p) (Box A)))).
    { apply D_logic_or_mono; [exact GL_classical_logic | |].
      - apply logic_identity. exact GL_classical_logic.
      - exact Hlift. }
    assert (Hpre :
      GL_proves
        (Imp (Box (Or (Box p) A))
             (Box (Or (Box p) (Box A))))).
    { exact (logic_box_regularity GL_normal_logic Hinside). }
    assert (Hpost :
      D_proves (Imp (Or (Box p) (Box A)) (Or (Box p) A))).
    { apply D_logic_or_mono; [exact D_classical_logic | |].
      - apply logic_identity. exact D_classical_logic.
      - exact IH. }
    assert (Hmiddle :
      D_proves
        (Imp (Box (Or (Box p) (Box A)))
             (Or (Box p) A))).
    { exact
        (logic_imp_trans D_classical_logic
          (D_proves_Dz p A) Hpost). }
    exact
      (logic_imp_trans D_classical_logic
        (GL_weaker_than_D Hpre) Hmiddle).
Qed.

(** The singleton instance is [box box p -> box p].  Foundation names this
    theorem [D.axiomFour]; [C4] is the local syntax name for the exact
    formula, avoiding confusion with transitivity's converse direction. *)
Theorem D_proves_C4 :
  forall p : formula nat, D_proves (C4 p).
Proof.
  intro p.
  pose proof (D_proves_list_Dz [p]) as Hsingleton.
  cbn [D_list_Dz D_boxed_list_disj D_list_disj] in Hsingleton.
  assert (Hleft : GL_proves (Imp (Box p) (Or (Box p) Bottom))).
  { apply (logic_classical_tautology GL_classical_logic).
    intro rho. unfold Or, Neg; simpl; tauto. }
  assert (Hpre :
    GL_proves
      (Imp (Box (Box p)) (Box (Or (Box p) Bottom)))).
  { exact (logic_box_regularity GL_normal_logic Hleft). }
  assert (Hpost : GL_proves (Imp (Or (Box p) Bottom) (Box p))).
  { apply (logic_classical_tautology GL_classical_logic).
    intro rho. unfold Or, Neg; simpl; tauto. }
  unfold C4.
  eapply logic_imp_trans; [exact D_classical_logic | |].
  - exact (GL_weaker_than_D Hpre).
  - eapply logic_imp_trans; [exact D_classical_logic | |].
    + exact Hsingleton.
    + exact (GL_weaker_than_D Hpost).
Qed.

(** Source-facing aliases for the finite Dz theorem and converse-Four
    consequence. *)
Definition D_ldisj_axiomDz := D_proves_list_Dz.
Definition D_fdisj_axiomDz := D_proves_list_Dz.
Definition D_axiomFour := D_proves_C4.

(** * The finite dz-subformula context *)

(** Foundation [Formula.dzSubformula].  The preimage of the subformula list
    under box is [formula_list_unbox]; [finite_powerset] enumerates every
    list subset needed by the semantic filter argument. *)
Definition D_dz_subformula_list (p : formula nat)
    : list (formula nat) :=
  map D_list_Dz
    (finite_powerset (formula_list_unbox (subformulas p))).

Definition D_dz_subformula_conj (p : formula nat) : formula nat :=
  logic_list_conj (D_dz_subformula_list p).

(** Extensional membership interface used by the later tail-model proof. *)
Theorem D_dz_subformula_list_spec :
  forall p q,
    In q (D_dz_subformula_list p) <->
    exists Gamma,
      In Gamma (finite_powerset (formula_list_unbox (subformulas p))) /\
      q = D_list_Dz Gamma.
Proof.
  intros p q. unfold D_dz_subformula_list.
  rewrite in_map_iff. split.
  - intros [Gamma [Hq Hmem]]. exists Gamma. split; [exact Hmem |].
    now symmetry.
  - intros [Gamma [Hmem ->]]. exists Gamma. now split.
Qed.

Theorem D_proves_dz_subformula_member :
  forall p q,
    In q (D_dz_subformula_list p) -> D_proves q.
Proof.
  intros p q Hq.
  apply D_dz_subformula_list_spec in Hq.
  destruct Hq as [Gamma [_ ->]].
  apply D_proves_list_Dz.
Qed.

(** Every finite Dz condition in the reduction context is a D theorem, so
    their finite conjunction is a D theorem as well. *)
Theorem D_proves_dz_subformula_conj :
  forall p, D_proves (D_dz_subformula_conj p).
Proof.
  intro p. unfold D_dz_subformula_conj.
  apply logic_list_conj_intro.
  - exact D_classical_logic.
  - intros q Hq. exact (@D_proves_dz_subformula_member p q Hq).
Qed.

(** Familiar source aliases. *)
Definition D_axiomP := D_proves_P.
Definition D_mem_axiomDz := D_proves_Dz.
