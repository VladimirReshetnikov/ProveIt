(** Substitution-free K4 boxdot algebra.

    This ports the theorem-level core of Foundation's
    [Modal/Entailment/K4.lean].  Raw proof objects and proposition-valued
    theoremhood coincide in this Coq layer, so [_raw] declarations retain
    the source distinction and their unsuffixed aliases expose the wrapped
    names. *)

From FoundationModal Require Import
  Syntax Axioms LogicInfrastructure EntailmentExtensions.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

Record k4_entailment {AtomType}
    (L : modal_logic_set AtomType) : Prop := {
  k4_K : k_entailment L;
  k4_Four : has_Four L
}.

Lemma k4_dia_four :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    k4_entailment L -> forall p,
    L (Imp (Dia (Dia p)) (Dia p)).
Proof.
  intros AtomType L HK4 p.
  exact (axiom_Four_dual
    (e_entailment_of_k (k4_K HK4)) (k4_Four HK4) p).
Qed.

Lemma k4_dia_four_applied :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    k4_entailment L -> forall p,
    L (Dia (Dia p)) -> L (Dia p).
Proof.
  intros AtomType L HK4 p Hdia.
  exact (logic_modus_ponens (k_classical (k4_K HK4))
    (k4_dia_four HK4 p) Hdia).
Qed.

Lemma imply_BoxBoxdot_Box_raw :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    k4_entailment L -> forall p,
    L (Imp (Box (Boxdot p)) (Box p)).
Proof.
  intros AtomType L HK4 p.
  apply box_regularity_of_k; [exact (k4_K HK4) |].
  exact (k_boxdot_axiom_T (k4_K HK4) p).
Qed.

Definition imply_boxboxdot_box := @imply_BoxBoxdot_Box_raw.

Lemma imply_Box_BoxBoxdot_raw :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    k4_entailment L -> forall p,
    L (Imp (Box p) (Box (Boxdot p))).
Proof.
  intros AtomType L HK4 p.
  pose proof (k4_K HK4) as HK.
  pose proof (k_classical HK) as Hclass.
  assert (Hpair : L (Imp (Box p) (And (Box p) (Box (Box p))))).
  { apply logic_imp_and_intro; [exact Hclass | |].
    - exact (logic_identity Hclass (Box p)).
    - exact (has_Four_axiom (k4_Four HK4) p). }
  exact (logic_imp_trans Hclass Hpair
    (k_box_iter_and_collect HK 1 p (Box p))).
Qed.

Definition imply_box_boxboxdot := @imply_Box_BoxBoxdot_raw.

Lemma imply_Box_BoxBoxdot_applied :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    k4_entailment L -> forall p,
    L (Box p) -> L (Box (Boxdot p)).
Proof.
  intros AtomType L HK4 p Hp.
  exact (logic_modus_ponens (k_classical (k4_K HK4))
    (imply_Box_BoxBoxdot_raw HK4 p) Hp).
Qed.

Lemma iff_Box_BoxBoxdot_raw :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    k4_entailment L -> forall p,
    L (Iff (Box p) (Box (Boxdot p))).
Proof.
  intros AtomType L HK4 p.
  apply logic_iff_intro; [exact (k_classical (k4_K HK4)) | |].
  - exact (imply_Box_BoxBoxdot_raw HK4 p).
  - exact (imply_BoxBoxdot_Box_raw HK4 p).
Qed.

Definition iff_box_boxboxdot := @iff_Box_BoxBoxdot_raw.

Lemma iff_Box_BoxdotBox_raw :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    k4_entailment L -> forall p,
    L (Iff (Box p) (Boxdot (Box p))).
Proof.
  intros AtomType L HK4 p; unfold Boxdot.
  pose proof (k_classical (k4_K HK4)) as Hclass.
  apply logic_iff_intro; [exact Hclass | |].
  - apply logic_imp_and_intro; [exact Hclass | |].
    + exact (logic_identity Hclass (Box p)).
    + exact (has_Four_axiom (k4_Four HK4) p).
  - exact (logic_and_elim_left_imp Hclass (Box p) (Box (Box p))).
Qed.

Definition iff_box_boxdotbox := @iff_Box_BoxdotBox_raw.

Lemma iff_Boxdot_BoxdotBoxdot_raw :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    k4_entailment L -> forall p,
    L (Iff (Boxdot p) (Boxdot (Boxdot p))).
Proof.
  intros AtomType L HK4 p; unfold Boxdot at 2.
  pose proof (k4_K HK4) as HK.
  pose proof (k_classical HK) as Hclass.
  apply logic_iff_intro; [exact Hclass | |].
  - apply logic_imp_and_intro; [exact Hclass | |].
    + exact (logic_identity Hclass (Boxdot p)).
    + eapply logic_imp_trans; [exact Hclass | |].
      * exact (k_boxdot_box HK p).
      * exact (imply_Box_BoxBoxdot_raw HK4 p).
  - exact (logic_and_elim_left_imp Hclass (Boxdot p) (Box (Boxdot p))).
Qed.

Definition iff_boxdot_boxdotboxdot := @iff_Boxdot_BoxdotBoxdot_raw.

Lemma boxdot_axiomFour_raw :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    k4_entailment L -> forall p,
    L (Imp (Boxdot p) (Boxdot (Boxdot p))).
Proof.
  intros AtomType L HK4 p.
  exact (logic_iff_elim_left (k_classical (k4_K HK4))
    (iff_Boxdot_BoxdotBoxdot_raw HK4 p)).
Qed.

Definition boxdot_axiomFour := @boxdot_axiomFour_raw.
