(**
  The elementary S4 boxdot and diadot equivalences.

  This file independently ports the complete active theorem surface of the
  pinned Foundation module [Modal/Entailment/S4.lean].  Foundation's
  diadot connective [⟐p] is [p \/ Dia p]; unlike [Boxdot], it was not yet
  named in the local syntax, so [Diadot] supplies the source-facing spelling.

  Foundation distinguishes raw proof objects [|-!] from the proposition that
  a proof exists [|-].  Theoremhood is already Prop-valued here, so each pair
  shares one proof: the [_raw] name records the source proof-object theorem,
  and the unsuffixed alias records its wrapped [!] twin.
*)

From Stdlib Require Import Logic.Classical_Prop.
From FoundationModal Require Import
  Syntax Axioms LogicInfrastructure EntailmentExtensions.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

(** Foundation's [Entailment.S4] is the substitution-free combination
    [K + T + Four]. *)
Record s4_entailment {AtomType}
    (L : modal_logic_set AtomType) : Prop := {
  s4_K : k_entailment L;
  s4_T : has_T L;
  s4_Four : has_Four L
}.

(** Foundation's dotted diamond [p \/ Dia p]. *)
Definition Diadot {AtomType} (p : formula AtomType) : formula AtomType :=
  Or p (Dia p).

(** [S4.lean: iff_box_boxdot]. *)
Lemma iff_box_boxdot_raw :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    s4_entailment L -> forall p,
    L (Iff (Box p) (Boxdot p)).
Proof.
  intros AtomType L HS4 p.
  pose proof (e_entailment_of_k (s4_K HS4)) as HE.
  pose proof (e_classical HE) as Hclass.
  apply logic_iff_intro; [exact Hclass | |].
  - unfold Boxdot.
    apply logic_imp_and_intro; [exact Hclass | |].
    + exact (has_T_axiom (s4_T HS4) p).
    + exact (logic_identity Hclass (Box p)).
  - unfold Boxdot.
    exact (logic_and_elim_right_imp Hclass p (Box p)).
Qed.

(** [S4.lean: iff_box_boxdot!]. *)
Definition iff_box_boxdot := @iff_box_boxdot_raw.

(** [S4.lean: iff_dia_diadot]. *)
Lemma iff_dia_diadot_raw :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    s4_entailment L -> forall p,
    L (Iff (Dia p) (Diadot p)).
Proof.
  intros AtomType L HS4 p.
  pose proof (e_entailment_of_k (s4_K HS4)) as HE.
  pose proof (e_classical HE) as Hclass.
  pose proof (has_DiaTc_of_E_T (dia_dual_of_E HE) (s4_T HS4)) as HDiaTc.
  apply logic_iff_intro; [exact Hclass | |].
  - apply (logic_classical_tautology Hclass).
    intro rho; unfold Diadot, Or, Dia, Neg; simpl; tauto.
  - assert (Hcollapse :
        L (Imp (Imp p (Dia p)) (Imp (Diadot p) (Dia p)))).
    { apply (logic_classical_tautology Hclass).
      intro rho; unfold Diadot, Or, Dia, Neg; simpl; tauto. }
    exact (logic_modus_ponens Hclass Hcollapse
      (has_DiaTc_axiom HDiaTc p)).
Qed.

(** [S4.lean: iff_dia_diadot!]. *)
Definition iff_dia_diadot := @iff_dia_diadot_raw.
