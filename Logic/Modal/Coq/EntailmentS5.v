(**
  The derived-rule surface of Foundation's [Modal/Entailment/S5.lean].

  The pinned source exposes ten declarations: four raw/wrapped theorem pairs
  and two implication-lifting helpers used by the subsequent S5Grz module.
  Theoremhood in this development is Prop-valued, so each Foundation
  proof-object/wrapped pair has one proof and two public Coq names.  Names
  ending in [_raw] record the source proof-object spelling, while names
  ending in [_applied] correspond to the source names carrying a prime.

  Foundation proves [diabox_box] by a chain of duality rewrites.  The generic
  entailment layer has already packaged that argument as the dual of Five,
  so the idiomatic proof here is a direct application of
  [axiom_Five_dual_raw].
*)

From FoundationModal Require Import
  Syntax Axioms LogicInfrastructure EntailmentExtensions.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

(** Foundation's [Entailment.S5] is K together with T and Five.  Keeping the
    record substitution-free preserves the source entailment abstraction. *)
Record s5_entailment {AtomType}
    (L : modal_logic_set AtomType) : Prop := {
  s5_K : k_entailment L;
  s5_T : has_T L;
  s5_Five : has_Five L
}.

Definition s5_E {AtomType} {L : modal_logic_set AtomType}
    (HS5 : s5_entailment L) : e_entailment L :=
  e_entailment_of_k (s5_K HS5).

(** [diabox_box] / [diabox_box!]. *)
Lemma diabox_box_raw :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    s5_entailment L -> forall p,
    L (Imp (Dia (Box p)) (Box p)).
Proof.
  intros AtomType L HS5 p.
  exact (axiom_Five_dual_raw (s5_E HS5) (s5_Five HS5) p).
Qed.

Definition diabox_box := @diabox_box_raw.

(** [diabox_box'] / [diabox_box'!]. *)
Lemma diabox_box_applied_raw :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    s5_entailment L -> forall p,
    L (Dia (Box p)) -> L (Box p).
Proof.
  intros AtomType L HS5 p Hp.
  exact (logic_modus_ponens (k_classical (s5_K HS5))
    (diabox_box_raw HS5 p) Hp).
Qed.

Definition diabox_box_applied := @diabox_box_applied_raw.

(** [rm_diabox] / [rm_diabox!]. *)
Lemma rm_diabox_raw :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    s5_entailment L -> forall p,
    L (Imp (Dia (Box p)) p).
Proof.
  intros AtomType L HS5 p.
  exact (logic_imp_trans (k_classical (s5_K HS5))
    (diabox_box_raw HS5 p)
    (has_T_axiom (s5_T HS5) p)).
Qed.

Definition rm_diabox := @rm_diabox_raw.

(** [rm_diabox'] / [rm_diabox'!]. *)
Lemma rm_diabox_applied_raw :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    s5_entailment L -> forall p,
    L (Dia (Box p)) -> L p.
Proof.
  intros AtomType L HS5 p Hp.
  exact (logic_modus_ponens (k_classical (s5_K HS5))
    (rm_diabox_raw HS5 p) Hp).
Qed.

Definition rm_diabox_applied := @rm_diabox_applied_raw.

(** The source's [lem₁_diaT_of_S5Grz].  This is the composition of the
    two directions of diamond duality under implication. *)
Lemma lem1_diaT_of_S5Grz :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    s5_entailment L -> forall p,
    L (Imp
      (Imp (Neg (Box (Neg p))) (Neg (Box (Neg (Box p)))))
      (Imp (Dia p) (Dia (Box p)))).
Proof.
  intros AtomType L HS5 p.
  pose proof (s5_E HS5) as HE.
  pose proof (e_classical HE) as Hclass.
  pose proof (diaDuality_mp HE p) as Hleft.
  pose proof (diaDuality_mpr HE (Box p)) as Hright.
  assert (Hlift :
      L (Imp
        (Imp (Dia p) (Neg (Box (Neg p))))
        (Imp
          (Imp (Neg (Box (Neg (Box p)))) (Dia (Box p)))
          (Imp
            (Imp (Neg (Box (Neg p))) (Neg (Box (Neg (Box p)))))
            (Imp (Dia p) (Dia (Box p))))))).
  { apply (logic_classical_tautology Hclass).
    intro rho; unfold Neg; simpl; tauto. }
  pose proof (logic_modus_ponens Hclass Hlift Hleft) as Hwith_left.
  exact (logic_modus_ponens Hclass Hwith_left Hright).
Qed.

(** The source's [lem₂_diaT_of_S5Grz]. *)
Lemma lem2_diaT_of_S5Grz :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    s5_entailment L -> forall p,
    L (Imp
      (Imp (Dia p) (Dia (Box p)))
      (Imp (Dia p) p)).
Proof.
  intros AtomType L HS5 p.
  pose proof (k_classical (s5_K HS5)) as Hclass.
  assert (Hlift :
      L (Imp
        (Imp (Dia (Box p)) p)
        (Imp
          (Imp (Dia p) (Dia (Box p)))
          (Imp (Dia p) p)))).
  { apply (logic_classical_tautology Hclass).
    intro rho; unfold Neg; simpl; tauto.
  }
  exact (logic_modus_ponens Hclass Hlift (rm_diabox_raw HS5 p)).
Qed.
