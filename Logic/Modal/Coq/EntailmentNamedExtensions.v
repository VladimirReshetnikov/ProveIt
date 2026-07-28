(**
  Named substitution-free modal entailment extensions.

  This file independently ports the complete active theorem surfaces of the
  pinned Foundation modules

    - Modal/Entailment/EMK.lean,
    - Modal/Entailment/END.lean,
    - Modal/Entailment/ET.lean,
    - Modal/Entailment/ET5.lean,
    - Modal/Entailment/ETB.lean,
    - Modal/Entailment/KP.lean, and
    - Modal/Entailment/N.lean.

  The last module has no active declarations.  As in EntailmentExtensions,
  theoremhood is Prop-valued, so Foundation's raw/wrapped proof twins have
  one proof with two public Coq names.  None of the records below adds the
  substitution field carried by this repository's stronger [normal_logic].
*)

From Stdlib Require Import Logic.Classical_Prop.
From FoundationModal Require Import
  Syntax Axioms LogicInfrastructure EntailmentExtensions.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

(** * Additional source-facing capabilities *)

Record has_D {AtomType} (L : modal_logic_set AtomType) : Prop := {
  has_D_axiom : forall p, L (D p)
}.

Record has_B {AtomType} (L : modal_logic_set AtomType) : Prop := {
  has_B_axiom : forall p, L (B p)
}.

Record has_Point2 {AtomType} (L : modal_logic_set AtomType) : Prop := {
  has_Point2_axiom : forall p, L (Point2 p)
}.

(** The implicational fragment of Foundation's [Entailment.Minimal] used by
    ETB's generic [C_of]: modus ponens and the K combinator only. *)
Record minimal_implication_entailment {AtomType}
    (L : modal_logic_set AtomType) : Prop := {
  minimal_implication_mp :
    forall p q, L (Imp p q) -> L p -> L q;
  minimal_implication_K :
    forall p q, L (Imp p (Imp q p))
}.

Definition minimal_implication_of_classical {AtomType}
    {L : modal_logic_set AtomType} (Hclass : classical_logic L)
    : minimal_implication_entailment L.
Proof.
  constructor.
  - exact (logic_modus_ponens Hclass).
  - intros p q. apply (logic_classical_tautology Hclass).
    intro rho; simpl; tauto.
Defined.

(** Capabilities declared in Entailment/Basic.lean and used by this tranche. *)
Record et_entailment {AtomType}
    (L : modal_logic_set AtomType) : Prop := {
  et_E : e_entailment L;
  et_T : has_T L
}.

Record ed_entailment {AtomType}
    (L : modal_logic_set AtomType) : Prop := {
  ed_E : e_entailment L;
  ed_D : has_D L
}.

Record eb_entailment {AtomType}
    (L : modal_logic_set AtomType) : Prop := {
  eb_E : e_entailment L;
  eb_B : has_B L
}.

Record e5_entailment {AtomType}
    (L : modal_logic_set AtomType) : Prop := {
  e5_E : e_entailment L;
  e5_Five : has_Five L
}.

Record kp_entailment {AtomType}
    (L : modal_logic_set AtomType) : Prop := {
  kp_K : k_entailment L;
  kp_P : has_P L
}.

(** * EMK.lean: two active declarations *)

Record emk_entailment {AtomType}
    (L : modal_logic_set AtomType) : Prop := {
  emk_EM : em_entailment L;
  emk_K : has_K L
}.

Lemma has_C_of_EMK :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    emk_entailment L -> has_C L.
Proof.
  intros AtomType L HEMK; constructor; intros p q; unfold C.
  pose proof (em_E (emk_EM HEMK)) as HE.
  pose proof (e_classical HE) as Hclass.
  pose proof (box_regularity_of_EM (emk_EM HEMK)) as Hreg.
  assert (Hintro : L (Imp p (Imp q (And p q)))).
  { apply (logic_classical_tautology Hclass); intro rho.
    unfold And, Neg; simpl.
    destruct (classic (classical_eval rho p));
      destruct (classic (classical_eval rho q)); tauto. }
  pose proof (Hreg _ _ Hintro) as Hboxed_intro.
  pose proof (has_K_axiom (emk_K HEMK) q (And p q)) as HK.
  pose proof (logic_and_elim_left_imp Hclass (Box p) (Box q)) as Hleft.
  pose proof (logic_and_elim_right_imp Hclass (Box p) (Box q)) as Hright.
  pose proof (logic_imp_trans Hclass Hleft Hboxed_intro) as Hboxed_imp.
  assert (Hlift :
      L (Imp (And (Box p) (Box q))
             (Imp (Box (Imp q (And p q)))
                  (Imp (Box q) (Box (And p q)))))).
  { now apply (logic_imply_intro Hclass). }
  pose proof (logic_under_mp Hclass Hlift Hboxed_imp) as Hwith_q.
  exact (logic_under_mp Hclass Hwith_q Hright).
Qed.

(** * END.lean: two active declarations *)

Record end_entailment {AtomType}
    (L : modal_logic_set AtomType) : Prop := {
  end_EN : en_entailment L;
  end_D : has_D L
}.

Lemma has_P_of_END :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    end_entailment L -> has_P L.
Proof.
  intros AtomType L HEND; constructor.
  pose proof (e_classical (en_E (end_EN HEND))) as Hclass.
  pose proof (has_D_axiom (end_D HEND) Bottom) as HD.
  pose proof (has_N_axiom (en_N (end_EN HEND))) as HN.
  change (L (Imp (Box Bottom) (Neg (Box Top)))) in HD.
  unfold P.
  assert (Hswap :
      L (Imp (Imp (Box Bottom) (Neg (Box Top)))
             (Imp (Box Top) (Neg (Box Bottom))))).
  { apply (logic_classical_tautology Hclass).
    intro rho; unfold Neg; simpl; tauto. }
  pose proof (logic_modus_ponens Hclass Hswap HD) as Hby_N.
  exact (logic_modus_ponens Hclass Hby_N HN).
Qed.

(** * ET.lean: four active declarations *)

Lemma diabot_raw :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    et_entailment L -> L (Dia Top).
Proof.
  intros AtomType L HET.
  pose proof (et_E HET) as HE.
  pose proof (e_classical HE) as Hclass.
  pose proof (has_DiaTc_of_E_T (dia_dual_of_E HE) (et_T HET)) as HDiaTc.
  eapply (logic_modus_ponens Hclass).
  - exact (has_DiaTc_axiom HDiaTc Top).
  - now apply logic_mem_top.
Qed.

Definition diabot := @diabot_raw.

Lemma has_D_of_ET :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    et_entailment L -> has_D L.
Proof.
  intros AtomType L HET; constructor; intro p; unfold D.
  pose proof (et_E HET) as HE.
  pose proof (has_DiaTc_of_E_T (dia_dual_of_E HE) (et_T HET)) as HDiaTc.
  exact (logic_imp_trans (e_classical HE)
    (has_T_axiom (et_T HET) p)
    (has_DiaTc_axiom HDiaTc p)).
Qed.

Lemma ED_of_ET :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    et_entailment L -> ed_entailment L.
Proof.
  intros AtomType L HET; constructor.
  - exact (et_E HET).
  - now apply has_D_of_ET.
Qed.

(** * ETB.lean: eight active declarations *)

Lemma C_of_raw :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    minimal_implication_entailment L -> forall p q,
    L p -> L (Imp q p).
Proof.
  intros AtomType L Hminimal p q Hp.
  eapply (minimal_implication_mp Hminimal).
  - exact (minimal_implication_K Hminimal p q).
  - exact Hp.
Qed.

Definition C_of := @C_of_raw.

Record etb_entailment {AtomType}
    (L : modal_logic_set AtomType) : Prop := {
  etb_E : e_entailment L;
  etb_T : has_T L;
  etb_B : has_B L
}.

Lemma ET_of_ETB :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    etb_entailment L -> et_entailment L.
Proof.
  intros AtomType L HETB; constructor.
  - exact (etb_E HETB).
  - exact (etb_T HETB).
Qed.

Lemma EB_of_ETB :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    etb_entailment L -> eb_entailment L.
Proof.
  intros AtomType L HETB; constructor.
  - exact (etb_E HETB).
  - exact (etb_B HETB).
Qed.

Lemma necessitation_of_ETB :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    etb_entailment L -> necessitation L.
Proof.
  intros AtomType L HETB p Hp.
  pose proof (etb_E HETB) as HE.
  pose proof (e_classical HE) as Hclass.
  pose proof (has_DiaTc_of_E_T
    (dia_dual_of_E HE) (etb_T HETB)) as HDiaTc.
  pose proof (@C_of_raw AtomType L
    (minimal_implication_of_classical Hclass) p (Dia p) Hp) as Hback.
  pose proof (logic_iff_intro Hclass
    (has_DiaTc_axiom HDiaTc p) Hback) as Hiff.
  pose proof (e_replacement HE Hiff) as Hboxed_iff.
  pose proof (logic_iff_elim_right Hclass Hboxed_iff) as Hbox_back.
  pose proof (has_B_axiom (etb_B HETB) p) as HB.
  pose proof (logic_modus_ponens Hclass HB Hp) as Hbox_dia.
  exact (logic_modus_ponens Hclass Hbox_back Hbox_dia).
Qed.

Lemma has_N_of_ETB :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    etb_entailment L -> has_N L.
Proof.
  intros AtomType L HETB.
  apply has_N_of_necessitation.
  - now apply logic_mem_top, e_classical, etb_E.
  - now apply necessitation_of_ETB.
Qed.

Lemma EN_of_ETB :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    etb_entailment L -> en_entailment L.
Proof.
  intros AtomType L HETB; constructor.
  - exact (etb_E HETB).
  - now apply has_N_of_ETB.
Qed.

(** * ET5.lean: eight active declarations *)

Record et5_entailment {AtomType}
    (L : modal_logic_set AtomType) : Prop := {
  et5_E : e_entailment L;
  et5_T : has_T L;
  et5_Five : has_Five L
}.

Lemma ET_of_ET5 :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    et5_entailment L -> et_entailment L.
Proof.
  intros AtomType L HET5; constructor.
  - exact (et5_E HET5).
  - exact (et5_T HET5).
Qed.

Lemma E5_of_ET5 :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    et5_entailment L -> e5_entailment L.
Proof.
  intros AtomType L HET5; constructor.
  - exact (et5_E HET5).
  - exact (et5_Five HET5).
Qed.

Lemma has_B_of_ET5 :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    et5_entailment L -> has_B L.
Proof.
  intros AtomType L HET5; constructor; intro p; unfold B.
  pose proof (et5_E HET5) as HE.
  exact (logic_imp_trans (e_classical HE)
    (axiom_T_dual_raw HE (et5_T HET5) p)
    (has_Five_axiom (et5_Five HET5) p)).
Qed.

Lemma ETB_of_ET5 :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    et5_entailment L -> etb_entailment L.
Proof.
  intros AtomType L HET5; constructor.
  - exact (et5_E HET5).
  - exact (et5_T HET5).
  - now apply has_B_of_ET5.
Qed.

Lemma EN_of_ET5 :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    et5_entailment L -> en_entailment L.
Proof.
  intros AtomType L HET5.
  now apply EN_of_ETB, ETB_of_ET5.
Qed.

Lemma has_Point2_of_ET5 :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    et5_entailment L -> has_Point2 L.
Proof.
  intros AtomType L HET5; constructor; intro p; unfold Point2.
  pose proof (et5_E HET5) as HE.
  pose proof (axiom_Five_dual_raw HE (et5_Five HET5) p) as Hfive_dual.
  pose proof (has_T_axiom (et5_T HET5) p) as HT.
  pose proof (has_B_axiom (has_B_of_ET5 HET5) p) as HB.
  exact (logic_imp_trans (e_classical HE)
    (logic_imp_trans (e_classical HE) Hfive_dual HT) HB).
Qed.

Lemma has_Four_of_ET5 :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    et5_entailment L -> has_Four L.
Proof.
  intros AtomType L HET5; constructor; intro p; unfold Four.
  pose proof (et5_E HET5) as HE.
  pose proof (e_classical HE) as Hclass.
  pose proof (axiom_T_dual_raw HE (et5_T HET5) (Box p)) as HT_dual.
  pose proof (has_Five_axiom (et5_Five HET5) (Box p)) as HFive.
  pose proof (logic_imp_trans Hclass HT_dual HFive) as Hto_box_dia.
  pose proof (axiom_Five_dual_raw HE (et5_Five HET5) p) as HFive_dual.
  pose proof (logic_iff_intro Hclass HFive_dual HT_dual) as Hiff.
  pose proof (e_replacement HE Hiff) as Hboxed_iff.
  pose proof (logic_iff_elim_left Hclass Hboxed_iff) as Hto_box_box.
  exact (logic_imp_trans Hclass Hto_box_dia Hto_box_box).
Qed.

(** * KP.lean: two active declarations *)

Lemma KP_axiomD :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    kp_entailment L -> forall p, L (D p).
Proof.
  intros AtomType L HKP p; unfold D.
  pose proof (kp_K HKP) as HK.
  pose proof (k_classical HK) as Hclass.
  pose proof (box_regularity_of_k HK) as Hreg.
  assert (Hdni : L (Imp p (Neg (Neg p)))).
  { apply (logic_iff_elim_left Hclass).
    now apply logic_double_neg_iff. }
  pose proof (Hreg _ _ Hdni) as Hboxed_dni.
  pose proof (has_K_axiom (k_axiom HK) (Neg p) Bottom) as HKneg.
  pose proof (logic_imp_trans Hclass Hboxed_dni HKneg) as Hcurried.
  assert (Htransform :
      L (Imp (Imp (Box p) (Imp (Box (Neg p)) (Box Bottom)))
             (Imp (Neg (Box Bottom))
                  (Imp (Box p) (Neg (Box (Neg p))))))).
  { apply (logic_classical_tautology Hclass).
    intro rho; unfold Neg; simpl; tauto. }
  pose proof (logic_modus_ponens Hclass Htransform Hcurried) as Hunder_P.
  pose proof (logic_modus_ponens Hclass Hunder_P
    (has_P_axiom (kp_P HKP))) as Hneg_box.
  pose (HD := {| dia_dual_classical := k_classical HK;
                 dia_dual_schema :=
                   {| has_DiaDuality_axiom := k_dia_duality HK |} |}).
  exact (logic_imp_trans Hclass Hneg_box (INLNM_raw HD p)).
Qed.

Lemma has_D_of_KP :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    kp_entailment L -> has_D L.
Proof.
  intros AtomType L HKP; constructor; intro p.
  exact (KP_axiomD HKP p).
Qed.

(** N.lean has no active declarations at the pinned revision. *)
