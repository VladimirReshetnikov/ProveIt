(**
  Substitution-free modal entailments, replacement of equivalents, duality,
  and the elementary E/EM/EN/EMC/EMCN theorem hierarchy.

  This file is an independent Coq port of the active theorem surfaces in the
  pinned Foundation modules

    - Modal/Entailment/DiaDuality.lean,
    - Modal/Entailment/E.lean,
    - Modal/Entailment/EM.lean,
    - Modal/Entailment/EN.lean,
    - Modal/Entailment/EMC.lean,
    - Modal/Entailment/EMCN.lean, and
    - Modal/Entailment/AxiomGeach.lean.

  The small capability records below also port the portion of
  Modal/Entailment/Basic.lean needed by those modules.  In particular,
  [k_entailment] deliberately does not require substitution closure: the
  source entailment class K is weaker than this repository's [normal_logic].

  Foundation distinguishes proof objects [|-!] from the proposition that a
  proof exists [|-].  Here theoremhood is already Prop-valued, so each such
  pair has one proof and two public names; names ending in [_raw] document the
  source proof-object spelling.
*)

From Stdlib Require Import Lists.List.
From Stdlib Require Import Logic.Classical_Prop.
From FoundationModal Require Import Syntax Axioms LogicInfrastructure.

Import ListNotations.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

(** * Minimal substitution-free capability layer *)

Definition replacement_of_equivalents {AtomType}
    (L : modal_logic_set AtomType) : Prop :=
  forall p q, L (Iff p q) -> L (Iff (Box p) (Box q)).

Definition box_regularity {AtomType}
    (L : modal_logic_set AtomType) : Prop :=
  forall p q, L (Imp p q) -> L (Imp (Box p) (Box q)).

Definition necessitation {AtomType}
    (L : modal_logic_set AtomType) : Prop :=
  forall p, L p -> L (Box p).

Record has_M {AtomType} (L : modal_logic_set AtomType) : Prop := {
  has_M_axiom : forall p q, L (M p q)
}.

Record has_C {AtomType} (L : modal_logic_set AtomType) : Prop := {
  has_C_axiom : forall p q, L (C p q)
}.

Record has_N {AtomType} (L : modal_logic_set AtomType) : Prop := {
  has_N_axiom : L N
}.

Record has_K {AtomType} (L : modal_logic_set AtomType) : Prop := {
  has_K_axiom : forall p q, L (K p q)
}.

Record has_T {AtomType} (L : modal_logic_set AtomType) : Prop := {
  has_T_axiom : forall p, L (T p)
}.

Record has_DiaTc {AtomType} (L : modal_logic_set AtomType) : Prop := {
  has_DiaTc_axiom : forall p, L (DiaTc p)
}.

Record has_P {AtomType} (L : modal_logic_set AtomType) : Prop := {
  has_P_axiom : L P
}.

Record has_Four {AtomType} (L : modal_logic_set AtomType) : Prop := {
  has_Four_axiom : forall p, L (Four p)
}.

Record has_Five {AtomType} (L : modal_logic_set AtomType) : Prop := {
  has_Five_axiom : forall p, L (Five p)
}.

Record has_Geach {AtomType} (g : geach_tuple)
    (L : modal_logic_set AtomType) : Prop := {
  has_Geach_axiom : forall p, L (Geach g p)
}.

Record has_DiaDuality {AtomType}
    (L : modal_logic_set AtomType) : Prop := {
  has_DiaDuality_axiom : forall p, L (DiaDuality p)
}.

(** The exact dependency of DiaDuality.lean: classical propositional
    entailment plus the diamond/box duality schema, but no replacement rule. *)
Record dia_dual_entailment {AtomType}
    (L : modal_logic_set AtomType) : Prop := {
  dia_dual_classical : classical_logic L;
  dia_dual_schema : has_DiaDuality L
}.

Definition dia_dual_axiom {AtomType} {L : modal_logic_set AtomType}
    (HD : dia_dual_entailment L) : forall p, L (DiaDuality p) :=
  has_DiaDuality_axiom (dia_dual_schema HD).

Record e_entailment {AtomType}
    (L : modal_logic_set AtomType) : Prop := {
  e_classical : classical_logic L;
  e_dia_duality : forall p, L (DiaDuality p);
  e_replacement : replacement_of_equivalents L
}.

Definition dia_dual_of_E {AtomType} {L : modal_logic_set AtomType}
    (HE : e_entailment L) : dia_dual_entailment L :=
  {| dia_dual_classical := e_classical HE;
     dia_dual_schema := {| has_DiaDuality_axiom := e_dia_duality HE |} |}.

Record em_entailment {AtomType}
    (L : modal_logic_set AtomType) : Prop := {
  em_E : e_entailment L;
  em_M : has_M L
}.

Record en_entailment {AtomType}
    (L : modal_logic_set AtomType) : Prop := {
  en_E : e_entailment L;
  en_N : has_N L
}.

Record emc_entailment {AtomType}
    (L : modal_logic_set AtomType) : Prop := {
  emc_EM : em_entailment L;
  emc_C : has_C L
}.

Record emcn_entailment {AtomType}
    (L : modal_logic_set AtomType) : Prop := {
  emcn_EMC : emc_entailment L;
  emcn_N : has_N L
}.

Record k_entailment {AtomType}
    (L : modal_logic_set AtomType) : Prop := {
  k_classical : classical_logic L;
  k_necessitation : necessitation L;
  k_axiom : has_K L;
  k_dia_duality : forall p, L (DiaDuality p)
}.

(** * Classical object-logic adapters *)

Lemma logic_iff_intro :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    classical_logic L -> forall p q,
    L (Imp p q) -> L (Imp q p) -> L (Iff p q).
Proof.
  intros AtomType L Hclass p q Hpq Hqp.
  unfold Iff. now apply (logic_and_intro Hclass).
Qed.

Lemma logic_iff_elim_left :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    classical_logic L -> forall p q,
    L (Iff p q) -> L (Imp p q).
Proof.
  intros AtomType L Hclass p q Hiff.
  eapply (logic_modus_ponens Hclass); [|exact Hiff].
  unfold Iff. now apply logic_and_elim_left_imp.
Qed.

Lemma logic_iff_elim_right :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    classical_logic L -> forall p q,
    L (Iff p q) -> L (Imp q p).
Proof.
  intros AtomType L Hclass p q Hiff.
  eapply (logic_modus_ponens Hclass); [|exact Hiff].
  unfold Iff. now apply logic_and_elim_right_imp.
Qed.

Lemma logic_iff_sym :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    classical_logic L -> forall p q,
    L (Iff p q) -> L (Iff q p).
Proof.
  intros AtomType L Hclass p q Hiff.
  apply logic_iff_intro; [exact Hclass | |].
  - now apply (logic_iff_elim_right Hclass).
  - now apply (logic_iff_elim_left Hclass).
Qed.

Lemma logic_iff_trans :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    classical_logic L -> forall p q r,
    L (Iff p q) -> L (Iff q r) -> L (Iff p r).
Proof.
  intros AtomType L Hclass p q r Hpq Hqr.
  apply logic_iff_intro; [exact Hclass | |].
  - eapply logic_imp_trans; [exact Hclass | |].
    + exact (@logic_iff_elim_left AtomType L Hclass p q Hpq).
    + exact (@logic_iff_elim_left AtomType L Hclass q r Hqr).
  - eapply logic_imp_trans; [exact Hclass | |].
    + exact (@logic_iff_elim_right AtomType L Hclass q r Hqr).
    + exact (@logic_iff_elim_right AtomType L Hclass p q Hpq).
Qed.

Lemma logic_contraposition :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    classical_logic L -> forall p q,
    L (Imp p q) -> L (Imp (Neg q) (Neg p)).
Proof.
  intros AtomType L Hclass p q Hpq.
  eapply (logic_modus_ponens Hclass); [|exact Hpq].
  apply (logic_classical_tautology Hclass).
  intro rho; unfold Neg; simpl; tauto.
Qed.

Lemma logic_neg_iff :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    classical_logic L -> forall p q,
    L (Iff p q) -> L (Iff (Neg p) (Neg q)).
Proof.
  intros AtomType L Hclass p q Hiff.
  apply logic_iff_intro; [exact Hclass | |].
  - apply logic_contraposition; [exact Hclass |].
    now apply (logic_iff_elim_right Hclass).
  - apply logic_contraposition; [exact Hclass |].
    now apply (logic_iff_elim_left Hclass).
Qed.

Lemma logic_double_neg_iff :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    classical_logic L -> forall p, L (Iff p (Neg (Neg p))).
Proof.
  intros AtomType L Hclass p.
  apply (logic_classical_tautology Hclass).
  intro rho; unfold Iff, And, Neg; simpl.
  destruct (classic (classical_eval rho p)); tauto.
Qed.

Lemma logic_double_neg_iff_rev :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    classical_logic L -> forall p, L (Iff (Neg (Neg p)) p).
Proof.
  intros AtomType L Hclass p.
  apply logic_iff_sym; [exact Hclass |].
  now apply logic_double_neg_iff.
Qed.

Lemma logic_iff_top_left_from :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    classical_logic L -> forall p, L p -> L (Iff p Top).
Proof.
  intros AtomType L Hclass p Hp.
  eapply (logic_modus_ponens Hclass); [|exact Hp].
  apply (logic_classical_tautology Hclass).
  intro rho; unfold Iff, And, Top, Neg; simpl.
  destruct (classic (classical_eval rho p)); tauto.
Qed.

Lemma logic_iff_not_top_bottom :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    classical_logic L -> L (Iff (Neg Top) Bottom).
Proof.
  intros AtomType L Hclass.
  apply (logic_classical_tautology Hclass).
  intro rho; unfold Iff, And, Top, Neg; simpl; tauto.
Qed.

(** * DiaDuality.lean: 17 active declarations *)

Lemma conj_cons :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    classical_logic L -> forall p Gamma,
    L (Iff (And p (logic_list_conj2 Gamma))
           (logic_list_conj2 (p :: Gamma))).
Proof.
  intros AtomType L Hclass p Gamma; destruct Gamma as [|q Gamma].
  - apply (logic_classical_tautology Hclass); intro rho.
    unfold Iff, And, Top, Neg; simpl.
    destruct (classic (classical_eval rho p)); tauto.
  - simpl. apply logic_iff_intro; [exact Hclass | |];
      now apply logic_identity.
Qed.

Definition iff_top_left_raw := @logic_iff_top_left_from.
Definition iff_top_left := @logic_iff_top_left_from.
Definition iff_symm := @logic_iff_sym.

Lemma iff_top_right :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    classical_logic L -> forall p, L p -> L (Iff Top p).
Proof.
  intros AtomType L Hclass p Hp.
  apply logic_iff_sym; [exact Hclass |].
  now apply logic_iff_top_left_from.
Qed.

Definition iff_not_bot_top := @logic_iff_not_top_bottom.

Definition EMNLN_raw {AtomType} (L : modal_logic_set AtomType)
    (HD : has_DiaDuality L) (p : formula AtomType) :
    L (DiaDuality p) :=
  has_DiaDuality_axiom HD p.

Definition EMNLN := @EMNLN_raw.

Lemma IMNLN_raw :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    dia_dual_entailment L -> forall p,
    L (Imp (Dia p) (Neg (Box (Neg p)))).
Proof.
  intros AtomType L HD p.
  apply (logic_iff_elim_left (dia_dual_classical HD)).
  exact (dia_dual_axiom HD p).
Qed.

Definition IMNLN := @IMNLN_raw.

Lemma NLN_of_M :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    dia_dual_entailment L -> forall p,
    L (Dia p) -> L (Neg (Box (Neg p))).
Proof.
  intros AtomType L HD p Hp.
  eapply (logic_modus_ponens (dia_dual_classical HD)); [|exact Hp].
  now apply IMNLN_raw.
Qed.

Lemma INLNM_raw :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    dia_dual_entailment L -> forall p,
    L (Imp (Neg (Box (Neg p))) (Dia p)).
Proof.
  intros AtomType L HD p.
  apply (logic_iff_elim_right (dia_dual_classical HD)).
  exact (dia_dual_axiom HD p).
Qed.

Definition INLNM := @INLNM_raw.

Lemma M_of_NLN_raw :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    dia_dual_entailment L -> forall p,
    L (Neg (Box (Neg p))) -> L (Dia p).
Proof.
  intros AtomType L HD p Hp.
  eapply (logic_modus_ponens (dia_dual_classical HD)); [|exact Hp].
  now apply INLNM_raw.
Qed.

Definition M_of_NLN := @M_of_NLN_raw.

Lemma has_DiaTc_of_E_T :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    dia_dual_entailment L -> has_T L -> has_DiaTc L.
Proof.
  intros AtomType L HD HT; constructor; intro p.
  eapply (logic_modus_ponens (dia_dual_classical HD));
    [|exact (has_T_axiom HT (Neg p))].
  apply (logic_classical_tautology (dia_dual_classical HD)).
  intro rho; unfold T, DiaTc, Dia, Neg; simpl.
  destruct (classic (classical_eval rho p));
    destruct (classic (rho (Box (Neg p)))); tauto.
Qed.

Lemma has_P_of_T :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    has_T L -> has_P L.
Proof.
  intros AtomType L HT; constructor.
  exact (has_T_axiom HT Bottom).
Qed.

(** * E.lean: 52 active declarations *)

Lemma multire_raw :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    e_entailment L -> forall n p q,
    L (Iff p q) -> L (Iff (box_iter n p) (box_iter n q)).
Proof.
  intros AtomType L HE n; induction n as [|n IH]; intros p q Hpq; simpl.
  - exact Hpq.
  - apply (e_replacement HE). now apply IH.
Qed.

Definition multire := @multire_raw.

Lemma multi_ELLNN_raw :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    e_entailment L -> forall n p,
    L (Iff (box_iter n p) (box_iter n (Neg (Neg p)))).
Proof.
  intros AtomType L HE n p.
  apply multire_raw; [exact HE |].
  now apply logic_double_neg_iff, e_classical.
Qed.

Definition multi_ELLNN := @multi_ELLNN_raw.

Lemma ELLNN_raw :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    e_entailment L -> forall p,
    L (Iff (Box p) (Box (Neg (Neg p)))).
Proof. intros; exact (multi_ELLNN_raw H 1 p). Qed.

Definition ELLNN := @ELLNN_raw.

Lemma ILLNN_raw :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    e_entailment L -> forall p,
    L (Imp (Box p) (Box (Neg (Neg p)))).
Proof.
  intros AtomType L HE p.
  apply (logic_iff_elim_left (e_classical HE)).
  now apply ELLNN_raw.
Qed.

Definition ILLNN := @ILLNN_raw.
(** Source aliases [box_dni] and [box_dni!]. *)
Definition box_dni := @ILLNN_raw.
Definition box_dni_bang := @ILLNN.

Lemma ILNNL_raw :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    e_entailment L -> forall p,
    L (Imp (Box (Neg (Neg p))) (Box p)).
Proof.
  intros AtomType L HE p.
  apply (logic_iff_elim_right (e_classical HE)).
  now apply ELLNN_raw.
Qed.

Definition ILNNL := @ILNNL_raw.
(** Source aliases [box_dne] and [box_dne!]. *)
Definition box_dne := @ILNNL_raw.
Definition box_dne_bang := @ILNNL.

Lemma box_dne_applied_raw :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    e_entailment L -> forall p,
    L (Box (Neg (Neg p))) -> L (Box p).
Proof.
  intros AtomType L HE p Hp.
  eapply (logic_modus_ponens (e_classical HE)); [|exact Hp].
  now apply ILNNL_raw.
Qed.

Definition box_dne_applied := @box_dne_applied_raw.

Lemma INMNL_raw :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    e_entailment L -> forall p,
    L (Imp (Neg (Dia (Neg p))) (Box p)).
Proof.
  intros AtomType L HE p.
  change (L (Imp (Neg (Neg (Box (Neg (Neg p))))) (Box p))).
  eapply logic_imp_trans; [exact (e_classical HE) | |].
  - apply (logic_iff_elim_right (e_classical HE)).
    apply logic_double_neg_iff; exact (e_classical HE).
  - now apply ILNNL_raw.
Qed.

Definition INMNL := @INMNL_raw.

Lemma INLMN_raw :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    e_entailment L -> forall p,
    L (Imp (Neg (Box p)) (Dia (Neg p))).
Proof.
  intros AtomType L HE p.
  eapply logic_imp_trans; [exact (e_classical HE) | |].
  - apply logic_contraposition; [exact (e_classical HE) |].
    now apply INMNL_raw.
  - apply (logic_iff_elim_right (e_classical HE)).
    apply logic_double_neg_iff; exact (e_classical HE).
Qed.

Definition INLMN := @INLMN_raw.

Lemma multiDiaDuality :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    e_entailment L -> forall n p,
    L (Iff (dia_iter n p) (Neg (box_iter n (Neg p)))).
Proof.
  intros AtomType L HE n; induction n as [|n IH]; intro p.
  - simpl. apply logic_double_neg_iff; exact (e_classical HE).
  - simpl; unfold Dia.
    apply logic_neg_iff; [exact (e_classical HE) |].
    apply (e_replacement HE).
    eapply logic_iff_trans; [exact (e_classical HE) | |].
    + apply logic_neg_iff; [exact (e_classical HE) | exact (IH p)].
    + apply logic_double_neg_iff_rev; exact (e_classical HE).
Qed.

Definition diaItr_duality := @multiDiaDuality.

Lemma diaItrDuality_mp :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    e_entailment L -> forall n p,
    L (Imp (dia_iter n p) (Neg (box_iter n (Neg p)))).
Proof.
  intros AtomType L HE n p.
  apply (logic_iff_elim_left (e_classical HE)).
  now apply multiDiaDuality.
Qed.

Lemma diaDuality_mp :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    e_entailment L -> forall p,
    L (Imp (Dia p) (Neg (Box (Neg p)))).
Proof. intros; exact (diaItrDuality_mp H 1 p). Qed.

Lemma diaItrDuality_mpr :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    e_entailment L -> forall n p,
    L (Imp (Neg (box_iter n (Neg p))) (dia_iter n p)).
Proof.
  intros AtomType L HE n p.
  apply (logic_iff_elim_right (e_classical HE)).
  now apply multiDiaDuality.
Qed.

Lemma diaDuality_mpr :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    e_entailment L -> forall p,
    L (Imp (Neg (Box (Neg p))) (Dia p)).
Proof. intros; exact (diaItrDuality_mpr H 1 p). Qed.

Lemma diaDuality_prime_mp :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    e_entailment L -> forall p,
    L (Dia p) -> L (Neg (Box (Neg p))).
Proof.
  intros AtomType L HE p Hp.
  eapply (logic_modus_ponens (e_classical HE)); [|exact Hp].
  now apply diaDuality_mp.
Qed.

Lemma diaDuality_prime_mpr :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    e_entailment L -> forall p,
    L (Neg (Box (Neg p))) -> L (Dia p).
Proof.
  intros AtomType L HE p Hp.
  eapply (logic_modus_ponens (e_classical HE)); [|exact Hp].
  now apply diaDuality_mpr.
Qed.

Definition diaItr_duality_mp := @diaItrDuality_mp.
Definition dia_duality_mp := @diaDuality_mp.
Definition diaItr_duality_mpr := @diaItrDuality_mpr.
Definition dia_duality_mpr := @diaDuality_mpr.

Lemma dia_duality_iff :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    e_entailment L -> forall p,
    L (Dia p) <-> L (Neg (Box (Neg p))).
Proof.
  intros AtomType L HE p; split.
  - now apply diaDuality_prime_mp.
  - now apply diaDuality_prime_mpr.
Qed.

Lemma diaItr_duality_iff :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    e_entailment L -> forall n p,
    L (dia_iter n p) <-> L (Neg (box_iter n (Neg p))).
Proof.
  intros AtomType L HE n p; split; intro Hp.
  - eapply (logic_modus_ponens (e_classical HE)); [|exact Hp].
    now apply diaItrDuality_mp.
  - eapply (logic_modus_ponens (e_classical HE)); [|exact Hp].
    now apply diaItrDuality_mpr.
Qed.

Lemma boxItrDuality :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    e_entailment L -> forall n p,
    L (Iff (box_iter n p) (Neg (dia_iter n (Neg p)))).
Proof.
  intros AtomType L HE n; induction n as [|n IH]; intro p.
  - simpl. apply logic_double_neg_iff; exact (e_classical HE).
  - simpl; unfold Dia.
    eapply logic_iff_trans; [exact (e_classical HE) | |].
    + apply (e_replacement HE). exact (IH p).
    + apply logic_double_neg_iff; exact (e_classical HE).
Qed.

Definition boxItr_duality := @boxItrDuality.

Lemma boxItrDuality_mp :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    e_entailment L -> forall n p,
    L (Imp (box_iter n p) (Neg (dia_iter n (Neg p)))).
Proof.
  intros AtomType L HE n p.
  apply (logic_iff_elim_left (e_classical HE)).
  now apply boxItrDuality.
Qed.

Lemma boxDuality_mp :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    e_entailment L -> forall p,
    L (Imp (Box p) (Neg (Dia (Neg p)))).
Proof. intros; exact (boxItrDuality_mp H 1 p). Qed.

Lemma boxItrDuality_mpr :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    e_entailment L -> forall n p,
    L (Imp (Neg (dia_iter n (Neg p))) (box_iter n p)).
Proof.
  intros AtomType L HE n p.
  apply (logic_iff_elim_right (e_classical HE)).
  now apply boxItrDuality.
Qed.

Lemma boxDuality_mpr :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    e_entailment L -> forall p,
    L (Imp (Neg (Dia (Neg p))) (Box p)).
Proof. intros; exact (boxItrDuality_mpr H 1 p). Qed.

Definition boxItr_duality_mp := @boxItrDuality_mp.

Lemma boxItr_duality_mp_applied :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    e_entailment L -> forall n p,
    L (box_iter n p) -> L (Neg (dia_iter n (Neg p))).
Proof.
  intros AtomType L HE n p Hp.
  eapply (logic_modus_ponens (e_classical HE)); [|exact Hp].
  now apply boxItrDuality_mp.
Qed.

Definition boxItr_duality_mpr := @boxItrDuality_mpr.

Lemma boxItr_duality_mpr_applied :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    e_entailment L -> forall n p,
    L (Neg (dia_iter n (Neg p))) -> L (box_iter n p).
Proof.
  intros AtomType L HE n p Hp.
  eapply (logic_modus_ponens (e_classical HE)); [|exact Hp].
  now apply boxItrDuality_mpr.
Qed.

Lemma boxDuality :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    e_entailment L -> forall p,
    L (Iff (Box p) (Neg (Dia (Neg p)))).
Proof. intros; exact (boxItrDuality H 1 p). Qed.

Definition box_duality := @boxDuality.
Definition boxDuality_mp_wrapped := @boxDuality_mp.

Lemma boxDuality_mp_applied_raw :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    e_entailment L -> forall p,
    L (Box p) -> L (Neg (Dia (Neg p))).
Proof.
  intros AtomType L HE p Hp.
  exact (@boxItr_duality_mp_applied AtomType L HE 1 p Hp).
Qed.

Definition boxDuality_mp_applied := @boxDuality_mp_applied_raw.
Definition boxDuality_mpr_wrapped := @boxDuality_mpr.

Lemma boxDuality_mpr_applied_raw :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    e_entailment L -> forall p,
    L (Neg (Dia (Neg p))) -> L (Box p).
Proof.
  intros AtomType L HE p Hp.
  exact (@boxItr_duality_mpr_applied AtomType L HE 1 p Hp).
Qed.

Definition boxDuality_mpr_applied := @boxDuality_mpr_applied_raw.

(** * EM, EN, EMC, and EMCN *)

Lemma logic_curry :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    classical_logic L -> forall p q r,
    L (Imp (And p q) r) -> L (Imp p (Imp q r)).
Proof.
  intros AtomType L Hclass p q r H.
  eapply (logic_modus_ponens Hclass); [|exact H].
  apply (logic_classical_tautology Hclass); intro rho.
  unfold And, Neg; simpl.
  destruct (classic (classical_eval rho p));
    destruct (classic (classical_eval rho q));
    destruct (classic (classical_eval rho r)); tauto.
Qed.

(** EM.lean, forward instance. *)
Lemma box_regularity_of_EM :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    em_entailment L -> box_regularity L.
Proof.
  intros AtomType L HEM p q Hpq.
  pose proof (e_classical (em_E HEM)) as Hclass.
  assert (Hp_and : L (Imp p (And p q))).
  { apply logic_imp_and_intro; [exact Hclass | |exact Hpq].
    now apply logic_identity. }
  assert (Hand_p : L (Imp (And p q) p)).
  { now apply logic_and_elim_left_imp. }
  assert (Hiff : L (Iff p (And p q))).
  { now apply (logic_iff_intro Hclass). }
  pose proof (e_replacement (em_E HEM) Hiff) as Hboxed_iff.
  pose proof (logic_iff_elim_left Hclass Hboxed_iff) as Hinto.
  pose proof (has_M_axiom (em_M HEM) p q) as HM.
  pose proof (logic_and_elim_right_imp Hclass (Box p) (Box q)) as Hright.
  exact (logic_imp_trans Hclass
    (logic_imp_trans Hclass Hinto HM) Hright).
Qed.

(** EM.lean, reverse instance. *)
Lemma EM_of_E_box_regularity :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    e_entailment L -> box_regularity L -> em_entailment L.
Proof.
  intros AtomType L HE Hreg; constructor; [exact HE |].
  constructor; intros p q; unfold M.
  apply logic_imp_and_intro; [exact (e_classical HE) | |].
  - apply Hreg. now apply logic_and_elim_left_imp, e_classical.
  - apply Hreg. now apply logic_and_elim_right_imp, e_classical.
Qed.

(** EN.lean, forward instance. *)
Lemma necessitation_of_EN :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    en_entailment L -> necessitation L.
Proof.
  intros AtomType L HEN p Hp.
  pose proof (e_classical (en_E HEN)) as Hclass.
  pose proof (logic_iff_top_left_from Hclass Hp) as Hiff.
  pose proof (e_replacement (en_E HEN) Hiff) as Hboxed.
  eapply (logic_modus_ponens Hclass); [|exact (has_N_axiom (en_N HEN))].
  exact (logic_iff_elim_right Hclass Hboxed).
Qed.

(** EN.lean, reverse instance. *)
Lemma has_N_of_necessitation :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    L Top -> necessitation L -> has_N L.
Proof.
  intros AtomType L Htop Hnec; constructor; unfold N.
  now apply Hnec.
Qed.

(** EMC.lean. *)
Lemma has_K_of_EMC :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    emc_entailment L -> has_K L.
Proof.
  intros AtomType L HEMC; constructor; intros p q; unfold K.
  pose proof (em_E (emc_EM HEMC)) as HE.
  pose proof (e_classical HE) as Hclass.
  pose proof (box_regularity_of_EM (emc_EM HEMC)) as Hreg.
  assert (Hmp : L (Imp (And (Imp p q) p) q)).
  { apply (logic_classical_tautology Hclass); intro rho.
    unfold And, Neg; simpl.
    destruct (classic (classical_eval rho p));
      destruct (classic (classical_eval rho q)); tauto. }
  pose proof (Hreg _ _ Hmp) as Hboxed_mp.
  pose proof (has_C_axiom (emc_C HEMC) (Imp p q) p) as HC.
  apply logic_curry; [exact Hclass |].
  exact (logic_imp_trans Hclass HC Hboxed_mp).
Qed.

Lemma box_regularity_of_k :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    k_entailment L -> box_regularity L.
Proof.
  intros AtomType L HK p q Hpq.
  eapply (logic_modus_ponens (k_classical HK)).
  - exact (has_K_axiom (k_axiom HK) p q).
  - now apply (k_necessitation HK).
Qed.

Lemma e_entailment_of_k :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    k_entailment L -> e_entailment L.
Proof.
  intros AtomType L HK; constructor.
  - exact (k_classical HK).
  - exact (k_dia_duality HK).
  - intros p q Hiff.
    pose proof (k_classical HK) as Hclass.
    apply logic_iff_intro; [exact Hclass | |].
    + apply box_regularity_of_k; [exact HK |].
      now apply (logic_iff_elim_left Hclass).
    + apply box_regularity_of_k; [exact HK |].
      now apply (logic_iff_elim_right Hclass).
Qed.

Lemma has_C_of_k :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    k_entailment L -> has_C L.
Proof.
  intros AtomType L HK; constructor; intros p q; unfold C.
  pose proof (k_classical HK) as Hclass.
  assert (Hintro : L (Imp p (Imp q (And p q)))).
  { apply (logic_classical_tautology Hclass); intro rho.
    unfold And, Neg; simpl.
    destruct (classic (classical_eval rho p));
      destruct (classic (classical_eval rho q)); tauto. }
  pose proof (k_necessitation HK Hintro) as Hboxed_intro.
  pose proof (has_K_axiom (k_axiom HK) p (Imp q (And p q))) as HK1.
  pose proof (logic_modus_ponens Hclass HK1 Hboxed_intro) as Hstep1.
  pose proof (has_K_axiom (k_axiom HK) q (And p q)) as Hstep2.
  pose proof (logic_and_elim_left_imp Hclass (Box p) (Box q)) as Hleft.
  pose proof (logic_and_elim_right_imp Hclass (Box p) (Box q)) as Hright.
  pose proof (logic_imp_trans Hclass Hleft Hstep1) as Hboxed_imp.
  assert (Hlift :
      L (Imp (And (Box p) (Box q))
             (Imp (Box (Imp q (And p q)))
                  (Imp (Box q) (Box (And p q)))))).
  { now apply (logic_imply_intro Hclass). }
  pose proof (logic_under_mp Hclass Hlift Hboxed_imp) as Hwith_q.
  exact (logic_under_mp Hclass Hwith_q Hright).
Qed.

(** * K.lean: substitution-free derived modal algebra *)

Lemma k_multinecessitation :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    k_entailment L -> forall n p,
    L p -> L (box_iter n p).
Proof.
  intros AtomType L HK n; induction n as [|n IH]; intros p Hp; simpl.
  - exact Hp.
  - apply (k_necessitation HK). now apply IH.
Qed.

(** Iterating K does not require substitution closure.  At each successor,
    one necessitated induction hypothesis and two instances of K suffice. *)
Lemma k_box_iter_axiom_K :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    k_entailment L -> forall n p q,
    L (Imp (box_iter n (Imp p q))
      (Imp (box_iter n p) (box_iter n q))).
Proof.
  intros AtomType L HK n; induction n as [|n IH]; intros p q; simpl.
  - now apply logic_identity, k_classical.
  - pose proof (k_classical HK) as Hclass.
    pose proof (k_necessitation HK (IH p q)) as Hnec.
    pose proof
      (logic_modus_ponens Hclass
        (has_K_axiom (k_axiom HK)
          (box_iter n (Imp p q))
          (Imp (box_iter n p) (box_iter n q))) Hnec) as Hfirst.
    exact (logic_imp_trans Hclass Hfirst
      (has_K_axiom (k_axiom HK) (box_iter n p) (box_iter n q))).
Qed.

Lemma k_box_iter_regularity :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    k_entailment L -> forall n p q,
    L (Imp p q) ->
    L (Imp (box_iter n p) (box_iter n q)).
Proof.
  intros AtomType L HK n p q Hpq.
  eapply (logic_modus_ponens (k_classical HK)).
  - exact (k_box_iter_axiom_K HK n p q).
  - exact (k_multinecessitation HK n Hpq).
Qed.

Lemma k_box_congruence :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    k_entailment L -> forall p q,
    L (Iff p q) -> L (Iff (Box p) (Box q)).
Proof.
  intros AtomType L HK p q Hiff.
  pose proof (k_classical HK) as Hclass.
  apply logic_iff_intro; [exact Hclass | |].
  - apply box_regularity_of_k; [exact HK |].
    now apply (logic_iff_elim_left Hclass).
  - apply box_regularity_of_k; [exact HK |].
    now apply (logic_iff_elim_right Hclass).
Qed.

Lemma k_box_iter_congruence :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    k_entailment L -> forall n p q,
    L (Iff p q) ->
    L (Iff (box_iter n p) (box_iter n q)).
Proof.
  intros AtomType L HK n p q Hiff.
  pose proof (k_classical HK) as Hclass.
  apply logic_iff_intro; [exact Hclass | |].
  - apply k_box_iter_regularity; [exact HK |].
    now apply (logic_iff_elim_left Hclass).
  - apply k_box_iter_regularity; [exact HK |].
    now apply (logic_iff_elim_right Hclass).
Qed.

Lemma k_box_iter_top :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    k_entailment L -> forall n,
    L (box_iter n Top).
Proof.
  intros AtomType L HK n.
  apply k_multinecessitation; [exact HK |].
  now apply logic_mem_top, k_classical.
Qed.

Lemma k_box_iter_and_collect :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    k_entailment L -> forall n p q,
    L (Imp (And (box_iter n p) (box_iter n q))
      (box_iter n (And p q))).
Proof.
  intros AtomType L HK n p q.
  pose proof (k_classical HK) as Hclass.
  assert (Hintro : L (Imp p (Imp q (And p q)))).
  { apply (logic_classical_tautology Hclass).
    intro rho; unfold And, Neg; simpl; tauto. }
  pose proof (k_box_iter_regularity HK n Hintro) as Hfirst.
  pose proof (k_box_iter_axiom_K HK n q (And p q)) as Hsecond.
  pose proof (logic_imp_trans Hclass Hfirst Hsecond) as Hcurried.
  eapply (logic_modus_ponens Hclass); [|exact Hcurried].
  apply (logic_classical_tautology Hclass).
  intro rho; unfold And, Neg; simpl; tauto.
Qed.

Lemma k_box_iter_and_distribute :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    k_entailment L -> forall n p q,
    L (Imp (box_iter n (And p q))
      (And (box_iter n p) (box_iter n q))).
Proof.
  intros AtomType L HK n p q.
  pose proof (k_classical HK) as Hclass.
  apply logic_imp_and_intro; [exact Hclass | |].
  - apply k_box_iter_regularity; [exact HK |].
    now apply logic_and_elim_left_imp.
  - apply k_box_iter_regularity; [exact HK |].
    now apply logic_and_elim_right_imp.
Qed.

Lemma k_box_iter_or_collect :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    k_entailment L -> forall n p q,
    L (Imp (Or (box_iter n p) (box_iter n q))
      (box_iter n (Or p q))).
Proof.
  intros AtomType L HK n p q.
  pose proof (k_classical HK) as Hclass.
  assert (Hleft0 : L (Imp p (Or p q))).
  { apply (logic_classical_tautology Hclass).
    intro rho; unfold Or, Neg; simpl; tauto. }
  assert (Hright0 : L (Imp q (Or p q))).
  { apply (logic_classical_tautology Hclass).
    intro rho; unfold Or, Neg; simpl; tauto. }
  pose proof (k_box_iter_regularity HK n Hleft0) as Hleft.
  pose proof (k_box_iter_regularity HK n Hright0) as Hright.
  eapply (logic_modus_ponens Hclass); [|exact Hright].
  eapply (logic_modus_ponens Hclass); [|exact Hleft].
  apply (logic_classical_tautology Hclass).
  intro rho; unfold Or, Neg; simpl; tauto.
Qed.

(** Boxdot is the conjunction [p /\ box p].  Its normality laws are already
    consequences of K; no additional modal capability is required. *)
Lemma k_boxdot_top :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    k_entailment L -> L (Boxdot Top).
Proof.
  intros AtomType L HK; unfold Boxdot.
  apply logic_and_intro; [exact (k_classical HK) | |].
  - now apply logic_mem_top, k_classical.
  - exact (k_box_iter_top HK 1).
Qed.

Lemma k_boxdot_axiom_K :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    k_entailment L -> forall p q,
    L (Imp (Boxdot (Imp p q))
      (Imp (Boxdot p) (Boxdot q))).
Proof.
  intros AtomType L HK p q.
  pose proof (k_classical HK) as Hclass.
  set (a := Boxdot (Imp p q)).
  set (b := Boxdot p).
  assert (Ha_imp : L (Imp a (Imp p q))).
  { unfold a, Boxdot. now apply logic_and_elim_left_imp. }
  assert (Ha_box_imp : L (Imp a (Box (Imp p q)))).
  { unfold a, Boxdot. now apply logic_and_elim_right_imp. }
  assert (Hb_p : L (Imp b p)).
  { unfold b, Boxdot. now apply logic_and_elim_left_imp. }
  assert (Hb_box_p : L (Imp b (Box p))).
  { unfold b, Boxdot. now apply logic_and_elim_right_imp. }
  pose proof (logic_and_elim_left_imp Hclass a b) as Hab_a.
  pose proof (logic_and_elim_right_imp Hclass a b) as Hab_b.
  pose proof (logic_imp_trans Hclass Hab_a Ha_imp) as Hab_imp.
  pose proof (logic_imp_trans Hclass Hab_b Hb_p) as Hab_p.
  pose proof (logic_under_mp Hclass Hab_imp Hab_p) as Hab_q.
  pose proof (logic_imp_trans Hclass Hab_a Ha_box_imp) as Hab_box_imp.
  pose proof (logic_imp_trans Hclass Hab_b Hb_box_p) as Hab_box_p.
  pose proof (logic_imply_intro Hclass (And a b)
    (has_K_axiom (k_axiom HK) p q)) as Hab_K.
  pose proof (logic_under_mp Hclass Hab_K Hab_box_imp) as Hab_box_mp.
  pose proof (logic_under_mp Hclass Hab_box_mp Hab_box_p) as Hab_box_q.
  apply logic_curry; [exact Hclass |].
  change (L (Imp (And a b) (And q (Box q)))).
  exact (logic_imp_and_intro Hclass Hab_q Hab_box_q).
Qed.

Lemma k_boxdot_axiom_T :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    k_entailment L -> forall p,
    L (Imp (Boxdot p) p).
Proof.
  intros AtomType L HK p; unfold Boxdot.
  now apply logic_and_elim_left_imp, k_classical.
Qed.

Lemma k_boxdot_nec :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    k_entailment L -> forall p,
    L p -> L (Boxdot p).
Proof.
  intros AtomType L HK p Hp; unfold Boxdot.
  apply logic_and_intro; [exact (k_classical HK) | exact Hp |].
  now apply k_necessitation.
Qed.

Lemma k_boxdot_box :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    k_entailment L -> forall p,
    L (Imp (Boxdot p) (Box p)).
Proof.
  intros AtomType L HK p; unfold Boxdot.
  now apply logic_and_elim_right_imp, k_classical.
Qed.

Lemma k_box_boxdot_to_boxdot_box :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    k_entailment L -> forall p,
    L (Imp (Box (Boxdot p)) (Boxdot (Box p))).
Proof.
  intros AtomType L HK p; unfold Boxdot.
  exact (k_box_iter_and_distribute HK 1 p (Box p)).
Qed.

(** Pointwise boxes commute with normalized finite conjunctions.  Lists are
    duplicate-tolerant enumerations, so these theorems simultaneously cover
    Foundation's list and finite-set presentations without equality tests. *)
Lemma k_box_iter_list_conj2_distribute :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    k_entailment L -> forall n Gamma,
    L (Imp (box_iter n (logic_list_conj2 Gamma))
      (logic_list_conj2 (map (box_iter n) Gamma))).
Proof.
  intros AtomType L HK n Gamma; induction Gamma as [|p Gamma IH]; simpl.
  - apply (logic_classical_tautology (k_classical HK)).
    intro rho; unfold Top, Neg; simpl; tauto.
  - destruct Gamma as [|q Gamma].
    + simpl. now apply logic_identity, k_classical.
    + simpl in IH |- *.
      pose proof (k_classical HK) as Hclass.
      pose proof
        (k_box_iter_and_distribute HK n p
          (logic_list_conj2 (q :: Gamma))) as Hdist.
      apply logic_imp_and_intro; [exact Hclass | |].
      * eapply logic_imp_trans; [exact Hclass | exact Hdist |].
        now apply logic_and_elim_left_imp.
      * eapply logic_imp_trans; [exact Hclass | exact Hdist |].
        eapply logic_imp_trans; [exact Hclass | |exact IH].
        now apply logic_and_elim_right_imp.
Qed.

Lemma k_box_iter_list_conj2_collect :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    k_entailment L -> forall n Gamma,
    L (Imp (logic_list_conj2 (map (box_iter n) Gamma))
      (box_iter n (logic_list_conj2 Gamma))).
Proof.
  intros AtomType L HK n Gamma; induction Gamma as [|p Gamma IH]; simpl.
  - apply logic_imply_intro; [exact (k_classical HK) |].
    exact (k_box_iter_top HK n).
  - destruct Gamma as [|q Gamma].
    + simpl. now apply logic_identity, k_classical.
    + simpl in IH |- *.
      pose proof (k_classical HK) as Hclass.
      set (a := And (box_iter n p)
        (logic_list_conj2 (map (box_iter n) (q :: Gamma)))).
      assert (Hleft : L (Imp a (box_iter n p))).
      { unfold a. now apply logic_and_elim_left_imp. }
      assert (Hright :
          L (Imp a (box_iter n (logic_list_conj2 (q :: Gamma))))).
      { eapply logic_imp_trans; [exact Hclass | |exact IH].
        unfold a. now apply logic_and_elim_right_imp. }
      eapply logic_imp_trans; [exact Hclass | |].
      * exact (logic_imp_and_intro Hclass Hleft Hright).
      * exact (k_box_iter_and_collect HK n p
          (logic_list_conj2 (q :: Gamma))).
Qed.

Lemma k_dia_regularity :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    k_entailment L -> forall p q,
    L (Imp p q) -> L (Imp (Dia p) (Dia q)).
Proof.
  intros AtomType L HK p q Hpq.
  pose proof (k_classical HK) as Hclass.
  unfold Dia.
  apply logic_contraposition; [exact Hclass |].
  apply box_regularity_of_k; [exact HK |].
  now apply logic_contraposition.
Qed.

Lemma k_dia_iter_regularity :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    k_entailment L -> forall n p q,
    L (Imp p q) ->
    L (Imp (dia_iter n p) (dia_iter n q)).
Proof.
  intros AtomType L HK n; induction n as [|n IH]; intros p q Hpq; simpl.
  - exact Hpq.
  - apply k_dia_regularity; [exact HK |]. now apply IH.
Qed.

Lemma k_dia_or_collect :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    k_entailment L -> forall p q,
    L (Imp (Or (Dia p) (Dia q)) (Dia (Or p q))).
Proof.
  intros AtomType L HK p q.
  pose proof (k_classical HK) as Hclass.
  assert (Hleft0 : L (Imp p (Or p q))).
  { apply (logic_classical_tautology Hclass).
    intro rho; unfold Or, Neg; simpl; tauto. }
  assert (Hright0 : L (Imp q (Or p q))).
  { apply (logic_classical_tautology Hclass).
    intro rho; unfold Or, Neg; simpl; tauto. }
  pose proof (k_dia_regularity HK Hleft0) as Hleft.
  pose proof (k_dia_regularity HK Hright0) as Hright.
  eapply (logic_modus_ponens Hclass); [|exact Hright].
  eapply (logic_modus_ponens Hclass); [|exact Hleft].
  apply (logic_classical_tautology Hclass).
  intro rho; unfold Or, Neg; simpl; tauto.
Qed.

Lemma k_dia_or_distribute :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    k_entailment L -> forall p q,
    L (Imp (Dia (Or p q)) (Or (Dia p) (Dia q))).
Proof.
  intros AtomType L HK p q.
  pose proof (k_classical HK) as Hclass.
  assert (Hdm : L (Imp (And (Neg p) (Neg q)) (Neg (Or p q)))).
  { apply (logic_classical_tautology Hclass).
    intro rho; unfold And, Or, Neg; simpl; tauto. }
  pose proof (box_regularity_of_k HK Hdm) as Hreg.
  pose proof (has_C_axiom (has_C_of_k HK) (Neg p) (Neg q)) as Hcollect.
  pose proof (logic_imp_trans Hclass Hcollect Hreg) as Hboth.
  pose proof (logic_contraposition Hclass Hboth) as Hcontra.
  unfold Dia.
  eapply logic_imp_trans; [exact Hclass | exact Hcontra |].
  apply (logic_classical_tautology Hclass).
  intro rho; unfold And, Or, Neg; simpl; tauto.
Qed.

Lemma k_dia_iter_or_collect :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    k_entailment L -> forall n p q,
    L (Imp (Or (dia_iter n p) (dia_iter n q))
      (dia_iter n (Or p q))).
Proof.
  intros AtomType L HK n p q.
  pose proof (k_classical HK) as Hclass.
  assert (Hleft0 : L (Imp p (Or p q))).
  { apply (logic_classical_tautology Hclass).
    intro rho; unfold Or, Neg; simpl; tauto. }
  assert (Hright0 : L (Imp q (Or p q))).
  { apply (logic_classical_tautology Hclass).
    intro rho; unfold Or, Neg; simpl; tauto. }
  pose proof (k_dia_iter_regularity HK n Hleft0) as Hleft.
  pose proof (k_dia_iter_regularity HK n Hright0) as Hright.
  eapply (logic_modus_ponens Hclass); [|exact Hright].
  eapply (logic_modus_ponens Hclass); [|exact Hleft].
  apply (logic_classical_tautology Hclass).
  intro rho; unfold Or, Neg; simpl; tauto.
Qed.

Lemma k_dia_iter_or_distribute :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    k_entailment L -> forall n p q,
    L (Imp (dia_iter n (Or p q))
      (Or (dia_iter n p) (dia_iter n q))).
Proof.
  intros AtomType L HK n; induction n as [|n IH]; intros p q; simpl.
  - now apply logic_identity, k_classical.
  - pose proof (k_classical HK) as Hclass.
    exact (logic_imp_trans Hclass
      (k_dia_regularity HK (IH p q))
      (k_dia_or_distribute HK (dia_iter n p) (dia_iter n q))).
Qed.

Lemma k_dia_and_distribute :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    k_entailment L -> forall p q,
    L (Imp (Dia (And p q)) (And (Dia p) (Dia q))).
Proof.
  intros AtomType L HK p q.
  pose proof (k_classical HK) as Hclass.
  apply logic_imp_and_intro; [exact Hclass | |].
  - apply k_dia_regularity; [exact HK |].
    now apply logic_and_elim_left_imp.
  - apply k_dia_regularity; [exact HK |].
    now apply logic_and_elim_right_imp.
Qed.

Lemma k_dia_iter_and_distribute :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    k_entailment L -> forall n p q,
    L (Imp (dia_iter n (And p q))
      (And (dia_iter n p) (dia_iter n q))).
Proof.
  intros AtomType L HK n; induction n as [|n IH]; intros p q; simpl.
  - now apply logic_identity, k_classical.
  - pose proof (k_classical HK) as Hclass.
    exact (logic_imp_trans Hclass
      (k_dia_regularity HK (IH p q))
      (k_dia_and_distribute HK (dia_iter n p) (dia_iter n q))).
Qed.

Lemma k_not_dia_bottom :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    k_entailment L -> L (Neg (Dia Bottom)).
Proof.
  intros AtomType L HK.
  pose proof (k_classical HK) as Hclass.
  unfold Dia, Top.
  change (L (Neg (Neg (Box (Neg Bottom))))).
  eapply (logic_modus_ponens Hclass).
  - apply (logic_iff_elim_left Hclass).
    exact (logic_double_neg_iff Hclass (Box (Neg Bottom))).
  - change (L (Box Top)). exact (k_box_iter_top HK 1).
Qed.

Lemma k_not_dia_iter_bottom :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    k_entailment L -> forall n,
    L (Neg (dia_iter n Bottom)).
Proof.
  intros AtomType L HK n; induction n as [|n IH]; simpl.
  - change (L Top). now apply logic_mem_top, k_classical.
  - exact (logic_imp_trans (k_classical HK)
      (k_dia_regularity HK IH) (k_not_dia_bottom HK)).
Qed.

(** EMCN.lean, forward instance. *)
Lemma k_entailment_of_EMCN :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    emcn_entailment L -> k_entailment L.
Proof.
  intros AtomType L HEMCN.
  pose proof (emcn_EMC HEMCN) as HEMC.
  pose proof (em_E (emc_EM HEMC)) as HE.
  constructor.
  - exact (e_classical HE).
  - apply necessitation_of_EN.
    constructor; [exact HE | exact (emcn_N HEMCN)].
  - now apply has_K_of_EMC.
  - exact (e_dia_duality HE).
Qed.

(** EMCN.lean, reverse instance. *)
Lemma EMCN_of_k_entailment :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    k_entailment L -> emcn_entailment L.
Proof.
  intros AtomType L HK.
  pose proof (e_entailment_of_k HK) as HE.
  pose proof (box_regularity_of_k HK) as Hreg.
  pose proof (EM_of_E_box_regularity HE Hreg) as HEM.
  constructor.
  - constructor; [exact HEM | now apply has_C_of_k].
  - apply has_N_of_necessitation.
    + now apply logic_mem_top, k_classical.
    + exact (k_necessitation HK).
Qed.

(** * AxiomGeach.lean *)

Definition geach_dual (g : geach_tuple) : geach_tuple :=
  {| geach_i := geach_j g;
     geach_j := geach_i g;
     geach_m := geach_n g;
     geach_n := geach_m g |}.

Lemma has_Geach_dual :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    e_entailment L -> forall g,
    has_Geach g L -> has_Geach (geach_dual g) L.
Proof.
  intros AtomType L HE [i j m n] HG; constructor; intro p.
  pose proof (e_classical HE) as Hclass.
  pose proof (has_Geach_axiom HG (Neg p)) as Horig.
  unfold Geach, geach_dual in Horig |- *; simpl in Horig |- *.
  pose proof (logic_contraposition Hclass Horig) as Hcontra.

  pose proof (multiDiaDuality HE j (box_iter n p)) as Hdj.
  pose proof (boxItrDuality HE n p) as Hbn.
  pose proof (logic_neg_iff Hclass Hbn) as Hnegbn.
  pose proof (logic_double_neg_iff_rev Hclass
    (dia_iter n (Neg p))) as Hdnen.
  pose proof (logic_iff_trans Hclass Hnegbn Hdnen) as Hinnerj.
  pose proof (multire_raw HE j Hinnerj) as Hboxj.
  pose proof (logic_neg_iff Hclass Hboxj) as Hnegboxj.
  pose proof (logic_imp_trans Hclass
    (logic_iff_elim_left Hclass Hdj)
    (logic_iff_elim_left Hclass Hnegboxj)) as Hpre.

  pose proof (multiDiaDuality HE i (box_iter m (Neg p))) as Hdi.
  pose proof (logic_neg_iff Hclass Hdi) as Hnegdi.
  pose proof (logic_double_neg_iff_rev Hclass
    (box_iter i (Neg (box_iter m (Neg p))))) as Hdnei.
  pose proof (logic_iff_trans Hclass Hnegdi Hdnei) as Hcollapse.
  pose proof (multiDiaDuality HE m p) as Hm.
  pose proof (logic_iff_sym Hclass Hm) as Hmsym.
  pose proof (multire_raw HE i Hmsym) as Hboxi.
  pose proof (logic_imp_trans Hclass
    (logic_iff_elim_left Hclass Hcollapse)
    (logic_iff_elim_left Hclass Hboxi)) as Hpost.

  exact (logic_imp_trans Hclass
    (logic_imp_trans Hclass Hpre Hcontra) Hpost).
Qed.

Lemma axiom_T_dual_raw :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    e_entailment L -> has_T L -> forall p, L (Imp p (Dia p)).
Proof.
  intros AtomType L HE HT p.
  set (g := {| geach_i := 0; geach_j := 0;
               geach_m := 1; geach_n := 0 |}).
  assert (HG : has_Geach g L).
  { constructor; intro q; unfold g, Geach; simpl.
    exact (has_T_axiom HT q). }
  pose proof (has_Geach_dual HE HG) as HD.
  exact (has_Geach_axiom HD p).
Qed.

Definition axiom_T_dual := @axiom_T_dual_raw.

Lemma axiom_Four_dual_raw :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    e_entailment L -> has_Four L -> forall p,
    L (Imp (Dia (Dia p)) (Dia p)).
Proof.
  intros AtomType L HE HFour p.
  set (g := {| geach_i := 0; geach_j := 2;
               geach_m := 1; geach_n := 0 |}).
  assert (HG : has_Geach g L).
  { constructor; intro q; unfold g, Geach, Four; simpl.
    exact (has_Four_axiom HFour q). }
  pose proof (has_Geach_dual HE HG) as HD.
  exact (has_Geach_axiom HD p).
Qed.

Definition axiom_Four_dual := @axiom_Four_dual_raw.

Lemma axiom_Five_dual_raw :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    e_entailment L -> has_Five L -> forall p,
    L (Imp (Dia (Box p)) (Box p)).
Proof.
  intros AtomType L HE HFive p.
  set (g := {| geach_i := 1; geach_j := 1;
               geach_m := 0; geach_n := 1 |}).
  assert (HG : has_Geach g L).
  { constructor; intro q; unfold g, Geach, Five; simpl.
    exact (has_Five_axiom HFive q). }
  pose proof (has_Geach_dual HE HG) as HD.
  exact (has_Geach_axiom HD p).
Qed.

Definition axiom_Five_dual := @axiom_Five_dual_raw.
