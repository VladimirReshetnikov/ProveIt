(**
  Reflexive substitution-free modal entailments.

  This file independently ports the complete active theorem surface of the
  pinned Foundation module [Modal/Entailment/KT.lean].  Foundation's [KT']
  packages K with the diamond presentation [p -> diamond p], whereas [KT]
  packages K with the usual T axiom [box p -> p].  The records below retain
  that distinction without imposing this repository's stronger substitution
  closure requirements.

  Foundation's theorem [reduce_box_in_CAnt!] uses [!] to mark proposition-
  valued theoremhood.  Theoremhood in this Coq layer is already Prop-valued,
  so its source-facing spelling is [reduce_box_in_CAnt_bang].
*)

From Stdlib Require Import Arith.PeanoNat Logic.Classical_Prop.
From FoundationModal Require Import
  Syntax Axioms LogicInfrastructure EntailmentExtensions
  EntailmentNamedExtensions.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

(** * Source-facing capabilities from Entailment/Basic.lean *)

Record kd_entailment {AtomType}
    (L : modal_logic_set AtomType) : Prop := {
  kd_K : k_entailment L;
  kd_D : has_D L
}.

Record kt_entailment {AtomType}
    (L : modal_logic_set AtomType) : Prop := {
  kt_K : k_entailment L;
  kt_T : has_T L
}.

Record kt_prime_entailment {AtomType}
    (L : modal_logic_set AtomType) : Prop := {
  kt_prime_K : k_entailment L;
  kt_prime_DiaTc : has_DiaTc L
}.

(** * KT'.lean namespace: four active instances *)

Lemma has_T_of_KT_prime :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    kt_prime_entailment L -> has_T L.
Proof.
  intros AtomType L HKT'; constructor; intro p; unfold T.
  pose proof (kt_prime_K HKT') as HK.
  pose proof (e_entailment_of_k HK) as HE.
  pose proof (k_classical HK) as Hclass.
  pose proof (ILLNN_raw HE p) as Hbox_dni.
  pose proof (has_DiaTc_axiom (kt_prime_DiaTc HKT') (Neg p))
    as HdiaTc.
  change (L (Imp (Neg p) (Neg (Box (Neg (Neg p)))))) in HdiaTc.
  assert (Hcombine :
      L (Imp (Imp (Box p) (Box (Neg (Neg p))))
          (Imp (Imp (Neg p) (Neg (Box (Neg (Neg p)))))
               (Imp (Box p) p)))).
  { apply (logic_classical_tautology Hclass).
    intro rho; unfold Neg; simpl; tauto. }
  pose proof (logic_modus_ponens Hclass Hcombine Hbox_dni) as Hstep.
  exact (logic_modus_ponens Hclass Hstep HdiaTc).
Qed.

Lemma KT_of_KT_prime :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    kt_prime_entailment L -> kt_entailment L.
Proof.
  intros AtomType L HKT'; constructor.
  - exact (kt_prime_K HKT').
  - now apply has_T_of_KT_prime.
Qed.

Lemma KP_of_KT_prime :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    kt_prime_entailment L -> kp_entailment L.
Proof.
  intros AtomType L HKT'; constructor.
  - exact (kt_prime_K HKT').
  - apply has_P_of_T. now apply has_T_of_KT_prime.
Qed.

Lemma KD_of_KT_prime :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    kt_prime_entailment L -> kd_entailment L.
Proof.
  intros AtomType L HKT'; constructor.
  - exact (kt_prime_K HKT').
  - apply has_D_of_KP. now apply KP_of_KT_prime.
Qed.

(** * KT.lean section: two instances and one theorem *)

Lemma ET_of_KT :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    kt_entailment L -> et_entailment L.
Proof.
  intros AtomType L HKT; constructor.
  - now apply e_entailment_of_k, kt_K.
  - exact (kt_T HKT).
Qed.

Lemma KD_of_KT :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    kt_entailment L -> kd_entailment L.
Proof.
  intros AtomType L HKT; constructor.
  - exact (kt_K HKT).
  - apply has_D_of_ET. now apply ET_of_KT.
Qed.

Lemma reduce_box_in_CAnt_bang :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    kt_entailment L -> forall i n (p : formula AtomType),
    L (Imp (box_iter (i + n) p) (box_iter i p)).
Proof.
  intros AtomType L HKT i n; induction n as [|n IH]; intro p.
  - rewrite Nat.add_0_r. now apply logic_identity, k_classical, kt_K.
  - rewrite Nat.add_succ_r; simpl.
    eapply logic_imp_trans.
    + exact (k_classical (kt_K HKT)).
    + exact (has_T_axiom (kt_T HKT) (box_iter (i + n) p)).
    + exact (IH p).
Qed.
