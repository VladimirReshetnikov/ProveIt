(** Main222.v (SHA256 f8291fb4a06656bbaf8210abd8d844fda93eaccbe1f642997d62c86d56aa6067) renamed for dag219. *)
(** * Main219: the structured seed-K 222 source halts from the boot register file iff
    StandardZFC is inconsistent.  As Elliot Glazer's [Main230], with dag219 and [thm222]. *)
From Stdlib Require Import List.
From Undecidability.FOL Require Import Sets.minZF Deduction.FullNDFacts.
From K230 Require Import RM RMEquiv Prog230.
From K230P Require Import Bisim230.
From K230S Require Import KQuotZFC.
From K218F Require Import Dag219 ProgLib219 L2Root219 Enum222 L1_Comp222 Seed222 Complete222.
Import ListNotations.

Lemma R0_enc_seed222 : approx R0 (enc seed222).
Proof. intros i. do 9 (destruct i as [|i]; [reflexivity|]). reflexivity. Qed.

Lemma dag219_wf : wf dag219.
Proof. apply wf_check_sound. vm_compute. reflexivity. Qed.

Theorem dag219_iff_seed : rm_halts dag219 ([], R0) <-> L1_Comp222.halts_from seed222.
Proof.
  rewrite (rm_halts_iff_iter _ dag219_wf).
  exact (iter_halts_dag seed222 R0 R0_enc_seed222).
Qed.

Theorem dag219_iff_standardZFC : rm_halts dag219 ([], R0) <-> StandardZFC ⊢TC ⊥.
Proof. rewrite dag219_iff_seed, seed222_iff_thm. exact thm222_iff_standardZFC. Qed.

Print Assumptions dag219_iff_standardZFC.
