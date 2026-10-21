(** The 218's Main219.v (SHA256 df64be24173ad6768f3d6cb8a9a6b4a34bfb804142c4440037f8af4c1461bdd7) for dagPerm, from R0p. *)
(** Main222.v (SHA256 f8291fb4a06656bbaf8210abd8d844fda93eaccbe1f642997d62c86d56aa6067) renamed for dagPerm. *)
(** * MainPerm: the structured seed-K 222 source halts from the boot register file iff
    StandardZFC is inconsistent.  As Elliot Glazer's [Main230], with dagPerm and [thm222]. *)
From Stdlib Require Import List.
From Undecidability.FOL Require Import Sets.minZF Deduction.FullNDFacts.
From K230 Require Import RM RMEquiv Prog230.
From K230P Require Import Bisim230.
From K230S Require Import KQuotZFC.
From K215F Require Import DagPerm ProgLibPerm L2RootPerm EnumPerm L1_CompPerm SeedPerm Complete222 Regs215.
Import ListNotations.

Lemma R0p_enc_seedPerm : approx R0p (enc seedPerm).
Proof. intros i. do 9 (destruct i as [|i]; [reflexivity|]). reflexivity. Qed.

Lemma dagPerm_wf : wf dagPerm.
Proof. apply wf_check_sound. vm_compute. reflexivity. Qed.

Theorem dagPerm_iff_seed : rm_halts dagPerm ([], R0p) <-> L1_CompPerm.halts_from seedPerm.
Proof.
  rewrite (rm_halts_iff_iter _ dagPerm_wf).
  exact (iter_halts_dag seedPerm R0p R0p_enc_seedPerm).
Qed.

Theorem dagPerm_iff_standardZFC : rm_halts dagPerm ([], R0p) <-> StandardZFC ⊢TC ⊥.
Proof. rewrite dagPerm_iff_seed, seedPerm_iff_thm. exact thm222_iff_standardZFC. Qed.

Print Assumptions dagPerm_iff_standardZFC.
