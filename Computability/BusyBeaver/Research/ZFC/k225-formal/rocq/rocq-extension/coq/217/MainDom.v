(** The 218's Main219.v (SHA256 df64be24173ad6768f3d6cb8a9a6b4a34bfb804142c4440037f8af4c1461bdd7) for dagDom. *)
(** Main222.v (SHA256 f8291fb4a06656bbaf8210abd8d844fda93eaccbe1f642997d62c86d56aa6067) renamed for dagDom. *)
(** * MainDom: the structured seed-K 222 source halts from the boot register file iff
    StandardZFC is inconsistent.  As Elliot Glazer's [Main230], with dagDom and [thm222]. *)
From Stdlib Require Import List.
From Undecidability.FOL Require Import Sets.minZF Deduction.FullNDFacts.
From K230 Require Import RM RMEquiv Prog230.
From K230P Require Import Bisim230.
From K230S Require Import KQuotZFC.
From K217F Require Import DagDom ProgLibDom L2RootDom EnumDom L1_CompDom SeedDom Complete222.
Import ListNotations.

Lemma R0_enc_seed222 : approx R0 (enc seed222).
Proof. intros i. do 9 (destruct i as [|i]; [reflexivity|]). reflexivity. Qed.

Lemma dagDom_wf : wf dagDom.
Proof. apply wf_check_sound. vm_compute. reflexivity. Qed.

Theorem dagDom_iff_seed : rm_halts dagDom ([], R0) <-> L1_CompDom.halts_from seed222.
Proof.
  rewrite (rm_halts_iff_iter _ dagDom_wf).
  exact (iter_halts_dag seed222 R0 R0_enc_seed222).
Qed.

Theorem dagDom_iff_standardZFC : rm_halts dagDom ([], R0) <-> StandardZFC ⊢TC ⊥.
Proof. rewrite dagDom_iff_seed, seed222_iff_thm. exact thm222_iff_standardZFC. Qed.

Print Assumptions dagDom_iff_standardZFC.
