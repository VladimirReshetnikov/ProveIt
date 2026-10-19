(** Closed endpoint for the sparse-label 226-state runtime. *)
From Undecidability.FOL Require Import Sets.minZF Deduction.FullNDFacts.
From K226F Require TM230 Sim230Main.
From K226F Require Import Source226.
From K230P Require Import Main230.
From K230S Require Import KQuotZFC.
From K230L Require Import Seed230 Consistency230.

Theorem tm226_sparse_halts_iff_ZFC_inconsistent :
  K226F.TM230.TM230.halts K226F.TM230.tm K226F.TM230.TM230.c0
  <-> StandardZFC ⊢TC ⊥.
Proof.
  rewrite K226F.Sim230Main.tm230_rm, p226_p230, prog230, seed230_iff_thm.
  exact thm230_iff_standardZFC.
Qed.
Corollary tm226_sparse_nonhalting_iff_ZFC_consistent :
  (~ K226F.TM230.TM230.halts K226F.TM230.tm K226F.TM230.TM230.c0)
  <-> ~(StandardZFC ⊢TC ⊥).
Proof. rewrite tm226_sparse_halts_iff_ZFC_inconsistent. reflexivity. Qed.
Print Assumptions tm226_sparse_halts_iff_ZFC_inconsistent.
Print Assumptions tm226_sparse_nonhalting_iff_ZFC_consistent.
