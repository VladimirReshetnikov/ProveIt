(** Closed endpoint for the sparse-label 227-state runtime. *)
From Undecidability.FOL Require Import Sets.minZF Deduction.FullNDFacts.
From K227F Require TM230 Sim230Main.
From K227F Require Import Source227.
From K230P Require Import Main230.
From K230S Require Import KQuotZFC.
From K230L Require Import Seed230 Consistency230.

Theorem tm227_sparse_halts_iff_ZFC_inconsistent :
  K227F.TM230.TM230.halts K227F.TM230.tm K227F.TM230.TM230.c0
  <-> StandardZFC ⊢TC ⊥.
Proof.
  rewrite K227F.Sim230Main.tm230_rm, p227_p230, prog230, seed230_iff_thm.
  exact thm230_iff_standardZFC.
Qed.
Corollary tm227_sparse_nonhalting_iff_ZFC_consistent :
  (~ K227F.TM230.TM230.halts K227F.TM230.tm K227F.TM230.TM230.c0)
  <-> ~(StandardZFC ⊢TC ⊥).
Proof. rewrite tm227_sparse_halts_iff_ZFC_inconsistent. reflexivity. Qed.
Print Assumptions tm227_sparse_halts_iff_ZFC_inconsistent.
Print Assumptions tm227_sparse_nonhalting_iff_ZFC_consistent.
