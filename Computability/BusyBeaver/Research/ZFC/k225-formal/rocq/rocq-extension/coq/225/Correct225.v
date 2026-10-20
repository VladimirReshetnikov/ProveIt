(** Closed endpoint for the sparse-label 225-state runtime. *)
From Undecidability.FOL Require Import Sets.minZF Deduction.FullNDFacts.
From K225F Require TM230 Sim230Main.
From K225F Require Import Source225.
From K230P Require Import Main230.
From K230S Require Import KQuotZFC.
From K230L Require Import Seed230 Consistency230.

Theorem tm225_sparse_halts_iff_ZFC_inconsistent :
  K225F.TM230.TM230.halts K225F.TM230.tm K225F.TM230.TM230.c0
  <-> StandardZFC ⊢TC ⊥.
Proof.
  rewrite K225F.Sim230Main.tm230_rm, p225_p230, prog230, seed230_iff_thm.
  exact thm230_iff_standardZFC.
Qed.
Corollary tm225_sparse_nonhalting_iff_ZFC_consistent :
  (~ K225F.TM230.TM230.halts K225F.TM230.tm K225F.TM230.TM230.c0)
  <-> ~(StandardZFC ⊢TC ⊥).
Proof. rewrite tm225_sparse_halts_iff_ZFC_inconsistent. reflexivity. Qed.
Print Assumptions tm225_sparse_halts_iff_ZFC_inconsistent.
Print Assumptions tm225_sparse_nonhalting_iff_ZFC_consistent.
