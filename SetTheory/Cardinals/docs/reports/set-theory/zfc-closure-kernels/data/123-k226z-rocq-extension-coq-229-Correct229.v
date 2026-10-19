(** Exact 229-row sparse-label endpoint, using unchanged K230 source and logic. *)
From Undecidability.FOL Require Import Sets.minZF Deduction.FullNDFacts.
From K230F Require TM230 Sim230Main.
From K230P Require Import Main230.
From K230S Require Import KQuotZFC.
From K230L Require Import Seed230 Consistency230.

Theorem tm229_sparse_halts_iff_ZFC_inconsistent :
  K230F.TM230.TM230.halts K230F.TM230.tm K230F.TM230.TM230.c0
  <-> StandardZFC ⊢TC ⊥.
Proof.
  rewrite K230F.Sim230Main.tm230_rm, prog230, seed230_iff_thm.
  exact thm230_iff_standardZFC.
Qed.

Corollary tm229_sparse_nonhalting_iff_ZFC_consistent :
  (~ K230F.TM230.TM230.halts K230F.TM230.tm K230F.TM230.TM230.c0)
  <-> ~(StandardZFC ⊢TC ⊥).
Proof. rewrite tm229_sparse_halts_iff_ZFC_inconsistent. reflexivity. Qed.

Print Assumptions tm229_sparse_halts_iff_ZFC_inconsistent.
Print Assumptions tm229_sparse_nonhalting_iff_ZFC_consistent.
