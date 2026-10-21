(** Closed endpoint for the sparse-label 215-state runtime. *)
From Undecidability.FOL Require Import Sets.minZF Deduction.FullNDFacts.
From K215F Require TM230 Sim230Main.
From K215F Require Import Source215 MainPerm.
From K230S Require Import KQuotZFC.

Theorem tm215_sparse_halts_iff_ZFC_inconsistent :
  K215F.TM230.TM230.halts K215F.TM230.tm K215F.TM230.TM230.c0
  <-> StandardZFC ⊢TC ⊥.
Proof.
  rewrite K215F.Sim230Main.tm230_rm, p215_dagPerm.
  exact dagPerm_iff_standardZFC.
Qed.
Corollary tm215_sparse_nonhalting_iff_ZFC_consistent :
  (~ K215F.TM230.TM230.halts K215F.TM230.tm K215F.TM230.TM230.c0)
  <-> ~(StandardZFC ⊢TC ⊥).
Proof. rewrite tm215_sparse_halts_iff_ZFC_inconsistent. reflexivity. Qed.
Print Assumptions tm215_sparse_halts_iff_ZFC_inconsistent.
Print Assumptions tm215_sparse_nonhalting_iff_ZFC_consistent.
