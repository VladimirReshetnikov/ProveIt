(** Closed endpoint for the sparse-label 218-state runtime. *)
From Undecidability.FOL Require Import Sets.minZF Deduction.FullNDFacts.
From K218F Require TM230 Sim230Main.
From K218F Require Import Source218 Main219.
From K230S Require Import KQuotZFC.

Theorem tm218_sparse_halts_iff_ZFC_inconsistent :
  K218F.TM230.TM230.halts K218F.TM230.tm K218F.TM230.TM230.c0
  <-> StandardZFC ⊢TC ⊥.
Proof.
  rewrite K218F.Sim230Main.tm230_rm, p218_dag219.
  exact dag219_iff_standardZFC.
Qed.
Corollary tm218_sparse_nonhalting_iff_ZFC_consistent :
  (~ K218F.TM230.TM230.halts K218F.TM230.tm K218F.TM230.TM230.c0)
  <-> ~(StandardZFC ⊢TC ⊥).
Proof. rewrite tm218_sparse_halts_iff_ZFC_inconsistent. reflexivity. Qed.
Print Assumptions tm218_sparse_halts_iff_ZFC_inconsistent.
Print Assumptions tm218_sparse_nonhalting_iff_ZFC_consistent.
