(** Closed endpoint for the sparse-label 221-state runtime. *)
From Undecidability.FOL Require Import Sets.minZF Deduction.FullNDFacts.
From K221F Require TM230 Sim230Main.
From K221F Require Import Source221 Main222.
From K230S Require Import KQuotZFC.

Theorem tm221_sparse_halts_iff_ZFC_inconsistent :
  K221F.TM230.TM230.halts K221F.TM230.tm K221F.TM230.TM230.c0
  <-> StandardZFC ⊢TC ⊥.
Proof.
  rewrite K221F.Sim230Main.tm230_rm, p221_dag222.
  exact dag222_iff_standardZFC.
Qed.
Corollary tm221_sparse_nonhalting_iff_ZFC_consistent :
  (~ K221F.TM230.TM230.halts K221F.TM230.tm K221F.TM230.TM230.c0)
  <-> ~(StandardZFC ⊢TC ⊥).
Proof. rewrite tm221_sparse_halts_iff_ZFC_inconsistent. reflexivity. Qed.
Print Assumptions tm221_sparse_halts_iff_ZFC_inconsistent.
Print Assumptions tm221_sparse_nonhalting_iff_ZFC_consistent.
